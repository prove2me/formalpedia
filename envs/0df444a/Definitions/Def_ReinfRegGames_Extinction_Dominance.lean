-- Prove2me | Definitions.Def_ReinfRegGames_Extinction_Dominance
-- name    : ReinfRegGames_Extinction_Dominance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:16:06.871175+00:00
-- url     : https://prove2.me/theorems/bd7ad5a5-8027-4e2a-b0e6-d91d1f096880
-- title:
--   Proof of Theorem 4.1, p. 18 — the pure strategies $\mathcal A^r_k$ surviving $r$ rounds of iterated strict dominance
-- statement:
--   For a finite game with payoff functions $u_k$, define for each round $r\ge0$ and each player $k$ the set $\mathcal A^r_k\subseteq\mathcal A_k$ of pure strategies that survive $r$ rounds of iterated elimination of strictly dominated strategies:
--
--   $$
--   \mathcal A^0_k=\mathcal A_k,\qquad
--   \mathcal A^{r+1}_k=\Bigl\{\alpha\in\mathcal A^r_k:\ \text{there is no } p'_k\in\Delta(\mathcal A^r_k)\text{ with } u_k(\alpha;z_{-k})<u_k(p'_k;z_{-k})\ \text{for all } z\in\textstyle\prod_\ell\Delta(\mathcal A^r_\ell)\Bigr\}.
--   $$
--
--   In words: at each round, a surviving pure strategy is removed when some mixed strategy supported on the surviving strategies of the same player earns strictly more against every mixed profile supported on the surviving strategies of all players. This is the dominance relation (4.1) of p. 16, applied in the restriction of the game to the survivors, and the sets $\mathcal A^r_k$ are the sets of surviving pure strategies used in the induction of the proof of Theorem 4.1.
--
--   A mixed strategy is iteratively dominated when, at some round $r$, it is supported on $\mathcal A^r_k$ and is strictly dominated, against every profile supported on the $r$-survivors, by another mixed strategy supported on $\mathcal A^r_k$. A strategy that survives all rounds is iteratively undominated.
--
--   **Formalization Note** The page defines the survivors only inside the proof of Theorem 4.1, as mixed strategy sets $\mathcal X^r_k$ with $\mathcal A^r_k=\mathcal A_k\cap\mathcal X^r_k$. This definition records the pure survivors directly; every mixed survivor is supported on pure survivors, and dominance against profiles in $\prod_\ell\mathcal X^r_\ell$ is equivalent, by multilinearity, to dominance against profiles supported on $\prod_\ell\mathcal A^r_\ell$. The dominating strategy is allowed to be any lottery supported on $\mathcal A^r_k$. Profiles are mixed profiles in the sense of `agt_games` whose nonzero entries lie in the survivor sets.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 16, (4.1) and the paragraph on iteratively dominated strategies; p. 18, proof of Theorem 4.1 (the sets X^r_k, A^r_k)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.Extinction

/-- The pure strategies of player `k` that survive `r` rounds of iterated elimination of
strictly dominated strategies, the sets `A^r_k` of the proof of Theorem 4.1
(arXiv:1407.6267v2, p. 18). Round `0` keeps every pure strategy. A pure strategy `α` that
survives `r` rounds survives round `r + 1` unless some mixed strategy `p'` of player `k`
supported on the `r`-survivors strictly beats `α` against every mixed profile `z` supported on
the `r`-survivors (dominance (4.1), p. 16, in the restriction of the game to the survivors). -/
def survivors {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) : ℕ → ∀ k, Set (A k)
  | 0 => fun _ => Set.univ
  | r + 1 => fun k =>
      {α | α ∈ survivors u r k ∧
        ¬ ∃ p' : A k → ℝ, AGT.IsLottery p' ∧ (∀ β, p' β ≠ 0 → β ∈ survivors u r k) ∧
          ∀ z : ∀ ℓ, A ℓ → ℝ, AGT.IsMixedProfile z →
            (∀ ℓ β, z ℓ β ≠ 0 → β ∈ survivors u r ℓ) →
            payoffVec u z k α < AGT.expectedPayoff u (Function.update z k p') k}

end ReinfRegGames.Extinction


