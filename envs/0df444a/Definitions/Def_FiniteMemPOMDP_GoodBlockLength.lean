-- Prove2me | Definitions.Def_FiniteMemPOMDP_GoodBlockLength
-- name    : FiniteMemPOMDP_GoodBlockLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:08.704262+00:00
-- url     : https://prove2.me/theorems/d34ff1ff-f1b4-49c4-aff3-4fe3948a2459
-- title:
--   Block length $n_0$ chosen in §6.4
-- statement:
--   Let $\varepsilon>0$. A block length $n_0\ge1$ is **good** if for every class $i$, every occurring super-support $\mathcal D^j$ and every $k\in\mathcal D^j_i$,
--
--   $$\mathbb E^k_{\sigma[h^j]}\Big(\frac1{n_0}\sum_{m=1}^{n_0}G_m\Big)\ge\gamma^i_\infty-\varepsilon .$$
--
--   **Formalization Note** The quantifier over $j$ is a quantifier over histories $h$ of positive $\mathbb P^{p^*}_\sigma$-probability with $\mathcal D=B(h)$ and $h^j=$ `rep D`; classes are indexed by their value $c$.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §6.4, p.18

import Mathlib
import Definitions.Def_FiniteMemPOMDP_superSupp
import Definitions.Def_FiniteMemPOMDP_shift

open MeasureTheory

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [DecidableEq K] [Fintype A] [Fintype S] [Nonempty A]
  [Nonempty S]

/-- **The block length `n0` of §6.4.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §6.4, p.18: "Let ε > 0. By Lemma 6.5, there
exists n0 ∈ N∗ such that for all i ∈ [1 .. I], j ∈ [1 .. J] and k ∈ D^j_i,
E^k_{σ[hj]} ( (1/n0) ∑_{m=1}^{n0} Gm ) ≥ γ^i_∞ − ε."

`GoodBlockLength Γ p σ rep ε n0` says that `n0 ≥ 1` and, for every super-support `D = B(h)` that
occurs (`P^p_σ(H = h) > 0`), every class value `c` and every `k ∈ D_c`, the expected average reward
over the first `n0` stages of the shifted strategy `σ[rep D]` started from `k` is at least `c − ε`.

**Formalization Note** The quantifier over `j ∈ [1 .. J]` (the occurring super-supports) is
written as a quantifier over histories of positive probability and their super-supports
`D = superSuppTuple Γ p σ h`; `h^j` is `rep D`. -/
def GoodBlockLength (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (rep : (ℝ → Set K) → List (A × S)) (ε : ℝ) (n0 : ℕ) : Prop :=
  1 ≤ n0 ∧
    ∀ h : List (A × S), 0 < historyProb Γ p σ h → ∀ c : ℝ, ∀ k ∈ superSuppTuple Γ p σ h c,
      c - ε ≤ ∫ ω, avgReward Γ n0 ω
        ∂(lawOfPlays Γ (pointBelief k) (shift σ (rep (superSuppTuple Γ p σ h))))

end FiniteMemPOMDP


