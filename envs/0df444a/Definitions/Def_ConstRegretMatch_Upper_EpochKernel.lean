-- Prove2me | Definitions.Def_ConstRegretMatch_Upper_EpochKernel
-- name    : ConstRegretMatch_Upper_EpochKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:48.266024+00:00
-- url     : https://prove2.me/theorems/dd8c996a-3b44-446d-b5fb-637486628bb2
-- title:
--   §4.3, p. 21 — the transition kernel of the epoch chain (Q^{t_k}, k ∈ ℕ) of the exhaustive resolving policy
-- statement:
--   Under the exhaustive resolving policy with delay $\tau$, the pre-match queue vectors at the decision epochs form a Markov chain $(Q^{t_k},k\in\mathbb N)$ on $\mathbb Z^n_{\ge0}$. From a state $q$, the policy performs the selected matches, removes the leftovers of $\mathcal Q_+$, and then $\tau$ independent arrivals with law $\lambda$ join. The transition kernel is therefore
--   $$P(q,\cdot)=\sum_{w\in\mathcal A^\tau}\Big(\prod_{s<\tau}\lambda_{w_s}\Big)\,\delta_{\,q^+ + c(w)},$$
--   where $q^+$ is the post-match queue vector of $q$ and $c(w)_i=\#\{s:w_s=i\}$ counts the type-$i$ arrivals in the block $w$.
--
--   Its stationary distributions are the objects of display (11).
--
--   **Formalization Note** The state space `Fin n → ℕ` carries its product σ-algebra, in which every set is measurable (the space is countable with measurable singletons). The kernel is a finite mixture of Dirac masses with weights `ENNReal.ofReal (∏ λ)`; for arrival rates summing to one it is a Markov kernel.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 21, §4.3 (the Markov chain (Q^{t_k}, k ∈ ℕ)); p. 23

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_Resolving

namespace ConstRegretMatch.Upper

open MeasureTheory ProbabilityTheory

variable {n d : ℕ}

/-- The number of type-`i` arrivals in a block `w` of `τ` consecutive arrivals. -/
def blockCount {τ : ℕ} (w : Fin τ → Fin n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun s => w s = i)).card

/-- The transition kernel of the epoch chain `(Q^{t_k}, k ∈ ℕ)` of the exhaustive resolving policy
(§4.3, p. 21) on the state space `ℤ^n_{≥0}` (as `Fin n → ℕ`, discrete σ-algebra): from the pre-match
queue vector `q`, the next pre-match queue vector is `postMatch q + A^τ`, where `A^τ` counts `τ`
i.i.d. arrivals with law `lam`. It is the finite mixture
`P(q, ·) = ∑_{w ∈ (Fin n)^τ} (∏_s λ_{w_s}) δ_{postMatch q + count(w)}`. -/
noncomputable def epochKernel (N : MatchingNetwork n d) (lam : Fin n → ℝ)
    (sel : (Fin n → ℕ) → Fin d → ℕ) (Qp : Finset (Fin n)) (τ : ℕ) :
    Kernel (Fin n → ℕ) (Fin n → ℕ) where
  toFun q := ∑ w : Fin τ → Fin n, ENNReal.ofReal (∏ s, lam (w s)) •
    Measure.dirac (fun i => postMatch N sel Qp q i + blockCount w i)
  measurable' := measurable_of_countable _

end ConstRegretMatch.Upper


