-- Prove2me | Definitions.Def_SybilClinch_WeakPO
-- name    : SybilClinch_WeakPO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:33.279202+00:00
-- url     : https://prove2.me/theorems/1c4b8571-aab8-4247-8be9-ccfb61472636
-- title:
--   Weak Pareto optimality for eligible bids
-- statement:
--   Fix an exact-settlement-feasible outcome under truthful reporting. Each eligible user $i$ has post-batch holdings and value coefficient
--   $$(H^X_i,H^Y_i,t_i)=\begin{cases}(R_{X,i},\,Q_i-S_{Y,i},\,V_i)&\text{sell-}Y,\\(R_i-S_{X,i},\,R_{Y,i},\,U_i)&\text{sell-}X,\end{cases}\qquad(7)$$
--   so a change $(\delta x_i,\delta y_i)$ in its holdings changes its utility by $t_i\delta x_i+\delta y_i$. The outcome is **weakly Pareto optimal for eligible bids** if
--
--   1. no subset $J$ of eligible users has an internal trade with $\sum_J\delta x_i=0$, $\sum_J\delta y_i=0$, $\delta x_i\ge-H^X_i$, $\delta y_i\ge-H^Y_i$ that weakly increases $t_i\delta x_i+\delta y_i$ for every $i\in J$ and strictly for one; and
--   2. no eligible user can make a strictly utility-improving trade with the pool in the direction of its type, using its post-batch holding of the token it sells: a sell-$Y$ user buying $r$ units of $X$ pays $\varphi(x_t-r)-\varphi(x_t)\le H^Y_i$ units of $Y$, a sell-$X$ user selling $\delta\le H^X_i$ units of $X$ receives $\varphi(x_t)-\varphi(x_t+\delta)$ units of $Y$, where $x_t=x_0-X_{\rm pool}$ is the terminal $X$ reserve.
--
--   Reverse-direction pool trades are deliberately not counted.
--
--   **Formalization Note** On an exact-settlement-feasible outcome $\varphi(x_t)=y_0+Y_{\rm pool}$, so the pool trade of clause 2 moves along the reserve curve from the terminal reserves.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.3, (7) and Definition 2.7, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_SybilClinch_IsEligible
import Definitions.Def_SybilClinch_flowX

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.3, holdings (7) and Definition 2.7 (Weak Pareto optimality), printed p.8 (PDF p.10).

Under truthful reporting each eligible user `i` has post-batch holdings and value coefficient
`(H^X_i, H^Y_i, tᵢ) = (R_{X,i}, Qᵢ − S_{Y,i}, Vᵢ)` (sell-`Y`) or `(Rᵢ − S_{X,i}, R_{Y,i}, Uᵢ)`
(sell-`X`). The outcome is weakly Pareto optimal for eligible bids if

1. no set `J` of eligible users has an internal trade `(δxᵢ, δyᵢ)_{i∈J}` with
   `Σ δxᵢ = 0`, `Σ δyᵢ = 0`, `δxᵢ ≥ −H^X_i`, `δyᵢ ≥ −H^Y_i` that weakly increases `tᵢδxᵢ + δyᵢ`
   for all `i ∈ J` and strictly for one; and
2. no eligible user can make a strictly utility-improving trade with the pool in the direction of
   its type, using its post-batch holding of the token it sells: a sell-`Y` user buying `r` units of
   `X` from the pool pays `φ(x_t − r) − φ(x_t)` units of `Y` (at most `H^Y_i`); a sell-`X` user
   selling `δ ≤ H^X_i` units of `X` receives `φ(x_t) − φ(x_t + δ)` units of `Y`. Here
   `x_t = x₀ − X_pool` is the terminal `X` reserve.

**Formalization Note.** The definition is applied to exact-settlement-feasible outcomes, where
`φ(x_t) = y₀ + Y_pool` is the terminal `Y` reserve; the pool trade moves along the reserve curve
from the terminal state. -/
def WeakPO (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) (f : ℕ → Fill) : Prop :=
  let HX : ℕ → ℝ := fun i => match (rep i).dir with
    | Dir.sellY => (f i).recv
    | Dir.sellX => (rep i).bud - (f i).sold
  let HY : ℕ → ℝ := fun i => match (rep i).dir with
    | Dir.sellY => (rep i).bud - (f i).sold
    | Dir.sellX => (f i).recv
  let xt : ℝ := A.x0 - flowX ids rep f
  (¬ ∃ (J : Finset ℕ) (δx δy : ℕ → ℝ), J ⊆ ids ∧ (∀ i ∈ J, IsEligible A (rep i)) ∧
      ∑ i ∈ J, δx i = 0 ∧ ∑ i ∈ J, δy i = 0 ∧ (∀ i ∈ J, -HX i ≤ δx i ∧ -HY i ≤ δy i) ∧
      (∀ i ∈ J, 0 ≤ (rep i).val * δx i + δy i) ∧ (∃ i ∈ J, 0 < (rep i).val * δx i + δy i)) ∧
    ∀ i ∈ ids, IsEligible A (rep i) →
      match (rep i).dir with
      | Dir.sellY => ¬ ∃ r : ℝ, 0 < r ∧ r < xt ∧ A.φ (xt - r) - A.φ xt ≤ HY i ∧
          0 < (rep i).val * r - (A.φ (xt - r) - A.φ xt)
      | Dir.sellX => ¬ ∃ δ : ℝ, 0 < δ ∧ δ ≤ HX i ∧
          0 < (A.φ xt - A.φ (xt + δ)) - (rep i).val * δ

end SybilClinch


