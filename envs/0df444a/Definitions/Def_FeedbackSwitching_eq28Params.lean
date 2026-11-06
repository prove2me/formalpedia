-- Prove2me | Definitions.Def_FeedbackSwitching_eq28Params
-- name    : FeedbackSwitching_eq28Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:08.780564+00:00
-- url     : https://prove2.me/theorems/32d7880b-0618-448b-9eae-68317ac9dd7b
-- title:
--   Parameters of Eq. (28): $H=1/(8\kappa)$, $\delta=(KT)^{-20}$, $M=100\log(2/\delta)$, $\eta=\kappa/(2^{25}Mm\Lambda)$; $\kappa_\star$ and $m$
-- statement:
--   With $\Lambda=\log(eKT)$ and $\kappa=2^{-m}$, Algorithm 1 is run with
--   $$
--   H=\frac1{8\kappa},\qquad\delta=(KT)^{-20},\qquad M=100\log\frac2\delta,\qquad\eta=\frac{\kappa}{2^{25}Mm\Lambda},\qquad\varepsilon=\frac1T .
--   $$
--   For the regret bound, $\kappa_\star=\Lambda\sqrt{\log K/T}$ and $m=\lfloor\log_2(1/\kappa_\star)\rfloor$.
--
--   **Formalization Note** $H=2^{m-3}$ as a natural number (an integer for $m\ge3$).
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), §4.6, Eq. (28), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_FeedbackSwitching_rateLaw

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

`Λ = log(eKT)` (§4.6, p.23 = PDF p.25). -/
noncomputable def bigLambda (K T : ℕ) : ℝ :=
  Real.log (Real.exp 1 * K * T)

/-- `δ = (KT)^{−20}` (Eq. (28)). -/
noncomputable def eq28Delta (K T : ℕ) : ℝ :=
  (((K : ℝ) * T) ^ 20)⁻¹

/-- Score threshold `M = 100 log(2/δ)` (Eq. (28)). -/
noncomputable def eq28M (K T : ℕ) : ℝ :=
  100 * Real.log (2 / eq28Delta K T)

/-- Learning rate `η = κ / (2^{25} M m Λ)` with `κ = 2^{−m}` (Eq. (28)). -/
noncomputable def eq28Eta (K T m : ℕ) : ℝ :=
  baseRate m / (2 ^ 25 * eq28M K T * m * bigLambda K T)

/-- **The parameters of Eq. (28)**, p.23: block length `H = 1/(8κ)` with `κ = 2^{−m}`, i.e.
`H = 2^{m−3}` (an integer for `m ≥ 3`; the paper uses `m ≥ 5`). The other parameters of (28) are
`eq28Delta`, `eq28M`, `eq28Eta` above, and the smoothing `ε = 1/T`. -/
def eq28H (m : ℕ) : ℕ :=
  2 ^ (m - 3)

/-- `κ⋆ = Λ √(log K / T)` (§4.6, p.23). -/
noncomputable def kappaStar (K T : ℕ) : ℝ :=
  bigLambda K T * Real.sqrt (Real.log K / T)

/-- `m = ⌊log₂(1/κ⋆)⌋` (§4.6, p.23), so that `κ = 2^{−m}` satisfies `κ⋆ ≤ κ < 2κ⋆`. -/
noncomputable def tsExponent (K T : ℕ) : ℕ :=
  ⌊Real.logb 2 (1 / kappaStar K T)⌋₊

end FeedbackSwitching


