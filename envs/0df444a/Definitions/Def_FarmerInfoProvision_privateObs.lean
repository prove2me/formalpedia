-- Prove2me | Definitions.Def_FarmerInfoProvision_privateObs
-- name    : FarmerInfoProvision_privateObs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:38:21.634734+00:00
-- url     : https://prove2.me/theorems/5e4712e6-984b-4122-aff1-49b12f56f994
-- title:
--   Private observation $s_i=\sqrt\gamma\,u+\xi_i$ (rescaled private signal)
-- statement:
--   The game uses the private observation
--
--   $$
--   s_i=\sqrt\gamma\,u+\xi_i,\qquad \xi_i=Z_{\mathrm{private}\,i}\sim N(0,1).
--   $$
--
--   For $\gamma>0$, $s_i=\sqrt\gamma\,x_i$ is a bijective rescaling of the paper's signal $x_i=u+\epsilon_i$ with $\epsilon_i\sim N(0,1/\gamma)$, so it carries the same information. For $\gamma=0$, $s_i$ is independent of everything else in the model: the farmer has no private information, which is the paper's meaning of $\gamma=0$ ("private signal is not available", p. 9).
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, pp. 8–9

import Mathlib
import Definitions.Def_FarmerInfoProvision_demandShock

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **The private observation `s_i = √γ·u + ξ_i` of farmer `i` (a rescaling of the paper's `x_i`).**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, pp. 8–9: "`x_i = u + ϵ_i`, and the noise `ϵ_i ∼ N(0, σ_f²)`"
(p. 8); "We use `γ ≡ 1/σ_f²` … so that `γ = 0` corresponds to the case when private signal is
not available" (p. 9).

`privateObs M α γ i = √γ · u + Z (privateNoise i)`, with `u = demandShock M α` and
`Z (privateNoise i) ∼ N(0, 1)`.

**Formalization Note.** For `γ > 0`, `s_i = √γ · x_i` with `x_i = u + ϵ_i`,
`ϵ_i = Z (privateNoise i)/√γ ∼ N(0, 1/γ)`: a bijective rescaling of the paper's signal, so it
carries the same information and admits the same strategies. For `γ = 0`, `s_i` is independent
of the demand shock and of every other signal: the farmer has no private information, which
is the paper's reading of `γ = 0`. -/
noncomputable def privateObs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (α γ : ℝ) (i : Fin n) : Ω → ℝ :=
  fun ω => Real.sqrt γ * demandShock M α ω + M.Z (Shock.privateNoise i) ω

end FarmerInfoProvision


