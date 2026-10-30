-- Prove2me | Definitions.Def_FarmerInfoProvision_privateSignal
-- name    : FarmerInfoProvision_privateSignal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:37:30.64568+00:00
-- url     : https://prove2.me/theorems/5eaa1357-b480-4e2a-9975-cc879875fd81
-- title:
--   Private signal $x_i=u+\epsilon_i$, $\epsilon_i\sim N(0,1/\gamma)$
-- statement:
--   Farmer $i$'s private signal is $x_i=u+\epsilon_i$ with $\epsilon_i\sim N(0,\sigma_f^2)$ and $\gamma=1/\sigma_f^2$. In terms of the Gaussian primitive, $x_i=u+Z_{\mathrm{private}\,i}/\sqrt\gamma$.
--
--   **Formalization Note** This is meaningful only for $\gamma>0$ and is used only in Lemma 1. At $\gamma=0$ Lean's $x/0=0$ would turn it into $u$ (perfect information), so the game uses the rescaled observation $s_i=\sqrt\gamma\,u+Z_{\mathrm{private}\,i}$ instead.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, pp. 8–9

import Mathlib
import Definitions.Def_FarmerInfoProvision_demandShock

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **The paper's private signal `x_i = u + ϵ_i`, `ϵ_i ∼ N(0, 1/γ)` (for `γ > 0`).**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, pp. 8–9: "each farmer `i` is endowed with a noisy private
signal `x_i` … where: `x_i = u + ϵ_i`, and the noise `ϵ_i ∼ N(0, σ_f²)`, `∀i`" (p. 8); "We use
`γ ≡ 1/σ_f²` to represent the precision of each farmer's estimation" (p. 9).

`privateSignal M α γ i = u + Z (privateNoise i) / √γ`.

**Formalization Note.** This is the paper's `x_i` and is meaningful only for `γ > 0`; it is used
only in Lemma 1, which assumes `γ > 0`. At `γ = 0` Lean's `x/0 = 0` would make it equal to
`u` (perfect information, the opposite of the paper's "no private signal"), so the game itself
uses the rescaled observation `privateObs` instead, which is meaningful at `γ = 0`. -/
noncomputable def privateSignal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (α γ : ℝ) (i : Fin n) : Ω → ℝ :=
  fun ω => demandShock M α ω + M.Z (Shock.privateNoise i) ω / Real.sqrt γ

end FarmerInfoProvision


