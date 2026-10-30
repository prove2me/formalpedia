-- Prove2me | Definitions.Def_FarmerInfoProvision_Admissible
-- name    : FarmerInfoProvision_Admissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:40:19.979634+00:00
-- url     : https://prove2.me/theorems/66bbc93b-a994-4a10-a342-013620d1eb10
-- title:
--   Admissible strategies (measurable, square-integrable quantities)
-- statement:
--   A strategy $g:\mathbb R^2\to\mathbb R$ of farmer $i$ under the informed set $I$ is *admissible* when $g$ is Borel measurable and the quantity $g(\mathrm{obs}_I(i))$ is square integrable.
--
--   **Formalization Note** The paper takes expectations of profits without stating an integrability condition. Square integrability is exactly what makes every expected profit $\mathbb E[(a-bQ+u-c)q_i]$ well defined (the demand shock is Gaussian), so no non-integrable deviation receives Lean's junk expectation $0$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, problems (2)–(3), p. 10

import Mathlib
import Definitions.Def_FarmerInfoProvision_obs

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **Admissible strategies: measurable functions of the farmer's observation with square
integrable output.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, problems (2)–(3), p. 10: farmer `i ∈ I` chooses `q_i` given
"`x_i, y`", farmer `j ∈ J` given "`x_j`".

`Admissible M α β γ I i g` holds when `g : ℝ × ℝ → ℝ` is Borel measurable and the quantity
`ω ↦ g (obs M α β γ I i ω)` is in `L²(P)`.

**Formalization Note.** The paper takes expectations of profits without stating an
integrability condition; square integrability is exactly what makes every expected profit
`E[(a − bQ + u − c) q_i]` well defined (the demand shock is Gaussian), so that no
non-integrable deviation gets Lean's junk value `0` for its expectation. -/
def Admissible {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (α β γ : ℝ) (I : Finset (Fin n)) (i : Fin n)
    (g : ℝ × ℝ → ℝ) : Prop :=
  Measurable g ∧ MemLp (fun ω => g (obs M α β γ I i ω)) 2 P

end FarmerInfoProvision


