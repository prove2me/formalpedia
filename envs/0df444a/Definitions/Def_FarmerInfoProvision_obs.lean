-- Prove2me | Definitions.Def_FarmerInfoProvision_obs
-- name    : FarmerInfoProvision_obs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:12.978349+00:00
-- url     : https://prove2.me/theorems/2a304834-d400-44c1-876e-478102f180e1
-- title:
--   Observation of farmer $i$ when the set $I$ is informed
-- statement:
--   When the central planner gives the public signal to the set $I$ of farmers ($|I|=n_1$), farmer $i$ observes
--
--   $$
--   \mathrm{obs}_I(i)=\begin{cases}(s_i,\,y) & i\in I,\\ (s_i,\,0) & i\notin I,\end{cases}
--   $$
--
--   where $s_i$ is the private observation and $y$ the public signal. An uninformed farmer's second coordinate is the constant $0$, so her strategy is in effect a function of her private observation only.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, pp. 9–11

import Mathlib
import Definitions.Def_FarmerInfoProvision_publicSignal
import Definitions.Def_FarmerInfoProvision_privateObs

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **What farmer `i` observes when the set `I` of farmers receives the public signal.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, pp. 9–11: "farmers in set `I` who gain information access and
farmers in set `J` who do not have access. Therefore, `|I| = n1` and `|I| + |J| = n`" (p. 9);
"Each farmer `i` receives the public signal along with his private signal `x_i` … and each
farmer in set `J` receives only his private signal `x_j`" (p. 11).

`obs M α β γ I i ω = (s_i ω, y ω)` if `i ∈ I`, and `(s_i ω, 0)` if `i ∉ I`, where `s_i` is the
private observation (`privateObs`) and `y` the public signal (`publicSignal`).

**Formalization Note.** The second coordinate of an uninformed farmer is the constant `0`, so a
strategy of an uninformed farmer is in effect a function of `s_j` alone. -/
noncomputable def obs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (α β γ : ℝ) (I : Finset (Fin n)) (i : Fin n) :
    Ω → ℝ × ℝ :=
  fun ω => (privateObs M α γ i ω, if i ∈ I then publicSignal M α β ω else 0)

end FarmerInfoProvision


