-- Prove2me | Definitions.Def_FarmerInfoProvision_linearProfile
-- name    : FarmerInfoProvision_linearProfile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:42:36.424885+00:00
-- url     : https://prove2.me/theorems/793e2257-87ec-43be-af9b-eeed05d14418
-- title:
--   Proposition 1's linear strategy profile (6)
-- statement:
--   Proposition 1's equilibrium, written as functions of the observations, with coefficients (7) at $n_1=|I|$:
--
--   $$
--   q_i=A_0+A_1x_i+A_2y\quad(i\in I),\qquad q_j=B_0+B_1x_j\quad(j\notin I),
--   $$
--
--   where $x_i=s_i/\sqrt\gamma$ is recovered from the private observation.
--
--   **Formalization Note** At $\gamma=0$ the value $s/\sqrt0=0$ is junk but is multiplied by $A_1=B_1=0$, so uninformed farmers produce the constant $A_0$ and informed ones $A_0+A_2y$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (6), p. 12

import Mathlib
import Definitions.Def_FarmerInfoProvision_coefA0
import Definitions.Def_FarmerInfoProvision_coefA1
import Definitions.Def_FarmerInfoProvision_coefA2
import Definitions.Def_FarmerInfoProvision_coefB1

namespace FarmerInfoProvision

/-- **Proposition 1's linear strategy profile (6), in the observation variables.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (6), p. 12:
"`q_i(x_i, y) = A0 + A1 x_i + A2 y`, `∀i ∈ I`, `q_j(x_j) = B0 + B1 x_j`, `∀j ∈ J`", with the
coefficients (7) at `n1 = |I|`.

`linearProfile a b c n α β γ I i (s, t)` is `A0 + A1·(s/√γ) + A2·t` for `i ∈ I` and
`A0 + B1·(s/√γ)` for `i ∉ I`, where `n1 = |I|`.

**Formalization Note.** The game's private observation is `s_i = √γ·x_i` (see `privateObs`), so
`s/√γ = x_i` for `γ > 0`. At `γ = 0` the value `s/√0 = 0` is junk, but it is multiplied by
`A1 = B1 = 0`, so the profile is the constant `A0` for uninformed farmers and `A0 + A2·y` for
informed ones. `B0` is written `coefA0` since `A0 = B0` by (7). -/
noncomputable def linearProfile (a b c : ℝ) (n : ℕ) (α β γ : ℝ) (I : Finset (Fin n)) :
    Fin n → ℝ × ℝ → ℝ :=
  fun i p =>
    if i ∈ I then
      coefA0 a b c n + coefA1 b n I.card α β γ * (p.1 / Real.sqrt γ) +
        coefA2 b n I.card α β γ * p.2
    else
      coefA0 a b c n + coefB1 b n I.card α β γ * (p.1 / Real.sqrt γ)

end FarmerInfoProvision


