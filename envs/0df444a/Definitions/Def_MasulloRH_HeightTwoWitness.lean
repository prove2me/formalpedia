-- Prove2me | Definitions.Def_MasulloRH_HeightTwoWitness
-- name    : MasulloRH_HeightTwoWitness
-- status  : Definition
-- author  : @sflicht
-- created : 2026-11-21T19:18:11.467153+00:00
-- url     : https://prove2.me/theorems/d1967a7a-bf7f-42bd-8ad5-820a7680a39d
-- title:
--   An explicit eleven-term rational theta candidate at height two
-- statement:
--   Define eleven rational coefficients and their paired shifts by
--
--   $$a=(271/100,-51/10,863/100,-299/25,729/50,-1003/100,201/50,-53/20,191/100,-101/100,37/100),$$
--
--   $$y=(-3/8,-1/4,1/8,3/8,3/4,1,11/8,7/4,2,9/4,19/8).$$
--
--   The entries are indexed in this order by $0,\ldots,10$. Their canonical complex and real embeddings supply inputs for the mission's residual $p_2(x)-\sum_i a_i\theta(x-y_i)$. This definition stores only the exact rational data and their embeddings. Any assertion about the residual's integrability or energy is a separate theorem.
-- source:
--   Rational candidate constructed for the Prove2Me Masullo RH specialization mission. The earlier external interval experiment is documented in the mission discussion; this definition makes no numerical accuracy or energy assertion. https://prove2.me/missions/Masullo%3A_The_Music_of_the_Primes_%E2%80%94_Riemann_Hypothesis_specialization/discussions

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace MasulloRH.HeightTwoWitness

/-- The eleven exact rational coefficients of the height-two candidate.
This definition is data only and carries no energy or approximation assertion. -/
def coeffsQ : Fin 11 → ℚ :=
  ![271/100, -51/10, 863/100, -299/25, 729/50, -1003/100,
    201/50, -53/20, 191/100, -101/100, 37/100]

/-- The exact rational translates paired with `coeffsQ`. -/
def shiftsQ : Fin 11 → ℚ :=
  ![-3/8, -1/4, 1/8, 3/8, 3/4, 1, 11/8, 7/4, 2, 9/4, 19/8]

/-- The canonical complex casts of the rational coefficients. -/
noncomputable def coeffs : Fin 11 → ℂ := fun i => (coeffsQ i : ℂ)

/-- The canonical real casts of the rational translates. -/
noncomputable def shifts : Fin 11 → ℝ := fun i => (shiftsQ i : ℝ)

end MasulloRH.HeightTwoWitness


