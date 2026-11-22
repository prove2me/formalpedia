-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:42.663832+00:00
-- url     : https://prove2.me/theorems/f83d16db-ba07-4d82-85dc-554f9c462e72
-- title:
--   Derived
-- statement:
--   Definitions and structural lemmas for Derived, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/Derived.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
namespace PI.UnitaryDenseWork
noncomputable def detPoly {ι : Type} (n : ℕ) (τ : ι) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  Matrix.det (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ))
end PI.UnitaryDenseWork
open PI.UnitaryDenseWork


