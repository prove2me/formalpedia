-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:31.883046+00:00
-- url     : https://prove2.me/theorems/f7b4205c-7f3a-44e8-9f94-2d059673721b
-- title:
--   Exist Gen
-- statement:
--   Definitions and structural lemmas for Exist Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ExistGen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.FJMX
section Deriv
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
end Deriv
section Minor
variable {R : Type*} [CommRing R] {σ : Type*}
def minorPolynomial (R : Type*) [CommRing R] {k : ℕ} (g : Fin k → Fin k → σ) : MvPolynomial σ R :=
  (Matrix.of fun i j => (X (g i j) : MvPolynomial σ R)).det
end Minor
end PI.FJMX


