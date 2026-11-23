-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:50.443644+00:00
-- url     : https://prove2.me/theorems/8875de6f-7231-4b55-8327-4dfdabf29167
-- title:
--   Stabilizer Fixes Frame Vector
-- statement:
--   Definitions and structural lemmas for Stabilizer Fixes Frame Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/StabilizerFixesFrameVector.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
end Gen
end PI.VolSemiDirect.W


