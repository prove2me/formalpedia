-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:36.573831+00:00
-- url     : https://prove2.me/theorems/b2403ec1-e134-4698-bcd1-e32867568bad
-- title:
--   Unitary Matrix Eq Prod Quasi Reflections
-- statement:
--   Definitions and structural lemmas for Unitary Matrix Eq Prod Quasi Reflections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryMatrixEqProdQuasiReflections.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.UnRep.ReflGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}
end GlobalTheory.UnRep.ReflGen


