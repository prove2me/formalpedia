-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:03.107626+00:00
-- url     : https://prove2.me/theorems/a14900ec-fd30-48a9-be35-96a5cee67626
-- title:
--   Unitary Eq Quasi Reflection Mul Transvections
-- statement:
--   Definitions and structural lemmas for Unitary Eq Quasi Reflection Mul Transvections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryEqQuasiReflectionMulTransvections.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryMatrixEqProdQuasiReflectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
namespace GlobalTheory.UTrans.Gen
end GlobalTheory.UTrans.Gen
namespace GlobalTheory.UTrans
end GlobalTheory.UTrans


