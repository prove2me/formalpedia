-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqUnitaryTransvectionMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:16.494507+00:00
-- url     : https://prove2.me/theorems/9b3c017e-6036-4379-b6b1-bdff04462b2c
-- title:
--   Quasi Reflection Eq Unitary Transvection Mul
-- statement:
--   Definitions and structural lemmas for Quasi Reflection Eq Unitary Transvection Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/QuasiReflectionEqUnitaryTransvectionMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement
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
namespace GlobalTheory.UTrans.Chain
variable {E : Type} [Field E] [CharZero E] {n : ℕ}
end GlobalTheory.UTrans.Chain


