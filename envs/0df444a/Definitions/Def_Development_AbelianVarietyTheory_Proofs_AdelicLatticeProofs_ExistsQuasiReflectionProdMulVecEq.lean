-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEq
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuasiReflectionProdMulVecEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:46.436474+00:00
-- url     : https://prove2.me/theorems/7b646ce7-2343-4685-8c4b-3a3743157dce
-- title:
--   Exists Quasi Reflection Prod Mul Vec Eq
-- statement:
--   Definitions and structural lemmas for Exists Quasi Reflection Prod Mul Vec Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuasiReflectionProdMulVecEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
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
namespace GlobalTheory.UnRep.ReflStep
variable {F E : Type} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
end GlobalTheory.UnRep.ReflStep


