-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaxPrincipleWeightedFiniteTypeInt
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaxPrincipleWeightedFiniteTypeInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:08.059824+00:00
-- url     : https://prove2.me/theorems/d40b11c0-ec77-4cfd-92a7-3fb0ad1e5d89
-- title:
--   Local Max Principle Weighted Finite Type Int
-- statement:
--   Definitions and structural lemmas for Local Max Principle Weighted Finite Type Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaxPrincipleWeightedFiniteTypeInt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaximumPrincipleWeightFiniteMvPolynomialStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory
noncomputable def ratExtPoint {B : Type} [CommRing B] (x : B →+* ℂ) : ℚ ⊗[ℤ] B →+* ℂ :=
  (Algebra.TensorProduct.lift (algebraMap ℚ ℂ).toIntAlgHom x.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom
end GlobalTheory


