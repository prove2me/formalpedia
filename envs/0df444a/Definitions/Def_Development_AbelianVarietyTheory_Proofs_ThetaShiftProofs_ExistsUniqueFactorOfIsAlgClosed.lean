-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:53.336102+00:00
-- url     : https://prove2.me/theorems/338c52b8-176d-489f-b3e1-5bbef3057095
-- title:
--   Exists Unique Factor Of Is Alg Closed
-- statement:
--   Definitions and structural lemmas for Exists Unique Factor Of Is Alg Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsUniqueFactorOfIsAlgClosed.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory.FixedPoint
universe u v w
section Algebra
variable {K₀ : Type u} {K₁ : Type v} {L : Type w} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
end Algebra
section Scheme
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
end Scheme
end GlobalTheory.FixedPoint


