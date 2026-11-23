-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalMatrixIdentityTransferToComplexMap
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RationalMatrixIdentityTransferToComplexMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:45.925275+00:00
-- url     : https://prove2.me/theorems/25367186-acd6-437d-ad72-c89e34e391f5
-- title:
--   Rational Matrix Identity Transfer To Complex Map
-- statement:
--   Definitions and structural lemmas for Rational Matrix Identity Transfer To Complex Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RationalMatrixIdentityTransferToComplexMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory
noncomputable def endRealMatrixRingHom {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Module.End ℂ (Fin g → ℂ) →+* Matrix (Fin n) (Fin n) ℝ where
  toFun f := LinearMap.toMatrix e e (f.restrictScalars ℝ)
  map_one' := by
    have : ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 := rfl
    rw [this]; exact LinearMap.toMatrix_one e
  map_mul' f h := by
    have : ((f * h).restrictScalars ℝ) = f.restrictScalars ℝ * h.restrictScalars ℝ := rfl
    rw [this]; exact LinearMap.toMatrix_mul e _ _
  map_zero' := by
    have : ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 := rfl
    rw [this]; exact map_zero _
  map_add' f h := by
    have : ((f + h).restrictScalars ℝ) = f.restrictScalars ℝ + h.restrictScalars ℝ := rfl
    rw [this]; exact map_add _ _ _
end GlobalTheory


