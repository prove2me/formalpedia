-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:22.178892+00:00
-- url     : https://prove2.me/theorems/322c0b9d-24df-40b1-8f73-f01a314e5d5d
-- title:
--   Exists Integral Model Of Forms
-- statement:
--   Definitions and structural lemmas for Exists Integral Model Of Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIntegralModelOfForms.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open WeierstrassCurve Polynomial
section Saturation
variable {K : Type*} [Field K]
def powSaturation (S : Subring K) (p : ℕ) : Subring K where
  carrier := {x | ∃ n : ℕ, (p : K) ^ n * x ∈ S}
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨m + n, by convert S.mul_mem hm hn using 1; ring⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    convert S.add_mem (S.mul_mem (S.pow_mem (natCast_mem S p) n) hm)
      (S.mul_mem (S.pow_mem (natCast_mem S p) m) hn) using 1
    ring
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨m, hm⟩
    exact ⟨m, by convert S.neg_mem hm using 1; ring⟩
end Saturation
section Models
variable (A : Type*) [CommRing A] {K : Type*} [Field K] [Algebra A K] [IsIntegrallyClosedIn A K]
variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
end Models
end GlobalTheory


