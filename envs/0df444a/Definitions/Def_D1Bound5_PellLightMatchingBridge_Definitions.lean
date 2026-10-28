-- Prove2me | Definitions.Def_D1Bound5_PellLightMatchingBridge_Definitions
-- name    : D1Bound5_PellLightMatchingBridge_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:53:23.820756+00:00
-- url     : https://prove2.me/theorems/c3b89ae8-4252-43d1-a110-402cc4144190
-- title:
--   Pell Light Matching Bridge
-- statement:
--   Definitions for pell light matching bridge in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `pellLightMasksToOriginal`. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/PellLightMatchingBridge.lean, lines 6-7, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 9-12, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 14-17, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 19-33, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 35-43, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 45-57, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 59-70, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 72-80, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e; D1Bound5/PellLightMatchingBridge.lean, lines 82-86, SHA-256 3af9720af80ec1c3ef20365df808d156ab2bd101049dc40f988188fc0fca462e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellLightMatching_Definitions
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions

section
namespace D1Bound5

def pellLightMasksToOriginal (m : PellLightSquareMasks) : PellSquareMasks :=
  ⟨m.k, m.ordinary, m.scaled⟩

theorem pellLightMatching_intCast_val (k : ℕ) (z : ℤ) :
    (z : ZMod (k + 1)).val = (z % Int.ofNat (k + 1)).toNat := by
  simpa only [Int.toNat_natCast, Int.ofNat_eq_natCast] using
    congrArg Int.toNat (ZMod.val_intCast (n := k + 1) z)

theorem pellLightScalarMaskBool_eq (k mask : ℕ) (z : ℤ) :
    pellLightScalarMaskBool k mask z = pellScalarMaskBool k mask z := by
  unfold pellLightScalarMaskBool pellScalarMaskBool
  rw [pellLightMatching_intCast_val]

theorem pellLightScalarMaskValidBool_iff (c : ℤ) (k mask : ℕ) :
    pellLightScalarMaskValidBool c k mask = true ↔ PellScalarMaskValid c k mask := by
  constructor
  · intro h r
    have hr : r.val ∈ List.range (k + 1) := List.mem_range.mpr (ZMod.val_lt r)
    have hh := (List.all_eq_true.mp h) r.val hr
    rw [pellLightScalarMaskBool_eq] at hh
    simpa only [pellScalarMaskBool, Int.ofNat_eq_natCast, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_zmod_val] using hh
  · intro h
    apply List.all_eq_true.mpr
    intro r _
    rw [pellLightScalarMaskBool_eq]
    simpa only [pellScalarMaskBool, Int.ofNat_eq_natCast, Int.cast_mul, Int.cast_natCast] using
      h (r : ZMod (k + 1))

theorem pellLightSelectMasks_eq (ms : List PellLightSquareMasks) (n : ℕ) :
    pellLightMasksToOriginal (pellLightSelectMasks ms n) =
      pellSelectMasks (ms.map pellLightMasksToOriginal) n := by
  induction ms generalizing n with
  | nil => rfl
  | cons m ms ih =>
      cases n with
      | zero => rfl
      | succ n => exact ih n

theorem pellLightPairChecks_eq (ms : List PellLightSquareMasks) (x : ℤ)
    (ys : List ℤ) (ws : List (ℕ × ℕ)) :
    pellLightPairChecks ms x ys ws =
      pellPairChecks (ms.map pellLightMasksToOriginal) x ys ws := by
  induction ys generalizing ws with
  | nil => cases ws <;> rfl
  | cons y ys ih =>
      cases ws with
      | nil => rfl
      | cons w ws =>
          simp only [pellLightPairChecks, pellPairChecks]
          simp only [← pellLightSelectMasks_eq]
          simp only [pellLightMasksToOriginal, pellLightScalarMaskBool_eq, ih]

theorem pellLightMatchingCheck_eq (ms : List PellLightSquareMasks)
    (xs : List ℤ) (wss : List (List (ℕ × ℕ))) :
    pellLightMatchingCheck ms xs wss =
      pellMatchingCheck (ms.map pellLightMasksToOriginal) xs wss := by
  induction xs generalizing wss with
  | nil => cases wss <;> rfl
  | cons x xs ih =>
      cases wss with
      | nil => rfl
      | cons ws wss =>
          simp only [pellLightMatchingCheck, pellMatchingCheck,
            pellLightPairChecks_eq, ih]

theorem pellLightMasks_valid (d : ℤ) (ms : List PellLightSquareMasks)
    (h : (ms.all fun m => m.validBool d) = true) :
    ∀ m ∈ ms.map pellLightMasksToOriginal, m.Valid d := by
  intro m hm
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
  have hh := (List.all_eq_true.mp h) u hu
  have hp := Bool.and_eq_true_iff.mp hh
  exact ⟨(pellLightScalarMaskValidBool_iff 1 u.k u.ordinary).mp hp.1,
    (pellLightScalarMaskValidBool_iff d u.k u.scaled).mp hp.2⟩

theorem pellLightMagnitudes_large (xs : List ℤ)
    (h : (xs.all fun x => decide (2 ≤ x)) = true) :
    ∀ x ∈ xs, 2 ≤ x := by
  intro x hx
  exact of_decide_eq_true ((List.all_eq_true.mp h) x hx)



end D1Bound5
end


