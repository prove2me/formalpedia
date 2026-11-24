-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexCharEqOneOfForallCircleChar
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexCharEqOneOfForallCircleChar
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:02.894618+00:00
-- url     : https://prove2.me/theorems/ffcfd7f1-3a3c-4d15-b398-048a0e841fe0
-- title:
--   Complex Char Eq One Of Forall Circle Char
-- statement:
--   Definitions and structural lemmas for Complex Char Eq One Of Forall Circle Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexCharEqOneOfForallCircleChar.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
noncomputable def circArgChar {G : Type} [Group G] (ν : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ), by
    have h : ‖(ν g : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν g).ne_zero
    simp [Submonoid.unitSphere, h]⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' a b := by
    apply Circle.ext
    show ((ν (a * b) : ℂˣ) : ℂ) / (‖((ν (a * b) : ℂˣ) : ℂ)‖ : ℂ) =
      ((ν a : ℂ) / (‖(ν a : ℂ)‖ : ℂ)) * ((ν b : ℂ) / (‖(ν b : ℂ)‖ : ℂ))
    rw [ν.map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
noncomputable def circNormChar {G : Type} [Group G] (ν : G →* ℂˣ) (t : ℝ) : G →* Circle where
  toFun g := Circle.exp (t * Real.log ‖(ν g : ℂ)‖)
  map_one' := by simp
  map_mul' a b := by
    have ha : ‖(ν a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν a).ne_zero
    have hb : ‖(ν b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν b).ne_zero
    show Circle.exp (t * Real.log ‖((ν (a * b) : ℂˣ) : ℂ)‖) = _
    rw [ν.map_mul, Units.val_mul, norm_mul, Real.log_mul ha hb, mul_add, Circle.exp_add]
end GlobalTheory


