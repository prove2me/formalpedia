-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThickFibIsPullback
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThickFibIsPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:05.285361+00:00
-- url     : https://prove2.me/theorems/beb9fe8b-8be4-4a57-81d5-f72bdf4c0984
-- title:
--   Thick Fib Is Pullback
-- statement:
--   Definitions and structural lemmas for Thick Fib Is Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThickFibIsPullback.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace GlobalTheory.SpecialConn
variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))
abbrev thickQ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.mk _
def thickR (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1 + 1) →+* O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
theorem thickR_comp (n : ℕ) : (thickR O n).comp (thickQ O (n + 1)) = thickQ O n := rfl
def thickFib (n : ℕ) : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (thickQ O n)))
def thickι (n : ℕ) : thickFib f n ⟶ Y := pullback.fst _ _
def thickStr (n : ℕ) : thickFib f n ⟶ Spec (.of (O ⧸ IsLocalRing.maximalIdeal O ^ (n + 1))) :=
  pullback.snd _ _
def thickTr (n : ℕ) : thickFib f n ⟶ thickFib f (n + 1) :=
  pullback.map _ _ _ _ (𝟙 Y) (Spec.map (CommRingCat.ofHom (thickR O n))) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, thickR_comp])
end GlobalTheory.SpecialConn


