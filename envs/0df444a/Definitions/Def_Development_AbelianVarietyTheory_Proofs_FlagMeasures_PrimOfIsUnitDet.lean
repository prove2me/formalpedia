-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:41.94626+00:00
-- url     : https://prove2.me/theorems/00ce5753-00f1-4aff-8515-c000dc23f730
-- title:
--   Prim Of Is Unit Det
-- statement:
--   Definitions and structural lemmas for Prim Of Is Unit Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.GramCount
variable {A : Type} [CommRing A]
def ip (c : A →+* A) {n : ℕ} (x y : Fin n → A) : A := ∑ i, x i * c (y i)
def Prim (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Prop :=
  ∃ y : Fin m → Fin n → A, ∀ a b, ip c (x a) (y b) = if a = b then 1 else 0
def sols (c : A →+* A) {m : ℕ} (n : ℕ) (G : Matrix (Fin m) (Fin m) A) :
    Set (Fin m → Fin n → A) :=
  {x | Prim c x ∧ ∀ a b, ip c (x b) (x a) = G a b}
variable (c : A →+* A) {n : ℕ}
end GlobalTheory.GramCount


