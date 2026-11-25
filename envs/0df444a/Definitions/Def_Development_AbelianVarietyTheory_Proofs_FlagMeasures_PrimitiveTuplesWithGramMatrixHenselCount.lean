-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCount
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCount
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:42.843631+00:00
-- url     : https://prove2.me/theorems/c7066fff-8762-48fa-ab8b-e3364fb69b4a
-- title:
--   Primitive Tuples With Gram Matrix Hensel Count
-- statement:
--   Definitions and structural lemmas for Primitive Tuples With Gram Matrix Hensel Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveTuplesWithGramMatrixHenselCount.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HenselStepCardComap
import Theorems.Thm_GlobalTheory_GramCount_ip_add_left
import Theorems.Thm_GlobalTheory_GramCount_ip_add_right
import Theorems.Thm_GlobalTheory_GramCount_ip_zero_left
import Theorems.Thm_GlobalTheory_GramCount_ip_zero_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
namespace GlobalTheory.GramCount
variable {A : Type} [CommRing A]
def henselHerm (c : A →+* A) (m : ℕ) (q : A) : AddSubgroup (Matrix (Fin m) (Fin m) A) where
  carrier := {H | (∀ a b, c (H b a) = H a b) ∧ ∀ a b, q ∣ H a b}
  zero_mem' := ⟨fun a b => by simp, fun a b => by simp⟩
  add_mem' := fun {H K} hH hK =>
    ⟨fun a b => by simp [Matrix.add_apply, hH.1, hK.1],
      fun a b => by simpa [Matrix.add_apply] using dvd_add (hH.2 a b) (hK.2 a b)⟩
  neg_mem' := fun {H} hH =>
    ⟨fun a b => by simp [Matrix.neg_apply, hH.1],
      fun a b => by simpa [Matrix.neg_apply] using hH.2 a b⟩
def henselGram (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Matrix (Fin m) (Fin m) A :=
  Matrix.of fun a b => ip c (x b) (x a)
def henselDiff (c : A →+* A) {m n : ℕ} (q : A) (x : Fin m → Fin n → A) :
    (Fin m → Fin n → A) →+ Matrix (Fin m) (Fin m) A where
  toFun w := Matrix.of fun a b => q * (ip c (w b) (x a) + ip c (x b) (w a))
  map_zero' := by
    ext a b
    simp [ip_zero_left, ip_zero_right]
  map_add' w w' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, ip_add_left, ip_add_right]
    ring
end GlobalTheory.GramCount


