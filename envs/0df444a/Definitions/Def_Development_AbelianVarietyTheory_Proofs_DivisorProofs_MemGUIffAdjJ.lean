-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:39.60786+00:00
-- url     : https://prove2.me/theorems/e14df845-1743-47f5-84a0-87bf744274df
-- title:
--   Mem GUIff Adj J
-- statement:
--   Definitions and structural lemmas for Mem GUIff Adj J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemGUIffAdjJ.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


set_option autoImplicit false
open GlobalTheory.LGrp Formalism.UG
noncomputable section
namespace GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
def upLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → Fin n → ℤ) :
    AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j)}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j h => by simp [hX.1 i j h, hY.1 i j h], fun i j h =>
    Valuation.map_add_le _ (hX.2 i j h) (hY.2 i j h)⟩
  neg_mem' := fun {X} hX => ⟨fun i j h => by simp [hX.1 i j h], fun i j h => by simpa using hX.2 i j h⟩
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in

theorem _root_.GlobalTheory.BorelUMod.mul_mem_upLat {a b c : Fin n → Fin n → ℤ}
    (h : ∀ i j k, i < j → j < k → c i k ≤ a i j + b j k)
    {X Y : Matrix (Fin n) (Fin n) L} (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L a)
    (hY : Y ∈ _root_.GlobalTheory.BorelUMod.upLat L b) : X * Y ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  obtain ⟨hX0, hXv⟩ := hX
  obtain ⟨hY0, hYv⟩ := hY
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · rw [hX0 i k hki, zero_mul]
    · rw [hY0 k j (hji.trans hik.le), mul_zero]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · simp [hX0 i k hki]
    rcases le_or_gt j k with hjk | hkj
    · simp [hY0 k j hjk]
    rw [Valuation.map_mul]
    calc Valued.v (X i k) * Valued.v (Y k j)
        ≤ WithZero.exp (-a i k) * WithZero.exp (-b k j) := mul_le_mul' (hXv i k hik) (hYv k j hkj)
      _ = WithZero.exp (-a i k + -b k j) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-c i j) := WithZero.exp_le_exp.2 (by linarith [h i k j hik hkj])
def adjJ (σ : L →+* L) (X : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := fun i j => σ (X j.rev i.rev)
def skewJ (σ : L →+* L) (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | adjJ σ X = -X}
  zero_mem' := by ext i j; simp [adjJ]
  add_mem' := fun {X Y} hX hY => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    have h2 := congrFun (congrFun hY i) j
    simp only [adjJ, Matrix.neg_apply] at h1 h2
    simp [adjJ, h1, h2, add_comm]
  neg_mem' := fun {X} hX => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    simp only [adjJ, Matrix.neg_apply] at h1
    simp [adjJ, h1]
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_sub (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X - Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X - _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_one (σ : L →+* L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [_root_.GlobalTheory.BorelUMod.adjJ]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.one_apply, h, h']
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in

theorem _root_.GlobalTheory.BorelUMod.mem_GU_iff_adjJ (σ : L →+* L) (g : GL (Fin n) L) :
    g ∈ _root_.Formalism.UG.GU σ n ↔ (g⁻¹).val = _root_.GlobalTheory.BorelUMod.adjJ σ g.val := by
  rw [_root_.GlobalTheory.LGrp.mem_GU_iff]
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mem_upLat {σ : L →+* L}
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ}
    (hc : ∀ i j, c j.rev i.rev = c i j) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) :
    _root_.GlobalTheory.BorelUMod.adjJ σ X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · simp [_root_.GlobalTheory.BorelUMod.adjJ, hX.1 j.rev i.rev (Fin.rev_le_rev.2 hji)]
  · simp only [_root_.GlobalTheory.BorelUMod.adjJ]
    rw [hσ, ← hc i j]
    exact hX.2 j.rev i.rev (Fin.rev_lt_rev.2 hij)
def IsWeight (c : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, c j.rev i.rev = c i j) ∧ ∀ i j k, i < j → j < k → c i k ≤ c i j + c j k
def IsIdealWeight (c C : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, i < j → c i j ≤ C i j) ∧ (∀ i j k, i < j → j < k → C i k ≤ c i j + C j k) ∧
    ∀ i j k, i < j → j < k → C i k ≤ C i j + c j k
def unipLat {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ} (hc : IsWeight c) :
    Subgroup (borelU σ n).U where
  carrier := {u | (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ upLat L c}
  one_mem' := by
    show ((1 : Matrix (Fin n) (Fin n) L)) - 1 ∈ upLat L c
    simp
  mul_mem' := fun {u w} hu hw => by
    show u.1.1.val * w.1.1.val - 1 ∈ upLat L c
    have : u.1.1.val * w.1.1.val - 1 = (u.1.1.val - 1) * (w.1.1.val - 1) + (u.1.1.val - 1) + (w.1.1.val - 1) := by
      noncomm_ring
    rw [this]
    exact add_mem (add_mem (mul_mem_upLat hc.2 hu hw) hu) hw
  inv_mem' := fun {u} hu => by
    show (u.1.1⁻¹).val - 1 ∈ upLat L c
    rw [(mem_GU_iff_adjJ σ _).1 u.1.2, ← adjJ_one σ, ← adjJ_sub]
    exact adjJ_mem_upLat hσ hc.1 hu
end GlobalTheory.BorelUMod


