-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:05.290002+00:00
-- url     : https://prove2.me/theorems/6833d42a-6365-4e51-8117-8030f3f3e953
-- title:
--   Row Data Adapted Chain Data
-- statement:
--   Definitions and structural lemmas for Row Data Adapted Chain Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
namespace GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => ha.mul_int hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => ha.neg
def admitted (V : VF C) (Q : Finset I) (P : Matrix I I C) : Prop :=
  (∀ c x, V.Ge 0 (P c x)) ∧ V.v P.det = 0 ∧ (∀ c, c ∉ Q → ∀ x, P c x = if x = c then 1 else 0) ∧
    ∀ c ∈ Q, ∀ x, x ∉ Q → P c x = 0
theorem isAdmissibleIntegralBasisChange_one (Q : Finset I) : admitted V Q (1 : Matrix I I C) := by
  refine ⟨fun c x => ?_, by simp, fun c _ x => by simp [Matrix.one_apply, eq_comm], fun c hc x hx => ?_⟩
  · rw [Matrix.one_apply]; split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · exact Matrix.one_apply_ne (fun h => hx (h ▸ hc))
theorem elim_one (Q : Finset I) (a : I → C) : ∃ (P : Matrix I I C) (Q' : Finset I), admitted V Q P ∧ Q' ⊆ Q ∧
    Q.card ≤ Q'.card + 1 ∧ ∀ c ∈ Q', ∑ x, P c x * a x = 0 := by
  by_cases h0 : ∀ c ∈ Q, a c = 0
  · refine ⟨1, Q, isAdmissibleIntegralBasisChange_one Q, subset_rfl, by omega, fun c hc => ?_⟩
    simp [Matrix.one_apply, h0 c hc]
  push_neg at h0
  obtain ⟨c1, hc1, ha1⟩ := h0
  obtain ⟨c0, hc0, hmin⟩ := Q.exists_min_image (fun c => V.v (a c)) ⟨c1, hc1⟩
  have ha0 : a c0 ≠ 0 := by
    intro h
    have := hmin c1 hc1
    simp only [h, V.v.map_zero, top_le_iff] at this
    exact ha1 (by simpa using this)
  have hint : ∀ c ∈ Q, V.Ge 0 (a c / a c0) := by
    intro c hc
    have h1 := hmin c hc
    have h2 : V.v (a c) = V.v (a c / a c0) + V.v (a c0) := by
      rw [← V.v.map_mul, div_mul_cancel₀ _ ha0]
    have h3 : V.v (a c0) ≠ ⊤ := by simpa using ha0
    rw [h2] at h1
    unfold VF.Ge
    have : (0 : WithTop ℝ) + V.v (a c0) ≤ V.v (a c / a c0) + V.v (a c0) := by simpa using h1
    exact (WithTop.add_le_add_iff_right h3).mp this
  set col : I → C := fun c => if c = c0 then 1 else if c ∈ Q then -(a c / a c0) else 0 with hcol
  refine ⟨Matrix.updateCol 1 c0 col, Q.erase c0, ⟨?_, ?_, ?_, ?_⟩, Finset.erase_subset _ _, ?_, ?_⟩
  · intro c x
    rw [Matrix.updateCol_apply]
    split_ifs with h
    · simp only [hcol]
      split_ifs with h1 h2
      · exact VF.Ge.one
      · exact (hint c h2).neg
      · exact VF.Ge.zero 0
    · exact (isAdmissibleIntegralBasisChange_one Q).1 c x
  · rw [← Matrix.cramer_apply, Matrix.cramer_one]
    simp [hcol]
  · intro c hc x
    have : c ≠ c0 := fun h => hc (h ▸ hc0)
    rw [Matrix.updateCol_apply]
    by_cases h : x = c0
    · subst h; simp [hcol, this, hc, this.symm]
    · simp [h, Matrix.one_apply, eq_comm]
  · intro c hc x hx
    have : x ≠ c0 := fun h => hx (h ▸ hc0)
    rw [Matrix.updateCol_apply, if_neg this]
    exact Matrix.one_apply_ne (fun h => hx (h ▸ hc))
  · rw [Finset.card_erase_of_mem hc0]; omega
  · intro c hc
    obtain ⟨hne, hcQ⟩ := Finset.mem_erase.mp hc
    have : ∀ x, Matrix.updateCol (1 : Matrix I I C) c0 col c x * a x =
        (if x = c0 then -(a c) else 0) + (if x = c then a c else 0) := by
      intro x
      rw [Matrix.updateCol_apply]
      by_cases h : x = c0
      · subst h; simp [hcol, hne, hcQ, hne.symm, ha0]
      · by_cases h' : x = c
        · subst h'; simp [h]
        · simp [h, h', Matrix.one_apply_ne (Ne.symm h')]
    simp only [this, Finset.sum_add_distrib]
    simp
theorem admitted.mul {Q Q' : Finset I} (hQ : Q' ⊆ Q) {P P' : Matrix I I C} (h : admitted V Q P)
    (h' : admitted V Q' P') : admitted V Q (P' * P) := by
  refine ⟨fun c x => ?_, ?_, fun c hc x => ?_, fun c hc x hx => ?_⟩
  · rw [Matrix.mul_apply]; exact VF.Ge.sum fun y _ => (h'.1 _ _).mul_int (h.1 _ _)
  · rw [Matrix.det_mul, V.v.map_mul, h.2.1, h'.2.1, add_zero]
  · rw [Matrix.mul_apply]
    simp only [h'.2.2.1 c (fun hh => hc (hQ hh))]
    simp [h.2.2.1 c hc x]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : y ∈ Q
    · rw [h.2.2.2 y hy x hx, mul_zero]
    · by_cases hc' : c ∈ Q'
      · rw [h'.2.2.2 c hc' y (fun hh => hy (hQ hh)), zero_mul]
      · rw [h'.2.2.1 c hc' y, if_neg (fun hh : y = c => hy (hh ▸ hc)), zero_mul]
theorem elim {M : Type} (Q : Finset I) (a : I → M → C) (E : Finset M) :
    ∃ (P : Matrix I I C) (Q' : Finset I), admitted V Q P ∧ Q' ⊆ Q ∧
    Q.card ≤ Q'.card + E.card ∧ ∀ c ∈ Q', ∀ e ∈ E, ∑ x, P c x * a x e = 0 := by
  induction E using Finset.induction_on with
  | empty => exact ⟨1, Q, isAdmissibleIntegralBasisChange_one Q, subset_rfl, by simp, by simp⟩
  | insert e E he ih =>
    obtain ⟨P, Q1, hP, h1, hc1, hz⟩ := ih
    obtain ⟨P', Q2, hP', h2, hc2, hz'⟩ := elim_one (V := V) Q1 (fun y => ∑ x, P y x * a x e)
    refine ⟨P' * P, Q2, hP.mul h1 hP', h2.trans h1, by rw [Finset.card_insert_of_notMem he]; omega, ?_⟩
    intro c hc e' he'
    have key : ∑ x, (P' * P) c x * a x e' = ∑ y, P' c y * ∑ x, P y x * a x e' := by
      simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [key]
    rcases Finset.mem_insert.mp he' with rfl | he'
    · exact hz' c hc
    · refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y ∈ Q1
      · rw [hz y hy e' he', mul_zero]
      · rw [hP'.2.2.2 c (h2 hc) y hy, zero_mul]
variable {X : Cart V d I J}
def Stable (V : VF C) (L : AddSubgroup (I → C)) : Prop := ∀ r, V.Ge 0 r → ∀ u ∈ L, r • u ∈ L
def intSpan (V : VF C) {ι : Type} [Fintype ι] (U : ι → I → C) : AddSubgroup (I → C) where
  carrier := {u | ∃ A : ι → C, (∀ b, V.Ge 0 (A b)) ∧ ∀ x, u x = ∑ b, A b * U b x}
  zero_mem' := ⟨0, fun _ => VF.Ge.zero 0, by simp⟩
  add_mem' := by
    rintro u u' ⟨A, h1, h2⟩ ⟨A', h1', h2'⟩
    exact ⟨A + A', fun b => (h1 b).add (h1' b), fun x => by
      simp [h2, h2', add_mul, Finset.sum_add_distrib]⟩
  neg_mem' := by
    rintro u ⟨A, h1, h2⟩
    exact ⟨-A, fun b => (h1 b).neg, fun x => by simp [h2]⟩
end GlobalTheory.AdaptedChain


