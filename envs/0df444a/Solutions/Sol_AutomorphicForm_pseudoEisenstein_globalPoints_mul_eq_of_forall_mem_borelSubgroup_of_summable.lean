-- Prove2me | solution 1 for AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/eb2e0323-c2d1-55f6-9630-88706cbf87e0

import Definitions.Def_AutomorphicForm_SlabProfile
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped OnePoint

noncomputable section

namespace R1Bruhat

variable {F : Type} [Field F]

def rep : OnePoint F → GL (Fin 2) F
  | ∞ => 1
  | (ξ : F) => gl2Weyl * unipotentGL2 ξ

@[scoped simp] theorem rep_infty : rep (∞ : OnePoint F) = 1 := rfl
@[scoped simp] theorem rep_coe (ξ : F) : rep (ξ : OnePoint F) = gl2Weyl * unipotentGL2 ξ := rfl

def swapAdj (γ : GL (Fin 2) F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![γ 1 1, γ 0 1; γ 1 0, γ 0 0] (by
    rw [Matrix.det_fin_two_of]
    intro h'
    apply γ.det_ne_zero
    rw [Matrix.det_fin_two]
    linear_combination h')

@[scoped simp] theorem swapAdj_apply_00 (γ : GL (Fin 2) F) : swapAdj γ 0 0 = γ 1 1 := rfl
@[scoped simp] theorem swapAdj_apply_01 (γ : GL (Fin 2) F) : swapAdj γ 0 1 = γ 0 1 := rfl
@[scoped simp] theorem swapAdj_apply_10 (γ : GL (Fin 2) F) : swapAdj γ 1 0 = γ 1 0 := rfl
@[scoped simp] theorem swapAdj_apply_11 (γ : GL (Fin 2) F) : swapAdj γ 1 1 = γ 0 0 := rfl

omit [Field F] in
theorem coe_unipotentGL2_inv {R : Type*} [CommRing R] (x : R) :
    (((unipotentGL2 x)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![1, -x; 0, 1] := rfl

theorem mul_unipotent_mul_weyl_apply_one_zero (A : Matrix (Fin 2) (Fin 2) F) (x : F) :
    (A * ((unipotentGL2 x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * ((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 0 = A 1 0 * x + A 1 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [unipotentGL2_coe, gl2Weyl_val]

theorem weyl_mul_unipotent_mul_apply_one_zero (A : Matrix (Fin 2) (Fin 2) F) (ξ : F) :
    (((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * ((unipotentGL2 ξ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * A) 1 0 = A 0 0 + ξ * A 1 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [unipotentGL2_coe, gl2Weyl_val]

theorem weyl_mul_unipotent_mul_apply_one (A : Matrix (Fin 2) (Fin 2) F) (ξ : F) (j : Fin 2) :
    (((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * ((unipotentGL2 ξ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * A) 1 j = A 0 j + ξ * A 1 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases j <;> simp [unipotentGL2_coe, gl2Weyl_val]

variable [DecidableEq F]

theorem rep_mul_mul_inv_mem_borel (γ : GL (Fin 2) F) (P : OnePoint F) :
    rep P * γ * (rep (swapAdj γ • P))⁻¹ ∈ borelSubgroup F := by
  show ((rep P * γ * (rep (swapAdj γ • P))⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  induction P using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : swapAdj γ 1 0 = 0
    · rw [if_pos hc]
      simp only [rep_infty, one_mul, inv_one, mul_one]
      exact hc
    · rw [if_neg hc]
      have hc' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := hc
      simp only [rep_infty, one_mul, rep_coe, mul_inv_rev, gl2Weyl_inv, swapAdj_apply_00, swapAdj_apply_10]
      rw [← mul_assoc, Units.val_mul, Units.val_mul, coe_unipotentGL2_inv,
        show (!![1, -(γ 1 1 / γ 1 0); 0, 1] : Matrix (Fin 2) (Fin 2) F)
          = ((unipotentGL2 (-(γ 1 1 / γ 1 0)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from rfl,
        mul_unipotent_mul_weyl_apply_one_zero]
      change (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * -((γ : Matrix (Fin 2) (Fin 2) F) 1 1
        / (γ : Matrix (Fin 2) (Fin 2) F) 1 0) + (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
      field_simp
      ring
  | coe ξ =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h0 : swapAdj γ 1 0 * ξ + swapAdj γ 1 1 = 0
    · rw [if_pos h0]
      have h0' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := h0
      simp only [rep_infty, inv_one, mul_one, rep_coe]
      rw [Units.val_mul, Units.val_mul, weyl_mul_unipotent_mul_apply_one_zero]
      linear_combination h0'
    · rw [if_neg h0]
      have h0' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := h0
      simp only [rep_coe, mul_inv_rev, gl2Weyl_inv, swapAdj_apply_00, swapAdj_apply_01, swapAdj_apply_10,
        swapAdj_apply_11]
      set t : F := (γ 1 1 * ξ + γ 0 1) / (γ 1 0 * ξ + γ 0 0) with ht
      rw [← mul_assoc, Units.val_mul, Units.val_mul, coe_unipotentGL2_inv,
        show (!![1, -t; 0, 1] : Matrix (Fin 2) (Fin 2) F)
          = (((unipotentGL2 (-t)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from rfl,
        mul_unipotent_mul_weyl_apply_one_zero, Units.val_mul, Units.val_mul,
        weyl_mul_unipotent_mul_apply_one, weyl_mul_unipotent_mul_apply_one]
      rw [ht]
      change ((γ : Matrix (Fin 2) (Fin 2) F) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 0)
          * -(((γ : Matrix (Fin 2) (Fin 2) F) 1 1 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 1)
            / ((γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0))
        + ((γ : Matrix (Fin 2) (Fin 2) F) 0 1 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 1) = 0
      have hX : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
        rw [add_comm, mul_comm]; exact h0'
      rw [show (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0
          = (γ : Matrix (Fin 2) (Fin 2) F) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 0 by ring,
        mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hX]
      ring

section Adelic

variable {F : Type} [Field F] [NumberField F]

def fam (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) : OnePoint F → ℂ :=
  fun P => f (globalPoints (𝓞 F) F (rep P) * x)

theorem globalPoints_unipotentGL2 (ξ : F) :
    globalPoints (𝓞 F) F (unipotentGL2 ξ) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  ext i j
  rw [globalPoints_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem fam_infty (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) : fam f x ∞ = f x := by
  simp [fam]

theorem fam_coe (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) (ξ : F) :
    fam f x ξ = f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) := by
  simp only [fam, rep_coe, map_mul, globalPoints_unipotentGL2]
  rfl

omit [Field F] [NumberField F] in

theorem tsum_onePoint (h : OnePoint F → ℂ) (hs : Summable fun ξ : F => h ξ) :
    ∑' P : OnePoint F, h P = h ∞ + ∑' ξ : F, h ξ := by
  let e : F ⊕ PUnit.{1} ≃ OnePoint F := (Equiv.optionEquivSumPUnit.{0, 0} F).symm
  have h1 : Summable ((h ∘ e) ∘ Sum.inl) := by
    have : (h ∘ e) ∘ Sum.inl = fun ξ : F => h ξ := by
      funext ξ; simp [e]; rfl
    rw [this]; exact hs
  have h2 : Summable ((h ∘ e) ∘ Sum.inr) := Summable.of_finite
  rw [← Equiv.tsum_eq e h]
  have hsplit : ∑' c : F ⊕ PUnit.{1}, (h ∘ e) c = (∑' a : F, (h ∘ e) (Sum.inl a))
      + ∑' b : PUnit.{1}, (h ∘ e) (Sum.inr b) := Summable.tsum_sum h1 h2
  simp only [Function.comp] at hsplit
  rw [hsplit, add_comm]
  congr 1
  rw [tsum_fintype]
  simp [e]
  rfl

omit [Field F] [NumberField F] in

theorem summable_onePoint (h : OnePoint F → ℂ) (hs : Summable fun ξ : F => h ξ) : Summable h := by
  let e : F ⊕ PUnit.{1} ≃ OnePoint F := (Equiv.optionEquivSumPUnit.{0, 0} F).symm
  have h1 : Summable ((h ∘ e) ∘ Sum.inl) := by
    have : (h ∘ e) ∘ Sum.inl = fun ξ : F => h ξ := by
      funext ξ; simp [e]; rfl
    rw [this]; exact hs
  have h2 : Summable ((h ∘ e) ∘ Sum.inr) := Summable.of_finite
  exact (Equiv.summable_iff e).mp (h1.hasSum.sum h2.hasSum).summable

theorem pseudoEisenstein_eq_tsum_fam (f : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F)
    (hs : Summable fun ξ : F => f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)) :
    pseudoEisenstein F f x = ∑' P : OnePoint F, fam f x P := by
  have hs' : Summable fun ξ : F => fam f x ξ := by simpa only [fam_coe] using hs
  rw [tsum_onePoint _ hs', fam_infty, pseudoEisenstein_apply]
  simp only [fam_coe]

theorem fam_globalPoints_mul [DecidableEq F] (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : ∀ b ∈ borelSubgroup F, ∀ y : AdelicGL2 (𝓞 F) F, f (globalPoints (𝓞 F) F b * y) = f y)
    (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F) (P : OnePoint F) :
    fam f (globalPoints (𝓞 F) F γ * x) P = fam f x (swapAdj γ • P) := by
  have hb := rep_mul_mul_inv_mem_borel γ P
  have hdec : rep P * γ = (rep P * γ * (rep (swapAdj γ • P))⁻¹) * rep (swapAdj γ • P) := by
    rw [inv_mul_cancel_right]
  unfold fam
  rw [← mul_assoc, ← map_mul, hdec, map_mul, mul_assoc, hf _ hb]

theorem pseudoEisenstein_globalPoints_mul (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : ∀ b ∈ borelSubgroup F, ∀ y : AdelicGL2 (𝓞 F) F, f (globalPoints (𝓞 F) F b * y) = f y)
    (x : AdelicGL2 (𝓞 F) F)
    (hs : Summable fun ξ : F => f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))
    (γ : GL (Fin 2) F) :
    Summable (fun ξ : F => f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)
        * (globalPoints (𝓞 F) F γ * x))) ∧
      pseudoEisenstein F f (globalPoints (𝓞 F) F γ * x) = pseudoEisenstein F f x := by
  classical

  have hsP : Summable (fam f x) := summable_onePoint _ (by simpa only [fam_coe] using hs)

  let σ : Equiv.Perm (OnePoint F) := MulAction.toPerm (swapAdj γ)
  have hfam : fam f (globalPoints (𝓞 F) F γ * x) = fam f x ∘ σ := by
    funext P; exact fam_globalPoints_mul f hf γ x P
  have hsγP : Summable (fam f (globalPoints (𝓞 F) F γ * x)) := by
    rw [hfam]; exact (Equiv.summable_iff σ).mpr hsP
  have hsγ : Summable fun ξ : F => f (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      * (globalPoints (𝓞 F) F γ * x)) := by
    have := hsγP.comp_injective OnePoint.coe_injective
    simpa only [Function.comp_def, fam_coe] using this
  refine ⟨hsγ, ?_⟩
  rw [pseudoEisenstein_eq_tsum_fam f _ hsγ, pseudoEisenstein_eq_tsum_fam f _ hs, hfam]
  exact Equiv.tsum_eq σ (fam f x)

end Adelic

end R1Bruhat
p2m_reactivate "P2MW.S_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable.R1Bruhat"

end
p2m_reactivate "P2MW.S_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable.R1Bruhat"

theorem solution
    (F : Type) [Field F] [NumberField F]
    (f : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ)
    (hf : ∀ b ∈ borelSubgroup F, ∀ y : AutomorphicForm.AdelicGL2 (𝓞 F) F,
      f (AutomorphicForm.globalPoints (𝓞 F) F b * y) = f y)
    (x : AutomorphicForm.AdelicGL2 (𝓞 F) F)
    (hs : Summable fun ξ : F =>
      f (AutomorphicForm.adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))
    (γ : GL (Fin 2) F) :
    Summable (fun ξ : F =>
        f (AutomorphicForm.adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)
          * (AutomorphicForm.globalPoints (𝓞 F) F γ * x))) ∧
      AutomorphicForm.pseudoEisenstein F f (AutomorphicForm.globalPoints (𝓞 F) F γ * x)
        = AutomorphicForm.pseudoEisenstein F f x :=
  R1Bruhat.pseudoEisenstein_globalPoints_mul f hf x hs γ

end S_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
end P2MW
export P2MW.S_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable (solution)
