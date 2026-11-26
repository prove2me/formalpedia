-- Prove2me | Definitions.Def_Malliavin_Symmetrization
-- name    : Malliavin_Symmetrization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:41:49.341864+00:00
-- url     : https://prove2.me/theorems/915511d7-85e1-43b8-aeec-58c07238ef0d
-- title:
--   Symmetrization
-- statement:
--   Definitions and structural lemmas for Symmetrization, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
namespace Malliavin
variable {T : Type*} {E : Type*}
def IsSymmetric (n : ℕ) (f : (Fin n → T) → E) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (t : Fin n → T), f (t ∘ σ) = f t
section Algebra
variable [AddCommGroup E] [Module ℝ E]
def symmetrize (n : ℕ) (f : (Fin n → T) → E) : (Fin n → T) → E :=
  fun t => ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), f (t ∘ σ)
theorem symmetrize_apply (n : ℕ) (f : (Fin n → T) → E) (t : Fin n → T) :
    symmetrize n f t = ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), f (t ∘ σ) :=
  rfl
theorem symmetrize_add (n : ℕ) (f g : (Fin n → T) → E) :
    symmetrize n (f + g) = symmetrize n f + symmetrize n g := by
  ext t
  simp only [symmetrize_apply, Pi.add_apply, sum_add_distrib, smul_add]
theorem symmetrize_smul (n : ℕ) (c : ℝ) (f : (Fin n → T) → E) :
    symmetrize n (c • f) = c • symmetrize n f := by
  ext t
  simp only [symmetrize_apply, Pi.smul_apply, smul_sum, smul_comm c]
@[simp]
theorem symmetrize_zero (n : ℕ) : symmetrize n (0 : (Fin n → T) → E) = 0 := by
  ext t
  simp only [symmetrize_apply, Pi.zero_apply, sum_const_zero, smul_zero]
def symmetrizeₗ (n : ℕ) : ((Fin n → T) → E) →ₗ[ℝ] ((Fin n → T) → E) where
  toFun := symmetrize n
  map_add' := symmetrize_add n
  map_smul' := symmetrize_smul n
@[simp]
theorem symmetrizeₗ_apply (n : ℕ) (f : (Fin n → T) → E) : symmetrizeₗ n f = symmetrize n f :=
  rfl
def symmetricSubmodule (T : Type*) (E : Type*) [AddCommGroup E] [Module ℝ E] (n : ℕ) :
    Submodule ℝ ((Fin n → T) → E) where
  carrier := {f | IsSymmetric n f}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hf hg σ t => by simp only [Pi.add_apply, hf σ t, hg σ t]
  smul_mem' := fun c _ hf σ t => by simp only [Pi.smul_apply, hf σ t]
end Algebra
section Measure
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem measurePreserving_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun t : Fin n → T => t ∘ σ)
      (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => μ) :=
  measurePreserving_arrowCongr' (fun _ : Fin n => μ) (fun _ : Fin n => μ) σ.symm
    (MeasurableEquiv.refl T) (fun _ => MeasurePreserving.id μ)
variable {μ}
variable (E) in
/-- The coordinate-permutation operator `f ↦ f ∘ (· ∘ σ)` on `Lp E p μ^{⊗n}`, as a continuous
linear map (it is in fact an isometry, being `Lp.compMeasurePreservingₗᵢ`). -/
def permL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Equiv.Perm (Fin n)) :
    Lp E p (Measure.pi fun _ : Fin n => μ) →L[ℝ] Lp E p (Measure.pi fun _ : Fin n => μ) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun t : Fin n → T => t ∘ σ)
    (measurePreserving_comp_perm μ n σ)).toContinuousLinearMap
variable (E) in
/-- The symmetrization operator on `Lp E p μ^{⊗n}`, as a continuous linear map: the average of
the (isometric) coordinate-permutation operators `permL`. -/
def symmetrizeL (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp E p (Measure.pi fun _ : Fin n => μ) →L[ℝ] Lp E p (Measure.pi fun _ : Fin n => μ) :=
  ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), permL E (μ := μ) n p σ
end Measure
section InnerProduct
variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
end InnerProduct
end Malliavin
end


