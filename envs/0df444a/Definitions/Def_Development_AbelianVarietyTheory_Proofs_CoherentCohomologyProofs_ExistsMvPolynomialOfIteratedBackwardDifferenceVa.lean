-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:56:54.436298+00:00
-- url     : https://prove2.me/theorems/054f3833-408f-43ef-aa25-2028b7f2c3b6
-- title:
--   Exists Mv Polynomial Of Iterated Backward Difference Va
-- statement:
--   Definitions and structural lemmas for Exists Mv Polynomial Of Iterated Backward Difference Va, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean

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
open Finset
section Calculus
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
def bwdDiff (g : G) (φ : G → M) : G → M := fun x ↦ φ x - φ (x - g)
def multiDiff {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) : G → M :=
  fun x ↦ ∑ S : Finset ι, (-1 : ℤ) ^ S.card • φ (x - ∑ i ∈ S, g i)
def DiffVanish (n : ℕ) (φ : G → M) : Prop := ∀ g : Fin n → G, multiDiff g φ = 0
theorem multiDiff_apply {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) (x : G) :
    multiDiff g φ x = ∑ S : Finset ι, (-1 : ℤ) ^ S.card • φ (x - ∑ i ∈ S, g i) := rfl
def shiftRep (G M : Type*) [AddCommGroup G] [AddCommGroup M] :
    Multiplicative G →* Module.End ℤ (G → M) where
  toFun g :=
    { toFun := fun φ x ↦ φ (x - g.toAdd)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [sub_sub]
noncomputable def shiftAct (G M : Type*) [AddCommGroup G] [AddCommGroup M] :
    AddMonoidAlgebra ℤ G →ₐ[ℤ] Module.End ℤ (G → M) :=
  AddMonoidAlgebra.lift ℤ _ G (shiftRep G M)
noncomputable def diffElt (g : G) : AddMonoidAlgebra ℤ G := 1 - AddMonoidAlgebra.of' ℤ G g
theorem shiftAct_of (g : G) (φ : G → M) (x : G) :
    shiftAct G M (AddMonoidAlgebra.of' ℤ G g) φ x = φ (x - g) := by
  simp [shiftAct, shiftRep]
theorem of'_add (a b : G) : AddMonoidAlgebra.of' ℤ G (a + b) =
    AddMonoidAlgebra.of' ℤ G a * AddMonoidAlgebra.of' ℤ G b := by
  simp [AddMonoidAlgebra.single_mul_single]
theorem of'_sum {ι : Type*} (s : Finset ι) (g : ι → G) :
    AddMonoidAlgebra.of' ℤ G (∑ i ∈ s, g i) = ∏ i ∈ s, AddMonoidAlgebra.of' ℤ G (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, of'_add, ih]
theorem diffElt_zero : diffElt (0 : G) = 0 := by
  simp [diffElt, AddMonoidAlgebra.one_def]
theorem diffElt_add (a b : G) :
    diffElt (a + b) = diffElt a + diffElt b - diffElt a * diffElt b := by
  simp only [diffElt, of'_add]; ring
theorem diffElt_neg (a : G) : diffElt (-a) = -(AddMonoidAlgebra.of' ℤ G (-a)) * diffElt a := by
  have : AddMonoidAlgebra.of' ℤ G (-a) * AddMonoidAlgebra.of' ℤ G a = 1 := by
    rw [← of'_add]; simp [AddMonoidAlgebra.one_def]
  simp only [diffElt]; linear_combination (-1 : AddMonoidAlgebra ℤ G) * this
theorem multiDiff_eq_shiftAct {ι : Type*} [Fintype ι] (g : ι → G) (φ : G → M) :
    multiDiff g φ = shiftAct G M (∏ i, diffElt (g i)) φ := by
  classical
  ext x
  simp only [diffElt, sub_eq_add_neg]
  rw [prod_one_add, powerset_univ, map_sum, LinearMap.sum_apply, Finset.sum_apply,
    multiDiff_apply]
  refine sum_congr rfl fun S _ ↦ ?_
  rw [prod_neg, ← of'_sum]
  have : (-1 : AddMonoidAlgebra ℤ G) ^ S.card * AddMonoidAlgebra.of' ℤ G (∑ i ∈ S, g i) =
      ((-1 : ℤ) ^ S.card) • AddMonoidAlgebra.of' ℤ G (∑ i ∈ S, g i) := by
    rw [zsmul_eq_mul]; push_cast; rfl
  rw [this, map_smul, LinearMap.smul_apply, Pi.smul_apply, shiftAct_of]
@[simp] theorem multiDiff_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (g : ι → G)
    (φ : G → M) : multiDiff g φ = φ := by
  simp [multiDiff_eq_shiftAct]
noncomputable def diffIdeal (G : Type*) [AddCommGroup G] : Ideal (AddMonoidAlgebra ℤ G) :=
  Ideal.span (Set.range (diffElt : G → _))
theorem diffElt_mem (g : G) : diffElt g ∈ diffIdeal G := Ideal.subset_span ⟨g, rfl⟩
theorem span_diffElt_image {S : Set G} (hS : AddSubgroup.closure S = ⊤) :
    Ideal.span (diffElt '' S) = diffIdeal G := by
  refine le_antisymm (Ideal.span_mono (Set.image_subset_range _ _)) (Ideal.span_le.2 ?_)
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top g
  induction hg using AddSubgroup.closure_induction with
  | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
  | zero => rw [diffElt_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    rw [diffElt_add]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hx hy) (Ideal.mul_mem_left _ _ hy)
  | neg x _ hx => rw [diffElt_neg]; exact Ideal.mul_mem_left _ _ hx
theorem prod_diffElt_mem {ι : Type*} (s : Finset ι) (g : ι → G) :
    ∏ i ∈ s, diffElt (g i) ∈ diffIdeal G ^ s.card := by
  rw [← prod_const]
  exact Ideal.prod_mem_prod fun i _ ↦ diffElt_mem _
theorem shiftAct_eq_zero_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) {n : ℕ}
    {φ : G → M} (h : ∀ g : Fin n → G, (∀ i, g i ∈ S) → multiDiff g φ = 0)
    {r : AddMonoidAlgebra ℤ G} (hr : r ∈ diffIdeal G ^ n) : shiftAct G M r φ = 0 := by
  rw [← span_diffElt_image hS, Ideal.span, Submodule.span_pow] at hr
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨f, rfl⟩ := Set.mem_pow.1 hr
    choose g hg hg' using fun i ↦ (f i).2
    rw [List.prod_ofFn, ← h g hg, multiDiff_eq_shiftAct]
    simp only [hg']
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]
theorem DiffVanish.shiftAct_eq_zero {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    {r : AddMonoidAlgebra ℤ G} (hr : r ∈ diffIdeal G ^ n) : shiftAct G M r φ = 0 :=
  shiftAct_eq_zero_of_generators (S := Set.univ) (by simp) (fun g _ ↦ h g) hr
theorem DiffVanish.multiDiff_update_add {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (i : Fin d) (a b : G) :
    multiDiff (Function.update g i (a + b)) φ =
      multiDiff (Function.update g i a) φ + multiDiff (Function.update g i b) φ := by
  have key : ∀ c : G, ∏ j, diffElt (Function.update g i c j) =
      diffElt c * ∏ j ∈ univ.erase i, diffElt (g j) := fun c ↦ by
    rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  have hm : diffElt a * (diffElt b * ∏ j ∈ univ.erase i, diffElt (g j)) ∈
      diffIdeal G ^ (d + 1) := by
    rw [← key b, pow_succ']
    exact Ideal.mul_mem_mul (diffElt_mem a)
      (by simpa using prod_diffElt_mem univ (Function.update g i b))
  simp only [multiDiff_eq_shiftAct, key]
  rw [diffElt_add, sub_mul, add_mul, mul_assoc, map_sub, map_add, LinearMap.sub_apply,
    h.shiftAct_eq_zero hm, sub_zero, LinearMap.add_apply]
def DiffVanish.form {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ) :
    MultilinearMap ℤ (fun _ : Fin d ↦ G) M :=
  MultilinearMap.mk' (fun g ↦ multiDiff g φ 0)
    (fun g i a b ↦ by exact congrFun (h.multiDiff_update_add g i a b) 0)
    (fun g i c a ↦ by
      exact map_zsmul (AddMonoidHom.mk' (fun a ↦ multiDiff (Function.update g i a) φ 0)
        (fun a b ↦ congrFun (h.multiDiff_update_add g i a b) 0)) c a)
end Calculus
section Polarization
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
end Polarization
section Polynomial
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]
noncomputable def diffTopPoly (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G)
    (φ : G → K) (x : G) : MvPolynomial ι K :=
  ∑ a : Fin d → ι, MvPolynomial.C ((d.factorial : K)⁻¹ * multiDiff (g ∘ a) φ x) *
    ∏ j, MvPolynomial.X (a j)
end Polynomial
end GlobalTheory


