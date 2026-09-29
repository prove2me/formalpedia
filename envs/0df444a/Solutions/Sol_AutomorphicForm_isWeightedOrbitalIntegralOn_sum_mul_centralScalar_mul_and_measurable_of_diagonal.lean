-- Prove2me | solution 1 for AutomorphicForm.isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7e49d72a-21b7-5056-ab93-7420983cfed3

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Theorems.Thm_AutomorphicForm_IsWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
import Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous
import Theorems.Thm_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField MeasureTheory

namespace BenchLOrbW

open Matrix

section Algebra

variable {A : Type*} [CommRing A]

def cyc (M : Matrix (Fin 2) (Fin 2) A) (a b : A) : Matrix (Fin 2) (Fin 2) A :=
  !![a, M 0 0 * a + M 0 1 * b; b, M 1 0 * a + M 1 1 * b]

private def _root_.BenchLOrbW.comp (t d : A) : Matrix (Fin 2) (Fin 2) A := !![0, -d; 1, t]

p2m_export "BenchLOrbW" "comp"
theorem det_cyc (M : Matrix (Fin 2) (Fin 2) A) (a b : A) :
    (cyc M a b).det = M 1 0 * a ^ 2 + (M 1 1 - M 0 0) * a * b - M 0 1 * b ^ 2 := by
  simp [cyc, Matrix.det_fin_two]; ring

theorem mul_cyc (M : Matrix (Fin 2) (Fin 2) A) (a b : A) :
    M * cyc M a b = cyc M a b * comp M.trace M.det := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc, comp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem discr_eq (M : Matrix (Fin 2) (Fin 2) A) :
    M.trace ^ 2 - 4 * M.det = (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]; ring

theorem exists_conj_eq_comp (M : Matrix (Fin 2) (Fin 2) A) {a b : A} (hu : IsUnit (cyc M a b).det) :
    ∃ P : GL (Fin 2) A, (P : Matrix (Fin 2) (Fin 2) A)⁻¹ * M * P = comp M.trace M.det := by
  have hP : IsUnit (cyc M a b) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
  refine ⟨hP.unit, ?_⟩
  rw [IsUnit.unit_spec, Matrix.mul_assoc, mul_cyc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP), Matrix.one_mul]

theorem exists_conj_of_cyclic (M N : Matrix (Fin 2) (Fin 2) A) {a b a' b' : A}
    (hM : IsUnit (cyc M a b).det) (hN : IsUnit (cyc N a' b').det)
    (htr : N.trace = M.trace) (hdet : N.det = M.det) :
    ∃ P : GL (Fin 2) A, N = (P : Matrix (Fin 2) (Fin 2) A)⁻¹ * M * P := by
  obtain ⟨P, hP⟩ := exists_conj_eq_comp M hM
  obtain ⟨Q, hQ⟩ := exists_conj_eq_comp N hN
  rw [htr, hdet, ← hP] at hQ
  refine ⟨P * Q⁻¹, ?_⟩
  have hQu : IsUnit ((Q : Matrix (Fin 2) (Fin 2) A).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit Q)
  have h1 : N = (Q : Matrix (Fin 2) (Fin 2) A) * ((P : Matrix (Fin 2) (Fin 2) A)⁻¹ * M * P) *
      (Q : Matrix (Fin 2) (Fin 2) A)⁻¹ := by
    rw [← hQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.mul_one]
  rw [h1]
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.mul_inv_rev]
  rw [Matrix.nonsing_inv_nonsing_inv _ hQu]
  simp only [Matrix.mul_assoc]

def Selectable (A : Type*) [CommRing A] : Prop :=
  ∀ a b c r s t : A, r * a + s * b + t * c = 1 →
    ∃ e₁ e₂ e₃ : A, e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧ e₃ * e₃ = e₃ ∧
      e₁ * e₂ = 0 ∧ e₁ * e₃ = 0 ∧ e₂ * e₃ = 0 ∧ IsUnit (e₁ * a + e₂ * b + e₃ * c)

theorem exists_isUnit_det_cyc (hA : Selectable A) (M : Matrix (Fin 2) (Fin 2) A)
    (hM : IsUnit (M.trace ^ 2 - 4 * M.det)) : ∃ a b : A, IsUnit (cyc M a b).det := by
  obtain ⟨u, hu⟩ := hM.exists_left_inv
  rw [discr_eq] at hu

  obtain ⟨e₁, e₂, e₃, h11, h22, h33, h12, h13, h23, hunit⟩ :=
    hA (M 1 0) (-M 0 1) (M 1 0 + (M 1 1 - M 0 0) - M 0 1)
      (-(u * (M 1 1 - M 0 0)) + 4 * u * M 0 1) (-(u * (M 1 1 - M 0 0))) (u * (M 1 1 - M 0 0))
      (by linear_combination hu)
  refine ⟨e₁ + e₃, e₂ + e₃, ?_⟩
  have key : (cyc M (e₁ + e₃) (e₂ + e₃)).det =
      e₁ * M 1 0 + e₂ * (-M 0 1) + e₃ * (M 1 0 + (M 1 1 - M 0 0) - M 0 1) := by
    rw [det_cyc]
    linear_combination (M 1 0) * (h11 + 2 * h13 + h33) +
      (M 1 1 - M 0 0) * (h12 + h13 + h23 + h33) - (M 0 1) * (h22 + 2 * h23 + h33)
  rw [key]
  exact hunit

theorem exists_conj_of_selectable (hA : Selectable A) (M N : Matrix (Fin 2) (Fin 2) A)
    (hM : IsUnit (M.trace ^ 2 - 4 * M.det)) (htr : N.trace = M.trace) (hdet : N.det = M.det) :
    ∃ P : GL (Fin 2) A, N = (P : Matrix (Fin 2) (Fin 2) A)⁻¹ * M * P := by
  have hN : IsUnit (N.trace ^ 2 - 4 * N.det) := by rw [htr, hdet]; exact hM
  obtain ⟨a, b, ha⟩ := exists_isUnit_det_cyc hA M hM
  obtain ⟨a', b', ha'⟩ := exists_isUnit_det_cyc hA N hN
  exact exists_conj_of_cyclic M N ha ha' htr hdet

end Algebra

section Pi

variable {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]

open Classical in
theorem selectable_pi : Selectable (Π i, F i) := by
  intro a b c r s t h
  refine ⟨fun i => if a i ≠ 0 then 1 else 0, fun i => if a i = 0 ∧ b i ≠ 0 then 1 else 0,
    fun i => if a i = 0 ∧ b i = 0 then 1 else 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; simp only [Pi.mul_apply]; split_ifs <;> simp
  · funext i; simp only [Pi.mul_apply]; split_ifs <;> simp
  · funext i; simp only [Pi.mul_apply]; split_ifs <;> simp
  · funext i; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs <;> simp_all
  · funext i; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs <;> simp_all
  · funext i; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs <;> simp_all
  · rw [Pi.isUnit_iff]
    intro i
    have hi := congr_fun h i
    simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply] at hi
    rw [isUnit_iff_ne_zero]
    simp only [Pi.add_apply, Pi.mul_apply]
    by_cases ha : a i = 0
    · by_cases hb : b i = 0
      · have hc : c i ≠ 0 := by
          intro hc; rw [ha, hb, hc] at hi; simp at hi
        simp [ha, hb, hc]
      · simp [ha, hb]
    · simp [ha]

end Pi

section Prod

variable {A B : Type*} [CommRing A] [CommRing B]

theorem selectable_prod (hA : Selectable A) (hB : Selectable B) : Selectable (A × B) := by
  intro a b c r s t h
  obtain ⟨e₁, e₂, e₃, h11, h22, h33, h12, h13, h23, hu⟩ :=
    hA a.1 b.1 c.1 r.1 s.1 t.1 (by simpa using congrArg Prod.fst h)
  obtain ⟨f₁, f₂, f₃, g11, g22, g33, g12, g13, g23, gu⟩ :=
    hB a.2 b.2 c.2 r.2 s.2 t.2 (by simpa using congrArg Prod.snd h)
  refine ⟨(e₁, f₁), (e₂, f₂), (e₃, f₃), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try (ext <;> simp [*])
  rw [Prod.isUnit_iff]
  exact ⟨by simpa using hu, by simpa using gu⟩

end Prod

section FiniteAdele

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

open scoped RestrictedProduct

section Coe
variable {R K}
variable (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R)
theorem fa_zero_apply : (0 : FiniteAdeleRing R K) v = 0 := rfl
theorem fa_one_apply : (1 : FiniteAdeleRing R K) v = 1 := rfl
theorem fa_add_apply : (x + y) v = x v + y v := rfl
theorem fa_mul_apply : (x * y) v = x v * y v := rfl
end Coe

variable {R K}

open Classical in

noncomputable def ind (p : HeightOneSpectrum R → Prop) : FiniteAdeleRing R K :=
  ⟨fun v => if p v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases hv : p v
    · simp only [hv, if_true]; exact one_mem _
    · simp only [hv, if_false]; exact zero_mem _⟩

open Classical in
theorem ind_apply (p : HeightOneSpectrum R → Prop) (v : HeightOneSpectrum R) :
    (ind p : FiniteAdeleRing R K) v = if p v then 1 else 0 := rfl

theorem ind_mul_ind_self (p : HeightOneSpectrum R → Prop) :
    (ind p : FiniteAdeleRing R K) * ind p = ind p := by
  ext v
  rw [fa_mul_apply, ind_apply]
  split_ifs <;> simp

theorem ind_mul_ind_eq_zero {p q : HeightOneSpectrum R → Prop} (h : ∀ v, p v → ¬ q v) :
    (ind p : FiniteAdeleRing R K) * ind q = 0 := by
  ext v
  rw [fa_mul_apply, ind_apply, ind_apply, fa_zero_apply]
  by_cases hp : p v
  · simp [hp, h v hp]
  · simp [hp]

theorem valued_mul_le_right {v : HeightOneSpectrum R} {r a : v.adicCompletion K}
    (hr : Valued.v r ≤ 1) : Valued.v (r * a) ≤ Valued.v a := by
  rw [Valuation.map_mul]
  calc Valued.v r * Valued.v a ≤ 1 * Valued.v a := mul_le_mul' hr le_rfl
    _ = Valued.v a := one_mul _

theorem selectable_finiteAdeleRing : Selectable (FiniteAdeleRing R K) := by
  classical
  intro a b c r s t h

  let V : FiniteAdeleRing R K → HeightOneSpectrum R → WithZero (Multiplicative ℤ) :=
    fun x v => Valued.v (x v)
  let p₁ : HeightOneSpectrum R → Prop := fun v => V b v ≤ V a v ∧ V c v ≤ V a v
  let p₂ : HeightOneSpectrum R → Prop := fun v => ¬ p₁ v ∧ V c v ≤ V b v
  let p₃ : HeightOneSpectrum R → Prop := fun v => ¬ p₁ v ∧ ¬ p₂ v
  refine ⟨ind p₁, ind p₂, ind p₃, ind_mul_ind_self p₁, ind_mul_ind_self p₂, ind_mul_ind_self p₃,
    ind_mul_ind_eq_zero (fun v h1 h2 => h2.1 h1), ind_mul_ind_eq_zero (fun v h1 h3 => h3.1 h1),
    ind_mul_ind_eq_zero (fun v h2 h3 => h3.2 h2), ?_⟩
  suffices H : ∀ u : FiniteAdeleRing R K, u = ind p₁ * a + ind p₂ * b + ind p₃ * c → IsUnit u from
    H _ rfl
  intro u hu_def
  have not_p₁ : ∀ v, ¬ p₁ v → V a v < V b v ∨ V a v < V c v := by
    intro v h1
    rcases not_and_or.mp h1 with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)

  have hu : ∀ v, (p₁ v ∧ u v = a v) ∨ (p₂ v ∧ u v = b v) ∨ (p₃ v ∧ u v = c v) := by
    intro v
    have huv : u v = (ind p₁ : FiniteAdeleRing R K) v * a v + (ind p₂ : FiniteAdeleRing R K) v * b v +
        (ind p₃ : FiniteAdeleRing R K) v * c v := by rw [hu_def]; rfl
    rw [huv, ind_apply, ind_apply, ind_apply]
    by_cases h1 : p₁ v
    · left
      have h2 : ¬ p₂ v := fun h => h.1 h1
      have h3 : ¬ p₃ v := fun h => h.1 h1
      refine ⟨h1, ?_⟩
      rw [if_pos h1, if_neg h2, if_neg h3]; ring
    · by_cases h2 : p₂ v
      · right; left
        have h3 : ¬ p₃ v := fun h => h.2 h2
        refine ⟨h2, ?_⟩
        rw [if_neg h1, if_pos h2, if_neg h3]; ring
      · right; right
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [if_neg h1, if_neg h2, if_pos (show p₃ v from ⟨h1, h2⟩)]; ring

  have hdom : ∀ v, V a v ≤ V u v ∧ V b v ≤ V u v ∧ V c v ≤ V u v := by
    intro v
    rcases hu v with ⟨h1, he⟩ | ⟨h2, he⟩ | ⟨h3, he⟩
    · show Valued.v (a v) ≤ Valued.v (u v) ∧ Valued.v (b v) ≤ Valued.v (u v) ∧
        Valued.v (c v) ≤ Valued.v (u v)
      rw [he]; exact ⟨le_rfl, h1.1, h1.2⟩
    · show Valued.v (a v) ≤ Valued.v (u v) ∧ Valued.v (b v) ≤ Valued.v (u v) ∧
        Valued.v (c v) ≤ Valued.v (u v)
      rw [he]
      have hcb : V c v ≤ V b v := h2.2
      have hab : V a v < V b v := by
        rcases not_p₁ v h2.1 with h | h
        · exact h
        · exact lt_of_lt_of_le h hcb
      exact ⟨hab.le, le_rfl, hcb⟩
    · show Valued.v (a v) ≤ Valued.v (u v) ∧ Valued.v (b v) ≤ Valued.v (u v) ∧
        Valued.v (c v) ≤ Valued.v (u v)
      rw [he]
      have hbc : V b v < V c v := by
        by_contra hh
        exact h3.2 ⟨h3.1, not_lt.mp hh⟩
      have hac : V a v < V c v := by
        rcases not_p₁ v h3.1 with h | h
        · exact lt_trans h hbc
        · exact h
      exact ⟨hac.le, hbc.le, le_rfl⟩
  rw [IsDedekindDomain.FiniteAdeleRing.isUnit_iff]
  constructor
  ·
    intro v hv0
    have hv1 := congrArg (fun x : FiniteAdeleRing R K => x v) h
    simp only [fa_add_apply, fa_mul_apply, fa_one_apply] at hv1
    have hz : ∀ x : FiniteAdeleRing R K, V x v ≤ V u v → x v = 0 := by
      intro x hx
      have : Valued.v (x v) ≤ 0 := by simpa [V, hv0] using hx
      exact (Valuation.zero_iff _).mp (le_antisymm this zero_le')
    obtain ⟨ha, hb, hc⟩ := hdom v
    rw [hz a ha, hz b hb, hz c hc] at hv1
    simp at hv1
  ·
    filter_upwards [r.2, s.2, t.2, u.2] with v hr hs ht huv
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hr hs ht huv
    refine le_antisymm huv ?_
    have hv1 := congrArg (fun x : FiniteAdeleRing R K => x v) h
    simp only [fa_add_apply, fa_mul_apply, fa_one_apply] at hv1
    obtain ⟨hda, hdb, hdc⟩ := hdom v
    have h1 : (1 : WithZero (Multiplicative ℤ)) = Valued.v (r v * a v + s v * b v + t v * c v) := by
      rw [hv1, Valuation.map_one]
    rw [h1]
    refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
      (max_le ?_ ?_)) ?_)
    · exact (valued_mul_le_right hr).trans hda
    · exact (valued_mul_le_right hs).trans hdb
    · exact (valued_mul_le_right ht).trans hdc

end FiniteAdele

section Adele

variable (K : Type*) [Field K]

theorem selectable_infiniteAdeleRing : Selectable (InfiniteAdeleRing K) :=
  selectable_pi (F := fun v : InfinitePlace K => v.Completion)

variable [NumberField K]

theorem selectable_adeleRing : Selectable (AdeleRing (𝓞 K) K) :=
  selectable_prod (selectable_infiniteAdeleRing K) (selectable_finiteAdeleRing (R := 𝓞 K) (K := K))

theorem exists_conj_adeleRing (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    (hM : IsUnit (M.trace ^ 2 - 4 * M.det)) (htr : N.trace = M.trace) (hdet : N.det = M.det) :
    ∃ P : GL (Fin 2) (AdeleRing (𝓞 K) K), N = (P : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))⁻¹ * M * P :=
  exists_conj_of_selectable (selectable_adeleRing K) M N hM htr hdet

end Adele

section Proper

open Topology Filter Set MulAction
open scoped Pointwise

variable {A : Type*} [CommRing A]

def fibre (γ : GL (Fin 2) A) : Set (GL (Fin 2) A) :=
  {g | (g : Matrix (Fin 2) (Fin 2) A).trace = (γ : Matrix (Fin 2) (Fin 2) A).trace ∧
    (g : Matrix (Fin 2) (Fin 2) A).det = (γ : Matrix (Fin 2) (Fin 2) A).det}

theorem self_mem_fibre (γ : GL (Fin 2) A) : γ ∈ fibre γ := ⟨rfl, rfl⟩

theorem conj_mem_fibre {γ g : GL (Fin 2) A} (hg : g ∈ fibre γ) (x : GL (Fin 2) A) :
    x * g * x⁻¹ ∈ fibre γ := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [← h1, Units.val_mul, Units.val_mul]
    exact Matrix.trace_units_conj x _
  · rw [← h2, Units.val_mul, Units.val_mul]
    exact Matrix.det_units_conj x _

theorem exists_conj_eq_of_mem_fibre (hA : Selectable A) {γ : GL (Fin 2) A}
    (hγ : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det))
    {g : GL (Fin 2) A} (hg : g ∈ fibre γ) : ∃ x : GL (Fin 2) A, x * γ * x⁻¹ = g := by
  obtain ⟨P, hP⟩ := exists_conj_of_selectable hA (γ : Matrix (Fin 2) (Fin 2) A)
    (g : Matrix (Fin 2) (Fin 2) A) hγ hg.1 hg.2
  refine ⟨P⁻¹, Units.ext ?_⟩
  rw [hP, Units.val_mul, Units.val_mul, inv_inv, Matrix.coe_units_inv]

theorem isClosed_fibre [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] (γ : GL (Fin 2) A) :
    IsClosed (fibre γ) := by
  have hc : Continuous fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) := Units.continuous_val
  exact IsClosed.inter (isClosed_eq hc.matrix_trace continuous_const)
    (isClosed_eq hc.matrix_det continuous_const)

scoped instance mulActionFibre (γ : GL (Fin 2) A) : MulAction (GL (Fin 2) A) (fibre γ) where
  smul x y := ⟨x * y * x⁻¹, conj_mem_fibre y.2 x⟩
  one_smul y := Subtype.ext (by change (1 : GL (Fin 2) A) * y * 1⁻¹ = y; simp)
  mul_smul x x' y := Subtype.ext (by
    change x * x' * (y : GL (Fin 2) A) * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹
    simp only [_root_.mul_inv_rev, mul_assoc])

theorem smul_val (γ : GL (Fin 2) A) (x : GL (Fin 2) A) (y : fibre γ) :
    ((x • y : fibre γ) : GL (Fin 2) A) = x * y * x⁻¹ := rfl

theorem continuousSMul_fibre [TopologicalSpace A] [IsTopologicalRing A] (γ : GL (Fin 2) A) :
    ContinuousSMul (GL (Fin 2) A) (fibre γ) := by
  refine ⟨?_⟩
  have : Continuous fun p : GL (Fin 2) A × fibre γ => p.1 * (p.2 : GL (Fin 2) A) * p.1⁻¹ :=
    (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst.inv
  exact this.subtype_mk _

theorem isPretransitive_fibre (hA : Selectable A) {γ : GL (Fin 2) A}
    (hγ : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det)) :
    IsPretransitive (GL (Fin 2) A) (fibre γ) := by
  refine ⟨fun y₁ y₂ => ?_⟩
  obtain ⟨a, ha⟩ := exists_conj_eq_of_mem_fibre hA hγ y₁.2
  obtain ⟨b, hb⟩ := exists_conj_eq_of_mem_fibre hA hγ y₂.2
  refine ⟨b * a⁻¹, Subtype.ext ?_⟩
  rw [smul_val, ← ha, ← hb]
  simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

theorem exists_isCompact_subset_centralizer_mul [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace (GL (Fin 2) A)] [SecondCountableTopology (GL (Fin 2) A)]
    (hA : Selectable A) (γ : GL (Fin 2) A)
    (hγ : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det))
    {C : Set (GL (Fin 2) A)} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) A), IsCompact D ∧
      {x : GL (Fin 2) A | x⁻¹ * γ * x ∈ C} ⊆
        (Subgroup.centralizer {γ} : Set (GL (Fin 2) A)) * D := by
  classical
  haveI : T2Space (GL (Fin 2) A) := by
    haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
    exact Units.isEmbedding_embedProduct.t2Space
  haveI : SigmaCompactSpace (GL (Fin 2) A) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hcl : IsClosed (fibre γ) := isClosed_fibre γ
  haveI : LocallyCompactSpace (fibre γ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : ContinuousSMul (GL (Fin 2) A) (fibre γ) := continuousSMul_fibre γ
  haveI : IsPretransitive (GL (Fin 2) A) (fibre γ) := isPretransitive_fibre hA hγ
  set y₀ : fibre γ := ⟨γ, self_mem_fibre γ⟩ with hy₀

  have hopen : IsOpenMap fun x : GL (Fin 2) A => x • y₀ := isOpenMap_smul_of_sigmaCompact y₀

  set Kc : Set (fibre γ) := ((↑) : fibre γ → GL (Fin 2) A) ⁻¹' C with hKc_def
  have hKc : IsCompact Kc := hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC

  have hN : ∀ x : GL (Fin 2) A, ∃ N : Set (GL (Fin 2) A), IsCompact N ∧ N ∈ 𝓝 x := fun x =>
    exists_compact_mem_nhds x
  choose N hNc hNn using hN
  have hcover : Kc ⊆ ⋃ x : GL (Fin 2) A, (fun x : GL (Fin 2) A => x • y₀) '' interior (N x) := by
    intro y _
    obtain ⟨x, hx⟩ := exists_smul_eq (GL (Fin 2) A) y₀ y
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hNn x), hx⟩
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover
    (fun x => (fun x : GL (Fin 2) A => x • y₀) '' interior (N x))
    (fun x => hopen _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, (N x)⁻¹, t.isCompact_biUnion fun x _ => (hNc x).inv, ?_⟩
  intro z hz
  have hzK : (z⁻¹ • y₀ : fibre γ) ∈ Kc := by
    change ((z⁻¹ • y₀ : fibre γ) : GL (Fin 2) A) ∈ C
    rw [smul_val, inv_inv]
    exact hz
  obtain ⟨x, hxt, n, hn, hnz⟩ : ∃ x ∈ t, ∃ n ∈ interior (N x), n • y₀ = z⁻¹ • y₀ := by
    have := ht hzK
    simp only [mem_iUnion, mem_image, exists_prop] at this
    obtain ⟨x, hxt, n, hn, hnz⟩ := this
    exact ⟨x, hxt, n, hn, hnz⟩
  have hval : n * γ * n⁻¹ = z⁻¹ * γ * z⁻¹⁻¹ := by
    have := congrArg (fun y : fibre γ => (y : GL (Fin 2) A)) hnz
    simpa only [smul_val] using this
  rw [inv_inv] at hval

  have hcen : z * n ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * n * γ = z * (n * γ * n⁻¹) * n := by group
      _ = z * (z⁻¹ * γ * z) * n := by rw [hval]
      _ = γ * (z * n) := by group
  refine Set.mem_mul.mpr ⟨z * n, hcen, n⁻¹, ?_, by group⟩
  exact mem_iUnion₂.mpr ⟨x, hxt, Set.inv_mem_inv.mpr (interior_subset hn)⟩

end Proper

section Centralizer

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  have e11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] (T : Subgroup G) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

end Centralizer

section Main

open scoped Pointwise
open Filter Topology NumberField.AdelicHaar

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem exists_continuous_section
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)} (hC : IsCompact C) :
    ∃ w : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧
      ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K, x⁻¹ * γ * x ∈ C →
        ∫ t : Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
          w ((t : AutomorphicForm.AdelicGL2 (𝓞 K) K) * x) ∂τ = 1 := by
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) := ⟨rfl⟩
  haveI : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hTc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) :
      Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) := by
    show IsClosed (({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))).centralizer)
    exact Set.isClosed_centralizer _
  have hcomm : ∀ s t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
      s * t = t * s :=
    fun s t => Subtype.ext (mul_comm_of_mem_centralizer hγ s.2 t.2)
  haveI : τ.IsMulRightInvariant := isMulRightInvariant_of_comm _ hcomm τ
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) :=
    hTc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) :=
    hTc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology

  obtain ⟨D, hD, hsub⟩ := exists_isCompact_subset_centralizer_mul (selectable_adeleRing K) γ hγ hC
  have hι : Topology.IsClosedEmbedding
      ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))).subtype) :=
    hTc.isClosedEmbedding_subtypeVal
  obtain ⟨w, hwc, hws, hw0, hw1⟩ :=
    MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one τ
      ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))).subtype) hι D hD
  refine ⟨w, hwc, hws, hw0, fun x hx => ?_⟩
  obtain ⟨t, ht, d, hd, rfl⟩ := Set.mem_mul.mp (hsub hx)
  have := hw1 ⟨t, ht⟩ d hd
  simpa [mul_assoc] using this

theorem eq_integral_of_isWeightedOrbitalIntegralOn
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    (wt : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
      ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K, wt ((t : AutomorphicForm.AdelicGL2 (𝓞 K) K) * x) = wt x)
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)}
    (w : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ) (hwc : Continuous w) (hws : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K, x⁻¹ * γ * x ∈ C →
        ∫ t : Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
          w ((t : AutomorphicForm.AdelicGL2 (𝓞 K) K) * x) ∂τ = 1)
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hfm : Measurable f) (hfb : ∃ B : ℝ, ∀ g, ‖f g‖ ≤ B)
    (hfC : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K, f (x⁻¹ * γ * x) ≠ 0 → x⁻¹ * γ * x ∈ C)
    {I : ℂ}
    (hI : AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) wt γ τ f I) :
    I = ∫ x, f (x⁻¹ * γ * x) * (wt x : ℂ) * (w x : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  have h2 : AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) wt γ τ f
      (∫ x, f (x⁻¹ * γ * x) * (wt x : ℂ) * (w x : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) :=
    ⟨w, ⟨hw0, hwc.measurable, hws, fun x hx => hw1 x (hfC x hx)⟩, rfl⟩
  exact AutomorphicForm.IsWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_of_forall_centralizer_mul_eq
    (AdeleRing (𝓞 K) K)
    (adelicGLHaar (Fin 2) (𝓞 K) K) (NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K)
    γ hγ τ inferInstance wt hwtc hwt f hfm hfb hI h2

theorem continuous_centralScalar :
    Continuous (fun z : (AdeleRing (𝓞 K) K)ˣ => AutomorphicForm.centralScalar (𝓞 K) K z) := by
  have hs : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 K) K → Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; (simp [Matrix.scalar_apply, Matrix.diagonal_apply_eq]; exact continuous_id)
    · simpa [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] using continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hs.comp Units.continuous_val
  · exact hs.comp Units.continuous_coe_inv

theorem main
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    (wt : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)),
      ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K, wt ((t : AutomorphicForm.AdelicGL2 (𝓞 K) K) * x) = wt x)
    (f : ι → AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i) ∧ HasCompactSupport (f i))
    (I : ι → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hI : ∀ i ∈ s, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) wt γ τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K => f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (I i z)) :
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K) wt γ τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          ∑ i ∈ s, c i * f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (∑ i ∈ s, c i * I i z)) ∧
    (∀ i ∈ s, Measurable (I i)) := by
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set cs : (AdeleRing (𝓞 K) K)ˣ → AutomorphicForm.AdelicGL2 (𝓞 K) K :=
    fun z => AutomorphicForm.centralScalar (𝓞 K) K z with hcs
  have hcsc : Continuous cs := continuous_centralScalar K
  have hconj : Continuous fun x : AutomorphicForm.AdelicGL2 (𝓞 K) K => x⁻¹ * γ * x :=
    (continuous_inv.mul continuous_const).mul continuous_id

  have hbdd : ∀ i ∈ s, ∃ B : ℝ, ∀ z g, ‖f i (cs z * g)‖ ≤ B := by
    intro i hi
    obtain ⟨B, hB⟩ := (hf i hi).1.bounded_above_of_compact_support (hf i hi).2
    exact ⟨B, fun z g => hB _⟩
  have hmeas : ∀ i ∈ s, ∀ z, Measurable fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K => f i (cs z * g) :=
    fun i hi z => ((hf i hi).1.comp (continuous_const_mul (cs z))).measurable

  have hint : ∀ i ∈ s, ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (w : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ),
      Continuous w → HasCompactSupport w →
      Integrable (fun x => f i (cs z * (x⁻¹ * γ * x)) * (wt x : ℂ) * (w x : ℂ)) μ := by
    intro i hi z w hwc hws
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((((hf i hi).1.comp ((continuous_const_mul (cs z)).comp hconj))).mul
        (Complex.continuous_ofReal.comp hwtc)).mul (Complex.continuous_ofReal.comp hwc)
    · exact (hws.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).mul_left
  refine ⟨fun z => ?_, fun i hi => ?_⟩
  ·
    set C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K) :=
      ⋃ i ∈ s, (fun g => (cs z)⁻¹ * g) '' tsupport (f i) with hCdef
    have hC : IsCompact C :=
      s.isCompact_biUnion fun i hi => ((hf i hi).2.isCompact.image (continuous_const_mul _))
    obtain ⟨w, hwc, hws, hw0, hw1⟩ := exists_continuous_section K γ hγ τ hC
    have hCf : ∀ i ∈ s, ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K,
        f i (cs z * (x⁻¹ * γ * x)) ≠ 0 → x⁻¹ * γ * x ∈ C := by
      intro i hi x hx
      rw [hCdef]
      refine Set.mem_biUnion hi ⟨cs z * (x⁻¹ * γ * x), subset_tsupport _ (Function.mem_support.mpr hx), ?_⟩
      simp
    have hval : ∀ i ∈ s, I i z = ∫ x, f i (cs z * (x⁻¹ * γ * x)) * (wt x : ℂ) * (w x : ℂ) ∂μ :=
      fun i hi => eq_integral_of_isWeightedOrbitalIntegralOn K γ hγ τ wt hwtc hwt w hwc hws hw0 hw1
        (fun g => f i (cs z * g)) (hmeas i hi z) ((hbdd i hi).imp fun B hB => hB z) (hCf i hi) (hI i hi z)
    refine ⟨w, ⟨hw0, hwc.measurable, hws, fun x hx => hw1 x ?_⟩, ?_⟩
    · obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      exact hCf i hi x (right_ne_zero_of_mul hne)
    · calc ∑ i ∈ s, c i * I i z
          = ∑ i ∈ s, ∫ x, c i * (f i (cs z * (x⁻¹ * γ * x)) * (wt x : ℂ) * (w x : ℂ)) ∂μ := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [hval i hi, integral_const_mul]
        _ = ∫ x, ∑ i ∈ s, c i * (f i (cs z * (x⁻¹ * γ * x)) * (wt x : ℂ) * (w x : ℂ)) ∂μ :=
            (integral_finsetSum s fun i hi => (hint i hi z w hwc hws).const_mul (c i)).symm
        _ = ∫ x, (∑ i ∈ s, c i * f i (cs z * (x⁻¹ * γ * x))) * (wt x : ℂ) * (w x : ℂ) ∂μ := by
            congr 1; ext x; rw [Finset.sum_mul, Finset.sum_mul]; simp only [mul_assoc]
  ·
    haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
    haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    obtain ⟨B, hB⟩ := hbdd i hi
    refine Continuous.measurable ?_
    refine continuous_iff_continuousAt.mpr fun z₀ => ?_

    obtain ⟨M, hMc, hMn⟩ := exists_compact_mem_nhds ((cs z₀)⁻¹)
    set N : Set (AdeleRing (𝓞 K) K)ˣ := {z | (cs z)⁻¹ ∈ M} with hNdef
    have hN : N ∈ 𝓝 z₀ := (hcsc.inv).continuousAt.preimage_mem_nhds hMn
    set C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K) :=
      (fun p : AutomorphicForm.AdelicGL2 (𝓞 K) K × AutomorphicForm.AdelicGL2 (𝓞 K) K => p.1 * p.2) ''
        (M ×ˢ tsupport (f i)) with hCdef
    have hC : IsCompact C := (hMc.prod (hf i hi).2.isCompact).image continuous_mul
    obtain ⟨w, hwc, hws, hw0, hw1⟩ := exists_continuous_section K γ hγ τ hC
    have hCf : ∀ z ∈ N, ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K,
        f i (cs z * (x⁻¹ * γ * x)) ≠ 0 → x⁻¹ * γ * x ∈ C := by
      intro z hz x hx
      rw [hCdef]
      refine ⟨((cs z)⁻¹, cs z * (x⁻¹ * γ * x)), ⟨hz, subset_tsupport _ (Function.mem_support.mpr hx)⟩, ?_⟩
      simp
    set Φ : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun z => ∫ x, f i (cs z * (x⁻¹ * γ * x)) * (wt x : ℂ) * (w x : ℂ) ∂μ with hΦ
    have hval : ∀ z ∈ N, I i z = Φ z :=
      fun z hz => eq_integral_of_isWeightedOrbitalIntegralOn K γ hγ τ wt hwtc hwt w hwc hws hw0 hw1
        (fun g => f i (cs z * g)) (hmeas i hi z) ⟨B, hB z⟩ (hCf z hz) (hI i hi z)
    have hΦc : ContinuousAt Φ z₀ := by
      refine continuousAt_of_dominated (bound := fun x => B * (‖(wt x : ℂ)‖ * ‖(w x : ℂ)‖)) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun z => (hint i hi z w hwc hws).aestronglyMeasurable
      · refine Eventually.of_forall fun z => Eventually.of_forall fun x => ?_
        rw [norm_mul, norm_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (hB z _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · exact ((((Complex.continuous_ofReal.comp hwtc).norm).mul ((Complex.continuous_ofReal.comp hwc).norm)).integrable_of_hasCompactSupport
          ((hws.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).norm.mul_left)).const_mul B
      · refine Eventually.of_forall fun x => ?_
        exact ((((hf i hi).1.comp ((continuous_mul_const (x⁻¹ * γ * x)).comp hcsc)).mul
          continuous_const).mul continuous_const).continuousAt
    refine hΦc.congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem hN fun z hz => hval z hz

end Main

end BenchLOrbW
p2m_reactivate "P2MW.S_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal.BenchLOrbW"

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

namespace BenchLOrbW

theorem globalPoints_apply (K : Type) [Field K] [NumberField K] (γ₀ : GL (Fin 2) K) (i j : Fin 2) :
    ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      algebraMap K (AdeleRing (𝓞 K) K) ((γ₀ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

theorem isRegularSemisimple_globalPoints (K : Type) [Field K] [NumberField K] (γ₀ : GL (Fin 2) K)
    (hγ₀ : (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.globalPoints (𝓞 K) K γ₀) := by
  obtain ⟨h10, h01, hne⟩ := hγ₀
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  have hd0 : d ≠ 0 := by
    intro hd0
    have hdet : (γ₀ : Matrix (Fin 2) (Fin 2) K).det = 0 := by
      rw [Matrix.det_fin_two, h10, ← hd, hd0]; ring
    have hu := (Matrix.GeneralLinearGroup.det γ₀).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hu
    exact hu hdet
  have had : a - d ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero.mp h, div_self hd0]
  unfold AutomorphicForm.IsRegularSemisimple
  have key : Matrix.trace ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ^ 2 -
      4 * Matrix.det ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = algebraMap K (AdeleRing (𝓞 K) K) ((a - d) ^ 2) := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [globalPoints_apply, h10, h01, ← ha, ← hd, map_zero, map_sub, map_pow]
    ring
  rw [key]
  exact (IsUnit.pow 2 (isUnit_iff_ne_zero.mpr had)).map _

theorem diagonal_of_mem_centralizer_globalPoints (K : Type) [Field K] [NumberField K] (γ₀ : GL (Fin 2) K)
    (hγ₀ : (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (ht : t ∈ Subgroup.centralizer
      ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) :
    (t : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
      (t : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 := by
  obtain ⟨h10, h01, hne⟩ := hγ₀
  set a := (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  set d := (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 1 with hd
  have hd0 : d ≠ 0 := by
    intro hd0
    have hdet : (γ₀ : Matrix (Fin 2) (Fin 2) K).det = 0 := by
      rw [Matrix.det_fin_two, h10, ← hd, hd0]; ring
    have hu := (Matrix.GeneralLinearGroup.det γ₀).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hu
    exact hu hdet
  have had : IsUnit (algebraMap K (AdeleRing (𝓞 K) K) (a - d)) := by
    refine (isUnit_iff_ne_zero.mpr ?_).map _
    intro h
    apply hne
    rw [sub_eq_zero.mp h, div_self hd0]
  have hc := (Subgroup.mem_centralizer_iff.mp ht) _ (Set.mem_singleton _)

  have hm : ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * (t : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      (t : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) *
        ((AutomorphicForm.globalPoints (𝓞 K) K γ₀ : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    have := congrArg (fun u : AutomorphicForm.AdelicGL2 (𝓞 K) K => (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) hc
    simpa only [Units.val_mul] using this
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, globalPoints_apply, h10, h01, ← ha, ← hd, map_zero,
    zero_mul, mul_zero, add_zero, zero_add] at e01 e10

  constructor
  · have h : algebraMap K (AdeleRing (𝓞 K) K) (a - d) * (t : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 := by
      rw [map_sub, sub_mul, mul_comm (algebraMap K (AdeleRing (𝓞 K) K) a), ← e10, sub_self]
    exact (had.mul_right_eq_zero).mp h
  · have h : algebraMap K (AdeleRing (𝓞 K) K) (a - d) * (t : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 := by
      rw [map_sub, sub_mul, e01, mul_comm, sub_self]
    exact (had.mul_right_eq_zero).mp h

end BenchLOrbW
p2m_reactivate "P2MW.S_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal.BenchLOrbW"

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (γ₀ : GL (Fin 2) K)
    (hγ₀ : (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ₀ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ₀ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ₀} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure]
    (f : ι → AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i) ∧ HasCompactSupport (f i))
    (J : ι → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJ : ∀ i ∈ s, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (fun x : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
        (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K => f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (J i z)) :
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (fun x : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
        (AutomorphicForm.globalPoints (𝓞 K) K γ₀) τ
        (fun g : AutomorphicForm.AdelicGL2 (𝓞 K) K =>
          ∑ i ∈ s, c i * f i (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (∑ i ∈ s, c i * J i z)) ∧
    (∀ i ∈ s, Measurable (J i)) := by
  obtain ⟨hinv, hcont⟩ :=
    NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous K
  refine BenchLOrbW.main K s c (AutomorphicForm.globalPoints (𝓞 K) K γ₀)
    (BenchLOrbW.isRegularSemisimple_globalPoints K γ₀ hγ₀) τ _ hcont ?_ f hf J hJ
  intro t x
  obtain ⟨h10, h01⟩ := BenchLOrbW.diagonal_of_mem_centralizer_globalPoints K γ₀ hγ₀ t t.2
  exact hinv (t : AutomorphicForm.AdelicGL2 (𝓞 K) K) h10 h01 x

end S_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_isWeightedOrbitalIntegralOn_sum_mul_centralScalar_mul_and_measurable_of_diagonal (solution)
