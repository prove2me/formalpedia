-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/55954dd9-e6be-5319-91c8-863acc8e8d06

import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Theorems.Thm_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

namespace CentralTorus

variable {G : Type} [Group G] {n : ℕ}

def P (δ : Fin (n + 1) → G) (j : Fin (n + 1)) : G := ((List.ofFn δ).take j.val).prod

theorem P_zero (δ : Fin (n + 1) → G) : P δ 0 = 1 := by simp [P]

theorem val_add_one_of_lt (j : Fin (n + 1)) (hj : j.val < n) : (j + 1 : Fin (n + 1)).val = j.val + 1 := by
  rw [Fin.val_add_one]
  split_ifs with h
  · exact absurd hj (by rw [h, Fin.val_last]; exact lt_irrefl n)
  · rfl

theorem P_succ (δ : Fin (n + 1) → G) (j : Fin (n + 1)) (hj : j.val < n) :
    P δ (j + 1) = P δ j * δ j := by
  simp only [P, val_add_one_of_lt j hj]
  rw [List.prod_take_succ _ _ (by simp [j.isLt]), List.getElem_ofFn]

theorem P_last_mul (δ : Fin (n + 1) → G) : P δ (Fin.last n) * δ (Fin.last n) = (List.ofFn δ).prod := by
  simp only [P, Fin.val_last]
  have h : δ (Fin.last n) = (List.ofFn δ)[n]'(by simp) := by
    rw [List.getElem_ofFn]; rfl
  rw [h, ← List.prod_take_succ, List.take_of_length_le (by simp)]

def tOf (δ : Fin (n + 1) → G) (s : G) : Fin (n + 1) → G := fun j => (P δ j)⁻¹ * s * P δ j

theorem tOf_apply (δ : Fin (n + 1) → G) (s : G) (j : Fin (n + 1)) : tOf δ s j = (P δ j)⁻¹ * s * P δ j := rfl

theorem tOf_zero (δ : Fin (n + 1) → G) (s : G) : tOf δ s 0 = s := by simp [tOf, P_zero]

theorem last_add_one : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
  apply Fin.ext; rw [Fin.val_add_one]; simp

theorem eq_last_of_not_lt (j : Fin (n + 1)) (hj : ¬ j.val < n) : j = Fin.last n := by
  apply Fin.ext; rw [Fin.val_last]; omega

theorem tOf_shift (δ : Fin (n + 1) → G) (s : G) (hs : s * (List.ofFn δ).prod = (List.ofFn δ).prod * s)
    (j : Fin (n + 1)) : (tOf δ s j)⁻¹ * δ j * tOf δ s (j + 1) = δ j := by
  by_cases hj : j.val < n
  · rw [tOf_apply, tOf_apply, P_succ δ j hj]; group
  · obtain rfl := eq_last_of_not_lt j hj
    rw [last_add_one, tOf_zero, tOf_apply]
    have hN := P_last_mul δ

    have key : s⁻¹ * (P δ (Fin.last n) * δ (Fin.last n)) * s = P δ (Fin.last n) * δ (Fin.last n) := by
      rw [hN, mul_assoc, ← hs, ← mul_assoc, inv_mul_cancel, one_mul]
    calc ((P δ (Fin.last n))⁻¹ * s * P δ (Fin.last n))⁻¹ * δ (Fin.last n) * s
        = (P δ (Fin.last n))⁻¹ * (s⁻¹ * (P δ (Fin.last n) * δ (Fin.last n)) * s) := by group
      _ = δ (Fin.last n) := by rw [key, ← mul_assoc, inv_mul_cancel, one_mul]

theorem eq_tOf_of_shift (δ : Fin (n + 1) → G) (t : Fin (n + 1) → G)
    (ht : ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j) : t = tOf δ (t 0) := by
  funext j
  induction j using Fin.induction with
  | zero => rw [tOf_zero]
  | succ i ih =>
    have hi : (Fin.castSucc i).val < n := by simp
    have hsucc : Fin.castSucc i + 1 = i.succ := by
      apply Fin.ext; rw [val_add_one_of_lt _ hi]; simp
    have hrel := ht (Fin.castSucc i)
    rw [hsucc] at hrel
    have hstep : t i.succ = (δ (Fin.castSucc i))⁻¹ * t (Fin.castSucc i) * δ (Fin.castSucc i) := by
      calc t i.succ = (δ (Fin.castSucc i))⁻¹ * t (Fin.castSucc i) * ((t (Fin.castSucc i))⁻¹ * δ (Fin.castSucc i) * t i.succ) := by group
        _ = (δ (Fin.castSucc i))⁻¹ * t (Fin.castSucc i) * δ (Fin.castSucc i) := by rw [hrel]
    rw [hstep, ih, tOf_apply, tOf_apply, ← hsucc, P_succ δ _ hi]
    group

theorem zero_comm_prod_of_shift (δ : Fin (n + 1) → G) (t : Fin (n + 1) → G)
    (ht : ∀ j, (t j)⁻¹ * δ j * t (j + 1) = δ j) : t 0 * (List.ofFn δ).prod = (List.ofFn δ).prod * t 0 := by
  have heq := eq_tOf_of_shift δ t ht
  have hl := ht (Fin.last n)
  rw [last_add_one] at hl
  have htl : t (Fin.last n) = (P δ (Fin.last n))⁻¹ * t 0 * P δ (Fin.last n) := by
    conv_lhs => rw [heq]
    rw [tOf_apply]
  rw [htl] at hl
  rw [← P_last_mul]

  calc t 0 * (P δ (Fin.last n) * δ (Fin.last n))
      = (P δ (Fin.last n)) * (((P δ (Fin.last n))⁻¹ * t 0 * P δ (Fin.last n)) * δ (Fin.last n)) := by group
    _ = (P δ (Fin.last n)) * (((P δ (Fin.last n))⁻¹ * t 0 * P δ (Fin.last n)) * (((P δ (Fin.last n))⁻¹ * t 0 * P δ (Fin.last n))⁻¹ * δ (Fin.last n) * t 0)) := by rw [hl]
    _ = (P δ (Fin.last n) * δ (Fin.last n)) * t 0 := by group

theorem inv_mul_P_mul_eq_P_twc (δ ξ : Fin (n + 1) → G) (j : Fin (n + 1)) :
    (ξ 0)⁻¹ * P δ j * ξ j = P (fun k => (ξ k)⁻¹ * δ k * ξ (k + 1)) j := by
  induction j using Fin.induction with
  | zero => rw [P_zero, P_zero, mul_one, inv_mul_cancel]
  | succ i ih =>
    have hi : (Fin.castSucc i).val < n := by simp
    have hsucc : Fin.castSucc i + 1 = i.succ := by
      apply Fin.ext; rw [val_add_one_of_lt _ hi]; simp
    rw [← hsucc, P_succ δ _ hi, P_succ _ _ hi, ← ih, hsucc]
    group

theorem prod_twc (δ ξ : Fin (n + 1) → G) :
    (List.ofFn fun k => (ξ k)⁻¹ * δ k * ξ (k + 1)).prod = (ξ 0)⁻¹ * (List.ofFn δ).prod * ξ 0 := by
  rw [← P_last_mul, ← P_last_mul δ, ← inv_mul_P_mul_eq_P_twc δ ξ (Fin.last n), last_add_one]
  group

end CentralTorus

namespace SplitCentralAux

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A]

theorem secondCountableTopology_gl : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_gl : LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem exists_isSectionFnOn_scalar
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA)
    (hμAr : @Measure.IsMulRightInvariant (GL (Fin 2) A) (glBorelOf A) _ μA)
    (z : Aˣ)
    (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)))
      (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)))
    (c₀ : ℝ≥0) (hc₀ : c₀ ≠ 0)
    (hτ : @Measure.map _ _ (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) (glBorelOf A)
      Subtype.val τ = c₀ • μA)
    (f : GL (Fin 2) A → ℂ) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    ∃ w : GL (Fin 2) A → ℝ, IsSectionFnOn A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) τ f w ∧
      Integrable w μA ∧ ∫ x, w x ∂μA = ((c₀ : ℝ))⁻¹ := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A))) :=
    centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  haveI : μA.IsHaarMeasure := hμA
  haveI : μA.IsMulRightInvariant := hμAr

  obtain ⟨K₀, hK₀c, hK₀n⟩ := exists_compact_mem_nhds (1 : GL (Fin 2) A)
  have hK₀pos : 0 < μA K₀ := Measure.measure_pos_of_mem_nhds μA hK₀n
  have hK₀fin : μA K₀ < ∞ := hK₀c.measure_lt_top
  set m : ℝ := (μA K₀).toReal with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hK₀pos.ne' hK₀fin.ne
  set a : ℝ := ((c₀ : ℝ) * m)⁻¹ with ha
  have hc₀pos : 0 < (c₀ : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hc₀
  have hapos : 0 < a := by rw [ha]; positivity
  let w : GL (Fin 2) A → ℝ := fun x => a * K₀.indicator (1 : GL (Fin 2) A → ℝ) x
  have hwm : Measurable w := (measurable_const.indicator hK₀c.measurableSet).const_mul a
  have hw0 : ∀ x, 0 ≤ w x := fun x => mul_nonneg hapos.le (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hwcs : HasCompactSupport w := by
    refine HasCompactSupport.intro hK₀c fun x hx => ?_
    simp [w, Set.indicator_of_notMem hx]
  have hwint : ∫ x, w x ∂μA = ((c₀ : ℝ))⁻¹ := by
    simp only [w]
    rw [integral_const_mul, integral_indicator_one hK₀c.measurableSet, Measure.real, ← hm, ha]
    field_simp
  have hwi : Integrable w μA := (((integrable_indicator_iff hK₀c.measurableSet).2
      (integrableOn_const hK₀fin.ne)).const_mul a)
  refine ⟨w, ⟨hw0, hwm, hwcs, fun x _ => ?_⟩, hwi, hwint⟩

  have hval : Measurable (Subtype.val : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)) → GL (Fin 2) A) :=
    continuous_subtype_val.measurable
  have h1 : ∫ t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)), w ((t : GL (Fin 2) A) * x) ∂τ
      = ∫ g, w (g * x) ∂(Measure.map Subtype.val τ) := by
    rw [integral_map hval.aemeasurable]
    exact ((hwm.comp (measurable_id.mul_const x)).aestronglyMeasurable)
  rw [h1, hτ, integral_smul_nnreal_measure, integral_mul_right_eq_self (fun g => w g) x, hwint]
  rw [NNReal.smul_def, smul_eq_mul]; push_cast
  field_simp

end SplitCentralAux

namespace SplitLiftAux

theorem prod_ofFn_eq_of_forall_ne_eq_one {G : Type} [Monoid G] : ∀ {m : ℕ} (f : Fin m → G) (i : Fin m),
    (∀ k, k ≠ i → f k = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | m + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hi : i = 0
    · subst hi
      have : (List.ofFn fun k : Fin m => f k.succ).prod = 1 := by
        rw [List.prod_eq_one]; intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨k, rfl⟩ := hx
        exact h _ (Fin.succ_ne_zero k)
      rw [this, mul_one]
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
      rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact prod_ofFn_eq_of_forall_ne_eq_one (fun k => f k.succ) i' fun k hk => h _ (fun e => hk (Fin.succ_injective _ e))

theorem add_eq_zero_iff_eq_neg {n : ℕ} (j k : Fin (n + 1)) : j + k = 0 ↔ k = -j := by
  constructor
  · intro h; exact eq_neg_of_add_eq_zero_right h
  · rintro rfl; exact add_neg_cancel j

end SplitLiftAux

namespace SplitLiftAux

section Helpers
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_algebraMap_tensor : Continuous (algebraMap A (L ⊗[K] A)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (L ⊗[K] A))

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
      = (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) := by
  ext i j
  simp [toTensorGL, Matrix.GeneralLinearGroup.map_apply, TensorProduct.RightActions.algebraMap_eval]

theorem continuous_toTensorGL : Continuous (toTensorGL K L A) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ toTensorGL K L A) =
        fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => coe_toTensorGL K L A g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_algebraMap_tensor K L A)
  · have h : (fun g : GL (Fin 2) A => ((toTensorGL K L A g)⁻¹ : GL (Fin 2) (L ⊗[K] A)).val) =
        fun g : GL (Fin 2) A => ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map (algebraMap A (L ⊗[K] A)) :=
      funext fun g => by rw [← map_inv, coe_toTensorGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_algebraMap_tensor K L A)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem mem_twistedCentralizer_iff_shift (σ : L ≃ₐ[K] L) {n : ℕ} (Θ : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (n + 1) → GL (Fin 2) A))
    (hΘσ : ∀ x δ : GL (Fin 2) (L ⊗[K] A),
      Θ (x⁻¹ * δ * sigmaGL K L A σ x) = fun j => (Θ x j)⁻¹ * Θ δ j * Θ x (j + 1))
    (δ s : GL (Fin 2) (L ⊗[K] A)) :
    s ∈ twistedCentralizer K L A σ δ ↔ ∀ j, (Θ s j)⁻¹ * Θ δ j * Θ s (j + 1) = Θ δ j := by
  rw [twistedCentralizer, mem_sigmaCentralizer_iff_inv, ← Θ.injective.eq_iff, hΘσ, funext_iff]
end Helpers

theorem const_of_shift_mulSingle {G : Type} [Group G] {n : ℕ} (γ : G) (t : Fin (n + 1) → G)
    (ht : ∀ j, (t j)⁻¹ * (Pi.mulSingle (0 : Fin (n + 1)) γ : Fin (n + 1) → G) j * t (j + 1) = (Pi.mulSingle (0 : Fin (n + 1)) γ : Fin (n + 1) → G) j) :
    (∀ j, t j = t 0) ∧ (t 0)⁻¹ * γ * t 0 = γ := by

  have hstep : ∀ j : Fin (n + 1), j ≠ 0 → t (j + 1) = t j := by
    intro j hj
    have h := ht j
    rw [Pi.mulSingle_eq_of_ne hj, mul_one] at h
    calc t (j + 1) = t j * ((t j)⁻¹ * t (j + 1)) := by group
      _ = t j := by rw [h, mul_one]

  have hall1 : ∀ j : Fin (n + 1), j ≠ 0 → t j = t 1 := by
    intro j
    induction j using Fin.induction with
    | zero => intro h; exact absurd rfl h
    | succ i ih =>
      intro _
      by_cases hi : Fin.castSucc i = 0
      · have hv : i.val = 0 := by simpa using congrArg Fin.val hi
        have h1 : i.succ = 1 := Fin.ext (by
          rw [Fin.val_succ, hv, Fin.val_one', Nat.mod_eq_of_lt (by omega)])
        rw [h1]
      · have hsucc : Fin.castSucc i + 1 = i.succ := by
          apply Fin.ext; rw [Fin.val_add_one]; simp [Fin.castSucc_ne_last]
        rw [← hsucc, hstep _ hi, ih hi]
  have h01 : t 0 = t 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact congrArg t (Fin.ext (by simp))
    · have hl : (Fin.last n : Fin (n + 1)) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have hwrap : Fin.last n + 1 = (0 : Fin (n + 1)) := by apply Fin.ext; rw [Fin.val_add_one]; simp
      rw [← hwrap, hstep _ hl, hall1 _ hl]
  have hconst : ∀ j, t j = t 0 := by
    intro j; by_cases hj : j = 0
    · rw [hj]
    · rw [hall1 j hj, ← h01]
  refine ⟨hconst, ?_⟩
  have h0 := ht 0
  rw [Pi.mulSingle_eq_same, hconst (0 + 1)] at h0
  exact h0

end SplitLiftAux

namespace SplitLiftAux

theorem exists_splitLift_coupled
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (ι : L →ₐ[K] A)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (glBorelOf (L ⊗[K] A)) μL)
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA)
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ) :
    ∃ δ₁ : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ₁ 1 ∧
      ∃ τ₁ : @Measure (twistedCentralizer K L A σ δ₁) (twistedCentralizerBorel K L A σ δ₁),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ₁) τ₁ ∧ Coupled K L A σ γ δ₁ 1 τ τ₁ := by
  classical
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  obtain ⟨hΘc, hΘc', hΘσ, hΘ1, hΘN, hΘN0, c, hc0, hcμ⟩ :=
    AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
      K L hdeg σ hσ A ι μL hμL μA hμA
  set Θ := AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ with hΘdef
  set s₁ : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A := Pi.mulSingle (0 : Fin (Module.finrank K L - 1 + 1)) γ with hs₁
  set δ₁ : GL (Fin 2) (L ⊗[K] A) := Θ.symm s₁ with hδ₁
  have hΘδ₁ : Θ δ₁ = s₁ := Θ.apply_symm_apply _

  have hN : IsNormConjugator K L A σ γ δ₁ 1 := by
    show toTensorGL K L A γ = 1⁻¹ * normString K L A σ δ₁ * 1
    rw [inv_one, one_mul, mul_one]
    apply Θ.injective
    rw [hΘ1]; funext j; rw [hΘN, hΘδ₁]
    symm
    rw [prod_ofFn_eq_of_forall_ne_eq_one (fun k => s₁ (j + k)) (-j) ?_]
    · show s₁ (j + -j) = γ
      rw [add_neg_cancel, hs₁, Pi.mulSingle_eq_same]
    · intro k hk
      show s₁ (j + k) = 1
      rw [hs₁]; apply Pi.mulSingle_eq_of_ne
      intro h; exact hk ((add_eq_zero_iff_eq_neg j k).1 h)
  refine ⟨δ₁, hN, ?_⟩

  have hΘσ' : ∀ x d : GL (Fin 2) (L ⊗[K] A),
      Θ (x⁻¹ * d * sigmaGL K L A σ x) = fun j => (Θ x j)⁻¹ * Θ d j * Θ x (j + 1) := by
    intro x d; funext j; simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hΘσ]
  have hmem : ∀ s : GL (Fin 2) (L ⊗[K] A), s ∈ twistedCentralizer K L A σ δ₁ ↔
      ∀ j, (Θ s j)⁻¹ * s₁ j * Θ s (j + 1) = s₁ j := by
    intro s; rw [mem_twistedCentralizer_iff_shift K L A σ Θ hΘσ' δ₁ s, hΘδ₁]
  have hin : ∀ s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)),
      toTensorGL K L A (s : GL (Fin 2) A) ∈ twistedCentralizer K L A σ δ₁ := by
    intro s; rw [hmem]; intro j; rw [hΘ1]
    by_cases hj : j = 0
    · subst hj
      rw [hs₁, Pi.mulSingle_eq_same]
      have hsγ : γ * (s : GL (Fin 2) A) = (s : GL (Fin 2) A) * γ :=
        (Subgroup.mem_centralizer_iff.1 s.2) γ (Set.mem_singleton γ)
      rw [mul_assoc, hsγ, ← mul_assoc, inv_mul_cancel, one_mul]
    · rw [hs₁, Pi.mulSingle_eq_of_ne hj]; group
  have hout : ∀ t : twistedCentralizer K L A σ δ₁,
      (∀ j, Θ (t : GL (Fin 2) (L ⊗[K] A)) j = Θ (t : GL (Fin 2) (L ⊗[K] A)) 0) ∧
        (Θ (t : GL (Fin 2) (L ⊗[K] A)) 0)⁻¹ * γ * Θ (t : GL (Fin 2) (L ⊗[K] A)) 0 = γ := by
    intro t
    have h := (hmem t).1 t.2
    rw [hs₁] at h
    exact const_of_shift_mulSingle γ (Θ (t : GL (Fin 2) (L ⊗[K] A))) h
  have hback : ∀ t : twistedCentralizer K L A σ δ₁,
      toTensorGL K L A (Θ (t : GL (Fin 2) (L ⊗[K] A)) 0) = (t : GL (Fin 2) (L ⊗[K] A)) := by
    intro t; apply Θ.injective; rw [hΘ1]; funext j; exact ((hout t).1 j).symm
  have hcen : ∀ t : twistedCentralizer K L A σ δ₁,
      Θ (t : GL (Fin 2) (L ⊗[K] A)) 0 ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) := by
    intro t; rw [Subgroup.mem_centralizer_iff]
    rintro m hm; rw [Set.mem_singleton_iff] at hm; rw [hm]
    have h := (hout t).2
    calc γ * Θ (t : GL (Fin 2) (L ⊗[K] A)) 0
        = Θ (t : GL (Fin 2) (L ⊗[K] A)) 0 * ((Θ (t : GL (Fin 2) (L ⊗[K] A)) 0)⁻¹ * γ * Θ (t : GL (Fin 2) (L ⊗[K] A)) 0) := by group
      _ = Θ (t : GL (Fin 2) (L ⊗[K] A)) 0 * γ := by rw [h]

  haveI : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A
  let e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃* twistedCentralizer K L A σ δ₁ :=
    { toFun := fun s => ⟨toTensorGL K L A (s : GL (Fin 2) A), hin s⟩
      invFun := fun t => ⟨Θ (t : GL (Fin 2) (L ⊗[K] A)) 0, hcen t⟩
      left_inv := fun s => Subtype.ext (by show Θ (toTensorGL K L A (s : GL (Fin 2) A)) 0 = s; rw [hΘ1])
      right_inv := fun t => Subtype.ext (hback t)
      map_mul' := fun a b => Subtype.ext (by show toTensorGL K L A ((a : GL (Fin 2) A) * b) = toTensorGL K L A a * toTensorGL K L A b; exact map_mul _ _ _) }
  have hec : Continuous e :=
    ((continuous_toTensorGL K L A).comp continuous_subtype_val).subtype_mk _
  have hec' : Continuous e.symm :=
    ((continuous_apply (0 : Fin (Module.finrank K L - 1 + 1))).comp (hΘc.comp continuous_subtype_val)).subtype_mk _
  let eC : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* twistedCentralizer K L A σ δ₁ :=
    { e with continuous_toFun := hec, continuous_invFun := hec' }
  have heC : ∀ s, ((eC s : twistedCentralizer K L A σ δ₁) : GL (Fin 2) (L ⊗[K] A)) = toTensorGL K L A (s : GL (Fin 2) A) :=
    fun s => rfl

  letI mC : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  letI mT : MeasurableSpace (twistedCentralizer K L A σ δ₁) := twistedCentralizerBorel K L A σ δ₁
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ δ₁) := ⟨rfl⟩
  haveI : τ.IsHaarMeasure := hτ
  haveI : (Measure.map eC τ).IsHaarMeasure := eC.isHaarMeasure_map τ
  refine ⟨Measure.map eC τ, inferInstance, ?_⟩
  show Measure.map (fun t : twistedCentralizer K L A σ δ₁ => (1 : GL (Fin 2) (L ⊗[K] A))⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * 1) (Measure.map eC τ) =
    Measure.map (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => toTensorGL K L A (s : GL (Fin 2) A)) τ
  have hm1 : Measurable (fun t : twistedCentralizer K L A σ δ₁ => (1 : GL (Fin 2) (L ⊗[K] A))⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * 1) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hm2 : Measurable (fun s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => eC s) := eC.continuous.measurable
  erw [Measure.map_map hm1 hm2]
  congr 1
  funext s
  simp only [Function.comp_apply, inv_one, one_mul, mul_one]
  exact heC s

end SplitLiftAux

namespace TwistedSectionAux
open AutomorphicForm CentralTorus

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

theorem continuous_P (j : Fin (n + 1)) : Continuous fun c : Fin (n + 1) → G => P c j := by
  induction j using Fin.induction with
  | zero => simp only [P_zero]; exact continuous_const
  | succ i ih =>
    have hi : (Fin.castSucc i).val < n := by simp
    have hsucc : Fin.castSucc i + 1 = i.succ := by
      apply Fin.ext; rw [val_add_one_of_lt _ hi]; simp
    have : (fun c : Fin (n + 1) → G => P c i.succ) = fun c => P c (Fin.castSucc i) * c (Fin.castSucc i) := by
      funext c; rw [← hsucc, P_succ c _ hi]
    rw [this]; exact ih.mul (continuous_apply _)

theorem continuous_Pvec : Continuous fun c : Fin (n + 1) → G => fun j => P c j :=
  continuous_pi fun j => continuous_P j

theorem continuous_tOf (δ : Fin (n + 1) → G) : Continuous fun s : G => tOf δ s :=
  continuous_pi fun j => (continuous_const.mul continuous_id).mul continuous_const

end TwistedSectionAux

section M4Generic
open AutomorphicForm CentralTorus TwistedSectionAux

theorem isRegularSemisimple_conj {A : Type} [CommRing A] (γ y : GL (Fin 2) A) (hγ : IsRegularSemisimple γ) :
    IsRegularSemisimple (y * γ * y⁻¹) := by
  unfold IsRegularSemisimple at hγ ⊢
  have hyy : ((y⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * (y : Matrix (Fin 2) (Fin 2) A) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : Matrix.trace ((y * γ * y⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.trace (γ : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, hyy, Matrix.one_mul]
  have hdet : Matrix.det ((y * γ * y⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = Matrix.det (γ : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (y : Matrix (Fin 2) (Fin 2) A)), mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, mul_one]
  rw [htr, hdet]; exact hγ

theorem secondCountableTopology_tensor' (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (L ⊗[K] A)
  have hq : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  exact hq.isQuotientMap.secondCountableTopology hq.isOpenMap

end M4Generic

section TSCentSplit
open AutomorphicForm CentralTorus TwistedSectionAux

theorem exists_continuous_section_scalar
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (hμA : @Measure.IsHaarMeasure (GL (Fin 2) A) _ _ (glBorelOf A) μA)
    (hμAr : @Measure.IsMulRightInvariant (GL (Fin 2) A) (glBorelOf A) _ μA)
    (z : Aˣ)
    (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)))
      (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)))
    (c₀ : ℝ≥0) (hc₀ : c₀ ≠ 0)
    (hτ : @Measure.map _ _ (centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) (glBorelOf A)
      Subtype.val τ = c₀ • μA) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    ∃ w : GL (Fin 2) A → ℝ, (∀ x, 0 ≤ w x) ∧ Continuous w ∧ HasCompactSupport w ∧
      ∀ x : GL (Fin 2) A, ∫ t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)),
        w ((t : GL (Fin 2) A) * x) ∂τ = 1 := by
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A))) :=
    centralizerBorel A (Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI := SplitCentralAux.locallyCompactSpace_gl A
  haveI := SplitCentralAux.secondCountableTopology_gl A
  haveI : μA.IsHaarMeasure := hμA
  haveI : μA.IsMulRightInvariant := hμAr

  obtain ⟨ψ, hψ1, -, hψcs, hψ01⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton : IsCompact ({1} : Set (GL (Fin 2) A)))
    isClosed_empty (Set.disjoint_empty _)
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => (hψ01 x).1
  have hψpos : 0 < ∫ x, ψ x ∂μA :=
    ψ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hψcs hψ0 (by rw [hψ1 (Set.mem_singleton 1)]; exact one_ne_zero)
  set m : ℝ := ∫ x, ψ x ∂μA with hm
  have hc₀pos : 0 < (c₀ : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hc₀
  set a : ℝ := ((c₀ : ℝ) * m)⁻¹ with ha
  have hapos : 0 < a := by rw [ha]; positivity
  refine ⟨fun x => a * ψ x, fun x => mul_nonneg hapos.le (hψ0 x), continuous_const.mul ψ.continuous, hψcs.mul_left, fun x => ?_⟩
  have hval : Measurable (Subtype.val : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)) → GL (Fin 2) A) :=
    continuous_subtype_val.measurable
  have h1 : ∫ t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) z} : Set (GL (Fin 2) A)), a * ψ ((t : GL (Fin 2) A) * x) ∂τ
      = ∫ g, a * ψ (g * x) ∂(Measure.map Subtype.val τ) := by
    rw [integral_map hval.aemeasurable]
    exact ((continuous_const.mul (ψ.continuous.comp (continuous_id.mul continuous_const))).measurable.aestronglyMeasurable)
  rw [h1, hτ, integral_smul_nnreal_measure, integral_const_mul, integral_mul_right_eq_self (fun g => ψ g) x, ← hm, ha]
  rw [NNReal.smul_def, smul_eq_mul]; push_cast
  field_simp

theorem exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom_field
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [Field A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (ι : L →ₐ[K] A)
    (δ : GL (Fin 2) (L ⊗[K] A)) (z : Aˣ)
    (hδ : normString K L A σ δ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ w : GL (Fin 2) (L ⊗[K] A) → ℝ, IsTwistedSectionFnOn K L A σ δ τ' φ w ∧ Continuous w := by
  classical
  letI mG : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  letI mGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  letI mT : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (GL (Fin 2) A) := borelSpace_glBorelOf A
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
  haveI : T2Space (L ⊗[K] A) := t2Space_tensor K L A
  haveI : LocallyCompactSpace (L ⊗[K] A) := locallyCompactSpace_tensor K L A
  haveI : SecondCountableTopology (L ⊗[K] A) := secondCountableTopology_tensor' K L A
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A
  haveI : LocallyCompactSpace (GL (Fin 2) A) := SplitCentralAux.locallyCompactSpace_gl A
  haveI : SecondCountableTopology (GL (Fin 2) A) := SplitCentralAux.secondCountableTopology_gl A
  haveI : LocallyCompactSpace (GL (Fin 2) (L ⊗[K] A)) := SplitCentralAux.locallyCompactSpace_gl (L ⊗[K] A)
  haveI : SecondCountableTopology (GL (Fin 2) (L ⊗[K] A)) := SplitCentralAux.secondCountableTopology_gl (L ⊗[K] A)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : τ'.IsHaarMeasure := hτ'
  let μA : Measure (GL (Fin 2) A) := Measure.haar
  have hμAr : μA.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μA).1
  obtain ⟨hΘc, hΘc', hΘσ, hΘ1, hΘN, hΘN0, -⟩ :=
    AutomorphicForm.SplitPlace.continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
      K L hdeg σ hσ A ι (Measure.haar) inferInstance μA inferInstance
  set Θ := AutomorphicForm.SplitPlace.coords A σ ι hdeg hσ with hΘdef
  set dv : Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A := Θ δ with hdv
  set ν : GL (Fin 2) A := Matrix.GeneralLinearGroup.scalar (Fin 2) z with hνz
  have hνdef : (List.ofFn dv).prod = ν := by
    rw [hdv, ← hΘN0, hδ, hΘ1]

  have hΘσ' : ∀ x d : GL (Fin 2) (L ⊗[K] A),
      Θ (x⁻¹ * d * sigmaGL K L A σ x) = fun j => (Θ x j)⁻¹ * Θ d j * Θ x (j + 1) := by
    intro x d; funext j; simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hΘσ]
  have hmem : ∀ s : GL (Fin 2) (L ⊗[K] A), s ∈ twistedCentralizer K L A σ δ ↔
      ∀ j, (Θ s j)⁻¹ * dv j * Θ s (j + 1) = dv j := by
    intro s; rw [SplitLiftAux.mem_twistedCentralizer_iff_shift K L A σ Θ hΘσ' δ s, hdv]
  have hcen : ∀ t : twistedCentralizer K L A σ δ, Θ (t : GL (Fin 2) (L ⊗[K] A)) 0 ∈ Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)) := by
    intro t; rw [Subgroup.mem_centralizer_iff]
    rintro m hm; rw [Set.mem_singleton_iff] at hm; rw [hm, ← hνdef]
    exact (zero_comm_prod_of_shift dv (Θ (t : GL (Fin 2) (L ⊗[K] A))) ((hmem _).1 t.2)).symm
  have hcomm : ∀ s : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)), (s : GL (Fin 2) A) * (List.ofFn dv).prod = (List.ofFn dv).prod * s := by
    intro s; rw [hνdef]; exact ((Subgroup.mem_centralizer_iff.1 s.2) ν (Set.mem_singleton ν)).symm
  have hin : ∀ s : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)), Θ.symm (tOf dv (s : GL (Fin 2) A)) ∈ twistedCentralizer K L A σ δ := by
    intro s; rw [hmem]; intro j; rw [MulEquiv.apply_symm_apply]; exact tOf_shift dv _ (hcomm s) j
  let e : twistedCentralizer K L A σ δ ≃* Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)) :=
    { toFun := fun t => ⟨Θ (t : GL (Fin 2) (L ⊗[K] A)) 0, hcen t⟩
      invFun := fun s => ⟨Θ.symm (tOf dv (s : GL (Fin 2) A)), hin s⟩
      left_inv := fun t => Subtype.ext (by
        show Θ.symm (tOf dv (Θ (t : GL (Fin 2) (L ⊗[K] A)) 0)) = t
        apply Θ.symm_apply_eq.mpr
        exact (eq_tOf_of_shift dv _ ((hmem _).1 t.2)).symm)
      right_inv := fun s => Subtype.ext (by
        show Θ (Θ.symm (tOf dv (s : GL (Fin 2) A))) 0 = s
        rw [MulEquiv.apply_symm_apply, tOf_zero])
      map_mul' := fun a b => Subtype.ext (by
        show Θ ((a : GL (Fin 2) (L ⊗[K] A)) * b) 0 = Θ (a : GL (Fin 2) (L ⊗[K] A)) 0 * Θ (b : GL (Fin 2) (L ⊗[K] A)) 0
        rw [map_mul, Pi.mul_apply]) }
  have hec : Continuous e :=
    ((continuous_apply (0 : Fin (Module.finrank K L - 1 + 1))).comp (hΘc.comp continuous_subtype_val)).subtype_mk _
  have hec' : Continuous e.symm :=
    (hΘc'.comp ((continuous_tOf dv).comp continuous_subtype_val)).subtype_mk _
  let eC : twistedCentralizer K L A σ δ ≃ₜ* Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)) :=
    { e with continuous_toFun := hec, continuous_invFun := hec' }
  have heC : ∀ t, ((eC t : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A))) : GL (Fin 2) A) = Θ (t : GL (Fin 2) (L ⊗[K] A)) 0 := fun t => rfl
  letI mC : MeasurableSpace (Subgroup.centralizer ({ν} : Set (GL (Fin 2) A))) := centralizerBorel A ν
  haveI : BorelSpace (Subgroup.centralizer ({ν} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  let τν : Measure (Subgroup.centralizer ({ν} : Set (GL (Fin 2) A))) := Measure.map eC τ'
  haveI hτν : τν.IsHaarMeasure := eC.isHaarMeasure_map τ'

  obtain ⟨c₀, hc₀ne, hc₀⟩ : ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧ Measure.map Subtype.val τν = c₀ • μA := by
    have htop : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x; rw [Subgroup.mem_centralizer_iff]
      rintro m rfl
      rw [hνz]; refine Units.ext ?_
      push_cast
      exact (Matrix.scalar_commute (z : A) (fun r' => mul_comm _ r') (x : Matrix (Fin 2) (Fin 2) A)).eq
    let e0 : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)) ≃* GL (Fin 2) A :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have he0 : ∀ s, e0 s = (s : GL (Fin 2) A) := fun s => rfl
    let e1 : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)) ≃ₜ* GL (Fin 2) A :=
      { e0 with
        continuous_toFun := by
          show Continuous fun s => e0 s
          simp only [he0]; exact continuous_subtype_val
        continuous_invFun := by
          have : ∀ g, e0.symm g = ⟨g, htop.symm ▸ Subgroup.mem_top g⟩ := fun g => by
            apply e0.injective; rw [MulEquiv.apply_symm_apply]; rfl
          show Continuous fun g => e0.symm g
          simp only [this]; exact continuous_id.subtype_mk _ }
    have he1 : ⇑e1 = (Subtype.val : _ → GL (Fin 2) A) := funext he0
    haveI : (Measure.map Subtype.val τν).IsHaarMeasure := by rw [← he1]; exact e1.isHaarMeasure_map τν
    exact ⟨Measure.haarScalarFactor (Measure.map Subtype.val τν) μA, (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
      Measure.isMulLeftInvariant_eq_smul _ _⟩

  obtain ⟨w, hw0, hwc, hwcs, hw1⟩ := exists_continuous_section_scalar A μA inferInstance hμAr z τν c₀ hc₀ne hc₀

  let Φ : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℂ := fun ξ => φ (Θ.symm ξ)
  have hΦcs : HasCompactSupport Φ := hφc.comp_homeomorph ⟨Θ.symm.toEquiv, hΘc', hΘc⟩
  let C := tsupport Φ
  have hC : IsCompact C := hΦcs
  let R₀ : Set (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) := (fun c => fun j => P c j) '' C
  have hR₀ : IsCompact R₀ := hC.image continuous_Pvec
  obtain ⟨β, hβ1, -, hβcs, hβ01⟩ := exists_continuous_one_zero_of_isCompact hR₀ isClosed_empty (Set.disjoint_empty R₀)
  let R : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
    fun ξ j => (ξ 0)⁻¹ * P dv j * ξ j
  have hRc : Continuous R := continuous_pi fun j =>
    (((continuous_apply 0).inv).mul continuous_const).mul (continuous_apply j)
  let W : (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → ℝ := fun ξ => w (ξ 0) * β (R ξ)
  have hWc : Continuous W := (hwc.comp (continuous_apply 0)).mul (β.continuous.comp hRc)
  let w' : GL (Fin 2) (L ⊗[K] A) → ℝ := fun x => W (Θ x)
  have hw'c : Continuous w' := hWc.comp hΘc
  let M : GL (Fin 2) A × (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) → (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
    fun p j => (P dv j)⁻¹ * p.1 * p.2 j
  have hMc : Continuous M := continuous_pi fun j =>
    ((continuous_const.mul continuous_fst)).mul ((continuous_apply j).comp continuous_snd)
  have hWcs : HasCompactSupport W := by
    refine HasCompactSupport.intro ((hwcs.prod hβcs).image hMc) fun ξ hξ => ?_
    by_contra hne
    have hw_ne : w (ξ 0) ≠ 0 := fun h => hne (by simp [W, h])
    have hβ_ne : β (R ξ) ≠ 0 := fun h => hne (by simp [W, h])
    apply hξ
    refine ⟨(ξ 0, R ξ), ⟨subset_tsupport _ hw_ne, subset_tsupport _ hβ_ne⟩, ?_⟩
    funext j; show (P dv j)⁻¹ * ξ 0 * ((ξ 0)⁻¹ * P dv j * ξ j) = ξ j; group
  have hw'cs : HasCompactSupport w' := hWcs.comp_homeomorph ⟨Θ.toEquiv, hΘc, hΘc'⟩
  refine ⟨w', ⟨fun x => mul_nonneg (hw0 _) (hβ01 _).1, hw'c.measurable, hw'cs, ?_⟩, hw'c⟩
  intro x hx
  set ξ := Θ x with hξ
  have htwc_mem : (fun j => (ξ j)⁻¹ * dv j * ξ (j + 1)) ∈ C := by
    apply subset_tsupport
    rw [Function.mem_support]
    show φ (Θ.symm (fun j => (ξ j)⁻¹ * dv j * ξ (j + 1))) ≠ 0
    have : Θ.symm (fun j => (ξ j)⁻¹ * dv j * ξ (j + 1)) = x⁻¹ * δ * sigmaGL K L A σ x := by
      apply Θ.symm_apply_eq.mpr; rw [hΘσ']
    rwa [this]
  have hRξ : R ξ ∈ R₀ := ⟨_, htwc_mem, by funext j; exact (inv_mul_P_mul_eq_P_twc dv ξ j).symm⟩
  have hβR : β (R ξ) = 1 := hβ1 hRξ
  have hint : ∀ t : twistedCentralizer K L A σ δ,
      w' ((t : GL (Fin 2) (L ⊗[K] A)) * x) = w (((eC t : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A))) : GL (Fin 2) A) * ξ 0) := by
    intro t
    have ht : Θ (t : GL (Fin 2) (L ⊗[K] A)) = tOf dv (Θ (t : GL (Fin 2) (L ⊗[K] A)) 0) := eq_tOf_of_shift dv _ ((hmem _).1 t.2)
    show W (Θ ((t : GL (Fin 2) (L ⊗[K] A)) * x)) = _
    rw [map_mul, ← hξ, ht, heC]
    simp only [W]
    have hR_inv : R (tOf dv (Θ (t : GL (Fin 2) (L ⊗[K] A)) 0) * ξ) = R ξ := by
      funext j; simp only [R, Pi.mul_apply, tOf_apply, P_zero, inv_one, one_mul, mul_one]; group
    rw [hR_inv, hβR, mul_one, Pi.mul_apply, tOf_zero]
  simp_rw [hint]
  have hmeas : AEMeasurable (fun t : twistedCentralizer K L A σ δ => eC t) τ' := eC.continuous.measurable.aemeasurable
  have : ∫ t : twistedCentralizer K L A σ δ, w (((eC t : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A))) : GL (Fin 2) A) * ξ 0) ∂τ'
      = ∫ s : Subgroup.centralizer ({ν} : Set (GL (Fin 2) A)), w ((s : GL (Fin 2) A) * ξ 0) ∂τν := by
    rw [show τν = Measure.map (fun t => eC t) τ' from rfl, integral_map hmeas]
    exact ((hwc.comp (continuous_subtype_val.mul continuous_const)).measurable.aestronglyMeasurable)
  rw [this]
  exact hw1 (ξ 0)

end TSCentSplit

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [Field A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (ι : L →ₐ[K] A)
    (δ : GL (Fin 2) (L ⊗[K] A)) (z : Aˣ)
    (hδ : normString K L A σ δ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ w : GL (Fin 2) (L ⊗[K] A) → ℝ, IsTwistedSectionFnOn K L A σ δ τ' φ w ∧ Continuous w := by
  exact exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom_field K L hdeg σ hσ A ι δ z hδ φ hφ hφc τ' hτ'

#print axioms solution

end S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom (solution)
