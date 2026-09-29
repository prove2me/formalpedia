-- Prove2me | solution 1 for AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3d413f73-ccb9-55d8-929d-8606cb69e235

import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import Theorems.Thm_AutomorphicForm_exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field
import Theorems.Thm_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_real
import Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real
import Theorems.Thm_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AutomorphicForm_SplitPlace_continuous_coords_and_coords_sigmaGL_and_coords_normString_and_exists_pos_map_coords_eq_smul_pi
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal ENNReal

open MeasureTheory
open scoped NNReal ENNReal

namespace SplitCentralAux
open AutomorphicForm

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

theorem SplitCoordAux.isRegularSemisimple_normString_of_isNormConjugator
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (hy : AutomorphicForm.IsNormConjugator K L A σ γ δ y) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ) := by
  have hN : AutomorphicForm.normString K L A σ δ = y * AutomorphicForm.toTensorGL K L A γ * y⁻¹ := by
    rw [show AutomorphicForm.toTensorGL K L A γ = y⁻¹ * AutomorphicForm.normString K L A σ δ * y from hy]; group
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  rw [hN]
  set T : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) := ((AutomorphicForm.toTensorGL K L A γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
  have hyy : ((y⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : Matrix.trace (((y * AutomorphicForm.toTensorGL K L A γ * y⁻¹ : GL (Fin 2) (L ⊗[K] A))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = Matrix.trace T := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, hyy, Matrix.one_mul]
  have hdet : Matrix.det (((y * AutomorphicForm.toTensorGL K L A γ * y⁻¹ : GL (Fin 2) (L ⊗[K] A))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) = Matrix.det T := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))), mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, mul_one]
  rw [htr, hdet]

  let f : A →+* L ⊗[K] A := (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom
  have hT : T = (γ : Matrix (Fin 2) (Fin 2) A).map f := rfl
  rw [hT]
  have hdet2 : Matrix.det ((γ : Matrix (Fin 2) (Fin 2) A).map f) = f (Matrix.det (γ : Matrix (Fin 2) (Fin 2) A)) := (RingHom.map_det f _).symm
  rw [hdet2]
  have htr2 : Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) A).map f) = f (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) A)) := by
    simp [Matrix.trace, Matrix.map_apply, map_sum]
  rw [htr2, ← map_pow, show (4 : L ⊗[K] A) = f 4 from (map_ofNat f 4).symm, ← map_mul, ← map_sub]
  exact hγ.map f

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

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
    (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℝ σ ι hdeg hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      HasCompactSupport φ)
    (f : GL (Fin 2) ℝ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
    (c : ℝˣ)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ δ : GL (Fin 2) (L ⊗[K] ℝ), IsRegularSemisimple (normString K L ℝ σ δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] ℝ), IsNormConjugator K L ℝ σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
        (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
        Coupled K L ℝ σ γ δ y τ τ' →
        ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I) :
    ∀ δ y : GL (Fin 2) (L ⊗[K] ℝ),
      IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
            (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
        Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
        ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I' := by
  intro δ y hy τ τ' hτ hτ' hcpl I' hI'
  classical
  letI mG : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  letI mGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] ℝ)) := glBorelOf (L ⊗[K] ℝ)
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf ℝ
  haveI : LocallyCompactSpace (GL (Fin 2) ℝ) := SplitCentralAux.locallyCompactSpace_gl ℝ
  haveI : SecondCountableTopology (GL (Fin 2) ℝ) := SplitCentralAux.secondCountableTopology_gl ℝ
  haveI : μA.IsHaarMeasure := hμA

  have hμAr : μA.IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two μA).1

  have hsec : ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
      ∀ τ₁ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ₁ →
      ∀ h : GL (Fin 2) ℝ → ℂ, HasCompactSupport h →
        ∃ w : GL (Fin 2) ℝ → ℝ, IsSectionFnOn ℝ γ τ₁ h w ∧ Continuous w := by
    intro γ hγ τ₁ hτ₁ h hh
    let hs : GL (Fin 2) ℝ → ℂ := (tsupport h).indicator (fun _ => (1 : ℂ))
    have hsm : Measurable hs := (measurable_const.indicator hh.isCompact.isClosed.measurableSet)
    have hscs : HasCompactSupport hs := by
      refine HasCompactSupport.intro hh fun x hx => ?_
      simp [hs, Set.indicator_of_notMem hx]
    have hsb : ∃ C : ℝ, ∀ g, ‖hs g‖ ≤ C := ⟨1, fun g => by
      by_cases hg : g ∈ tsupport h <;> simp [hs, hg]⟩
    obtain ⟨⟨w, hw, hwc⟩, -⟩ := AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field ℝ μA hμA γ hγ τ₁ hτ₁ hs hsm hscs hsb
    refine ⟨w, ⟨hw.1, hw.2.1, hw.2.2.1, fun x hx => hw.2.2.2 x ?_⟩, hwc⟩
    have hmem : x⁻¹ * γ * x ∈ tsupport h := subset_tsupport _ (Function.mem_support.2 hx)
    simp [hs, Set.indicator_of_mem hmem]

  obtain ⟨κ, hκ, hgen⟩ := AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_smul_splitFibreIntegral_of_isTwistedOrbitalIntegralOn_of_algHom_of_prime_of_forall_exists_isSectionFnOn_of_isMulRightInvariant K L hdeg σ hσ ℝ ι μL hμL μA hμA hsec hμAr
  obtain ⟨⟨Φs, hΦs, hφΦ⟩, hφcs⟩ := hφ
  have hφc : Continuous φ := by
    haveI : IsTopologicalRing (L ⊗[K] ℝ) := isTopologicalRing_tensor K L ℝ
    have hrepr : φ = fun g : GL (Fin 2) (L ⊗[K] ℝ) => Φs (fun k i j => SplitPlace.psi K L ℝ σ ι ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ)) i j) k) := by
      funext g; rw [hφΦ]; rfl
    rw [hrepr]
    refine hΦs.continuous.comp ?_
    refine continuous_pi fun k => continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply k).comp ((SplitPlace.continuous_psi ℝ σ ι).comp
      ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (L ⊗[K] ℝ))).matrix_elem i j))
  obtain ⟨hreg, hcent⟩ := hgen φ hφc hφcs

  obtain ⟨c₀, hc₀ne, hc₀⟩ : ∃ c₀ : ℝ≥0, c₀ ≠ 0 ∧
      @Measure.map _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) (glBorelOf ℝ) Subtype.val τ = c₀ • μA := by
    letI mT : MeasurableSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) :=
      centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    haveI : BorelSpace (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
    haveI : τ.IsHaarMeasure := hτ
    have htop : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      rw [Subgroup.mem_centralizer_iff]
      rintro m rfl
      refine Units.ext ?_
      push_cast
      exact (Matrix.scalar_commute (c : ℝ) (fun r' => mul_comm _ r') (x : Matrix (Fin 2) (Fin 2) ℝ)).eq
    let e0 : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) ≃* GL (Fin 2) ℝ :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    have he0 : ∀ s, e0 s = (s : GL (Fin 2) ℝ) := fun s => rfl
    let e : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) ≃ₜ* GL (Fin 2) ℝ :=
      { e0 with
        continuous_toFun := by
          show Continuous fun s => e0 s
          simp only [he0]; exact continuous_subtype_val
        continuous_invFun := by
          have : ∀ g, e0.symm g = ⟨g, htop.symm ▸ Subgroup.mem_top g⟩ := fun g => by
            apply e0.injective; rw [MulEquiv.apply_symm_apply]; rfl
          show Continuous fun g => e0.symm g
          simp only [this]; exact continuous_id.subtype_mk _ }
    have he : ⇑e = (Subtype.val : _ → GL (Fin 2) ℝ) := funext he0
    haveI : (Measure.map Subtype.val τ).IsHaarMeasure := by
      rw [← he]; exact e.isHaarMeasure_map τ
    refine ⟨Measure.haarScalarFactor (Measure.map Subtype.val τ) μA, (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
      Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hI'v := hcent δ c y hy τ τ' hτ hτ' hcpl c₀ hc₀ I' hI'

  obtain ⟨⟨F₂, hF₂s, hF₂⟩, hFcs⟩ :=
    AutomorphicForm.contDiff_splitFibreIntegral_psiGL_real K L hdeg σ hσ ι μA hμA φ ⟨⟨Φs, hΦs, hφΦ⟩, hφcs⟩
  obtain ⟨⟨F₁, hF₁s, hF₁⟩, hfcs⟩ := hf

  set g : GL (Fin 2) ℝ → ℂ := fun x => f x - ((κ : ℝ) • splitFibreIntegral K L hdeg σ hσ ℝ ι μA φ) x with hgdef
  have hgerm : g (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 := by
    refine AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegralOn_real_eq_zero
      μA hμA g ⟨⟨fun m => F₁ m - (κ : ℂ) * F₂ m, hF₁s.sub (contDiff_const.mul hF₂s), fun x => ?_⟩, ?_⟩ c ?_
    · simp only [hgdef, hF₁, Pi.smul_apply, hF₂, Complex.real_smul]
    · refine hfcs.sub (hFcs.mono fun x hx => ?_)
      intro h0; apply hx; simp [Pi.smul_apply, h0]
    ·
      obtain ⟨V, hV, hmatchV⟩ := hmatch
      refine ⟨V, hV, fun γ hγV _hdet hγ τγ hτγ I hI => ?_⟩
      letI mT : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) := centralizerBorel ℝ γ
      set Fκ : GL (Fin 2) ℝ → ℂ := (κ : ℝ) • splitFibreIntegral K L hdeg σ hσ ℝ ι μA φ with hFκ
      have hent : Continuous fun x : GL (Fin 2) ℝ => fun i j => (x : Matrix (Fin 2) (Fin 2) ℝ) i j :=
        continuous_pi fun i => continuous_pi fun j => (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)).matrix_elem i j
      have hfcont : Continuous f := by
        rw [show f = fun x : GL (Fin 2) ℝ => F₁ (fun i j => (x : Matrix (Fin 2) (Fin 2) ℝ) i j) from funext hF₁]; exact hF₁s.continuous.comp hent
      have hFcont : Continuous Fκ := by
        have : Fκ = fun x : GL (Fin 2) ℝ => (κ : ℂ) * F₂ (fun i j => (x : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
          funext x; simp only [hFκ, Pi.smul_apply, hF₂, Complex.real_smul]
        rw [this]; exact continuous_const.mul (hF₂s.continuous.comp hent)
      have hFκcs : HasCompactSupport Fκ := hFcs.mono fun x hx => by intro h0; apply hx; simp [hFκ, Pi.smul_apply, h0]
      have hgfun : g = fun x => f x - Fκ x := by rw [hgdef]
      have hgcont : Continuous g := by rw [hgfun]; exact hfcont.sub hFcont
      have hgcs : HasCompactSupport g := by rw [hgfun]; exact hfcs.sub hFκcs
      have bdd : ∀ u : GL (Fin 2) ℝ → ℂ, Continuous u → HasCompactSupport u → ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C := by
        intro u hu hucs; obtain ⟨C, hC⟩ := hucs.exists_bound_of_continuous hu; exact ⟨C, hC⟩

      let hs : GL (Fin 2) ℝ → ℂ := fun x => ((‖f x‖ + ‖Fκ x‖ : ℝ) : ℂ)
      have hsc : Continuous hs := Complex.continuous_ofReal.comp (hfcont.norm.add hFcont.norm)
      have hscs : HasCompactSupport hs := by
        refine HasCompactSupport.intro (hfcs.isCompact.union hFκcs.isCompact) fun x hx => ?_
        rw [Set.mem_union, not_or] at hx
        simp [hs, image_eq_zero_of_notMem_tsupport hx.1, image_eq_zero_of_notMem_tsupport hx.2]
      obtain ⟨⟨ws, hws, hwsc⟩, -⟩ := AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field ℝ μA hμA γ hγ τγ hτγ hs hsc.measurable hscs (bdd hs hsc hscs)
      obtain ⟨hws0, hwsm, hwscs, hws1⟩ := hws
      have hspos : ∀ x, f x ≠ 0 ∨ Fκ x ≠ 0 → hs x ≠ 0 := by
        intro x hx h0
        have h0' : ‖f x‖ + ‖Fκ x‖ = 0 := by
          have h1 : ((‖f x‖ + ‖Fκ x‖ : ℝ) : ℂ) = 0 := h0
          exact_mod_cast h1
        rcases hx with h | h
        · exact h (norm_eq_zero.mp (by linarith [norm_nonneg (f x), norm_nonneg (Fκ x)]))
        · exact h (norm_eq_zero.mp (by linarith [norm_nonneg (f x), norm_nonneg (Fκ x)]))
      have secf : IsSectionFnOn ℝ γ τγ f ws := ⟨hws0, hwsm, hwscs, fun x hx => hws1 x (hspos _ (Or.inl hx))⟩
      have secF : IsSectionFnOn ℝ γ τγ Fκ ws := ⟨hws0, hwsm, hwscs, fun x hx => hws1 x (hspos _ (Or.inr hx))⟩
      have secg : IsSectionFnOn ℝ γ τγ g ws := ⟨hws0, hwsm, hwscs, fun x hx => hws1 x (hspos _ (by
        by_contra hcon; simp only [not_or, not_not] at hcon; apply hx; rw [hgfun]; simp [hcon.1, hcon.2]))⟩

      obtain ⟨δ₁, hδ₁N, τ₁, hτ₁, hcpl₁⟩ := SplitLiftAux.exists_splitLift_coupled K L hdeg σ hσ ℝ ι μL hμL μA hμA γ τγ hτγ
      have hNreg : IsRegularSemisimple (normString K L ℝ σ δ₁) :=
        SplitCoordAux.isRegularSemisimple_normString_of_isNormConjugator K L ℝ σ γ δ₁ 1 hδ₁N hγ
      obtain ⟨I₁, hI₁⟩ := AutomorphicForm.exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real
        K L hdeg σ hσ ι μL hμL γ hγ δ₁ 1 hδ₁N τ₁ hτ₁ φ hφc hφcs
      set If : ℂ := ∫ x, f (x⁻¹ * γ * x) * (ws x : ℂ) ∂μA with hIf
      have hOIf : IsOrbitalIntegralOn ℝ μA γ τγ f If := ⟨ws, secf, hIf⟩
      have hm : I₁ = If := hmatchV δ₁ hNreg γ hγV hγ 1 hδ₁N τγ τ₁ hτγ hτ₁ hcpl₁ If I₁ hI₁ hOIf
      have hOIF : IsOrbitalIntegralOn ℝ μA γ τγ Fκ I₁ := by
        rw [hFκ]; exact hreg δ₁ γ hγ 1 hδ₁N τγ τ₁ hτγ hτ₁ hcpl₁ I₁ hI₁
      obtain ⟨-, hiffF⟩ := AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field ℝ μA hμA γ hγ τγ hτγ Fκ hFcont.measurable hFκcs (bdd Fκ hFcont hFκcs)
      obtain ⟨-, hiffg⟩ := AutomorphicForm.exists_continuous_isSectionFnOn_and_isOrbitalIntegralOn_iff_of_isRegularSemisimple_of_field ℝ μA hμA γ hγ τγ hτγ g hgcont.measurable hgcs (bdd g hgcont hgcs)
      have hIF : I₁ = ∫ x, Fκ (x⁻¹ * γ * x) * (ws x : ℂ) ∂μA := (hiffF ws secF I₁).1 hOIF
      have hIg : I = ∫ x, g (x⁻¹ * γ * x) * (ws x : ℂ) ∂μA := (hiffg ws secg I).1 hI

      have hconj : Continuous fun x : GL (Fin 2) ℝ => x⁻¹ * γ * x := (continuous_inv.mul continuous_const).mul continuous_id
      have hwc' : Continuous fun x => ((ws x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hwsc
      have hwcs' : HasCompactSupport fun x => ((ws x : ℝ) : ℂ) := hwscs.comp_left Complex.ofReal_zero
      have hint_f : Integrable (fun x => f (x⁻¹ * γ * x) * (ws x : ℂ)) μA :=
        ((hfcont.comp hconj).mul hwc').integrable_of_hasCompactSupport hwcs'.mul_left
      have hint_F : Integrable (fun x => Fκ (x⁻¹ * γ * x) * (ws x : ℂ)) μA :=
        ((hFcont.comp hconj).mul hwc').integrable_of_hasCompactSupport hwcs'.mul_left
      rw [hIg]
      have hsplit : (fun x => g (x⁻¹ * γ * x) * (ws x : ℂ)) = fun x => f (x⁻¹ * γ * x) * (ws x : ℂ) - Fκ (x⁻¹ * γ * x) * (ws x : ℂ) := by
        funext x; rw [hgfun]; ring
      rw [hsplit, integral_sub hint_f hint_F, ← hIf, ← hIF, hm, sub_self]

  obtain ⟨w, hwsec, hwi, hwint⟩ := SplitCentralAux.exists_isSectionFnOn_scalar ℝ μA hμA hμAr c τ c₀ hc₀ne hc₀ f
  refine ⟨w, hwsec, ?_⟩
  have hcentral : ∀ x : GL (Fin 2) ℝ, x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    intro x
    have hc2 : Matrix.GeneralLinearGroup.scalar (Fin 2) c * x = x * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      refine Units.ext ?_
      push_cast
      exact (Matrix.scalar_commute (c : ℝ) (fun r' => mul_comm _ r') (x : Matrix (Fin 2) (Fin 2) ℝ)).eq
    rw [mul_assoc, hc2, ← mul_assoc, inv_mul_cancel, one_mul]
  simp_rw [hcentral]
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal, hwint, hI'v]
  have hfg : f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = ((κ : ℝ) • splitFibreIntegral K L hdeg σ hσ ℝ ι μA φ) (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    have := hgerm; simp only [hgdef] at this; exact (sub_eq_zero.mp this)
  rw [hfg]

#print axioms solution

end S_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple
end P2MW
export P2MW.S_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple (solution)
