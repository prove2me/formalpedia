-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0ad17371-7f1a-5ec1-8d74-cb5990d09cdf

import Mathlib
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_forall_integrableOn_and_setIntegral_one_add_abs_log_norm_le_of_surjective
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_forall_measureReal_inter_norm_le_le_of_surjective
import Theorems.Thm_HeightOneSpectrum_adicCompletion_norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm
import Theorems.Thm_AutomorphicForm_semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow
import Theorems.Thm_Algebra_trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace TwWeightB

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))

noncomputable abbrev ι (s : v.adicCompletion K) : L ⊗[K] v.adicCompletion K := Algebra.TensorProduct.includeRight (R := K) (A := L) s

noncomputable abbrev Mop (u : v.adicCompletion K) (η : L ⊗[K] v.adicCompletion K) : L ⊗[K] v.adicCompletion K :=
  AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η - ι K L v u * η

noncomputable def Top (u : v.adicCompletion K) (z : L ⊗[K] v.adicCompletion K) : L ⊗[K] v.adicCompletion K :=
  ∑ j ∈ Finset.range (Module.finrank K L),
    ι K L v u ^ (Module.finrank K L - 1 - j) * ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z

theorem sigmaTensor_iota (s : v.adicCompletion K) :
    AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ (ι K L v s) = ι K L v s := by
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (v.adicCompletion K)) ((1 : L) ⊗ₜ s) = (1 : L) ⊗ₜ s
  rw [Algebra.TensorProduct.map_tmul]
  simp

theorem sigmaPow_iota (n : ℕ) (s : v.adicCompletion K) :
    ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ n) (ι K L v s) = ι K L v s := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, RingHom.coe_mul, Function.comp_apply, sigmaTensor_iota, ih]

theorem sigmaTensor_mul_apply' (τ₁ τ₂ : L ≃ₐ[K] L) (x : L ⊗[K] v.adicCompletion K) :
    AutomorphicForm.sigmaTensor K L (v.adicCompletion K) (τ₁ * τ₂) x =
      AutomorphicForm.sigmaTensor K L (v.adicCompletion K) τ₁ (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) τ₂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (τ₁ * τ₂).toAlgHom (AlgHom.id K (v.adicCompletion K)) (l ⊗ₜ a) =
      Algebra.TensorProduct.map τ₁.toAlgHom (AlgHom.id K (v.adicCompletion K))
        (Algebra.TensorProduct.map τ₂.toAlgHom (AlgHom.id K (v.adicCompletion K)) (l ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigmaTensor_one_apply' (x : L ⊗[K] v.adicCompletion K) : AutomorphicForm.sigmaTensor K L (v.adicCompletion K) 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l a =>
    change Algebra.TensorProduct.map (1 : L ≃ₐ[K] L).toAlgHom (AlgHom.id K (v.adicCompletion K)) (l ⊗ₜ a) = l ⊗ₜ a
    rw [Algebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaPow_eq (n : ℕ) (x : L ⊗[K] v.adicCompletion K) :
    ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ n) x = AutomorphicForm.sigmaTensor K L (v.adicCompletion K) (σ ^ n) x := by
  induction n with
  | zero => rw [pow_zero, pow_zero, RingHom.one_def, RingHom.id_apply, sigmaTensor_one_apply']
  | succ n ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, ← sigmaTensor_mul_apply', ← pow_succ']

theorem sigmaPow_finrank [FiniteDimensional K L] (x : L ⊗[K] v.adicCompletion K) :
    ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ Module.finrank K L) x = x := by
  have h : σ ^ Module.finrank K L = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = Nat.card (Subgroup.zpowers σ) :=
      IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers σ)
    rw [Nat.card_zpowers] at h1
    rw [← h1]
    exact Dvd.intro_left _ (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)
  rw [sigmaPow_eq, h, sigmaTensor_one_apply']

theorem sigmaTensor_tmul (τ : L ≃ₐ[K] L) (l : L) (a : v.adicCompletion K) :
    AutomorphicForm.sigmaTensor K L (v.adicCompletion K) τ (l ⊗ₜ a) = τ l ⊗ₜ a := by
  change Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id K (v.adicCompletion K)) (l ⊗ₜ a) = τ l ⊗ₜ a
  rw [Algebra.TensorProduct.map_tmul]; rfl

theorem Top_Mop [FiniteDimensional K L] (u : v.adicCompletion K) (η : L ⊗[K] v.adicCompletion K) :
    Top K L σ v u (Mop K L σ v u η) = ι K L v (1 - u ^ Module.finrank K L) * η := by
  set ℓ := Module.finrank K L with hℓ
  set S := AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ with hS

  set a : ℕ → L ⊗[K] v.adicCompletion K := fun j => ι K L v u ^ (ℓ - j) * (S ^ j) η with ha
  have hterm : ∀ j ∈ Finset.range ℓ,
      ι K L v u ^ (ℓ - 1 - j) * (S ^ j) (Mop K L σ v u η) = a (j + 1) - a j := by
    intro j hj
    have hjl : j < ℓ := Finset.mem_range.1 hj
    simp only [ha, Mop]
    rw [map_sub, map_mul, ← hS, sigmaPow_iota, show (S ^ j) (S η) = (S ^ (j + 1)) η by rw [pow_succ, RingHom.coe_mul, Function.comp_apply], mul_sub]
    congr 1
    · rw [show ℓ - (j + 1) = ℓ - 1 - j by omega]
    · rw [← mul_assoc, ← pow_succ, show ℓ - 1 - j + 1 = ℓ - j by omega]
  unfold Top
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub]
  simp only [ha, Nat.sub_self, pow_zero, one_mul, Nat.sub_zero]
  rw [hS, sigmaPow_finrank, RingHom.one_def, RingHom.id_apply]
  simp only [ι, map_sub, map_one, map_pow, sub_mul, one_mul]

theorem Top_one [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (z : L ⊗[K] v.adicCompletion K) :
    Top K L σ v 1 z = ι K L v (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z) := by
  classical
  unfold Top
  simp only [map_one, one_pow, one_mul]

  have hord : orderOf σ = Module.finrank K L :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L)
  have hinj : Set.InjOn (fun j : ℕ => σ ^ j) ↑(Finset.range (Module.finrank K L)) := by
    intro i hi j hj h
    have hi' : i < orderOf σ := by rw [hord]; exact Finset.mem_range.1 hi
    have hj' : j < orderOf σ := by rw [hord]; exact Finset.mem_range.1 hj
    exact pow_injOn_Iio_orderOf hi' hj' h
  have himg : Finset.image (fun j : ℕ => σ ^ j) (Finset.range (Module.finrank K L)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← hord, ← Nat.card_eq_fintype_card]
    exact (orderOf_eq_card_of_forall_mem_zpowers hgen)
  have hsum : ∀ x : L ⊗[K] v.adicCompletion K, ∑ j ∈ Finset.range (Module.finrank K L), ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) x =
      ∑ τ : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L (v.adicCompletion K) τ x := by
    intro x
    simp_rw [sigmaPow_eq]
    rw [← himg, Finset.sum_image hinj]
  rw [hsum]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp_rw [sigmaTensor_tmul]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms,
      Algebra.trace_tensorProduct_rightActions_tmul_eq_algebraMap_trace_mul]
    show algebraMap K L _ ⊗ₜ a = (1 : L) ⊗ₜ (algebraMap K (v.adicCompletion K) _ * a)
    rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]

theorem norm_iota [FiniteDimensional K L] (s : v.adicCompletion K) :
    Algebra.norm (v.adicCompletion K) (ι K L v s) = s ^ Module.finrank K L := by
  have h : ι K L v s = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) s := rfl
  rw [h, Algebra.norm_algebraMap, TensorProduct.finrank_rightAlgebra]

theorem integral_comp_Mop [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (u : (v.adicCompletion K)ˣ) (hu : u ^ Module.finrank K L ≠ 1) (Ψ : L ⊗[K] v.adicCompletion K → ℂ) (hΨ : Measurable Ψ) :
    (‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ : ℂ) *
        ∫ η, Ψ (Mop K L σ v (u : v.adicCompletion K) η) ∂ν = ∫ z, Ψ z ∂ν := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have hN : Algebra.norm (v.adicCompletion K) (ι K L v (u : v.adicCompletion K)) = ((u ^ Module.finrank K L : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    rw [norm_iota, Units.val_pow_eq_pow_val]
  have hN1 : Algebra.norm (v.adicCompletion K) (ι K L v (u : v.adicCompletion K)) ≠ 1 := by
    rw [hN]; exact fun h => hu (Units.val_eq_one.1 h)
  have hmap := AutomorphicForm.map_sigmaTensor_sub_mul_eq_inv_nnnorm_one_sub_norm_smul K L σ hgen v ν
    (ι K L v (u : v.adicCompletion K)) hN1
  have hMeq : (fun y : L ⊗[K] v.adicCompletion K => AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ y - ι K L v (u : v.adicCompletion K) * y) =
      Mop K L σ v (u : v.adicCompletion K) := rfl
  rw [hMeq, hN] at hmap
  have hcont : Continuous (Mop K L σ v (u : v.adicCompletion K)) := by
    have hσ : Continuous (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) :=
      IsModuleTopology.continuous_of_linearMap
        (TensorProduct.RightActions.AlgebraMap.baseChange K L L (v.adicCompletion K) σ.toAlgHom).toLinearMap
    exact hσ.sub (continuous_const.mul continuous_id)
  have hint : ∫ η, Ψ (Mop K L σ v (u : v.adicCompletion K) η) ∂ν = ∫ z, Ψ z ∂(Measure.map (Mop K L σ v (u : v.adicCompletion K)) ν) :=
    (integral_map hcont.measurable.aemeasurable hΨ.aestronglyMeasurable).symm
  set c : ℝ := ‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ with hc
  have hc0 : c ≠ 0 := by
    rw [hc, norm_ne_zero_iff, sub_ne_zero]
    exact fun h => hu (Units.val_eq_one.1 h.symm)
  rw [hint, hmap, integral_smul_nnreal_measure]
  rw [show ((‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖₊)⁻¹ : NNReal) •
      ∫ z, Ψ z ∂ν = ((c⁻¹ : ℝ) : ℂ) * ∫ z, Ψ z ∂ν from by
    rw [NNReal.smul_def, Complex.real_smul, NNReal.coe_inv, coe_nnnorm]]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hc0, Complex.ofReal_one, one_mul]

private noncomputable abbrev _root_.TwWeightB.comp (w : v.Extension (𝓞 L)) (y : L ⊗[K] v.adicCompletion K) : w.1.adicCompletion L :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w

p2m_export "TwWeightB" "comp"

theorem comp_mul (w : v.Extension (𝓞 L)) (x y : L ⊗[K] v.adicCompletion K) :
    comp K L v w (x * y) = comp K L v w x * comp K L v w y := by
  simp only [comp, map_mul, Pi.mul_apply]

theorem comp_add (w : v.Extension (𝓞 L)) (x y : L ⊗[K] v.adicCompletion K) :
    comp K L v w (x + y) = comp K L v w x + comp K L v w y := by
  have h := (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toLinearEquiv.map_add x y
  exact congrFun h w

theorem comp_zero (w : v.Extension (𝓞 L)) : comp K L v w (0 : L ⊗[K] v.adicCompletion K) = 0 := by
  have h := (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toLinearEquiv.map_zero
  exact congrFun h w

theorem comp_sub (w : v.Extension (𝓞 L)) (x y : L ⊗[K] v.adicCompletion K) :
    comp K L v w (x - y) = comp K L v w x - comp K L v w y := by
  have h := (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toLinearEquiv.map_sub x y
  exact congrFun h w

theorem comp_finset_sum (w : v.Extension (𝓞 L)) {ι' : Type*} (s : Finset ι') (f : ι' → L ⊗[K] v.adicCompletion K) :
    comp K L v w (∑ i ∈ s, f i) = ∑ i ∈ s, comp K L v w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, comp_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, comp_add, ih]

theorem comp_one (w : v.Extension (𝓞 L)) : comp K L v w (1 : L ⊗[K] v.adicCompletion K) = 1 := by
  simp only [comp, map_one, Pi.one_apply]

theorem norm_comp_iota (w : v.Extension (𝓞 L)) (s : v.adicCompletion K) :
    ‖comp K L v w (ι K L v s)‖ = ‖s‖ ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  have h : ι K L v s = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) s := rfl
  rw [h]
  exact (AutomorphicForm.semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow K L v).2.2 s w

theorem finrank_place_ne_zero (w : v.Extension (𝓞 L)) :
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) ≠ 0 := by
  intro h0
  have h := norm_comp_iota K L v w 0
  rw [h0, pow_zero] at h
  have h2 : ι K L v (0 : v.adicCompletion K) = 0 := by simp only [ι, map_zero]
  rw [h2, comp_zero, norm_zero] at h
  exact zero_ne_one h

theorem comp_ne_zero_of_isUnit (w : v.Extension (𝓞 L)) {x : L ⊗[K] v.adicCompletion K} (hx : IsUnit x) : comp K L v w x ≠ 0 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  intro h0
  have := congrArg (comp K L v w) hy
  rw [comp_mul, h0, zero_mul, comp_one] at this
  exact zero_ne_one this

theorem norm_algebraNorm_eq_prod [FiniteDimensional K L] (x : L ⊗[K] v.adicCompletion K) :
    letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    ‖Algebra.norm (v.adicCompletion K) x‖ = ∏ w : v.Extension (𝓞 L), ‖comp K L v w x‖ := by
  letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  rw [(HeightOneSpectrum.adicCompletion.norm_tensorProduct_eq_finprod_norm_baseChangeAlgEquiv_and_norm_norm_eq_norm K L v).2.2 x, finprod_eq_prod_of_fintype]

theorem prod_norm_pow_finrank_place [FiniteDimensional K L] (s : v.adicCompletion K) :
    letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    ∏ w : v.Extension (𝓞 L), ‖s‖ ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = ‖s‖ ^ Module.finrank K L := by
  letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have h := norm_algebraNorm_eq_prod K L v (ι K L v s)
  rw [norm_iota, norm_pow] at h
  rw [h]
  exact Finset.prod_congr rfl fun w _ => (norm_comp_iota K L v w s).symm

theorem norm_comp_Top_sub_Top_one [FiniteDimensional K L] (w : v.Extension (𝓞 L)) (u : v.adicCompletion K) (hu : ‖u - 1‖ < 1)
    (z : L ⊗[K] v.adicCompletion K) :
    ‖comp K L v w (Top K L σ v u z - Top K L σ v 1 z)‖ ≤
      ‖u - 1‖ ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) *
        ∑ j ∈ Finset.range (Module.finrank K L), ‖comp K L v w (((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z)‖ := by

  have hu1 : ‖u‖ = 1 := by
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := u - 1) (y := (1 : v.adicCompletion K))
      (by rw [norm_one]; exact hu.ne)
    rw [sub_add_cancel, norm_one, max_eq_right hu.le] at h
    exact h
  have hpow : ∀ m : ℕ, ‖u ^ m - 1‖ ≤ ‖u - 1‖ := by
    intro m
    have hgeom : ∀ k : ℕ, ‖∑ i ∈ Finset.range k, u ^ i‖ ≤ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by rw [norm_pow, hu1, one_pow]))
    rw [← geom_sum_mul u m, norm_mul]
    calc ‖∑ i ∈ Finset.range m, u ^ i‖ * ‖u - 1‖ ≤ 1 * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right (hgeom m) (norm_nonneg _)
      _ = _ := one_mul _
  unfold Top
  simp only [map_one, one_pow, one_mul]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range (Module.finrank K L),
      ι K L v u ^ (Module.finrank K L - 1 - j) * ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z -
        ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z =
      ι K L v (u ^ (Module.finrank K L - 1 - j) - 1) * ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z := by
    intro j _
    simp only [ι, map_sub, map_pow, map_one, sub_mul, one_mul]
  rw [Finset.sum_congr rfl hterm, comp_finset_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [comp_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_comp_iota]
  exact pow_le_pow_left₀ (norm_nonneg _) (hpow _) _

theorem trace_surjective [FiniteDimensional K L] :
    Function.Surjective (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) := by
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have hℓ : (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) : v.adicCompletion K) ≠ 0 := by
    rw [TensorProduct.finrank_rightAlgebra]; exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  intro s
  refine ⟨algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (s / (Module.finrank (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) : v.adicCompletion K)), ?_⟩
  rw [Algebra.trace_algebraMap, nsmul_eq_mul, mul_div_assoc', mul_div_cancel_left₀ _ hℓ]

theorem continuous_trace [FiniteDimensional K L] : Continuous (Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)) :=
  IsModuleTopology.continuous_of_linearMap _

theorem continuous_sigmaPow [FiniteDimensional K L] (j : ℕ) :
    Continuous ((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have hσ : Continuous (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) :=
    IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L (v.adicCompletion K) σ.toAlgHom).toLinearMap
  induction j with
  | zero => simpa using continuous_id
  | succ j ih => rw [pow_succ, RingHom.coe_mul]; exact ih.comp hσ

theorem continuous_Top [FiniteDimensional K L] (u : v.adicCompletion K) : Continuous (Top K L σ v u) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  unfold Top
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_sigmaPow K L σ v j)

theorem continuous_comp [FiniteDimensional K L] (w : v.Extension (𝓞 L)) : Continuous (comp K L v w) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI : ContinuousSMul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) := IsModuleTopology.toContinuousSMul (v.adicCompletion K) (L ⊗[K] v.adicCompletion K)
  have h := (continuous_apply w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).continuous
  exact h

theorem continuous_W [FiniteDimensional K L] :
    Continuous fun y : L ⊗[K] v.adicCompletion K => AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 y) := by
  letI := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  have h := (AutomorphicForm.semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow K L v).1
  have heq : (fun y : L ⊗[K] v.adicCompletion K => AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 y)) =
      fun y => ∑ w : v.Extension (𝓞 L), 2 * Real.log (max 1 ‖comp K L v w y‖) := by
    funext y; rw [h y, finsum_eq_sum_of_fintype]
  rw [heq]
  refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
  exact ((continuous_const.max (continuous_norm.comp (continuous_comp K L v w))).log
    fun y => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')

theorem ultra_norm_eq_of_norm_sub_lt {F' : Type*} [NormedField F'] [IsUltrametricDist F'] {a a' : F'} (h : ‖a' - a‖ < ‖a‖) :
    ‖a'‖ = ‖a‖ := by
  apply le_antisymm
  · have h1 : ‖a'‖ = ‖(a' - a) + a‖ := by rw [sub_add_cancel]
    rw [h1]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h.le le_rfl)
  · by_contra hlt
    push_neg at hlt
    have h2 : ‖a‖ = ‖(a - a') + a'‖ := by rw [sub_add_cancel]
    have h3 : ‖a - a'‖ < ‖a‖ := by rwa [norm_sub_rev]
    have := (IsUltrametricDist.norm_add_le_max (a - a') a')
    rw [← h2] at this
    exact absurd (this.trans_lt (max_lt h3 hlt)) (lt_irrefl _)

omit σ L in

theorem norm_pow_sub_one (n : ℕ) (u : v.adicCompletion K) (hu : ‖u - 1‖ < ‖(n : v.adicCompletion K)‖) :
    ‖u ^ n - 1‖ = ‖(n : v.adicCompletion K)‖ * ‖u - 1‖ := by
  have hn1 : ‖(n : v.adicCompletion K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ n
  have hu1 : ‖u‖ = 1 := by
    have := ultra_norm_eq_of_norm_sub_lt (a := 1) (a' := u) (by rw [norm_one]; exact lt_of_lt_of_le hu hn1)
    rwa [norm_one] at this

  have hultra : ∀ (m : ℕ) (g : ℕ → v.adicCompletion K) (C : ℝ), 0 ≤ C → (∀ i, ‖g i‖ ≤ C) →
      ‖∑ i ∈ Finset.range m, g i‖ ≤ C := by
    intro m g C hC hg
    induction m with
    | zero => simp [hC]
    | succ m ih => rw [Finset.sum_range_succ]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (hg m))
  have hgeom : ∀ m : ℕ, ‖∑ i ∈ Finset.range m, u ^ i‖ ≤ 1 := fun m =>
    hultra m (fun i => u ^ i) 1 zero_le_one (fun i => by rw [norm_pow, hu1, one_pow])
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ ≤ ‖u - 1‖ := by
    intro i
    rw [← geom_sum_mul u i, norm_mul]
    calc ‖∑ j ∈ Finset.range i, u ^ j‖ * ‖u - 1‖ ≤ 1 * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right (hgeom i) (norm_nonneg _)
      _ = ‖u - 1‖ := one_mul _
  have hdiff : ‖∑ i ∈ Finset.range n, u ^ i - (n : v.adicCompletion K)‖ ≤ ‖u - 1‖ := by
    have : ∑ i ∈ Finset.range n, u ^ i - (n : v.adicCompletion K) = ∑ i ∈ Finset.range n, (u ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact hultra n (fun i => u ^ i - 1) _ (norm_nonneg _) hpow
  have hS : ‖∑ i ∈ Finset.range n, u ^ i‖ = ‖(n : v.adicCompletion K)‖ :=
    ultra_norm_eq_of_norm_sub_lt (lt_of_le_of_lt hdiff hu)
  rw [← geom_sum_mul u n, norm_mul, hS]

set_option maxHeartbeats 4000000 in

theorem dominance [FiniteDimensional K L] [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (Z : Set (L ⊗[K] v.adicCompletion K)) (hZ : IsCompact Z) (Qc : Set (L ⊗[K] v.adicCompletion K)ˣ) (hQc : IsCompact Qc) :
    ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 ≤ C ∧ ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∀ u : (v.adicCompletion K)ˣ, u ∈ U → u ^ Module.finrank K L ≠ 1 →
      c₀ * ‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ ≤ 1 ∧
      ∀ q : (L ⊗[K] v.adicCompletion K)ˣ, q ∈ Qc → |Real.log ‖Algebra.norm (v.adicCompletion K) (q : L ⊗[K] v.adicCompletion K)‖| ≤ C ∧ ∀ z : L ⊗[K] v.adicCompletion K, z ∈ Z →
        (c₀ * ‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ ≤
            ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ →
          (∀ w : v.Extension (𝓞 L), 1 ≤ ‖comp K L v w
              ((q : L ⊗[K] v.adicCompletion K) * Ring.inverse (ι K L v ((1 : v.adicCompletion K) - (u : v.adicCompletion K) ^ Module.finrank K L)) *
                Top K L σ v (u : v.adicCompletion K) z)‖) ∧
          ‖Algebra.norm (v.adicCompletion K) (Top K L σ v (u : v.adicCompletion K) z)‖ =
            ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ ^ Module.finrank K L) ∧
        (‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ <
            c₀ * ‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ →
          |AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2
              ((q : L ⊗[K] v.adicCompletion K) * Ring.inverse (ι K L v ((1 : v.adicCompletion K) - (u : v.adicCompletion K) ^ Module.finrank K L)) *
                Top K L σ v (u : v.adicCompletion K) z))| ≤ C) := by
  classical
  letI hft : Fintype (v.Extension (𝓞 L)) := IsDedekindDomain.HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

  set n : v.Extension (𝓞 L) → ℕ := fun w => Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) with hn
  set N : ℕ := ∑ w, n w with hN
  have hn1 : ∀ w, 1 ≤ n w := fun w => Nat.one_le_iff_ne_zero.2 (finrank_place_ne_zero K L v w)
  have hnN : ∀ w, n w ≤ N := fun w =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  have hℓpos : 0 < ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ :=
    norm_pos_iff.2 (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  have hℓle : ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _

  set fB : L ⊗[K] v.adicCompletion K → ℝ := fun z => ∑ w, ∑ j ∈ Finset.range (Module.finrank K L),
      ‖comp K L v w (((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z)‖ with hfB
  have hfBc : Continuous fB := by
    refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_norm.comp ((continuous_comp K L v w).comp (continuous_sigmaPow K L σ v j))
  obtain ⟨B₀, hB₀⟩ := hZ.exists_bound_of_continuousOn hfBc.continuousOn
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ z ∈ Z, ∀ w, ∑ j ∈ Finset.range (Module.finrank K L),
      ‖comp K L v w (((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z)‖ ≤ B := by
    intro z hz w
    have h1 : ∑ j ∈ Finset.range (Module.finrank K L),
        ‖comp K L v w (((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z)‖ ≤ fB z := by
      have h := Finset.single_le_sum (f := fun w => ∑ j ∈ Finset.range (Module.finrank K L),
        ‖comp K L v w (((AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ) ^ j) z)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ w)
      beta_reduce at h
      exact h
    have h2 : fB z ≤ B := by
      have h3 := hB₀ z hz
      rw [Real.norm_eq_abs] at h3
      exact (le_abs_self _).trans (h3.trans (le_max_left _ _))
    exact h1.trans h2

  set fM : (L ⊗[K] v.adicCompletion K)ˣ → ℝ := fun q => ∑ w, (‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ + ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖⁻¹) with hfM
  have hfMc : Continuous fM := by
    refine continuous_finsetSum _ fun w _ => ?_
    have h1 : Continuous fun q : (L ⊗[K] v.adicCompletion K)ˣ => ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ :=
      continuous_norm.comp ((continuous_comp K L v w).comp Units.continuous_val)
    exact h1.add (h1.inv₀ fun q => norm_ne_zero_iff.2 (comp_ne_zero_of_isUnit K L v w q.isUnit))
  obtain ⟨M₀, hM₀⟩ := hQc.exists_bound_of_continuousOn hfMc.continuousOn
  set M : ℝ := max M₀ 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMq : ∀ q ∈ Qc, ∀ w, ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ ≤ M ∧ ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖⁻¹ ≤ M := by
    intro q hq w
    have hle : ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ + ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖⁻¹ ≤ fM q := by
      have h := Finset.single_le_sum (f := fun w => ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ + ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖⁻¹)
        (fun _ _ => by positivity) (Finset.mem_univ w)
      beta_reduce at h
      exact h
    have h2 : fM q ≤ M := by
      have h3 := hM₀ q hq
      rw [Real.norm_eq_abs] at h3
      exact (le_abs_self _).trans (h3.trans (le_max_left _ _))
    have hi0 : 0 ≤ ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
    have hq0 := norm_nonneg (comp K L v w (q : L ⊗[K] v.adicCompletion K))
    exact ⟨by linarith, by linarith⟩

  set cℓ : ℝ := ‖((Module.finrank K L : ℕ) : v.adicCompletion K)‖ with hcℓ
  set c₀ : ℝ := M + (B + 1) / cℓ with hc₀def
  have hc₀M : M ≤ c₀ := by
    have h0 : 0 ≤ (B + 1) / cℓ := by positivity
    linarith
  have hc₀1 : 1 ≤ c₀ := hM1.trans hc₀M
  have hc₀pos : 0 < c₀ := lt_of_lt_of_le one_pos hc₀1
  have hc₀ℓ : B + 1 ≤ c₀ * cℓ := by
    rw [hc₀def, add_mul, div_mul_cancel₀ _ hℓpos.ne']
    linarith [mul_nonneg hM0.le hℓpos.le]
  set Y : ℝ := M * (c₀ ^ N + B * cℓ⁻¹ ^ N) with hYdef
  set C : ℝ := max ((Fintype.card (v.Extension (𝓞 L)) : ℝ) * (2 * Real.log (max 1 Y)))
      ((Fintype.card (v.Extension (𝓞 L)) : ℝ) * Real.log M) with hCdef
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlogY : 0 ≤ Real.log (max 1 Y) := Real.log_nonneg (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_of_le_right (by positivity)
  set δ : ℝ := min cℓ c₀⁻¹ with hδ
  have hδpos : 0 < δ := lt_min hℓpos (inv_pos.2 hc₀pos)
  set U : Set (v.adicCompletion K)ˣ := {u | ‖(u : v.adicCompletion K) - 1‖ < δ} with hU
  have hUn : U ∈ nhds (1 : (v.adicCompletion K)ˣ) := by
    have hO : IsOpen U := isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
    exact hO.mem_nhds (by show ‖((1 : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1‖ < δ; simpa using hδpos)
  refine ⟨c₀, C, hc₀pos, hC0, U, hUn, ?_⟩
  intro u hu hul

  have huδ : ‖(u : v.adicCompletion K) - 1‖ < δ := hu
  have huℓ : ‖(u : v.adicCompletion K) - 1‖ < cℓ := lt_of_lt_of_le huδ (min_le_left _ _)
  have huc : ‖(u : v.adicCompletion K) - 1‖ < c₀⁻¹ := lt_of_lt_of_le huδ (min_le_right _ _)
  have hu1 : ‖(u : v.adicCompletion K) - 1‖ < 1 := lt_of_lt_of_le huℓ hℓle
  have hu0 : 0 < ‖(u : v.adicCompletion K) - 1‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h; apply hul; ext; rw [Units.val_pow_eq_pow_val, h, one_pow, Units.val_one]
  set ρ : ℝ := ‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ with hρ
  have hρeq : ρ = cℓ * ‖(u : v.adicCompletion K) - 1‖ := by
    rw [hρ, norm_sub_rev, Units.val_pow_eq_pow_val, hcℓ]
    exact norm_pow_sub_one K v _ _ huℓ
  have hρ0 : 0 < ρ := by rw [hρeq]; exact mul_pos hℓpos hu0
  have hc₀ρ : c₀ * ρ ≤ 1 := by
    have h1 : ρ ≤ ‖(u : v.adicCompletion K) - 1‖ := by
      rw [hρeq]
      calc cℓ * ‖(u : v.adicCompletion K) - 1‖ ≤ 1 * ‖(u : v.adicCompletion K) - 1‖ := mul_le_mul_of_nonneg_right hℓle hu0.le
        _ = _ := one_mul _
    have h2 : c₀ * ‖(u : v.adicCompletion K) - 1‖ < 1 := by
      have := mul_lt_mul_of_pos_left huc hc₀pos; rwa [mul_inv_cancel₀ hc₀pos.ne'] at this
    exact ((mul_le_mul_of_nonneg_left h1 hc₀pos.le).trans h2.le)
  refine ⟨hc₀ρ, fun q hq => ⟨?_, fun z hz => ?_⟩⟩
  ·
    have hprod := norm_algebraNorm_eq_prod K L v (q : L ⊗[K] v.adicCompletion K)
    have hpos : ∀ w, 0 < ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ := fun w =>
      norm_pos_iff.2 (comp_ne_zero_of_isUnit K L v w q.isUnit)
    rw [hprod, Real.log_prod (fun w _ => (hpos w).ne')]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun w _ => ?_) (le_trans (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]) (le_max_right _ _))
    obtain ⟨h1, h2⟩ := hMq q hq w
    rw [abs_le]
    constructor
    · have : M⁻¹ ≤ ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ := by
        have := inv_anti₀ (inv_pos.2 (hpos w)) h2; rwa [inv_inv] at this
      have := Real.log_le_log (inv_pos.2 hM0) this
      rwa [Real.log_inv] at this
    · exact Real.log_le_log (hpos w) h1

  set e : L ⊗[K] v.adicCompletion K := ι K L v ((1 : v.adicCompletion K) - (u : v.adicCompletion K) ^ Module.finrank K L) with he
  have hune : (1 : v.adicCompletion K) - (u : v.adicCompletion K) ^ Module.finrank K L ≠ 0 := by
    rw [sub_ne_zero, ← Units.val_pow_eq_pow_val]; exact fun h => hul (Units.val_eq_one.1 h.symm)
  have heu : IsUnit e := (isUnit_iff_ne_zero.2 hune).map _
  have hce : ∀ w, ‖comp K L v w e‖ = ρ ^ n w := by
    intro w; rw [he, norm_comp_iota, hρ, Units.val_pow_eq_pow_val]
  have hcei : ∀ w, ‖comp K L v w (Ring.inverse e)‖ = (ρ ^ n w)⁻¹ := by
    intro w
    have h1 : comp K L v w (Ring.inverse e) * comp K L v w e = 1 := by
      rw [← comp_mul, Ring.inverse_mul_cancel _ heu, comp_one]
    have h2 := congrArg (fun x => ‖x‖) h1
    simp only [norm_mul, norm_one, hce] at h2
    exact eq_inv_of_mul_eq_one_left h2
  set T : L ⊗[K] v.adicCompletion K := Top K L σ v (u : v.adicCompletion K) z with hT
  set T1 : L ⊗[K] v.adicCompletion K := Top K L σ v 1 z with hT1
  have hT1n : ∀ w, ‖comp K L v w T1‖ = ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ ^ n w := by
    intro w; rw [hT1, Top_one K L σ v hgen, norm_comp_iota]
  have hRn : ∀ w, ‖comp K L v w (T - T1)‖ ≤ ‖(u : v.adicCompletion K) - 1‖ ^ n w * B := by
    intro w
    refine (norm_comp_Top_sub_Top_one K L σ v w (u : v.adicCompletion K) hu1 z).trans ?_
    exact mul_le_mul_of_nonneg_left (hB z hz w) (pow_nonneg (norm_nonneg _) _)
  have hTdec : ∀ w, comp K L v w T = comp K L v w T1 + comp K L v w (T - T1) := by
    intro w; rw [← comp_add, add_sub_cancel]
  have hyn : ∀ w, ‖comp K L v w ((q : L ⊗[K] v.adicCompletion K) * Ring.inverse e * T)‖ =
      ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ * (ρ ^ n w)⁻¹ * ‖comp K L v w T‖ := by
    intro w; rw [comp_mul, comp_mul, norm_mul, norm_mul, hcei]
  have hρℓ : ‖(u : v.adicCompletion K) - 1‖ / ρ = cℓ⁻¹ := by
    rw [hρeq]; field_simp
  set tr : ℝ := ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ with htr
  refine ⟨fun hoff => ?_, fun hslab => ?_⟩
  ·
    have htr0 : 0 < tr := lt_of_lt_of_le (mul_pos hc₀pos hρ0) hoff
    have hdom : ∀ w, ‖comp K L v w (T - T1)‖ < ‖comp K L v w T1‖ := by
      intro w
      have hupos : 0 < ‖(u : v.adicCompletion K) - 1‖ ^ n w := pow_pos hu0 _
      calc ‖comp K L v w (T - T1)‖ ≤ ‖(u : v.adicCompletion K) - 1‖ ^ n w * B := hRn w
        _ < ‖(u : v.adicCompletion K) - 1‖ ^ n w * (B + 1) := mul_lt_mul_of_pos_left (by linarith) hupos
        _ ≤ ‖(u : v.adicCompletion K) - 1‖ ^ n w * (c₀ * cℓ) ^ n w := by
            refine mul_le_mul_of_nonneg_left ?_ hupos.le
            exact hc₀ℓ.trans (le_self_pow₀ (by linarith) (Nat.one_le_iff_ne_zero.1 (hn1 w)))
        _ = (c₀ * ρ) ^ n w := by rw [hρeq, ← mul_pow]; ring
        _ ≤ tr ^ n w := pow_le_pow_left₀ (mul_pos hc₀pos hρ0).le hoff _
        _ = ‖comp K L v w T1‖ := (hT1n w).symm
    have hTn : ∀ w, ‖comp K L v w T‖ = tr ^ n w := by
      intro w
      rw [← hT1n w]
      apply ultra_norm_eq_of_norm_sub_lt
      rw [hTdec w, add_sub_cancel_left]
      exact hdom w
    refine ⟨fun w => ?_, ?_⟩
    · rw [hyn, hTn]
      obtain ⟨h1, h2⟩ := hMq q hq w
      have hq0 : 0 < ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ := norm_pos_iff.2 (comp_ne_zero_of_isUnit K L v w q.isUnit)
      have hqM : M⁻¹ ≤ ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ := by
        have := inv_anti₀ (inv_pos.2 hq0) h2; rwa [inv_inv] at this
      have hρn : 0 < ρ ^ n w := pow_pos hρ0 _
      calc (1 : ℝ) = M⁻¹ * M := by rw [inv_mul_cancel₀ hM0.ne']
        _ ≤ M⁻¹ * c₀ := mul_le_mul_of_nonneg_left hc₀M (inv_pos.2 hM0).le
        _ ≤ M⁻¹ * c₀ ^ n w := mul_le_mul_of_nonneg_left (le_self_pow₀ hc₀1 (Nat.one_le_iff_ne_zero.1 (hn1 w))) (inv_pos.2 hM0).le
        _ = M⁻¹ * ((ρ ^ n w)⁻¹ * (c₀ * ρ) ^ n w) := by
            rw [mul_pow, ← mul_assoc (ρ ^ n w)⁻¹, mul_comm (ρ ^ n w)⁻¹, mul_assoc, inv_mul_cancel₀ hρn.ne',
              mul_one]
        _ ≤ ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ * ((ρ ^ n w)⁻¹ * tr ^ n w) := by
            refine mul_le_mul hqM ?_ (by positivity) (norm_nonneg _)
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hc₀pos hρ0).le hoff _) (inv_pos.2 hρn).le
        _ = _ := by ring
    · rw [hT, norm_algebraNorm_eq_prod, ← prod_norm_pow_finrank_place K L v]
      exact Finset.prod_congr rfl fun w _ => by rw [← hT, hTn w]
  ·
    have hTle : ∀ w, ‖comp K L v w T‖ ≤ (c₀ * ρ) ^ n w + ‖(u : v.adicCompletion K) - 1‖ ^ n w * B := by
      intro w
      rw [hTdec w]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hRn w))
      rw [hT1n]
      exact pow_le_pow_left₀ (norm_nonneg _) hslab.le _
    have hyle : ∀ w, ‖comp K L v w ((q : L ⊗[K] v.adicCompletion K) * Ring.inverse e * T)‖ ≤ Y := by
      intro w
      rw [hyn]
      obtain ⟨h1, h2⟩ := hMq q hq w
      have hρn : 0 < ρ ^ n w := pow_pos hρ0 _
      have hcℓi : 1 ≤ cℓ⁻¹ := one_le_inv₀ hℓpos |>.2 hℓle
      calc ‖comp K L v w (q : L ⊗[K] v.adicCompletion K)‖ * (ρ ^ n w)⁻¹ * ‖comp K L v w T‖
          ≤ M * (ρ ^ n w)⁻¹ * ((c₀ * ρ) ^ n w + ‖(u : v.adicCompletion K) - 1‖ ^ n w * B) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h1 (inv_pos.2 hρn).le) (hTle w) (norm_nonneg _)
              (by positivity)
        _ = M * (c₀ ^ n w + (‖(u : v.adicCompletion K) - 1‖ / ρ) ^ n w * B) := by
            rw [mul_pow, div_pow]; field_simp
        _ = M * (c₀ ^ n w + cℓ⁻¹ ^ n w * B) := by rw [hρℓ]
        _ ≤ M * (c₀ ^ N + cℓ⁻¹ ^ N * B) := by
            gcongr
            · exact hnN w
            · exact hnN w
        _ = Y := by rw [hYdef]; ring
    have hW := (AutomorphicForm.semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow K L v).1 ((q : L ⊗[K] v.adicCompletion K) * Ring.inverse e * T)
    rw [hW, finsum_eq_sum_of_fintype]
    have hterm : ∀ w, 0 ≤ 2 * Real.log (max 1 ‖comp K L v w ((q : L ⊗[K] v.adicCompletion K) * Ring.inverse e * T)‖) ∧
        2 * Real.log (max 1 ‖comp K L v w ((q : L ⊗[K] v.adicCompletion K) * Ring.inverse e * T)‖) ≤ 2 * Real.log (max 1 Y) := by
      intro w
      refine ⟨mul_nonneg zero_le_two (Real.log_nonneg (le_max_left _ _)), mul_le_mul_of_nonneg_left ?_ zero_le_two⟩
      exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) (max_le_max le_rfl (hyle w))
    rw [abs_of_nonneg (Finset.sum_nonneg fun w _ => (hterm w).1)]
    refine le_trans (Finset.sum_le_sum fun w _ => (hterm w).2) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact le_max_left _ _

end TwWeightB

set_option maxHeartbeats 8000000 in
open TwWeightB in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (Z : Set (L ⊗[K] v.adicCompletion K)) (hZ : IsCompact Z)
    (Qc : Set (L ⊗[K] v.adicCompletion K)ˣ) (hQc : IsCompact Qc) :
    IntegrableOn (fun z : (L ⊗[K] v.adicCompletion K) => Real.log ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖) Z ν ∧
    ∃ C : ℝ, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ u : (v.adicCompletion K)ˣ, u ∈ U → u ^ Module.finrank K L ≠ 1 → ∀ q : (L ⊗[K] v.adicCompletion K)ˣ, q ∈ Qc →
      ∀ g : (L ⊗[K] v.adicCompletion K) → ℂ, Measurable g → (∀ z, ‖g z‖ ≤ 1) → (∀ z, z ∉ Z → g z = 0) →
        ‖(‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℂ) *
            ∫ η : (L ⊗[K] v.adicCompletion K), g (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η -
                (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : (v.adicCompletion K)) : (L ⊗[K] v.adicCompletion K)) * η) *
              ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 (((q : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * η)) +
                  2 * (Module.finrank K L : ℝ) * Real.log ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℝ) : ℂ) ∂ν -
          ∫ z : (L ⊗[K] v.adicCompletion K), g z *
              ((2 * Real.log ‖Algebra.norm (v.adicCompletion K) (((q : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)))‖ +
                  2 * (Module.finrank K L : ℝ) * Real.log ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ : ℝ) : ℂ) ∂ν‖ ≤
          C * ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖|) ∧
        (‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℂ) * ∫ η : (L ⊗[K] v.adicCompletion K), g (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η -
                (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : (v.adicCompletion K)) : (L ⊗[K] v.adicCompletion K)) * η) ∂ν = ∫ z : (L ⊗[K] v.adicCompletion K), g z ∂ν := by
  classical
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  set Tr := Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) with hTr
  have hTrs : Function.Surjective Tr := trace_surjective K L v
  have hTrc : Continuous Tr := continuous_trace K L v
  obtain ⟨C_T, hCT0, hTS⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_forall_integrableOn_and_setIntegral_one_add_abs_log_norm_le_of_surjective K v (L ⊗[K] v.adicCompletion K) ν Tr hTrs Z hZ

  have hlogm : Measurable fun z : L ⊗[K] v.adicCompletion K => Real.log ‖Tr z‖ :=
    Real.measurable_log.comp (continuous_norm.comp hTrc).measurable
  have hInt : IntegrableOn (fun z : L ⊗[K] v.adicCompletion K => Real.log ‖Tr z‖) Z ν := by
    have h1 := (hTS 1 one_pos le_rfl).1

    have hA : IntegrableOn (fun z : L ⊗[K] v.adicCompletion K => Real.log ‖Tr z‖) (Z ∩ {z | ‖Tr z‖ ≤ 1}) ν := by
      refine Integrable.mono' h1 hlogm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs]
      linarith [abs_nonneg (Real.log ‖Tr z‖)]

    have hBc : IsCompact (Z ∩ {z | 1 ≤ ‖Tr z‖}) :=
      hZ.inter_right (isClosed_le continuous_const (continuous_norm.comp hTrc))
    have hB : IntegrableOn (fun z : L ⊗[K] v.adicCompletion K => Real.log ‖Tr z‖) (Z ∩ {z | 1 ≤ ‖Tr z‖}) ν := by
      refine ContinuousOn.integrableOn_compact hBc ?_
      refine (continuousOn_of_forall_continuousAt fun z hz => ?_)
      exact ((continuous_norm.comp hTrc).continuousAt).log (by
        have : (1 : ℝ) ≤ ‖Tr z‖ := hz.2; exact (lt_of_lt_of_le one_pos this).ne')
    have hcover : Z ⊆ (Z ∩ {z | ‖Tr z‖ ≤ 1}) ∪ (Z ∩ {z | 1 ≤ ‖Tr z‖}) := by
      intro z hz
      rcases le_total ‖Tr z‖ 1 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    exact (hA.union hB).mono_set hcover
  refine ⟨hInt, ?_⟩

  obtain ⟨c₀, C_D, hc₀, hCD, U, hU, hdom⟩ := dominance K L σ v hgen Z hZ Qc hQc
  obtain ⟨C_M, hCM0, hMS⟩ := IsDedekindDomain.HeightOneSpectrum.exists_forall_measureReal_inter_norm_le_le_of_surjective K v (L ⊗[K] v.adicCompletion K) ν Tr hTrs Z hZ
  set ℓ : ℕ := Module.finrank K L with hℓ
  refine ⟨(3 * C_D + 2 * ℓ) * C_M * c₀ + 2 * ℓ * C_T * c₀ * (1 + |Real.log c₀|), U, hU, ?_⟩
  intro u hu hul q hq g hgm hg1 hgZ
  obtain ⟨hρ1, hdomq⟩ := hdom u hu hul
  obtain ⟨hNq, hdz⟩ := hdomq q hq
  set ρ : ℝ := ‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ with hρ
  have hρ0 : 0 < ρ := by
    rw [hρ, norm_pos_iff, sub_ne_zero]; exact fun h => hul (Units.val_eq_one.1 h.symm)

  have hmass := integral_comp_Mop K L σ v hgen ν u hul g hgm
  refine ⟨?_, hmass⟩

  have hc₀ρ : 0 < c₀ * ρ := mul_pos hc₀ hρ0
  set e : L ⊗[K] v.adicCompletion K := ι K L v ((1 : v.adicCompletion K) - (u : v.adicCompletion K) ^ Module.finrank K L) with he
  have hune : (1 : v.adicCompletion K) - (u : v.adicCompletion K) ^ Module.finrank K L ≠ 0 := by
    rw [sub_ne_zero, ← Units.val_pow_eq_pow_val]; exact fun h => hul (Units.val_eq_one.1 h.symm)
  have heu : IsUnit e := (isUnit_iff_ne_zero.2 hune).map _
  set y : L ⊗[K] v.adicCompletion K → L ⊗[K] v.adicCompletion K := fun z => (q : L ⊗[K] v.adicCompletion K) * Ring.inverse e * Top K L σ v (u : v.adicCompletion K) z with hy
  have hyc : Continuous y := (continuous_const.mul (continuous_Top K L σ v (u : v.adicCompletion K)))
  set W : L ⊗[K] v.adicCompletion K → ℝ := fun z => AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 (y z)) with hW
  have hWc : Continuous W := (continuous_W K L v).comp hyc
  set Kq : L ⊗[K] v.adicCompletion K → ℝ := fun z => 2 * Real.log ‖Algebra.norm (v.adicCompletion K) (q : L ⊗[K] v.adicCompletion K)‖ +
      2 * (Module.finrank K L : ℝ) * Real.log ‖Tr z‖ with hKq
  set D : L ⊗[K] v.adicCompletion K → ℝ := fun z => W z + 2 * (Module.finrank K L : ℝ) * Real.log ρ - Kq z with hD

  have hA : ∀ η : L ⊗[K] v.adicCompletion K, (q : L ⊗[K] v.adicCompletion K) * η = y (Mop K L σ v (u : v.adicCompletion K) η) := by
    intro η
    simp only [hy]
    rw [Top_Mop, ← he, mul_assoc, ← mul_assoc (Ring.inverse e), Ring.inverse_mul_cancel _ heu, one_mul]

  set Ψ : L ⊗[K] v.adicCompletion K → ℂ := fun z => g z * ((W z + 2 * (Module.finrank K L : ℝ) * Real.log ρ : ℝ) : ℂ) with hΨ
  have hΨm : Measurable Ψ :=
    hgm.mul (Complex.measurable_ofReal.comp (hWc.add continuous_const).measurable)
  have hB : (fun η : L ⊗[K] v.adicCompletion K => g (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η -
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : v.adicCompletion K) : L ⊗[K] v.adicCompletion K) * η) *
        ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 (((q : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) * η)) +
          2 * (Module.finrank K L : ℝ) * Real.log ‖(1 : v.adicCompletion K) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : v.adicCompletion K)‖ : ℝ) : ℂ)) =
      fun η => Ψ (Mop K L σ v (u : v.adicCompletion K) η) := by
    funext η
    simp only [hΨ, hW, hA η]
    rfl
  have hC := integral_comp_Mop K L σ v hgen ν u hul Ψ hΨm
  rw [hB, hC]

  set S : Set (L ⊗[K] v.adicCompletion K) := Z ∩ {z | ‖Tr z‖ ≤ c₀ * ρ} with hS
  have hSm : MeasurableSet S := hZ.isClosed.measurableSet.inter
    (isClosed_le (continuous_norm.comp hTrc) continuous_const).measurableSet
  have hSZ : S ⊆ Z := Set.inter_subset_left
  have hνS : ν S < ⊤ := (measure_mono hSZ).trans_lt hZ.measure_lt_top
  obtain ⟨hTSi, hTSb⟩ := hTS (c₀ * ρ) hc₀ρ hρ1
  have hMSb := hMS (c₀ * ρ) hc₀ρ hρ1
  set A : ℝ := 3 * C_D + 2 * (Module.finrank K L : ℝ) * |Real.log ρ| with hAdef
  have hA0 : 0 ≤ A := by positivity
  set bnd : L ⊗[K] v.adicCompletion K → ℝ := S.indicator (fun z => A + 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖|) with hbnd

  have hDoff : ∀ z ∈ Z, c₀ * ρ ≤ ‖Tr z‖ → D z = 0 := by
    intro z hz hoff
    obtain ⟨hcomp, hNT⟩ := (hdz z hz).1 hoff
    have hWz : W z = 2 * Real.log ‖Algebra.norm (v.adicCompletion K) (y z)‖ :=
      (AutomorphicForm.semiLocalWeight_unipotentGL2_eq_finsum_log_max_and_eq_log_norm_norm_of_one_le_and_norm_baseChangeAlgEquiv_algebraMap_eq_pow K L v).2.1 (y z) hcomp
    have hTz : 0 < ‖Tr z‖ := lt_of_lt_of_le hc₀ρ hoff
    have hNe : ‖Algebra.norm (v.adicCompletion K) e‖ = ρ ^ Module.finrank K L := by
      rw [he, norm_iota, norm_pow, hρ, Units.val_pow_eq_pow_val]
    have hNinv : ‖Algebra.norm (v.adicCompletion K) (Ring.inverse e)‖ = (ρ ^ Module.finrank K L)⁻¹ := by
      have h1 : Algebra.norm (v.adicCompletion K) (Ring.inverse e) * Algebra.norm (v.adicCompletion K) e = 1 := by
        rw [← map_mul, Ring.inverse_mul_cancel _ heu, map_one]
      have h2 := congrArg (fun x : v.adicCompletion K => ‖x‖) h1
      simp only [norm_mul, norm_one, hNe] at h2
      exact eq_inv_of_mul_eq_one_left h2
    have hNq0 : 0 < ‖Algebra.norm (v.adicCompletion K) (q : L ⊗[K] v.adicCompletion K)‖ :=
      norm_pos_iff.2 (((q.isUnit).map (Algebra.norm (v.adicCompletion K))).ne_zero)
    have hNy : ‖Algebra.norm (v.adicCompletion K) (y z)‖ =
        ‖Algebra.norm (v.adicCompletion K) (q : L ⊗[K] v.adicCompletion K)‖ * (ρ ^ Module.finrank K L)⁻¹ * ‖Tr z‖ ^ Module.finrank K L := by
      simp only [hy]
      rw [map_mul, map_mul, norm_mul, norm_mul, hNinv, hNT]
    simp only [hD, hKq, hWz, hNy]
    rw [Real.log_mul (mul_pos hNq0 (inv_pos.2 (pow_pos hρ0 _))).ne' (pow_pos hTz _).ne',
      Real.log_mul hNq0.ne' (inv_pos.2 (pow_pos hρ0 _)).ne', Real.log_inv, Real.log_pow, Real.log_pow]
    ring
  have hDslab : ∀ z ∈ Z, ‖Tr z‖ < c₀ * ρ → |D z| ≤ A + 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖| := by
    intro z hz hsl
    have hWb : |W z| ≤ C_D := (hdz z hz).2 hsl
    have h2ℓ : 0 ≤ 2 * (Module.finrank K L : ℝ) := by positivity
    have h2 : |2 * (Module.finrank K L : ℝ) * Real.log ρ| ≤ 2 * (Module.finrank K L : ℝ) * |Real.log ρ| := by
      rw [abs_mul, abs_of_nonneg h2ℓ]
    have h3 : |2 * Real.log ‖Algebra.norm (v.adicCompletion K) (q : L ⊗[K] v.adicCompletion K)‖| ≤ 2 * C_D := by
      rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left hNq (by norm_num)
    have h4 : |2 * (Module.finrank K L : ℝ) * Real.log ‖Tr z‖| ≤ 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖| := by
      rw [abs_mul, abs_of_nonneg h2ℓ]
    simp only [hD, hKq, hAdef]
    calc |W z + 2 * (Module.finrank K L : ℝ) * Real.log ρ -
          (2 * Real.log ‖Algebra.norm (v.adicCompletion K) (q : L ⊗[K] v.adicCompletion K)‖ + 2 * (Module.finrank K L : ℝ) * Real.log ‖Tr z‖)|
        ≤ |W z| + |2 * (Module.finrank K L : ℝ) * Real.log ρ| +
          (|2 * Real.log ‖Algebra.norm (v.adicCompletion K) (q : L ⊗[K] v.adicCompletion K)‖| + |2 * (Module.finrank K L : ℝ) * Real.log ‖Tr z‖|) :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
      _ ≤ C_D + 2 * (Module.finrank K L : ℝ) * |Real.log ρ| +
          (2 * C_D + 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖|) := by linarith
      _ = _ := by ring
  have hpt : ∀ z : L ⊗[K] v.adicCompletion K, ‖g z * ((D z : ℝ) : ℂ)‖ ≤ bnd z := by
    intro z
    by_cases hz : z ∈ Z
    · by_cases hsl : ‖Tr z‖ < c₀ * ρ
      · have hzS : z ∈ S := ⟨hz, hsl.le⟩
        simp only [hbnd, Set.indicator_of_mem hzS]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖g z‖ * |D z| ≤ 1 * |D z| := mul_le_mul_of_nonneg_right (hg1 z) (abs_nonneg _)
          _ = |D z| := one_mul _
          _ ≤ _ := hDslab z hz hsl
      · rw [hDoff z hz (not_lt.1 hsl)]
        simp only [Complex.ofReal_zero, mul_zero, norm_zero, hbnd]
        exact Set.indicator_nonneg (fun w _ => by positivity) z
    · rw [hgZ z hz, zero_mul, norm_zero]
      simp only [hbnd]
      exact Set.indicator_nonneg (fun w _ => by positivity) z

  have hlogS : IntegrableOn (fun z : L ⊗[K] v.adicCompletion K => |Real.log ‖Tr z‖|) S ν := by
    refine Integrable.mono' hTSi (hlogm.norm.aestronglyMeasurable) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    linarith [abs_nonneg (Real.log ‖Tr z‖)]
  have hbndS : IntegrableOn (fun z : L ⊗[K] v.adicCompletion K => A + 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖|) S ν :=
    (integrableOn_const (hs := hνS.ne)).add (hlogS.const_mul _)
  have hbndi : Integrable bnd ν := by
    rw [hbnd, integrable_indicator_iff hSm]; exact hbndS
  have hgDi : Integrable (fun z : L ⊗[K] v.adicCompletion K => g z * ((D z : ℝ) : ℂ)) ν := by
    refine Integrable.mono' hbndi ?_ (Filter.Eventually.of_forall hpt)
    have hDm : Measurable D := by
      simp only [hD, hKq]
      exact ((hWc.measurable.add measurable_const).sub (measurable_const.add (measurable_const.mul hlogm)))
    exact (hgm.mul (Complex.measurable_ofReal.comp hDm)).aestronglyMeasurable

  have hZm : MeasurableSet Z := hZ.isClosed.measurableSet
  have hKm : Measurable Kq := by
    simp only [hKq]; exact measurable_const.add (measurable_const.mul hlogm)
  have hgKi : Integrable (fun z : L ⊗[K] v.adicCompletion K => g z * ((Kq z : ℝ) : ℂ)) ν := by
    have hbK : IntegrableOn (fun z : L ⊗[K] v.adicCompletion K => 2 * C_D + 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖|) Z ν :=
      (integrableOn_const (hs := hZ.measure_lt_top.ne)).add ((hInt.norm).const_mul _)
    have hbKi : Integrable (Z.indicator fun z : L ⊗[K] v.adicCompletion K => 2 * C_D + 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖|) ν := by
      rw [integrable_indicator_iff hZm]
      simpa only [Real.norm_eq_abs] using hbK
    refine Integrable.mono' hbKi ((hgm.mul (Complex.measurable_ofReal.comp hKm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ Z
    · rw [Set.indicator_of_mem hz, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h2ℓ : 0 ≤ 2 * (Module.finrank K L : ℝ) := by positivity
      have hK : |Kq z| ≤ 2 * C_D + 2 * (Module.finrank K L : ℝ) * |Real.log ‖Tr z‖| := by
        simp only [hKq]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_two, abs_mul, abs_of_nonneg h2ℓ]
        linarith [mul_le_mul_of_nonneg_left hNq (show (0:ℝ) ≤ 2 by norm_num)]
      calc ‖g z‖ * |Kq z| ≤ 1 * |Kq z| := mul_le_mul_of_nonneg_right (hg1 z) (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hK
    · rw [hgZ z hz, zero_mul, norm_zero, Set.indicator_of_notMem hz]
  have hΨeq : Ψ = fun z => g z * ((D z : ℝ) : ℂ) + g z * ((Kq z : ℝ) : ℂ) := by
    funext z; simp only [hΨ, hD]; push_cast; ring
  have hΨi : Integrable Ψ ν := by rw [hΨeq]; exact hgDi.add hgKi
  have hsub : (fun z : L ⊗[K] v.adicCompletion K => Ψ z - g z * ((Kq z : ℝ) : ℂ)) = fun z => g z * ((D z : ℝ) : ℂ) := by
    funext z; simp only [hΨeq]; ring
  have hKq' : (fun z : L ⊗[K] v.adicCompletion K => g z * ((2 * Real.log ‖Algebra.norm (v.adicCompletion K) ((q : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)‖ +
      2 * (Module.finrank K L : ℝ) * Real.log ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ : ℝ) : ℂ)) =
      fun z => g z * ((Kq z : ℝ) : ℂ) := rfl
  rw [hKq', ← integral_sub hΨi hgKi, hsub]

  have hlog_le : ∫ z in S, |Real.log ‖Tr z‖| ∂ν ≤ C_T * (c₀ * ρ) * (1 + |Real.log (c₀ * ρ)|) := by
    refine le_trans (setIntegral_mono hlogS hTSi fun z => ?_) hTSb
    linarith [abs_nonneg (Real.log ‖Tr z‖)]
  have hint_bnd : ∫ z, bnd z ∂ν = A * (ν S).toReal +
      2 * (Module.finrank K L : ℝ) * ∫ z in S, |Real.log ‖Tr z‖| ∂ν := by
    simp only [hbnd]
    rw [integral_indicator hSm, integral_add (integrableOn_const (C := A) (hs := hνS.ne)) (hlogS.const_mul (2 * (Module.finrank K L : ℝ))),
      setIntegral_const, integral_const_mul, smul_eq_mul, mul_comm]
    first | rfl | simp [Measure.real]
  have hX1 : 1 ≤ 1 + |Real.log ρ| := by linarith [abs_nonneg (Real.log ρ)]
  have hlogc : |Real.log (c₀ * ρ)| ≤ |Real.log c₀| + |Real.log ρ| := by
    rw [Real.log_mul hc₀.ne' hρ0.ne']; exact abs_add_le _ _
  have hℓ0 : 0 ≤ (Module.finrank K L : ℝ) := Nat.cast_nonneg _
  calc ‖∫ z, g z * ((D z : ℝ) : ℂ) ∂ν‖ ≤ ∫ z, ‖g z * ((D z : ℝ) : ℂ)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ z, bnd z ∂ν := integral_mono hgDi.norm hbndi hpt
    _ = A * (ν S).toReal + 2 * (Module.finrank K L : ℝ) * ∫ z in S, |Real.log ‖Tr z‖| ∂ν := hint_bnd
    _ ≤ A * (C_M * (c₀ * ρ)) + 2 * (Module.finrank K L : ℝ) * (C_T * (c₀ * ρ) * (1 + |Real.log (c₀ * ρ)|)) := by
        gcongr
    _ ≤ (3 * C_D + 2 * (Module.finrank K L : ℝ)) * (1 + |Real.log ρ|) * (C_M * (c₀ * ρ)) +
          2 * (Module.finrank K L : ℝ) * (C_T * (c₀ * ρ) * ((1 + |Real.log c₀|) * (1 + |Real.log ρ|))) := by
        have i1 : A ≤ (3 * C_D + 2 * (Module.finrank K L : ℝ)) * (1 + |Real.log ρ|) := by
          simp only [hAdef]; nlinarith [hCD, hℓ0, abs_nonneg (Real.log ρ)]
        have i2 : 1 + |Real.log (c₀ * ρ)| ≤ (1 + |Real.log c₀|) * (1 + |Real.log ρ|) := by
          nlinarith [hlogc, abs_nonneg (Real.log c₀), abs_nonneg (Real.log ρ)]
        gcongr
    _ = ((3 * C_D + 2 * ↑ℓ) * C_M * c₀ + 2 * ↑ℓ * C_T * c₀ * (1 + |Real.log c₀|)) * ρ * (1 + |Real.log ρ|) := by
        simp only [hℓ]; ring

end S_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le (solution)
