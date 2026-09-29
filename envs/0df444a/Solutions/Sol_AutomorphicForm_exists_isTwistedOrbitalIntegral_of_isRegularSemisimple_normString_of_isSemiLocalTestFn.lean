-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b52cf25a-06ed-52a7-befc-4d3d81f70593

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
import Theorems.Thm_MeasureTheory_exists_isLocallyConstant_integral_subgroup_mul_eq_one
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn

set_option autoImplicit false

section

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace TwistedNormDescent

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
private theorem twist_smul_tmul (s : A) (l : L) (t : A) : s • (l ⊗ₜ[K] t) = l ⊗ₜ[K] (s * t) := by
  rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, TensorProduct.comm_symm_tmul]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
private theorem twist_sigmaTensor_tmul (l : L) (t : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] t) = σ l ⊗ₜ[K] t := by
  show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (l ⊗ₜ[K] t) = σ l ⊗ₜ[K] t
  rw [Algebra.TensorProduct.map_tmul]
  rfl

private def twist_sigmaLinear : (L ⊗[K] A) →ₗ[A] (L ⊗[K] A) where
  toFun := AutomorphicForm.sigmaTensor K L A σ
  map_add' x y := map_add _ x y
  map_smul' s x := by
    simp only [RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul l t => rw [twist_smul_tmul, twist_sigmaTensor_tmul, twist_sigmaTensor_tmul, twist_smul_tmul]
    | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
private theorem twist_sigmaLinear_apply (x : L ⊗[K] A) :
    twist_sigmaLinear K L A σ x = AutomorphicForm.sigmaTensor K L A σ x := rfl

private theorem twist_continuous_sigmaTensor : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI : ContinuousSMul A (L ⊗[K] A) := IsModuleTopology.toContinuousSMul A (L ⊗[K] A)
  exact (IsModuleTopology.continuous_of_linearMap (twist_sigmaLinear K L A σ)).congr fun _ => rfl

private theorem twist_continuous_sigmaGL : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h : Continuous ((AutomorphicForm.sigmaTensor K L A σ).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] A) → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    (continuous_id.matrix_map (twist_continuous_sigmaTensor K L A σ)).congr fun _ => rfl
  exact (Units.continuous_map h).congr fun _ => rfl

private theorem twist_continuous_sigmaGL_iterate (i : ℕ) :
    Continuous ((⇑(AutomorphicForm.sigmaGL K L A σ))^[i]) :=
  (twist_continuous_sigmaGL K L A σ).iterate i

private theorem twist_continuous_normString :
    Continuous (AutomorphicForm.normString K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  show Continuous fun δ : GL (Fin 2) (L ⊗[K] A) =>
    ((List.range (Module.finrank K L)).map fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ).prod
  refine continuous_list_prod _ fun i _ => ?_
  exact twist_continuous_sigmaGL_iterate K L A σ i

private theorem twist_continuous_twistedConj (δ : GL (Fin 2) (L ⊗[K] A)) :
    Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  exact (continuous_id.mul continuous_const).mul (twist_continuous_sigmaGL K L A σ).inv

variable [T2Space A]

private theorem twist_isClosed_twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  exact isClosed_singleton.preimage (twist_continuous_twistedConj K L A σ δ)

variable [LocallyCompactSpace A]

private theorem twist_locallyCompactSpace_twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    LocallyCompactSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := by
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L A
  exact (twist_isClosed_twistedCentralizer K L A σ δ).isClosedEmbedding_subtypeVal.locallyCompactSpace

omit [T2Space A] [LocallyCompactSpace A] in
private theorem twist_isTopologicalGroup_twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsTopologicalGroup (AutomorphicForm.twistedCentralizer K L A σ δ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  infer_instance

omit [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] in
private theorem twist_borelSpace_twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    @BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) _
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ) :=
  @BorelSpace.mk _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) rfl

private theorem twist_exists_isHaarMeasure_twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    ∃ τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L A σ δ),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ' := by
  letI := AutomorphicForm.twistedCentralizerBorel K L A σ δ
  haveI := twist_borelSpace_twistedCentralizer K L A σ δ
  haveI := twist_isTopologicalGroup_twistedCentralizer K L A σ δ
  haveI := twist_locallyCompactSpace_twistedCentralizer K L A σ δ
  exact ⟨Measure.haar, inferInstance⟩

end Generic

section FinitePlace

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

example (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' :=
  twist_exists_isHaarMeasure_twistedCentralizer K L (v.adicCompletion K) σ δ

example (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsClosed (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :
      Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
  twist_isClosed_twistedCentralizer K L (v.adicCompletion K) σ δ

example (S : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hS : IsCompact S) :
    IsCompact (AutomorphicForm.normString K L (v.adicCompletion K) σ '' S) :=
  hS.image (twist_continuous_normString K L (v.adicCompletion K) σ)

end FinitePlace

end TwistedNormDescent

end

end

section

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace TwistedNormDescent

section Order

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

private theorem normStr_pow_finrank_eq_one (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  have h1 : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = orderOf σ := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  have h2 := Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L
  rw [h1] at h2
  exact Dvd.intro_left _ h2

end Order

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

private theorem normStr_sigmaTensor_tmul (l : L) (t : A) :
    AutomorphicForm.sigmaTensor K L A σ (l ⊗ₜ[K] t) = σ l ⊗ₜ[K] t := by
  show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (l ⊗ₜ[K] t) = σ l ⊗ₜ[K] t
  rw [Algebra.TensorProduct.map_tmul]
  rfl

private theorem normStr_iterate_sigmaTensor_tmul (i : ℕ) (l : L) (t : A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (l ⊗ₜ[K] t) = ((⇑σ)^[i] l) ⊗ₜ[K] t := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, normStr_sigmaTensor_tmul, Function.iterate_succ_apply']

variable [FiniteDimensional K L]

private theorem normStr_iterate_sigmaTensor_finrank (x : L ⊗[K] A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[Module.finrank K L] x = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact Function.iterate_fixed (map_zero _) _
  | tmul l t =>
      rw [normStr_iterate_sigmaTensor_tmul, ← AlgEquiv.coe_pow, normStr_pow_finrank_eq_one]
      rfl
  | add x y hx hy =>
      rw [← RingHom.coe_pow] at hx hy ⊢
      rw [map_add, hx, hy]

private theorem normStr_iterate_sigmaGL_finrank (x : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(AutomorphicForm.sigmaGL K L A σ))^[Module.finrank K L] x = x :=
  LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self (normStr_iterate_sigmaTensor_finrank K L A σ) x

omit [FiniteDimensional K L] in
private theorem normStr_normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ =
      LT.TwistedNorm.sigmaNormPow (AutomorphicForm.sigmaGL K L A σ) (Module.finrank K L) δ := by
  rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  rfl

private theorem normStr_normString_sigmaConj (x δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) =
      x⁻¹ * AutomorphicForm.normString K L A σ δ * x := by
  rw [normStr_normString_eq_sigmaNormPow, normStr_normString_eq_sigmaNormPow]
  exact LT.TwistedNorm.sigmaNormPow_sigmaConj_generalLinearGroup
    (normStr_iterate_sigmaTensor_finrank K L A σ) x δ

private theorem normStr_twistedCentralizer_le_centralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer {AutomorphicForm.normString K L A σ δ} := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hinv : t⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ t = δ :=
    AutomorphicForm.mem_sigmaCentralizer_iff_inv.1 ht
  have h := normStr_normString_sigmaConj K L A σ t δ
  rw [hinv] at h
  calc t * AutomorphicForm.normString K L A σ δ
      = t * (t⁻¹ * AutomorphicForm.normString K L A σ δ * t) := by rw [← h]
    _ = AutomorphicForm.normString K L A σ δ * t := by group

private theorem normStr_twistedCentralizer_comm (δ : GL (Fin 2) (L ⊗[K] A))
    (hZ : ∀ s ∈ Subgroup.centralizer {AutomorphicForm.normString K L A σ δ},
      ∀ t ∈ Subgroup.centralizer {AutomorphicForm.normString K L A σ δ}, s * t = t * s) :
    ∀ s ∈ AutomorphicForm.twistedCentralizer K L A σ δ,
      ∀ t ∈ AutomorphicForm.twistedCentralizer K L A σ δ, s * t = t * s :=
  fun s hs t ht => hZ s (normStr_twistedCentralizer_le_centralizer K L A σ δ hs) t
    (normStr_twistedCentralizer_le_centralizer K L A σ δ ht)

private theorem normStr_sigmaGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.normString K L A σ δ) =
      δ⁻¹ * AutomorphicForm.normString K L A σ δ * δ := by
  rw [normStr_normString_eq_sigmaNormPow]
  exact LT.TwistedNorm.map_sigmaNormPow_generalLinearGroup (normStr_iterate_sigmaTensor_finrank K L A σ) δ

private theorem normStr_conj_sigmaGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    δ * AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.normString K L A σ δ) * δ⁻¹ =
      AutomorphicForm.normString K L A σ δ := by
  rw [normStr_sigmaGL_normString]
  group

end Twist

section Alpha

variable {G : Type} [Group G] (σ : G →* G) (δ : G)

private theorem normStr_iterate_conj_comp (k : ℕ) (t : G) :
    (fun s => δ * σ s * δ⁻¹)^[k] t =
      LT.TwistedNorm.sigmaPartialNorm σ δ k * (⇑σ)^[k] t * (LT.TwistedNorm.sigmaPartialNorm σ δ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, LT.TwistedNorm.sigmaPartialNorm_succ',
        Function.iterate_succ_apply']
      simp only [map_mul, map_inv]
      group

private theorem normStr_iterate_conj_comp_of_period {ℓ : ℕ} {t : G} (ht : (⇑σ)^[ℓ] t = t) :
    (fun s => δ * σ s * δ⁻¹)^[ℓ] t =
      LT.TwistedNorm.sigmaNormPow σ ℓ δ * t * (LT.TwistedNorm.sigmaNormPow σ ℓ δ)⁻¹ := by
  rw [normStr_iterate_conj_comp, ht, LT.TwistedNorm.sigmaNormPow_def]

private theorem normStr_iterate_conj_comp_eq_self {ℓ : ℕ} {t : G} (ht : (⇑σ)^[ℓ] t = t)
    (hZ : t ∈ Subgroup.centralizer {LT.TwistedNorm.sigmaNormPow σ ℓ δ}) :
    (fun s => δ * σ s * δ⁻¹)^[ℓ] t = t := by
  rw [normStr_iterate_conj_comp_of_period σ δ ht]
  rw [Subgroup.mem_centralizer_singleton_iff] at hZ
  rw [← hZ]
  group

end Alpha

section TwistAlpha

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

private theorem normStr_iterate_alpha_eq_self (δ t : GL (Fin 2) (L ⊗[K] A))
    (hZ : t ∈ Subgroup.centralizer {AutomorphicForm.normString K L A σ δ}) :
    (fun s => δ * AutomorphicForm.sigmaGL K L A σ s * δ⁻¹)^[Module.finrank K L] t = t := by
  rw [normStr_normString_eq_sigmaNormPow] at hZ
  exact normStr_iterate_conj_comp_eq_self (AutomorphicForm.sigmaGL K L A σ) δ
    (normStr_iterate_sigmaGL_finrank K L A σ t) hZ

private theorem normStr_alpha_mem_centralizer (δ : GL (Fin 2) (L ⊗[K] A)) {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer {AutomorphicForm.normString K L A σ δ}) :
    δ * AutomorphicForm.sigmaGL K L A σ z * δ⁻¹ ∈
      Subgroup.centralizer {AutomorphicForm.normString K L A σ δ} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
  have hN := normStr_conj_sigmaGL_normString K L A σ δ
  have hzN : AutomorphicForm.sigmaGL K L A σ z * AutomorphicForm.sigmaGL K L A σ
      (AutomorphicForm.normString K L A σ δ) = AutomorphicForm.sigmaGL K L A σ
      (AutomorphicForm.normString K L A σ δ) * AutomorphicForm.sigmaGL K L A σ z := by
    rw [← map_mul, hz, map_mul]
  calc δ * AutomorphicForm.sigmaGL K L A σ z * δ⁻¹ * AutomorphicForm.normString K L A σ δ
      = δ * AutomorphicForm.sigmaGL K L A σ z * δ⁻¹ *
          (δ * AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.normString K L A σ δ) * δ⁻¹) := by
        rw [hN]
    _ = δ * (AutomorphicForm.sigmaGL K L A σ z *
          AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.normString K L A σ δ)) * δ⁻¹ := by group
    _ = δ * (AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.normString K L A σ δ) *
          AutomorphicForm.sigmaGL K L A σ z) * δ⁻¹ := by rw [hzN]
    _ = (δ * AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.normString K L A σ δ) * δ⁻¹) *
          (δ * AutomorphicForm.sigmaGL K L A σ z * δ⁻¹) := by group
    _ = AutomorphicForm.normString K L A σ δ * (δ * AutomorphicForm.sigmaGL K L A σ z * δ⁻¹) := by
        rw [hN]

end TwistAlpha

end TwistedNormDescent

end

end

section

namespace TwistedNormDescent

variable {A : Type*} [CommRing A]

private theorem commutant_exists_eq_smul_one_add_smul (g x : Matrix (Fin 2) (Fin 2) A)
    (hΔ : IsUnit (Matrix.trace g ^ 2 - 4 * Matrix.det g)) (hx : x * g = g * x) :
    ∃ a b : A, x = a • (1 : Matrix (Fin 2) (Fin 2) A) + b • g := by
  obtain ⟨υ, hυ⟩ := hΔ
  have hu : ((υ⁻¹ : Aˣ) : A) * (Matrix.trace g ^ 2 - 4 * Matrix.det g) = 1 := by
    rw [← hυ]; exact Units.inv_mul υ
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
  set u : A := ((υ⁻¹ : Aˣ) : A) with hu_def
  have e00 : (x * g) 0 0 = (g * x) 0 0 := by rw [hx]
  have e01 : (x * g) 0 1 = (g * x) 0 1 := by rw [hx]
  have e10 : (x * g) 1 0 = (g * x) 1 0 := by rw [hx]
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  have rel1 : x 0 1 * g 1 0 = g 0 1 * x 1 0 := by linear_combination e00
  have rel2 : g 0 1 * (x 0 0 - x 1 1) = x 0 1 * (g 0 0 - g 1 1) := by linear_combination e01
  have rel3 : x 1 0 * (g 0 0 - g 1 1) = g 1 0 * (x 0 0 - x 1 1) := by linear_combination e10
  set w : A := u * (4 * g 1 0 * x 0 1 + (g 0 0 - g 1 1) * (x 0 0 - x 1 1)) with hw_def
  have hw1 : w * (g 0 0 - g 1 1) = x 0 0 - x 1 1 := by
    linear_combination (g 0 0 - g 1 1) * hw_def + (x 0 0 - x 1 1) * hu - 4 * u * g 1 0 * rel2
  have hw2 : w * g 0 1 = x 0 1 := by
    linear_combination g 0 1 * hw_def + x 0 1 * hu + u * (g 0 0 - g 1 1) * rel2
  have hw3 : w * g 1 0 = x 1 0 := by
    linear_combination g 1 0 * hw_def + x 1 0 * hu + 4 * u * g 1 0 * rel1 - u * (g 0 0 - g 1 1) * rel3
  refine ⟨x 1 1 - w * g 1 1, w, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination -hw1
  · linear_combination -hw2
  · linear_combination -hw3

private theorem commutant_exists_eq_of_mem_centralizer (g : GL (Fin 2) A)
    (hΔ : IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 -
      4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)))
    {x : GL (Fin 2) A} (hx : x ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) :
    ∃ a b : A, (x : Matrix (Fin 2) (Fin 2) A) =
      a • (1 : Matrix (Fin 2) (Fin 2) A) + b • (g : Matrix (Fin 2) (Fin 2) A) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : (x : Matrix (Fin 2) (Fin 2) A) * g = g * x := by
    have := congrArg Units.val hx
    simpa only [Units.val_mul] using this
  exact commutant_exists_eq_smul_one_add_smul _ _ hΔ hx'

private theorem centralizer_comm_of_isUnit_disc (g : GL (Fin 2) A)
    (hΔ : IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 -
      4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A))) :
    ∀ s ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)),
      ∀ t ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)), s * t = t * s := by
  intro s hs t ht
  obtain ⟨a, b, hs'⟩ := commutant_exists_eq_of_mem_centralizer g hΔ hs
  obtain ⟨a', b', ht'⟩ := commutant_exists_eq_of_mem_centralizer g hΔ ht
  have hc : Commute (a • (1 : Matrix (Fin 2) (Fin 2) A) + b • (g : Matrix (Fin 2) (Fin 2) A))
      (a' • (1 : Matrix (Fin 2) (Fin 2) A) + b' • (g : Matrix (Fin 2) (Fin 2) A)) := by
    refine Commute.add_left ?_ ?_
    · exact (Commute.one_left _).smul_left a
    · refine Commute.smul_left ?_ b
      exact Commute.add_right ((Commute.one_right _).smul_right a') ((Commute.refl _).smul_right b')
  apply Units.ext
  simp only [Units.val_mul]
  rw [hs', ht']
  exact hc.eq

end TwistedNormDescent

end

section

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

namespace TwistedNormDescent

section Generic

variable {A : Type*} [CommRing A]

private theorem integralUnitsSet_mul_mem {U : Set A} (hadd : ∀ x ∈ U, ∀ y ∈ U, x + y ∈ U)
    (hmul : ∀ x ∈ U, ∀ y ∈ U, x * y ∈ U) {a b : GL (Fin 2) A}
    (ha : a ∈ AutomorphicForm.integralUnitsSet U) (hb : b ∈ AutomorphicForm.integralUnitsSet U) :
    a * b ∈ AutomorphicForm.integralUnitsSet U := by
  rw [AutomorphicForm.mem_integralUnitsSet] at ha hb ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact hadd _ (hmul _ (ha.1 i 0) _ (hb.1 0 j)) _ (hmul _ (ha.1 i 1) _ (hb.1 1 j))
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact hadd _ (hmul _ (hb.2 i 0) _ (ha.2 0 j)) _ (hmul _ (hb.2 i 1) _ (ha.2 1 j))

private theorem integralUnitsSet_inv_mem {U : Set A} {a : GL (Fin 2) A}
    (ha : a ∈ AutomorphicForm.integralUnitsSet U) : a⁻¹ ∈ AutomorphicForm.integralUnitsSet U := by
  rw [AutomorphicForm.mem_integralUnitsSet] at ha ⊢
  refine ⟨ha.2, fun i j => ?_⟩
  rw [inv_inv]
  exact ha.1 i j

end Generic

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

omit [NumberField L] in
private theorem semiLocalIntegers_add_mem :
    ∀ x ∈ AutomorphicForm.semiLocalIntegers K L v, ∀ y ∈ AutomorphicForm.semiLocalIntegers K L v,
      x + y ∈ AutomorphicForm.semiLocalIntegers K L v := by
  unfold AutomorphicForm.semiLocalIntegers
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ⟨a + b, map_add _ a b⟩

omit [NumberField L] in
private theorem semiLocalIntegers_mul_mem :
    ∀ x ∈ AutomorphicForm.semiLocalIntegers K L v, ∀ y ∈ AutomorphicForm.semiLocalIntegers K L v,
      x * y ∈ AutomorphicForm.semiLocalIntegers K L v := by
  unfold AutomorphicForm.semiLocalIntegers
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact ⟨a * b, map_mul _ a b⟩

private def semiLocalIntegralSubgroup : Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) where
  carrier := AutomorphicForm.semiLocalIntegralSet K L v
  one_mem' := AutomorphicForm.one_mem_semiLocalIntegralSet K L v
  mul_mem' ha hb :=
    integralUnitsSet_mul_mem (semiLocalIntegers_add_mem K L v) (semiLocalIntegers_mul_mem K L v) ha hb
  inv_mem' ha := integralUnitsSet_inv_mem ha

omit [NumberField L] in
private theorem coe_semiLocalIntegralSubgroup :
    (semiLocalIntegralSubgroup K L v : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      AutomorphicForm.semiLocalIntegralSet K L v :=
  rfl

private theorem isCompact_semiLocalIntegralSubgroup :
    IsCompact (semiLocalIntegralSubgroup K L v : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
  AutomorphicForm.isCompact_semiLocalIntegralSet K L v

private theorem isOpen_semiLocalIntegralSubgroup :
    IsOpen (semiLocalIntegralSubgroup K L v : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
  AutomorphicForm.isOpen_semiLocalIntegralSet K L v

end SemiLocal

end TwistedNormDescent

end

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ']
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv I' := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
  haveI := TwistedNormDescent.twist_borelSpace_twistedCentralizer K L (v.adicCompletion K) σ δ
  have hT : IsClosed (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :
      Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
    TwistedNormDescent.twist_isClosed_twistedCentralizer K L (v.adicCompletion K) σ δ
  have hcomm : ∀ s ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
      ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, s * t = t * s :=
    TwistedNormDescent.normStr_twistedCentralizer_comm K L (v.adicCompletion K) σ δ
      (TwistedNormDescent.centralizer_comm_of_isUnit_disc _ hδ)
  obtain ⟨Ω, hΩ, hTΩ⟩ :=
    AutomorphicForm.exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul K L v σ δ hδ
      (tsupport φv) hφv.2
  obtain ⟨w, hw0, hwlc, hwc, hw1⟩ :=
    MeasureTheory.exists_isLocallyConstant_integral_subgroup_mul_eq_one
      (TwistedNormDescent.semiLocalIntegralSubgroup K L v)
      (TwistedNormDescent.isCompact_semiLocalIntegralSubgroup K L v)
      (TwistedNormDescent.isOpen_semiLocalIntegralSubgroup K L v)
      (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) hT hcomm τ' Ω hΩ
  have hwm : Measurable w := hwlc.continuous.measurable
  unfold AutomorphicForm.IsTwistedOrbitalIntegral AutomorphicForm.IsTwistedOrbitalIntegralOn
    AutomorphicForm.IsTwistedSectionFnOn
  exact ⟨_, w, ⟨hw0, hwm, hwc, fun x hx => hw1 x (hTΩ x (subset_tsupport φv (Function.mem_support.2 hx)))⟩,
    rfl⟩

end S_AutomorphicForm_exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegral_of_isRegularSemisimple_normString_of_isSemiLocalTestFn (solution)
