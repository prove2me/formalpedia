-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e9f815cb-721d-57b7-8211-1f0d87bf7224

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Group.Pointwise
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul

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
open scoped Pointwise

namespace TwistedNormDescent

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

private noncomputable def bcRing :
    L ⊗[K] v.adicCompletion K ≃+* Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv

private theorem continuous_bcRing : Continuous (bcRing K L v) :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).continuous

private theorem continuous_bcRing_symm : Continuous (bcRing K L v).symm :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).symm.continuous

private noncomputable def glPi :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) ≃* Π w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L) :=
  (Units.mapEquiv ((bcRing K L v).mapMatrix (m := Fin 2)).toMulEquiv).trans
    ((Units.mapEquiv (Matrix.piRingEquiv (n := Fin 2)
      (β := fun w : v.Extension (𝓞 L) => w.1.adicCompletion L)).toMulEquiv).trans MulEquiv.piUnits)

private theorem coe_glPi_apply (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (w : v.Extension (𝓞 L)) :
    ((glPi K L v x w : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map (fun a => bcRing K L v a w) := by
  ext i j
  rfl

private theorem coe_inv_glPi_apply (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (w : v.Extension (𝓞 L)) :
    (((glPi K L v x w)⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      ((x⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map (fun a => bcRing K L v a w) := by
  rw [← coe_glPi_apply]
  congr 1

private theorem coe_glPi_symm_apply (u : Π w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L)) :
    (((glPi K L v).symm u : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      Matrix.of (fun i j => (bcRing K L v).symm (fun w => ((u w : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j)) := by
  ext i j
  rfl

private theorem coe_inv_glPi_symm_apply (u : Π w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L)) :
    ((((glPi K L v).symm u)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      Matrix.of (fun i j => (bcRing K L v).symm (fun w => (((u w)⁻¹ : GL (Fin 2) (w.1.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j)) := by
  rw [← map_inv (glPi K L v).symm u, coe_glPi_symm_apply]
  rfl

private theorem continuous_glPi : Continuous (glPi K L v) := by
  refine continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, coe_glPi_apply]
    exact Units.continuous_val.matrix_map ((continuous_apply w).comp (continuous_bcRing K L v))
  · simp only [coe_inv_glPi_apply]
    exact Units.continuous_coe_inv.matrix_map ((continuous_apply w).comp (continuous_bcRing K L v))

private theorem continuous_glPi_symm : Continuous (glPi K L v).symm := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, coe_glPi_symm_apply]
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    exact (continuous_bcRing_symm K L v).comp (continuous_pi fun w =>
      (Units.continuous_val.comp (continuous_apply w)).matrix_elem i j)
  · simp only [coe_inv_glPi_symm_apply]
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    exact (continuous_bcRing_symm K L v).comp (continuous_pi fun w =>
      (Units.continuous_coe_inv.comp (continuous_apply w)).matrix_elem i j)

private theorem mem_centralizer_iff_glPi (γ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    x ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ↔
      ∀ w, glPi K L v x w ∈ Subgroup.centralizer ({glPi K L v γ w} : Set (GL (Fin 2) (w.1.adicCompletion L))) := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h w
    have h' := congrArg (fun y => glPi K L v y w) h
    simpa only [map_mul, Pi.mul_apply] using h'
  · intro h
    apply (glPi K L v).injective
    funext w
    simpa only [map_mul, Pi.mul_apply] using h w

private theorem isRegularSemisimple_glPi {γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) (w : v.Extension (𝓞 L)) :
    AutomorphicForm.IsRegularSemisimple (glPi K L v γ w) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  rw [coe_glPi_apply]
  let φw : L ⊗[K] v.adicCompletion K →+* w.1.adicCompletion L :=
    (Pi.evalRingHom (fun w : v.Extension (𝓞 L) => w.1.adicCompletion L) w).comp (bcRing K L v).toRingHom
  have hφ : ∀ a, φw a = bcRing K L v a w := fun _ => rfl
  have hf := hγ.map φw
  have key : φw (Matrix.trace (γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      Matrix.trace ((γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map
          (fun a => bcRing K L v a w)) ^ 2 -
        4 * Matrix.det ((γ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map
          (fun a => bcRing K L v a w)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.map_apply,
      map_sub, map_mul, map_pow, map_add, map_ofNat]
    simp only [hφ]
  rw [key] at hf
  exact hf

section PerPlace

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

private theorem isClosed_localCentralizer (γ : GL (Fin 2) (u.adicCompletion F)) :
    IsClosed ((AutomorphicForm.localCentralizer F u γ : Subgroup (GL (Fin 2) (u.adicCompletion F))) :
      Set (GL (Fin 2) (u.adicCompletion F))) := by
  haveI : T2Space (GL (Fin 2) (u.adicCompletion F)) := Units.isEmbedding_embedProduct.t2Space
  exact Set.isClosed_centralizer _

private noncomputable def localCentralizerCompacts (γ : GL (Fin 2) (u.adicCompletion F)) :
    PositiveCompacts (AutomorphicForm.localCentralizer F u γ) where
  carrier := Subtype.val ⁻¹' AutomorphicForm.localIntegralSet F u
  isCompact' :=
    (isClosed_localCentralizer F u γ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (AutomorphicForm.isCompact_localIntegralSet F u)
  interior_nonempty' := by
    rw [(continuous_subtype_val.isOpen_preimage _ (AutomorphicForm.isOpen_localIntegralSet F u)).interior_eq]
    exact ⟨1, AutomorphicForm.one_mem_localIntegralSet F u⟩

private theorem exists_isCompact_forall_conj_mem_local (γ : GL (Fin 2) (u.adicCompletion F))
    (hγ : AutomorphicForm.IsRegularSemisimple γ) (S : Set (GL (Fin 2) (u.adicCompletion F)))
    (hS : IsCompact S) :
    ∃ Ω : Set (GL (Fin 2) (u.adicCompletion F)), IsCompact Ω ∧
      ∀ y : GL (Fin 2) (u.adicCompletion F), y⁻¹ * γ * y ∈ S →
        ∃ t ∈ AutomorphicForm.localCentralizer F u γ, ∃ d ∈ Ω, y = t * d := by
  haveI : T2Space (GL (Fin 2) (u.adicCompletion F)) := Units.isEmbedding_embedProduct.t2Space
  haveI : R1Space (GL (Fin 2) (u.adicCompletion F)) := T2Space.r1Space
  haveI := AutomorphicForm.locallyCompactSpace_localGL F u
  have hVc : IsCompact (S * AutomorphicForm.localIntegralSet F u) :=
    hS.mul (AutomorphicForm.isCompact_localIntegralSet F u)
  have hVo : IsOpen (S * AutomorphicForm.localIntegralSet F u) :=
    (AutomorphicForm.isOpen_localIntegralSet F u).mul_left
  have hfv : AutomorphicForm.IsLocalTestFn F u
      ((S * AutomorphicForm.localIntegralSet F u).indicator fun _ => (1 : ℂ)) :=
    ⟨AutomorphicForm.isLocallyConstant_indicator_one hVo hVc.isClosed,
      HasCompactSupport.intro hVc fun _ hg => by simp [hg]⟩
  letI : MeasurableSpace (AutomorphicForm.localCentralizer F u γ) := AutomorphicForm.localCentralizerBorel F u γ
  haveI : BorelSpace (AutomorphicForm.localCentralizer F u γ) := ⟨rfl⟩
  haveI : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel F u γ)
      (Measure.haarMeasure (localCentralizerCompacts F u γ)) :=
    Measure.isHaarMeasure_haarMeasure _
  obtain ⟨I, hI⟩ := AutomorphicForm.exists_isOrbitalIntegral_of_isRegularSemisimple_of_isLocalTestFn F u γ hγ
    (Measure.haarMeasure (localCentralizerCompacts F u γ)) _ hfv
  obtain ⟨w, hw, -⟩ := hI
  obtain ⟨-, -, hcs, hfib⟩ := hw
  refine ⟨tsupport w, hcs, fun y hy => ?_⟩
  have hyV : y⁻¹ * γ * y ∈ S * AutomorphicForm.localIntegralSet F u := by
    simpa using Set.mul_mem_mul hy (AutomorphicForm.one_mem_localIntegralSet F u)
  have hfy := hfib y (by rw [Set.indicator_of_mem hyV]; exact one_ne_zero)
  have hex : ∃ t : AutomorphicForm.localCentralizer F u γ, w (t * y) ≠ 0 := by
    by_contra hcon
    have hz : ∀ t : AutomorphicForm.localCentralizer F u γ, w (t * y) = 0 :=
      fun t => not_not.mp (not_exists.mp hcon t)
    simp [hz] at hfy
  obtain ⟨t, ht⟩ := hex
  refine ⟨(t⁻¹ : AutomorphicForm.localCentralizer F u γ), (t⁻¹).2, t * y,
    subset_tsupport w (Function.mem_support.2 ht), ?_⟩
  rw [Subgroup.coe_inv, inv_mul_cancel_left]

end PerPlace

private theorem exists_isCompact_forall_conj_mem {γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) (C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hC : IsCompact C) :
    ∃ Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact Ω ∧
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K), x⁻¹ * γ * x ∈ C →
        ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
          ∃ d ∈ Ω, x = t * d := by
  have hplace : ∀ w : v.Extension (𝓞 L), ∃ Ωw : Set (GL (Fin 2) (w.1.adicCompletion L)), IsCompact Ωw ∧
      ∀ y : GL (Fin 2) (w.1.adicCompletion L),
        y⁻¹ * glPi K L v γ w * y ∈ (fun g => glPi K L v g w) '' C →
          ∃ t ∈ AutomorphicForm.localCentralizer L w.1 (glPi K L v γ w), ∃ d ∈ Ωw, y = t * d :=
    fun w => exists_isCompact_forall_conj_mem_local L w.1 (glPi K L v γ w)
      (isRegularSemisimple_glPi K L v hγ w) _
      (hC.image ((continuous_apply w).comp (continuous_glPi K L v)))
  choose Ωw hΩw using hplace
  refine ⟨(glPi K L v).symm '' Set.pi Set.univ Ωw, ?_, fun x hx => ?_⟩
  · exact (isCompact_univ_pi fun w => (hΩw w).1).image (continuous_glPi_symm K L v)
  ·
    have hxw : ∀ w : v.Extension (𝓞 L),
        ∃ t ∈ AutomorphicForm.localCentralizer L w.1 (glPi K L v γ w), ∃ d ∈ Ωw w,
          glPi K L v x w = t * d := by
      intro w
      refine (hΩw w).2 (glPi K L v x w) ⟨x⁻¹ * γ * x, hx, ?_⟩
      simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
    choose tw htw dw hdw hxeq using hxw
    refine ⟨(glPi K L v).symm tw, ?_, (glPi K L v).symm dw, ⟨dw, fun w _ => hdw w, rfl⟩, ?_⟩
    · rw [mem_centralizer_iff_glPi K L v γ]
      intro w
      simpa only [MulEquiv.apply_symm_apply] using htw w
    · apply (glPi K L v).injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      funext w
      exact hxeq w

end TwistedNormDescent

end

section

namespace TwistedNormDescent

section NormRemainder

variable {G : Type*} [Group G]

private def normRemainder (α : G →* G) : ℕ → G → G
  | 0, _ => 1
  | r + 1, q => q ^ r * α (normRemainder α r q)

private theorem normRemainder_zero (α : G →* G) (q : G) : normRemainder α 0 q = 1 := rfl

private theorem normRemainder_succ (α : G →* G) (r : ℕ) (q : G) :
    normRemainder α (r + 1) q = q ^ r * α (normRemainder α r q) := rfl

private theorem sigmaPartialNorm_eq_pow_mul_normRemainder (α : G →* G) {z q : G} (hq : α z = z * q)
    (hzq : Commute z q) :
    ∀ r : ℕ, LT.TwistedNorm.sigmaPartialNorm α z r = z ^ r * normRemainder α r q
  | 0 => by rw [LT.TwistedNorm.sigmaPartialNorm_zero, normRemainder_zero, pow_zero, one_mul]
  | r + 1 => by
    rw [LT.TwistedNorm.sigmaPartialNorm_succ', sigmaPartialNorm_eq_pow_mul_normRemainder α hq hzq r, map_mul,
      map_pow, hq, hzq.mul_pow, normRemainder_succ, pow_succ']
    simp only [mul_assoc]

private theorem sigmaPartialNorm_mem (α : G →* G) (Z : Subgroup G) (hαZ : ∀ z ∈ Z, α z ∈ Z) {z : G}
    (hz : z ∈ Z) : ∀ r : ℕ, LT.TwistedNorm.sigmaPartialNorm α z r ∈ Z
  | 0 => by rw [LT.TwistedNorm.sigmaPartialNorm_zero]; exact Z.one_mem
  | r + 1 => by
    rw [LT.TwistedNorm.sigmaPartialNorm_succ']
    exact Z.mul_mem hz (hαZ _ (sigmaPartialNorm_mem α Z hαZ hz r))

variable [TopologicalSpace G] [IsTopologicalGroup G]

private theorem continuous_normRemainder (α : G →* G) (hα : Continuous α) : ∀ r : ℕ, Continuous (normRemainder α r)
  | 0 => by
    have h : normRemainder α 0 = fun _ : G => (1 : G) := funext fun q => normRemainder_zero α q
    rw [h]
    exact continuous_const
  | r + 1 => by
    have h : normRemainder α (r + 1) = fun q : G => q ^ r * α (normRemainder α r q) :=
      funext fun q => normRemainder_succ α r q
    rw [h]
    exact (continuous_id.pow r).mul (hα.comp (continuous_normRemainder α hα r))

private theorem exists_isCompact_forall_pow_eq_mul (α : G →* G) (hα : Continuous α) (Z : Subgroup G)
    (hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hαZ : ∀ z ∈ Z, α z ∈ Z) (n : ℕ)
    (hn : ∀ z ∈ Z, (⇑α)^[n] z = z) (T : Subgroup G) (hT : ∀ t ∈ Z, α t = t → t ∈ T)
    (Q : Set G) (hQ : IsCompact Q) :
    ∃ Q₁ : Set G, IsCompact Q₁ ∧
      ∀ z ∈ Z, z⁻¹ * α z ∈ Q → ∃ t ∈ T, ∃ q ∈ Q₁, z ^ n = t * q := by
  refine ⟨(fun q => (normRemainder α n q)⁻¹) '' Q, hQ.image (continuous_normRemainder α hα n).inv, fun z hz hzQ => ?_⟩
  have hqZ : z⁻¹ * α z ∈ Z := Z.mul_mem (Z.inv_mem hz) (hαZ z hz)
  have hNZ : LT.TwistedNorm.sigmaNormPow α n z ∈ Z := sigmaPartialNorm_mem α Z hαZ hz n
  refine ⟨LT.TwistedNorm.sigmaNormPow α n z, hT _ hNZ ?_, (normRemainder α n (z⁻¹ * α z))⁻¹, ⟨_, hzQ, rfl⟩, ?_⟩
  · rw [LT.TwistedNorm.map_sigmaNormPow α n (hn z hz), mul_assoc, hZcomm _ hNZ z hz, inv_mul_cancel_left]
  · rw [LT.TwistedNorm.sigmaNormPow_def,
      sigmaPartialNorm_eq_pow_mul_normRemainder α (mul_inv_cancel_left z (α z)).symm (hZcomm z hz _ hqZ) n,
      mul_inv_cancel_right]

end NormRemainder

end TwistedNormDescent

end

section

open Set

namespace TwistedNormDescent

variable {G : Type*} [Group G] {ι : Type*} [Finite ι]

private def chiLemma_HT (χ : G → (ι → ℤ)) (T : Subgroup G) (h1 : χ 1 = 0)
    (hmul : ∀ s ∈ T, ∀ t ∈ T, χ (s * t) = χ s + χ t) (hinv : ∀ t ∈ T, χ t⁻¹ = -χ t) :
    AddSubgroup (ι → ℤ) where
  carrier := χ '' (T : Set G)
  zero_mem' := ⟨1, T.one_mem, h1⟩
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s * t, T.mul_mem hs ht, hmul s hs t ht⟩
  neg_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t⁻¹, T.inv_mem ht, hinv t ht⟩

omit [Finite ι] in
private theorem chiLemma_mem_HT {χ : G → (ι → ℤ)} {T : Subgroup G} {h1 : χ 1 = 0}
    {hmul : ∀ s ∈ T, ∀ t ∈ T, χ (s * t) = χ s + χ t} {hinv : ∀ t ∈ T, χ t⁻¹ = -χ t} {a : ι → ℤ} :
    a ∈ chiLemma_HT χ T h1 hmul hinv ↔ ∃ t ∈ T, χ t = a :=
  Iff.rfl

private def chiLemma_sat (H : AddSubgroup (ι → ℤ)) (n : ℕ) : Submodule ℤ (ι → ℤ) where
  carrier := {a | n • a ∈ H}
  zero_mem' := by simp [H.zero_mem]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, nsmul_add] at ha hb ⊢
    exact H.add_mem ha hb
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [smul_comm]
    exact H.zsmul_mem ha c

omit [Finite ι] in
private theorem chiLemma_mem_sat {H : AddSubgroup (ι → ℤ)} {n : ℕ} {a : ι → ℤ} :
    a ∈ chiLemma_sat H n ↔ n • a ∈ H :=
  Iff.rfl

private theorem chiLemma_sat_subset (H : AddSubgroup (ι → ℤ)) {n : ℕ} (hn : 0 < n) :
    ∃ R : Set (ι → ℤ), R.Finite ∧ ∀ a, n • a ∈ H → ∃ r ∈ R, ∃ h ∈ H, a = h + r := by
  obtain ⟨s, hs⟩ : (chiLemma_sat H n).FG := IsNoetherian.noetherian _
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  refine ⟨Set.range fun ρ : s → Fin n => ∑ i : s, ((ρ i : ℕ) : ℤ) • (i : ι → ℤ), Set.finite_range _,
    fun a ha => ?_⟩
  have ha' : a ∈ Submodule.span ℤ (s : Set (ι → ℤ)) := by
    rw [hs]; exact chiLemma_mem_sat.2 ha
  obtain ⟨f, hf⟩ := Submodule.mem_span_finset'.1 ha'
  have hgen : ∀ i : s, (i : ι → ℤ) ∈ chiLemma_sat H n := fun i => by
    rw [← hs]; exact Submodule.subset_span i.2
  have hrem : ∀ i : s, 0 ≤ f i % n ∧ f i % n < n := fun i =>
    ⟨Int.emod_nonneg _ hn'.ne', Int.emod_lt_of_pos _ hn'⟩
  let ρ : s → Fin n := fun i => ⟨(f i % n).toNat, by have := hrem i; omega⟩
  have hρ : ∀ i : s, ((ρ i : ℕ) : ℤ) = f i % n := fun i => Int.toNat_of_nonneg (hrem i).1
  refine ⟨_, ⟨ρ, rfl⟩, ∑ i : s, (((n : ℤ) * (f i / n)) • (i : ι → ℤ)), ?_, ?_⟩
  · refine sum_mem fun i _ => ?_
    rw [mul_smul, natCast_zsmul]
    exact chiLemma_mem_sat.1 ((chiLemma_sat H n).smul_mem (f i / n) (hgen i))
  · rw [← hf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hρ, ← add_smul, add_comm, Int.emod_add_mul_ediv]

variable [TopologicalSpace G] [ContinuousMul G]

private theorem chiLemma_exists_isCompact (Z T : Subgroup G) (hTZ : T ≤ Z) (hZc : IsClosed (Z : Set G))
    (χ : G → (ι → ℤ)) (hχ : ∀ s ∈ Z, ∀ t ∈ Z, χ (s * t) = χ s + χ t)
    (hker : IsCompact {g : G | g ∈ Z ∧ χ g = 0})
    (hopen : ∃ O : Set G, IsOpen O ∧ {g : G | g ∈ Z ∧ χ g = 0} = (Z : Set G) ∩ O)
    {n : ℕ} (hn : 0 < n) (Q₁ : Set G) (hQ₁ : IsCompact Q₁) :
    ∃ Ω : Set G, IsCompact Ω ∧
      ∀ z ∈ Z, (∃ t ∈ T, ∃ q ∈ Q₁, z ^ n = t * q) → ∃ t ∈ T, ∃ d ∈ Ω, z = t * d := by
  classical
  have h1 : χ 1 = 0 := by
    have h := hχ 1 Z.one_mem 1 Z.one_mem
    rw [one_mul] at h
    simpa using h
  have hinv : ∀ g ∈ Z, χ g⁻¹ = -χ g := fun g hg => by
    have h := hχ g hg g⁻¹ (Z.inv_mem hg)
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hpow : ∀ g ∈ Z, ∀ k : ℕ, χ (g ^ k) = k • χ g := fun g hg k => by
    induction k with
    | zero => simp [h1]
    | succ k ih => rw [pow_succ, hχ _ (Z.pow_mem hg k) g hg, ih, succ_nsmul]
  have hfin : ∀ Q : Set G, IsCompact Q → (χ '' {g : G | g ∈ Q ∧ g ∈ Z}).Finite := by
    intro Q hQ
    obtain ⟨O, hO, hOker⟩ := hopen
    have h1O : (1 : G) ∈ O := by
      have : (1 : G) ∈ {g : G | g ∈ Z ∧ χ g = 0} := ⟨Z.one_mem, h1⟩
      rw [hOker] at this
      exact this.2
    have hQZ : IsCompact {g : G | g ∈ Q ∧ g ∈ Z} := by
      have : {g : G | g ∈ Q ∧ g ∈ Z} = Q ∩ (Z : Set G) := rfl
      rw [this]
      exact hQ.inter_right hZc
    obtain ⟨tset, htset, hcover⟩ := hQZ.elim_nhds_subcover (fun z => (fun g => z⁻¹ * g) ⁻¹' O)
      (fun z _ => (hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1O))
    refine (tset.finite_toSet.image χ).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    have hg' := hcover hg
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop] at hg'
    obtain ⟨z, hzt, hzO⟩ := hg'
    have hzZ : z ∈ Z := (htset z hzt).2
    have hkZ : z⁻¹ * g ∈ Z := Z.mul_mem (Z.inv_mem hzZ) hg.2
    have hk0 : χ (z⁻¹ * g) = 0 := by
      have hmem : z⁻¹ * g ∈ (Z : Set G) ∩ O := ⟨hkZ, hzO⟩
      rw [← hOker] at hmem
      exact hmem.2
    refine ⟨z, hzt, ?_⟩
    have := hχ z hzZ (z⁻¹ * g) hkZ
    rw [mul_inv_cancel_left, hk0, add_zero] at this
    exact this.symm
  set HT : AddSubgroup (ι → ℤ) :=
    chiLemma_HT χ T h1 (fun s hs t ht => hχ s (hTZ hs) t (hTZ ht)) (fun t ht => hinv t (hTZ ht)) with hHT
  obtain ⟨R, hRfin, hR⟩ := chiLemma_sat_subset HT hn
  set F : Set (ι → ℤ) := χ '' {g : G | g ∈ Q₁ ∧ g ∈ Z} with hF
  have hFfin : F.Finite := hfin Q₁ hQ₁
  set Vocc : Set (ι → ℤ) := {v | v ∈ F ∧ ∃ u : ι → ℤ, ∃ h ∈ HT, n • u = h + v} with hVocc
  have hVoccfin : Vocc.Finite := hFfin.subset fun v hv => hv.1
  have hVex : ∀ v ∈ Vocc, ∃ u : ι → ℤ, ∃ h ∈ HT, n • u = h + v := fun v hv => hv.2
  choose! uu huu using hVex
  set E : Set (ι → ℤ) := ⋃ v ∈ Vocc, (fun r => uu v + r) '' R with hE
  have hEfin : E.Finite := hVoccfin.biUnion fun v _ => hRfin.image _
  set Eocc : Set (ι → ℤ) := {e | e ∈ E ∧ ∃ g : G, g ∈ Z ∧ χ g = e} with hEocc
  have hEoccfin : Eocc.Finite := hEfin.subset fun e he => he.1
  have hEex : ∀ e ∈ Eocc, ∃ g : G, g ∈ Z ∧ χ g = e := fun e he => he.2
  choose! gg hgg using hEex
  refine ⟨⋃ e ∈ Eocc, (fun k => gg e * k) '' {g : G | g ∈ Z ∧ χ g = 0},
    hEoccfin.isCompact_biUnion fun e _ => hker.image (continuous_const.mul continuous_id), ?_⟩
  rintro z hz ⟨t, ht, q, hq, hzn⟩
  have hq' : q = t⁻¹ * z ^ n := by rw [hzn, inv_mul_cancel_left]
  have hqZ : q ∈ Z := by rw [hq']; exact Z.mul_mem (Z.inv_mem (hTZ ht)) (Z.pow_mem hz n)
  have hval : n • χ z = χ t + χ q := by rw [← hpow z hz n, hzn, hχ t (hTZ ht) q hqZ]
  have hvF : χ q ∈ F := ⟨q, ⟨hq, hqZ⟩, rfl⟩
  have hvocc : χ q ∈ Vocc := ⟨hvF, χ z, χ t, ⟨t, ht, rfl⟩, hval⟩
  obtain ⟨h', hh', hu⟩ := huu (χ q) hvocc
  have hsat : n • (χ z - uu (χ q)) ∈ HT := by
    rw [nsmul_sub, hval, hu, add_sub_add_right_eq_sub]
    exact HT.sub_mem ⟨t, ht, rfl⟩ hh'
  obtain ⟨r, hr, h'', hh'', hdecomp⟩ := hR _ hsat
  obtain ⟨t₀, ht₀, hχt₀⟩ := (chiLemma_mem_HT.1 hh'' :)
  set e : ι → ℤ := uu (χ q) + r with he_def
  have heE : e ∈ E := Set.mem_biUnion hvocc ⟨r, hr, rfl⟩
  have hdZ : t₀⁻¹ * z ∈ Z := Z.mul_mem (Z.inv_mem (hTZ ht₀)) hz
  have hχd : χ (t₀⁻¹ * z) = e := by
    rw [hχ _ (Z.inv_mem (hTZ ht₀)) z hz, hinv t₀ (hTZ ht₀), hχt₀, he_def]
    have := hdecomp
    rw [sub_eq_iff_eq_add] at this
    rw [this]; abel
  have heocc : e ∈ Eocc := ⟨heE, t₀⁻¹ * z, hdZ, hχd⟩
  obtain ⟨hggZ, hggχ⟩ := hgg e heocc
  refine ⟨t₀, ht₀, t₀⁻¹ * z, ?_, (mul_inv_cancel_left t₀ z).symm⟩
  refine Set.mem_biUnion heocc ⟨(gg e)⁻¹ * (t₀⁻¹ * z), ⟨Z.mul_mem (Z.inv_mem hggZ) hdZ, ?_⟩,
    mul_inv_cancel_left (gg e) _⟩
  rw [hχ _ (Z.inv_mem hggZ) _ hdZ, hinv _ hggZ, hggχ, hχd, neg_add_cancel]

end TwistedNormDescent

end

section

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

namespace TwistedNormDescent

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

private theorem coe_centralizer_eq_preimage (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :
        Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      glPi K L v ⁻¹' Set.pi Set.univ (fun w : v.Extension (𝓞 L) =>
        (Subgroup.centralizer ({glPi K L v γ w} : Set (GL (Fin 2) (w.1.adicCompletion L))) :
          Set (GL (Fin 2) (w.1.adicCompletion L)))) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_univ_pi]
  exact mem_centralizer_iff_glPi K L v γ x

private theorem isClosed_centralizer_coe (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsClosed (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :
      Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
  rw [coe_centralizer_eq_preimage]
  exact (isClosed_set_pi fun w _ => Set.isClosed_centralizer _).preimage (continuous_glPi K L v)

private theorem exists_chi_of_places (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hK2 : ∀ w : v.Extension (𝓞 L),
      ∃ χw : Subgroup.centralizer ({glPi K L v γ w} : Set (GL (Fin 2) (w.1.adicCompletion L))) →*
          Multiplicative (Fin 2 → ℤ),
        IsCompact (Subtype.val '' (χw.ker : Set (Subgroup.centralizer
            ({glPi K L v γ w} : Set (GL (Fin 2) (w.1.adicCompletion L)))))) ∧
          IsOpen (χw.ker : Set (Subgroup.centralizer
            ({glPi K L v γ w} : Set (GL (Fin 2) (w.1.adicCompletion L)))))) :
    ∃ χ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → (v.Extension (𝓞 L) × Fin 2 → ℤ),
      (∀ s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))), χ (s * t) = χ s + χ t) ∧
      IsCompact {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
        g ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ∧ χ g = 0} ∧
      ∃ O : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsOpen O ∧
        {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
            g ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ∧ χ g = 0} =
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :
            Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ∩ O := by
  classical
  haveI : Finite (v.Extension (𝓞 L)) := IsDedekindDomain.HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  choose χw hχw using hK2
  set Z := Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) with hZ
  let zw : ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), g ∈ Z → ∀ w : v.Extension (𝓞 L),
      Subgroup.centralizer ({glPi K L v γ w} : Set (GL (Fin 2) (w.1.adicCompletion L))) :=
    fun g hg w => ⟨glPi K L v g w, (mem_centralizer_iff_glPi K L v γ g).1 hg w⟩
  let χ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → (v.Extension (𝓞 L) × Fin 2 → ℤ) :=
    fun g p => if hg : g ∈ Z then Multiplicative.toAdd (χw p.1 (zw g hg p.1)) p.2 else 0
  have hχ0 : ∀ g (hg : g ∈ Z), χ g = 0 ↔ ∀ w, zw g hg w ∈ (χw w).ker := by
    intro g hg
    constructor
    · intro h w
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      have := congrFun h (w, i)
      simp only [χ, dif_pos hg, Pi.zero_apply] at this
      simpa using this
    · intro h
      funext p
      have hw := h p.1
      rw [MonoidHom.mem_ker] at hw
      simp only [χ, dif_pos hg, hw, Pi.zero_apply]
      simp
  refine ⟨χ, ?_, ?_, ?_⟩
  ·
    intro s hs t ht
    have hst : s * t ∈ Z := Z.mul_mem hs ht
    funext p
    have hmul : zw (s * t) hst p.1 = zw s hs p.1 * zw t ht p.1 := by
      apply Subtype.ext
      simp only [zw, map_mul, Pi.mul_apply, Subgroup.coe_mul]
    simp only [χ, dif_pos hs, dif_pos ht, dif_pos hst, Pi.add_apply, hmul, map_mul, toAdd_mul]
  ·
    have hbox : IsCompact (Set.pi Set.univ fun w => Subtype.val '' (SetLike.coe (χw w).ker)) :=
      isCompact_univ_pi fun w => (hχw w).1
    have heq : {g | g ∈ Z ∧ χ g = 0} =
        glPi K L v ⁻¹' (Set.pi Set.univ fun w => Subtype.val '' (SetLike.coe (χw w).ker)) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · rintro ⟨hg, h⟩ w
        exact ⟨zw g hg w, (hχ0 g hg).1 h w, rfl⟩
      · intro h
        have hg : g ∈ Z := (mem_centralizer_iff_glPi K L v γ g).2 fun w => by
          obtain ⟨z, -, hz⟩ := h w
          rw [← hz]; exact z.2
        refine ⟨hg, (hχ0 g hg).2 fun w => ?_⟩
        obtain ⟨z, hzker, hz⟩ := h w
        have : z = zw g hg w := Subtype.ext hz
        rw [← this]; exact hzker
    have himg : (glPi K L v).symm '' (Set.pi Set.univ fun w => Subtype.val '' (SetLike.coe (χw w).ker)) =
        glPi K L v ⁻¹' (Set.pi Set.univ fun w => Subtype.val '' (SetLike.coe (χw w).ker)) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro h
        exact ⟨glPi K L v g, h, by simp⟩
    rw [heq, ← himg]
    exact hbox.image (continuous_glPi_symm K L v)
  ·
    have hU : ∀ w, ∃ U : Set (GL (Fin 2) (w.1.adicCompletion L)), IsOpen U ∧
        Subtype.val ⁻¹' U = (SetLike.coe (χw w).ker) := fun w => by
      obtain ⟨U, hUo, hUeq⟩ := isOpen_induced_iff.1 (hχw w).2
      exact ⟨U, hUo, hUeq⟩
    choose U hUo hUeq using hU
    refine ⟨glPi K L v ⁻¹' Set.pi Set.univ U,
      (isOpen_set_pi Set.finite_univ fun w _ => hUo w).preimage (continuous_glPi K L v), ?_⟩
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · rintro ⟨hg, h⟩
      refine ⟨hg, fun w => ?_⟩
      have hk := (hχ0 g hg).1 h w
      rw [← SetLike.mem_coe, ← hUeq w, Set.mem_preimage] at hk
      exact hk
    · rintro ⟨hg, h⟩
      refine ⟨hg, (hχ0 g hg).2 fun w => ?_⟩
      rw [← SetLike.mem_coe, ← hUeq w, Set.mem_preimage]
      exact h w

end TwistedNormDescent

end

section

open scoped Pointwise

namespace TwistedNormDescent

private theorem exists_isCompact_twistedConj_of_conj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (σ' : G →* G) (hσ' : Continuous σ') (δ : G) (N : G → G) (hN : Continuous N)
    (hNconj : ∀ x, N (x⁻¹ * δ * σ' x) = x⁻¹ * N δ * x)
    (Z T : Subgroup G) (n : ℕ)
    (huntw : ∀ S₁ : Set G, IsCompact S₁ → ∃ Ω₁ : Set G, IsCompact Ω₁ ∧
      ∀ x, x⁻¹ * N δ * x ∈ S₁ → ∃ z ∈ Z, ∃ d ∈ Ω₁, x = z * d)
    (hd1 : ∀ Q : Set G, IsCompact Q → ∃ Q₁ : Set G, IsCompact Q₁ ∧
      ∀ z ∈ Z, z⁻¹ * (δ * σ' z * δ⁻¹) ∈ Q → ∃ t ∈ T, ∃ q ∈ Q₁, z ^ n = t * q)
    (hd2 : ∀ Q₁ : Set G, IsCompact Q₁ → ∃ Ω₂ : Set G, IsCompact Ω₂ ∧
      ∀ z ∈ Z, (∃ t ∈ T, ∃ q ∈ Q₁, z ^ n = t * q) → ∃ t ∈ T, ∃ d ∈ Ω₂, z = t * d)
    (S : Set G) (hS : IsCompact S) :
    ∃ Ω : Set G, IsCompact Ω ∧ ∀ x, x⁻¹ * δ * σ' x ∈ S → ∃ t ∈ T, ∃ d ∈ Ω, x = t * d := by
  obtain ⟨Ω₁, hΩ₁, h₁⟩ := huntw (N '' S) (hS.image hN)
  let f : G × G × G → G := fun p => p.1 * p.2.1 * (σ' p.2.2)⁻¹ * δ⁻¹
  have hf : Continuous f :=
    ((continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
      ((hσ'.comp (continuous_snd.comp continuous_snd)).inv)).mul continuous_const
  obtain ⟨Q₁, hQ₁, h₂⟩ := hd1 (f '' (Ω₁ ×ˢ S ×ˢ Ω₁)) ((hΩ₁.prod (hS.prod hΩ₁)).image hf)
  obtain ⟨Ω₂, hΩ₂, h₃⟩ := hd2 Q₁ hQ₁
  refine ⟨Ω₂ * Ω₁, hΩ₂.mul hΩ₁, fun x hx => ?_⟩
  have hNx : x⁻¹ * N δ * x ∈ N '' S := ⟨_, hx, hNconj x⟩
  obtain ⟨z, hz, d, hd, hxd⟩ := h₁ x hNx
  have hq : z⁻¹ * (δ * σ' z * δ⁻¹) ∈ f '' (Ω₁ ×ˢ S ×ˢ Ω₁) := by
    refine ⟨(d, x⁻¹ * δ * σ' x, d), Set.mk_mem_prod hd (Set.mk_mem_prod hx hd), ?_⟩
    show d * (x⁻¹ * δ * σ' x) * (σ' d)⁻¹ * δ⁻¹ = z⁻¹ * (δ * σ' z * δ⁻¹)
    rw [hxd, map_mul, mul_inv_rev]
    group
  obtain ⟨t, ht, d₂, hd₂, hzt⟩ := h₃ z hz (h₂ z hz hq)
  exact ⟨t, ht, d₂ * d, Set.mul_mem_mul hd₂ hd, by rw [hxd, hzt, mul_assoc]⟩

end TwistedNormDescent

end

set_option autoImplicit false

open NumberField IsDedekindDomain TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (S : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hS : IsCompact S) :
    ∃ Ω : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)), IsCompact Ω ∧
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∈ S →
          ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ, ∃ d ∈ Ω, x = t * d := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := IsDedekindDomain.HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  have hσc : Continuous (AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ) :=
    TwistedNormDescent.twist_continuous_sigmaGL K L (v.adicCompletion K) σ
  have hNc : Continuous (AutomorphicForm.normString K L (v.adicCompletion K) σ) :=
    TwistedNormDescent.twist_continuous_normString K L (v.adicCompletion K) σ
  have hNconj : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      AutomorphicForm.normString K L (v.adicCompletion K) σ
          (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) =
        x⁻¹ * AutomorphicForm.normString K L (v.adicCompletion K) σ δ * x :=
    fun x => TwistedNormDescent.normStr_normString_sigmaConj K L (v.adicCompletion K) σ x δ
  have hZcomm : ∀ a ∈ Subgroup.centralizer
      ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
      ∀ b ∈ Subgroup.centralizer
        ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
      a * b = b * a :=
    TwistedNormDescent.centralizer_comm_of_isUnit_disc _ hδ
  let α : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
    { toFun := fun z => δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹
      map_one' := by simp
      map_mul' := fun a b => by simp [map_mul, mul_assoc] }
  have hαapp : ∀ z, α z = δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹ := fun _ => rfl
  have hα : Continuous α := by
    show Continuous fun z => δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹
    exact (continuous_const.mul hσc).mul continuous_const
  have hαZ : ∀ z ∈ Subgroup.centralizer
      ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
      α z ∈ Subgroup.centralizer
        ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
    fun z hz => TwistedNormDescent.normStr_alpha_mem_centralizer K L (v.adicCompletion K) σ δ hz
  have hn : ∀ z ∈ Subgroup.centralizer
      ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
      (⇑α)^[Module.finrank K L] z = z :=
    fun z hz => TwistedNormDescent.normStr_iterate_alpha_eq_self K L (v.adicCompletion K) σ δ z hz
  have hT : ∀ t ∈ Subgroup.centralizer
      ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
      α t = t → t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ :=
    fun t _ ht => AutomorphicForm.mem_sigmaCentralizer_iff_fixed.2 ht
  have hTZ : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ≤ Subgroup.centralizer
      ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) :=
    TwistedNormDescent.normStr_twistedCentralizer_le_centralizer K L (v.adicCompletion K) σ δ
  have hZc :=
    TwistedNormDescent.isClosed_centralizer_coe K L v (AutomorphicForm.normString K L (v.adicCompletion K) σ δ)
  obtain ⟨χ, hχ, hker, hopen⟩ := TwistedNormDescent.exists_chi_of_places K L v
    (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) fun w =>
      AutomorphicForm.exists_monoidHom_localCentralizer_isCompact_ker_of_isRegularSemisimple L w.1
        (TwistedNormDescent.glPi K L v (AutomorphicForm.normString K L (v.adicCompletion K) σ δ) w)
        (TwistedNormDescent.isRegularSemisimple_glPi K L v hδ w)
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  exact TwistedNormDescent.exists_isCompact_twistedConj_of_conj (AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ)
    hσc δ
    (AutomorphicForm.normString K L (v.adicCompletion K) σ) hNc hNconj
    (Subgroup.centralizer
      ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))))
    (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) (Module.finrank K L)
    (fun S₁ hS₁ => TwistedNormDescent.exists_isCompact_forall_conj_mem K L v hδ S₁ hS₁)
    (fun Q hQ =>
      TwistedNormDescent.exists_isCompact_forall_pow_eq_mul α hα _ hZcomm hαZ (Module.finrank K L) hn _ hT Q hQ)
    (fun Q₁ hQ₁ => TwistedNormDescent.chiLemma_exists_isCompact _ _ hTZ hZc χ hχ hker hopen hpos Q₁ hQ₁)
    S hS

end S_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_sigmaConj_mem_exists_twistedCentralizer_mul (solution)
