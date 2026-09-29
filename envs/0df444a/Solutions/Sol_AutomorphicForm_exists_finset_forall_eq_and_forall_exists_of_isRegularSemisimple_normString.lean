-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d55a3471-76e8-5a3e-a3ae-de8b01ca8957

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TensorProduct
open scoped TensorProduct.RightActions

namespace TwistedSupport

section Commutant

variable {R : Type*} [CommRing R]

private theorem exists_eq_smul_one_add_smul_of_commute (g m : Matrix (Fin 2) (Fin 2) R)
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) :
    ∃ x y : R, m = x • (1 : Matrix (Fin 2) (Fin 2) R) + y • g := by
  obtain ⟨u, hu⟩ := hg
  have hinv : (↑u⁻¹ : R) * ((g 0 0 + g 1 1) ^ 2 - 4 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) = 1 := by
    have h := u.inv_mul
    rwa [hu, Matrix.trace_fin_two, Matrix.det_fin_two] at h
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  have h10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
  refine ⟨m 0 0 - (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)) * g 0 0,
    (↑u⁻¹ : R) * ((g 0 0 - g 1 1) * (m 0 0 - m 1 1) + 2 * (g 0 1 * m 1 0 + g 1 0 * m 0 1)), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.zero_eta, Fin.mk_one, Fin.isValue, if_true, if_false, mul_one, mul_zero, zero_add, one_ne_zero,
    zero_ne_one]
  · ring
  · linear_combination (-(m 0 1)) * hinv + (-((↑u⁻¹ : R) * (g 0 0 - g 1 1))) * h01 + (2 * (↑u⁻¹ : R) * g 0 1) * h00
  · linear_combination (-(m 1 0)) * hinv + ((↑u⁻¹ : R) * (g 0 0 - g 1 1)) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h00
  · linear_combination (m 0 0 - m 1 1) * hinv + (2 * (↑u⁻¹ : R) * g 0 1) * h10 + (-(2 * (↑u⁻¹ : R) * g 1 0)) * h01

private theorem commute_of_commute_of_commute {g m m' : Matrix (Fin 2) (Fin 2) R}
    (hg : IsUnit (g.trace ^ 2 - 4 * g.det)) (hm : m * g = g * m) (hm' : m' * g = g * m') : m * m' = m' * m := by
  obtain ⟨x, y, rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m hg hm
  obtain ⟨x', y', rfl⟩ := exists_eq_smul_one_add_smul_of_commute g m' hg hm'
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

private theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) R} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (s t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))) : s * t = t * s := by
  have hs : ((s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (γ : Matrix (Fin 2) (Fin 2) R) =
      (γ : Matrix (Fin 2) (Fin 2) R) * ((s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_iff.1 s.2) γ rfl]
  have ht : ((t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (γ : Matrix (Fin 2) (Fin 2) R) =
      (γ : Matrix (Fin 2) (Fin 2) R) * ((t : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_iff.1 t.2) γ rfl]
  exact Subtype.ext (Units.ext (commute_of_commute_of_commute hγ hs ht))

end Commutant

section IntegralUnits

variable {A : Type*} [CommRing A]

private theorem mul_mem_integralUnitsSet {S : Type*} [SetLike S A] [SubringClass S A] (R : S) {g h : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (R : Set A)) (hh : h ∈ AutomorphicForm.integralUnitsSet (R : Set A)) :
    g * h ∈ AutomorphicForm.integralUnitsSet (R : Set A) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hh.2 i k) (hg.2 k j)

private theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet U) :
    g⁻¹ ∈ AutomorphicForm.integralUnitsSet U :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

end IntegralUnits

section Twist

open TensorProduct
open scoped TensorProduct.RightActions

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A] [Algebra K A]

private theorem sigmaTensor_tmul (σ : L ≃ₐ[K] L) (ℓ : L) (a : A) :
    AutomorphicForm.sigmaTensor K L A σ (ℓ ⊗ₜ[K] a) = σ ℓ ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]

private theorem sigmaTensor_mul_apply (σ σ' : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    AutomorphicForm.sigmaTensor K L A (σ * σ') z =
      AutomorphicForm.sigmaTensor K L A σ (AutomorphicForm.sigmaTensor K L A σ' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ℓ a => rw [sigmaTensor_tmul, sigmaTensor_tmul, sigmaTensor_tmul, AlgEquiv.mul_apply]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

private theorem sigmaTensor_one_apply (z : L ⊗[K] A) : AutomorphicForm.sigmaTensor K L A 1 z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ℓ a => rw [sigmaTensor_tmul, AlgEquiv.one_apply]
  | add z₁ z₂ h₁ h₂ => rw [map_add, h₁, h₂]

private theorem iterate_sigmaTensor_apply (σ : L ≃ₐ[K] L) (k : ℕ) (z : L ⊗[K] A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[k] z = AutomorphicForm.sigmaTensor K L A (σ ^ k) z := by
  induction k generalizing z with
  | zero => rw [Function.iterate_zero_apply, pow_zero, sigmaTensor_one_apply]
  | succ k ih => rw [Function.iterate_succ_apply', ih, pow_succ', sigmaTensor_mul_apply]

private theorem pow_finrank_eq_one (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (θ : E ≃ₐ[F] E) : θ ^ Module.finrank F E = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _ (Module.finrank_mul_finrank F (IntermediateField.fixedField (Subgroup.zpowers θ)) E)

private theorem iterate_sigmaTensor_finrank [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (z : L ⊗[K] A) :
    (⇑(AutomorphicForm.sigmaTensor K L A σ))^[Module.finrank K L] z = z := by
  rw [iterate_sigmaTensor_apply, pow_finrank_eq_one K L σ, sigmaTensor_one_apply]

variable (σ : L ≃ₐ[K] L)

open AutomorphicForm

private theorem iterate_sigmaGL_eq_self (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    (x : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x :=
  LT.TwistedNorm.iterate_generalLinearGroup_map_eq_self hσn x

private theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) δ :=
  (LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range (sigmaGL K L A σ) δ (Module.finrank K L)).symm

private theorem commute_normString_of_mem_twistedCentralizer
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {δ t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) : t * normString K L A σ δ = normString K L A σ δ * t := by
  have h1 : t⁻¹ * δ * sigmaGL K L A σ t = δ := mem_sigmaCentralizer_iff_inv.1 ht
  have key := LT.TwistedNorm.sigmaNormPow_sigmaConjElt (sigmaGL K L A σ) (Module.finrank K L)
    (iterate_sigmaGL_eq_self σ hσn t) δ
  rw [h1] at key
  rw [normString_eq_sigmaNormPow]
  conv_lhs => rw [key]
  group

private theorem mul_comm_of_mem_twistedCentralizer
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z) {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : IsRegularSemisimple (normString K L A σ δ)) (s t : twistedCentralizer K L A σ δ) : s * t = t * s := by
  have hs : ((s : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
        ((s : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    rw [← Units.val_mul, ← Units.val_mul, commute_normString_of_mem_twistedCentralizer σ hσn s.2]
  have ht : ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (normString K L A σ δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
        ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    rw [← Units.val_mul, ← Units.val_mul, commute_normString_of_mem_twistedCentralizer σ hσn t.2]
  exact Subtype.ext (Units.ext (commute_of_commute_of_commute hδ hs ht))

end Twist

section SemiLocal

open TensorProduct
open scoped TensorProduct.RightActions

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  {v : HeightOneSpectrum (𝓞 K)}

open AutomorphicForm

private theorem continuous_sigmaTensor : Continuous (sigmaTensor K L (v.adicCompletion K) σ) := by
  have h : ⇑(sigmaTensor K L (v.adicCompletion K) σ) =
      ⇑(TensorProduct.RightActions.LinearMap.baseChange K L L (v.adicCompletion K) σ.toLinearMap) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul ℓ a =>
      rw [sigmaTensor_tmul]
      simp [TensorProduct.RightActions.LinearMap.baseChange, LinearMap.baseChange_tmul]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

private theorem continuous_sigmaGL : Continuous (sigmaGL K L (v.adicCompletion K) σ) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  have hf := continuous_sigmaTensor σ (v := v)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_map hf, ?_⟩
  have h : (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (((sigmaGL K L (v.adicCompletion K) σ g)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
      fun g => ((g⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map (sigmaTensor K L (v.adicCompletion K) σ) := by
    funext g
    rw [← map_inv]
    rfl
  rw [h]
  exact Units.continuous_coe_inv.matrix_map hf

end SemiLocal

section Phi

open TensorProduct
open scoped TensorProduct.RightActions

variable {K L : Type} [Field K] [Field L] [Algebra K L] {A : Type} [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

open AutomorphicForm

private def phi (δ : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] A) :=
  (MulAut.conj δ).toMonoidHom.comp (sigmaGL K L A σ)

private theorem phi_apply (δ g : GL (Fin 2) (L ⊗[K] A)) :
    phi σ δ g = δ * sigmaGL K L A σ g * δ⁻¹ := rfl

private theorem mem_twistedCentralizer_iff_phi {δ t : GL (Fin 2) (L ⊗[K] A)} :
    t ∈ twistedCentralizer K L A σ δ ↔ phi σ δ t = t := by
  rw [phi_apply]
  exact mem_sigmaCentralizer_iff_fixed

private theorem twistedDisplacement_eq (δ z : GL (Fin 2) (L ⊗[K] A)) :
    z⁻¹ * δ * sigmaGL K L A σ z * δ⁻¹ = z⁻¹ * phi σ δ z := by
  rw [phi_apply]
  group

private theorem phi_iterate (δ : GL (Fin 2) (L ⊗[K] A)) (k : ℕ) (g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(phi σ δ))^[k] g = LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ k *
      (⇑(sigmaGL K L A σ))^[k] g * (LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L A σ) δ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, phi_apply, LT.TwistedNorm.sigmaPartialNorm_succ',
      Function.iterate_succ_apply', map_mul, map_mul, map_inv]
    group

private theorem coe_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    ((sigmaGL K L A σ x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map (sigmaTensor K L A σ) := by
  ext i j
  rfl

private def phiM (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix (Fin 2) (Fin 2) (L ⊗[K] A) →+ Matrix (Fin 2) (Fin 2) (L ⊗[K] A) :=
  (AddMonoidHom.mulLeft (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))).comp
    ((AddMonoidHom.mulRight ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))).comp
      (sigmaTensor K L A σ).mapMatrix.toAddMonoidHom)

private theorem phiM_apply (δ : GL (Fin 2) (L ⊗[K] A)) (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :
    phiM σ δ m = (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) *
      (m.map (sigmaTensor K L A σ) * ((δ⁻¹ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) :=
  rfl

private theorem phiM_coe (δ g : GL (Fin 2) (L ⊗[K] A)) :
    phiM σ δ (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      ((phi σ δ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
  rw [phiM_apply, phi_apply, Units.val_mul, Units.val_mul, coe_sigmaGL, mul_assoc]

private theorem phi_iterate_finrank
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    (δ g : GL (Fin 2) (L ⊗[K] A)) :
    (⇑(phi σ δ))^[Module.finrank K L] g = normString K L A σ δ * g * (normString K L A σ δ)⁻¹ := by
  rw [phi_iterate, iterate_sigmaGL_eq_self σ hσn g, normString_eq_sigmaNormPow, LT.TwistedNorm.sigmaNormPow_def]

private theorem phi_normString
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    (δ : GL (Fin 2) (L ⊗[K] A)) : phi σ δ (normString K L A σ δ) = normString K L A σ δ := by
  rw [phi_apply, normString_eq_sigmaNormPow,
    LT.TwistedNorm.map_sigmaNormPow _ _ (iterate_sigmaGL_eq_self σ hσn δ)]
  group

private theorem phi_mem_centralizer
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    (δ : GL (Fin 2) (L ⊗[K] A)) {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    phi σ δ z ∈ Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  have h := hz _ rfl
  calc normString K L A σ δ * phi σ δ z
      = phi σ δ (normString K L A σ δ) * phi σ δ z := by rw [phi_normString σ hσn δ]
    _ = phi σ δ (normString K L A σ δ * z) := (map_mul _ _ _).symm
    _ = phi σ δ (z * normString K L A σ δ) := by rw [h]
    _ = phi σ δ z * normString K L A σ δ := by rw [map_mul, phi_normString σ hσn δ]

private theorem phi_iterate_finrank_of_mem
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    (δ : GL (Fin 2) (L ⊗[K] A)) {z : GL (Fin 2) (L ⊗[K] A)}
    (hz : z ∈ Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A)))) :
    (⇑(phi σ δ))^[Module.finrank K L] z = z := by
  rw [phi_iterate_finrank σ hσn]
  have h := (Subgroup.mem_centralizer_iff.1 hz) _ rfl
  rw [h]
  group

private theorem mem_centralizer_of_mem_twistedCentralizer
    (hσn : ∀ z : L ⊗[K] A, (⇑(sigmaTensor K L A σ))^[Module.finrank K L] z = z)
    {δ t : GL (Fin 2) (L ⊗[K] A)} (ht : t ∈ twistedCentralizer K L A σ δ) :
    t ∈ Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact (commute_normString_of_mem_twistedCentralizer σ hσn ht).symm

end Phi

private theorem inv_mul_mul_inv_mul_eq {G : Type*} [Group G] {a z b : G} (c : G)
    (haz : Commute a z) (hzb : Commute z b) (hab : Commute a b) :
    (a⁻¹ * z)⁻¹ * (b⁻¹ * c) = (a⁻¹ * b)⁻¹ * (z⁻¹ * c) := by
  have h1 : z⁻¹ * a = a * z⁻¹ := haz.inv_right.eq.symm
  have h2 : z⁻¹ * b⁻¹ = b⁻¹ * z⁻¹ := hzb.inv_inv.eq
  have h3 : a * b⁻¹ = b⁻¹ * a := hab.inv_right.eq
  calc (a⁻¹ * z)⁻¹ * (b⁻¹ * c) = z⁻¹ * a * b⁻¹ * c := by group
    _ = a * z⁻¹ * b⁻¹ * c := by rw [h1]
    _ = a * (z⁻¹ * b⁻¹) * c := by group
    _ = a * (b⁻¹ * z⁻¹) * c := by rw [h2]
    _ = a * b⁻¹ * z⁻¹ * c := by group
    _ = b⁻¹ * a * z⁻¹ * c := by rw [h3]
    _ = (a⁻¹ * b)⁻¹ * (z⁻¹ * c) := by group

private theorem sum_range_succ_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (n : ℕ) (h : f n = f 0) :
    ∑ i ∈ Finset.range n, f (i + 1) = ∑ i ∈ Finset.range n, f i := by
  have e1 := Finset.sum_range_succ' f n
  have e2 := Finset.sum_range_succ f n
  rw [h] at e2
  exact add_right_cancel (e1.symm.trans e2)

private theorem iterate_eq_mul_sigmaPartialNorm {G : Type*} [Group G] (Φ : G →* G) (z : G) (k : ℕ) :
    (⇑Φ)^[k] z = z * LT.TwistedNorm.sigmaPartialNorm Φ (z⁻¹ * Φ z) k := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, LT.TwistedNorm.sigmaPartialNorm_zero, mul_one]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, LT.TwistedNorm.sigmaPartialNorm_succ', ← mul_assoc,
      mul_inv_cancel_left]

private theorem map_mul_eq_self_of_iterate_eq {R : Type*} [CommRing R] (Φ : GL (Fin 2) R →* GL (Fin 2) R)
    (ΦM : Matrix (Fin 2) (Fin 2) R →+ Matrix (Fin 2) (Fin 2) R)
    (hΦ : ∀ g : GL (Fin 2) R,
      ΦM (g : Matrix (Fin 2) (Fin 2) R) = ((Φ g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R))
    {n : ℕ} {ν : R} (hnν : (n : R) * ν = 1) {z : GL (Fin 2) R} (hzn : (⇑Φ)^[n] z = z)
    (P : ℕ → GL (Fin 2) R) (hP : ∀ k, (⇑Φ)^[k] z = z * P k) {s : Matrix (Fin 2) (Fin 2) R}
    (hs : s = ∑ k ∈ Finset.range n, (((P k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) - 1))
    {u : GL (Fin 2) R} (hu : (u : Matrix (Fin 2) (Fin 2) R) = 1 + Matrix.scalar (Fin 2) ν * s) :
    Φ (z * u) = z * u := by

  have hνn : Matrix.scalar (Fin 2) ν * (n : Matrix (Fin 2) (Fin 2) R) = 1 := by
    rw [← map_natCast (Matrix.scalar (α := R) (Fin 2)) n, ← map_mul, mul_comm, hnν, map_one]
  have hnν' : (n : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) ν = 1 := by
    rw [← map_natCast (Matrix.scalar (α := R) (Fin 2)) n, ← map_mul, hnν, map_one]

  have hΦn : ∀ m : Matrix (Fin 2) (Fin 2) R,
      ΦM (m * (n : Matrix (Fin 2) (Fin 2) R)) = ΦM m * (n : Matrix (Fin 2) (Fin 2) R) := fun m => by
    rw [← nsmul_eq_mul', map_nsmul, nsmul_eq_mul']

  have h1 : ∑ k ∈ Finset.range n, (((⇑Φ)^[k] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (z : Matrix (Fin 2) (Fin 2) R) * (s + n) := by
    have h0 : ∀ k ∈ Finset.range n, (((⇑Φ)^[k] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
        (z : Matrix (Fin 2) (Fin 2) R) * ((P k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := fun k _ => by
      rw [hP k, Units.val_mul]
    rw [Finset.sum_congr rfl h0, ← Finset.mul_sum, hs, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_one, sub_add_cancel]
  have h2 : ((z * u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (n : Matrix (Fin 2) (Fin 2) R) =
      (z : Matrix (Fin 2) (Fin 2) R) * (s + n) := by
    rw [Units.val_mul, hu, mul_assoc, add_mul, one_mul, mul_assoc, ← Nat.cast_comm n s,
      ← mul_assoc (Matrix.scalar (Fin 2) ν), hνn, one_mul, add_comm]
  have hsum : ∑ k ∈ Finset.range n, (((⇑Φ)^[k] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      ((z * u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (n : Matrix (Fin 2) (Fin 2) R) := by
    rw [h1, h2]

  have h3 : ∀ k, ΦM (((⇑Φ)^[k] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (((⇑Φ)^[k + 1] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := fun k => by
    rw [hΦ, Function.iterate_succ_apply']
  have hfix : ΦM (∑ k ∈ Finset.range n, (((⇑Φ)^[k] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) =
      ∑ k ∈ Finset.range n, (((⇑Φ)^[k] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [map_sum]
    simp only [h3]
    refine sum_range_succ_shift (fun k => (((⇑Φ)^[k] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) n ?_
    show (((⇑Φ)^[n] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      (((⇑Φ)^[0] z : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
    rw [hzn, Function.iterate_zero_apply]

  apply Units.ext
  have h4 : ΦM (((z * u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (n : Matrix (Fin 2) (Fin 2) R)) =
      ((z * u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (n : Matrix (Fin 2) (Fin 2) R) := by
    rw [← hsum]
    exact hfix
  rw [hΦn, hΦ] at h4
  have h5 := congrArg (· * Matrix.scalar (Fin 2) ν) h4
  simpa only [mul_assoc, hnν', mul_one] using h5

section Radical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

private theorem semiLocalHomeomorph_apply (a : L ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K L v a =
      HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v a := rfl

private theorem semiLocalHomeomorph_mul (a b : L ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K L v (a * b) = semiLocalHomeomorph K L v a * semiLocalHomeomorph K L v b := by
  rw [semiLocalHomeomorph_apply, semiLocalHomeomorph_apply, semiLocalHomeomorph_apply, map_mul]

private theorem semiLocalHomeomorph_add (a b : L ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K L v (a + b) = semiLocalHomeomorph K L v a + semiLocalHomeomorph K L v b := by
  rw [semiLocalHomeomorph_apply, semiLocalHomeomorph_apply, semiLocalHomeomorph_apply, map_add]

private theorem semiLocalHomeomorph_neg (a : L ⊗[K] v.adicCompletion K) :
    semiLocalHomeomorph K L v (-a) = -semiLocalHomeomorph K L v a := by
  rw [semiLocalHomeomorph_apply, semiLocalHomeomorph_apply, map_neg]

private theorem semiLocalHomeomorph_one : semiLocalHomeomorph K L v 1 = 1 := by
  rw [semiLocalHomeomorph_apply, map_one]

private theorem semiLocalHomeomorph_zero : semiLocalHomeomorph K L v 0 = 0 := by
  rw [semiLocalHomeomorph_apply, map_zero]

private theorem mem_semiLocalIntegers_iff (a : L ⊗[K] v.adicCompletion K) :
    a ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), Valued.v (semiLocalHomeomorph K L v a w) ≤ 1 := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]

private def rad : Set (L ⊗[K] v.adicCompletion K) :=
  {a | ∀ w : v.Extension (𝓞 L), Valued.v (semiLocalHomeomorph K L v a w) < 1}

private theorem mem_rad (a : L ⊗[K] v.adicCompletion K) :
    a ∈ rad K L v ↔ ∀ w : v.Extension (𝓞 L), Valued.v (semiLocalHomeomorph K L v a w) < 1 := Iff.rfl

private theorem rad_subset_semiLocalIntegers : rad K L v ⊆ semiLocalIntegers K L v :=
  fun a ha => (mem_semiLocalIntegers_iff K L v a).2 fun w => le_of_lt ((mem_rad K L v a).1 ha w)

private theorem zero_mem_rad : (0 : L ⊗[K] v.adicCompletion K) ∈ rad K L v :=
  (mem_rad K L v 0).2 fun w => by
    rw [semiLocalHomeomorph_zero, Pi.zero_apply, map_zero]
    exact zero_lt_one

private theorem add_mem_rad {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ rad K L v) (hb : b ∈ rad K L v) :
    a + b ∈ rad K L v :=
  (mem_rad K L v _).2 fun w => by
    rw [semiLocalHomeomorph_add, Pi.add_apply]
    exact Valuation.map_add_lt _ ((mem_rad K L v a).1 ha w) ((mem_rad K L v b).1 hb w)

private theorem neg_mem_rad {a : L ⊗[K] v.adicCompletion K} (ha : a ∈ rad K L v) : -a ∈ rad K L v :=
  (mem_rad K L v _).2 fun w => by
    rw [semiLocalHomeomorph_neg, Pi.neg_apply, Valuation.map_neg]
    exact (mem_rad K L v a).1 ha w

private theorem sub_mem_rad {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ rad K L v) (hb : b ∈ rad K L v) :
    a - b ∈ rad K L v := by
  rw [sub_eq_add_neg]
  exact add_mem_rad K L v ha (neg_mem_rad K L v hb)

private theorem mul_mem_rad_left {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ rad K L v) : a * b ∈ rad K L v :=
  (mem_rad K L v _).2 fun w => by
    rw [semiLocalHomeomorph_mul, Pi.mul_apply, map_mul]
    calc Valued.v (semiLocalHomeomorph K L v a w) * Valued.v (semiLocalHomeomorph K L v b w)
        ≤ 1 * Valued.v (semiLocalHomeomorph K L v b w) :=
          mul_le_mul_left ((mem_semiLocalIntegers_iff K L v a).1 ha w) _
      _ = Valued.v (semiLocalHomeomorph K L v b w) := one_mul _
      _ < 1 := (mem_rad K L v b).1 hb w

private theorem mul_mem_rad_right {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ rad K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a * b ∈ rad K L v := by
  rw [mul_comm]
  exact mul_mem_rad_left K L v hb ha

private theorem sum_mem_rad {ι : Type*} (s : Finset ι) (f : ι → L ⊗[K] v.adicCompletion K)
    (h : ∀ i ∈ s, f i ∈ rad K L v) : ∑ i ∈ s, f i ∈ rad K L v :=
  Finset.sum_induction f (· ∈ rad K L v) (fun _ _ ha hb => add_mem_rad K L v ha hb) (zero_mem_rad K L v) h

private theorem add_mem_semiLocalIntegers {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a + b ∈ semiLocalIntegers K L v :=
  (mem_semiLocalIntegers_iff K L v _).2 fun w => by
    rw [semiLocalHomeomorph_add, Pi.add_apply]
    exact Valuation.map_add_le _ ((mem_semiLocalIntegers_iff K L v a).1 ha w)
      ((mem_semiLocalIntegers_iff K L v b).1 hb w)

private theorem mul_mem_semiLocalIntegers {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a * b ∈ semiLocalIntegers K L v :=
  (mem_semiLocalIntegers_iff K L v _).2 fun w => by
    rw [semiLocalHomeomorph_mul, Pi.mul_apply, map_mul]
    exact Left.mul_le_one ((mem_semiLocalIntegers_iff K L v a).1 ha w) ((mem_semiLocalIntegers_iff K L v b).1 hb w)

private theorem neg_mem_semiLocalIntegers {a : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v) :
    -a ∈ semiLocalIntegers K L v :=
  (mem_semiLocalIntegers_iff K L v _).2 fun w => by
    rw [semiLocalHomeomorph_neg, Pi.neg_apply, Valuation.map_neg]
    exact (mem_semiLocalIntegers_iff K L v a).1 ha w

private theorem natCast_mem_semiLocalIntegers (n : ℕ) :
    ((n : ℕ) : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact zero_mem_semiLocalIntegers K L v
  | succ n ih =>
    rw [Nat.cast_succ]
    exact add_mem_semiLocalIntegers K L v ih (one_mem_semiLocalIntegers K L v)

private theorem isUnit_one_add {ε : L ⊗[K] v.adicCompletion K} (hε : ε ∈ rad K L v) : IsUnit (1 + ε) := by
  have hne : ∀ w : v.Extension (𝓞 L),
      HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v (1 + ε) w ≠ 0 := by
    intro w h0
    have hlt := (mem_rad K L v ε).1 hε w
    rw [semiLocalHomeomorph_apply] at hlt
    have h1 := Valuation.map_one_add_of_lt _ hlt
    rw [map_add, map_one, Pi.add_apply, Pi.one_apply] at h0
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨b, hb⟩ : ∃ b : Π w : v.Extension (𝓞 L), w.1.adicCompletion L,
      HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v (1 + ε) * b = 1 :=
    ⟨fun w => (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v (1 + ε) w)⁻¹,
      funext fun w => mul_inv_cancel₀ (hne w)⟩
  obtain ⟨c, hc⟩ := EquivLike.surjective (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v) b
  refine isUnit_iff_exists_inv.2
    ⟨c, EquivLike.injective (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v) ?_⟩
  rw [map_mul, hc, hb, map_one]

private theorem inverse_mem_semiLocalIntegers {a : L ⊗[K] v.adicCompletion K} (hu : IsUnit a)
    (hva : ∀ w : v.Extension (𝓞 L), Valued.v (semiLocalHomeomorph K L v a w) = 1) :
    Ring.inverse a ∈ semiLocalIntegers K L v :=
  (mem_semiLocalIntegers_iff K L v _).2 fun w => by
    have h := congrArg (fun x => Valued.v (semiLocalHomeomorph K L v x w)) (Ring.mul_inverse_cancel a hu)
    simp only [semiLocalHomeomorph_mul, semiLocalHomeomorph_one, Pi.mul_apply, Pi.one_apply, map_mul, map_one,
      hva w, one_mul] at h
    exact h.le

private theorem exists_mem_semiLocalIntegralSet_coe_eq
    {μ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)} (hμ : ∀ i j, μ i j ∈ rad K L v) :
    ∃ u ∈ semiLocalIntegralSet K L v, (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = 1 + μ := by
  have hO : ∀ i j, (1 + μ) i j ∈ semiLocalIntegers K L v := fun i j => by
    rw [Matrix.add_apply]
    refine add_mem_semiLocalIntegers K L v ?_ (rad_subset_semiLocalIntegers K L v (hμ i j))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem_semiLocalIntegers K L v
    · exact zero_mem_semiLocalIntegers K L v
  have hdet : (1 + μ).det = 1 + (μ 0 0 + μ 1 1 + (μ 0 0 * μ 1 1 - μ 0 1 * μ 1 0)) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add]
    ring
  have hε : μ 0 0 + μ 1 1 + (μ 0 0 * μ 1 1 - μ 0 1 * μ 1 0) ∈ rad K L v :=
    add_mem_rad K L v (add_mem_rad K L v (hμ 0 0) (hμ 1 1))
      (sub_mem_rad K L v (mul_mem_rad_left K L v (rad_subset_semiLocalIntegers K L v (hμ 0 0)) (hμ 1 1))
        (mul_mem_rad_left K L v (rad_subset_semiLocalIntegers K L v (hμ 0 1)) (hμ 1 0)))
  have hvdet : ∀ w : v.Extension (𝓞 L), Valued.v (semiLocalHomeomorph K L v (1 + μ).det w) = 1 := fun w => by
    rw [hdet, semiLocalHomeomorph_add, semiLocalHomeomorph_one, Pi.add_apply, Pi.one_apply]
    exact Valuation.map_one_add_of_lt _ ((mem_rad K L v _).1 hε w)
  have hdetU : IsUnit (1 + μ).det := by
    rw [hdet]
    exact isUnit_one_add K L v hε
  have hmU : IsUnit (1 + μ) := (Matrix.isUnit_iff_isUnit_det _).2 hdetU
  have hadj : ∀ i j, (1 + μ).adjugate i j ∈ semiLocalIntegers K L v := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · simpa using hO 1 1
    · simpa using neg_mem_semiLocalIntegers K L v (hO 0 1)
    · simpa using neg_mem_semiLocalIntegers K L v (hO 1 0)
    · simpa using hO 0 0
  refine ⟨hmU.unit, ⟨fun i j => ?_, fun i j => ?_⟩, hmU.unit_spec⟩
  · rw [hmU.unit_spec]
    exact hO i j
  · rw [Matrix.coe_units_inv, hmU.unit_spec, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem_semiLocalIntegers K L v (inverse_mem_semiLocalIntegers K L v hdetU hvdet) (hadj i j)

private def Cong (ν : L ⊗[K] v.adicCompletion K) (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) : Prop :=
  ∀ i j, ν * (m - 1) i j ∈ rad K L v

private theorem cong_iff (ν : L ⊗[K] v.adicCompletion K) (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Cong K L v ν m ↔ ∀ i j, ν * (m - 1) i j ∈ rad K L v := Iff.rfl

private theorem cong_one (ν : L ⊗[K] v.adicCompletion K) : Cong K L v ν 1 :=
  (cong_iff K L v ν 1).2 fun i j => by
    rw [sub_self, Matrix.zero_apply, mul_zero]
    exact zero_mem_rad K L v

private theorem cong_mul {ν : L ⊗[K] v.adicCompletion K} (hn : ∃ c ∈ semiLocalIntegers K L v, c * ν = 1)
    {a b : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)} (ha : Cong K L v ν a) (hb : Cong K L v ν b) :
    Cong K L v ν (a * b) := by
  obtain ⟨c, hc, hcν⟩ := hn
  refine (cong_iff K L v ν _).2 fun i j => ?_
  have key : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one]
    abel
  rw [key, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add]
  refine add_mem_rad K L v (add_mem_rad K L v ((cong_iff K L v ν a).1 ha i j) ((cong_iff K L v ν b).1 hb i j)) ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine sum_mem_rad K L v _ _ fun k _ => ?_
  have hb' : (b - 1) k j ∈ semiLocalIntegers K L v := by
    have e : (b - 1) k j = c * (ν * (b - 1) k j) := by rw [← mul_assoc, hcν, one_mul]
    rw [e]
    exact rad_subset_semiLocalIntegers K L v (mul_mem_rad_left K L v hc ((cong_iff K L v ν b).1 hb k j))
  rw [← mul_assoc]
  exact mul_mem_rad_right K L v ((cong_iff K L v ν a).1 ha i k) hb'

private theorem cong_sigmaPartialNorm {ν : L ⊗[K] v.adicCompletion K}
    (hn : ∃ c ∈ semiLocalIntegers K L v, c * ν = 1)
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (w : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (N : ℕ)
    (hw : ∀ j < N, Cong K L v ν (((⇑Φ)^[j] w : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) :
    ∀ i ≤ N, Cong K L v ν ((LT.TwistedNorm.sigmaPartialNorm Φ w i : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [LT.TwistedNorm.sigmaPartialNorm_zero, Units.val_one]
    exact cong_one K L v ν
  | succ i ih =>
    intro hi
    rw [LT.TwistedNorm.sigmaPartialNorm_succ, Units.val_mul]
    exact cong_mul K L v hn (ih (Nat.le_of_succ_le hi)) (hw i (Nat.lt_of_succ_le hi))

private theorem isOpen_setOf_valued_lt_one (w : v.Extension (𝓞 L)) :
    IsOpen {x : w.1.adicCompletion L | Valued.v x < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  have hy' : Valued.v (y - x) < 1 := (Valuation.restrict_lt_one_iff _).1 hy
  rw [Set.mem_setOf_eq] at hx ⊢
  rw [← sub_add_cancel y x]
  exact Valuation.map_add_lt _ hy' hx

private theorem isOpen_rad : IsOpen (rad K L v) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  have h : rad K L v = ⋂ w : v.Extension (𝓞 L),
      (fun a => semiLocalHomeomorph K L v a w) ⁻¹' {x : w.1.adicCompletion L | Valued.v x < 1} := by
    ext a
    simp only [mem_rad, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
  rw [h]
  exact isOpen_iInter_of_finite fun w =>
    (isOpen_setOf_valued_lt_one K L v w).preimage ((continuous_apply w).comp (semiLocalHomeomorph K L v).continuous)

private theorem isOpen_setOf_cong (ν : L ⊗[K] v.adicCompletion K) :
    IsOpen {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
      Cong K L v ν (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))} := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  have h : {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
      Cong K L v ν (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))} =
      ⋂ i : Fin 2, ⋂ j : Fin 2, (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ν * ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) - 1) i j) ⁻¹' rad K L v := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, cong_iff]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (isOpen_rad K L v).preimage ?_
  exact continuous_const.mul ((Units.continuous_val.sub continuous_const).matrix_elem i j)

private theorem isUnit_natCast_finrank :
    IsUnit ((Module.finrank K L : ℕ) : L ⊗[K] v.adicCompletion K) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hK : ((Module.finrank K L : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h := (isUnit_iff_ne_zero.2 hK).map (algebraMap K (L ⊗[K] v.adicCompletion K))
  rwa [map_natCast] at h

private theorem isOpen_setOf_forall_cong_iterate (ν : L ⊗[K] v.adicCompletion K)
    {Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hΦc : Continuous Φ) (n : ℕ) :
    IsOpen {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) | ∀ j < n, Cong K L v ν
      (((⇑Φ)^[j] g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))} := by
  have h : {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) | ∀ j < n, Cong K L v ν
        (((⇑Φ)^[j] g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))} =
      ⋂ j ∈ Finset.range n, (fun g => (⇑Φ)^[j] g) ⁻¹'
        {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
          Cong K L v ν (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
  rw [h]
  exact isOpen_biInter_finset fun j _ => (isOpen_setOf_cong K L v ν).preimage (hΦc.iterate j)

private theorem scalar_mul_sum_sub_one_apply_mem_rad {ν : L ⊗[K] v.adicCompletion K} {n : ℕ}
    (P : ℕ → GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu : ∀ k ≤ n, Cong K L v ν ((P k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) (i j : Fin 2) :
    (Matrix.scalar (Fin 2) ν * ∑ k ∈ Finset.range n,
      (((P k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) - 1))
        i j ∈ rad K L v := by
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.sum_apply, Finset.mul_sum]
  exact sum_mem_rad K L v _ _ fun k hk => (cong_iff K L v ν _).1 (hu k (Finset.mem_range.1 hk).le) i j

end Radical

section Averaging

open AutomorphicForm
open scoped Pointwise

private theorem exists_mem_nhds_forall_mem_centralizer_exists_eq_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    ∃ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ z ∈ Subgroup.centralizer
          ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} :
            Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
        z⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹ ∈ V →
          ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
            ∃ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, z = t * u := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  have hσn : ∀ z : L ⊗[K] v.adicCompletion K,
      (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[Module.finrank K L] z = z :=
    fun z => iterate_sigmaTensor_finrank σ z

  obtain ⟨ν, hnν⟩ := (isUnit_natCast_finrank K L v).exists_right_inv
  have hn : ∃ c ∈ semiLocalIntegers K L v, c * ν = 1 :=
    ⟨_, natCast_mem_semiLocalIntegers K L v (Module.finrank K L), hnν⟩

  have hΦc : Continuous (phi σ δ) := by
    have hc : Continuous fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        δ * sigmaGL K L (v.adicCompletion K) σ g * δ⁻¹ :=
      (continuous_const.mul (continuous_sigmaGL σ (v := v))).mul continuous_const
    exact hc.congr fun g => (phi_apply σ δ g).symm

  refine ⟨{g | ∀ j < Module.finrank K L, Cong K L v ν
      (((⇑(phi σ δ))^[j] g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))}, ?_, fun z hz hzV => ?_⟩
  · refine (isOpen_setOf_forall_cong_iterate K L v ν hΦc _).mem_nhds fun j _ => ?_
    rw [Function.iterate_fixed (map_one (phi σ δ)) j, Units.val_one]
    exact cong_one K L v ν
  ·
    rw [Set.mem_setOf_eq, twistedDisplacement_eq] at hzV
    have hu := cong_sigmaPartialNorm K L v hn (phi σ δ) (z⁻¹ * phi σ δ z) (Module.finrank K L) hzV

    obtain ⟨u', hu'U, hu'⟩ := exists_mem_semiLocalIntegralSet_coe_eq K L v
      (scalar_mul_sum_sub_one_apply_mem_rad K L v
        (LT.TwistedNorm.sigmaPartialNorm (phi σ δ) (z⁻¹ * phi σ δ z)) hu)

    have hΦt := @map_mul_eq_self_of_iterate_eq (L ⊗[K] v.adicCompletion K) inferInstance (phi σ δ) (phiM σ δ)
      (phiM_coe σ δ) _ _ hnν _ (phi_iterate_finrank_of_mem σ hσn δ hz)
      (LT.TwistedNorm.sigmaPartialNorm (phi σ δ) (z⁻¹ * phi σ δ z)) (iterate_eq_mul_sigmaPartialNorm (phi σ δ) z)
      _ rfl _ hu'
    refine ⟨z * u', (mem_twistedCentralizer_iff_phi σ).2 hΦt, u'⁻¹, inv_mem_integralUnitsSet _ hu'U, ?_⟩
    rw [mul_inv_cancel_right]

private theorem exists_finset_forall_mem_centralizer_exists_eq_mul_of_isCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (D : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hD : IsCompact D) :
    ∃ R : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ z ∈ Subgroup.centralizer
          ({AutomorphicForm.normString K L (v.adicCompletion K) σ δ} :
            Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
        z⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹ ∈ D →
          ∃ r ∈ R, ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
            ∃ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, z = t * r * u := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  have hσn : ∀ z : L ⊗[K] v.adicCompletion K,
      (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[Module.finrank K L] z = z :=
    fun z => iterate_sigmaTensor_finrank σ z

  have hcomm : ∀ a ∈ Subgroup.centralizer ({normString K L (v.adicCompletion K) σ δ} :
        Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
      ∀ b ∈ Subgroup.centralizer ({normString K L (v.adicCompletion K) σ δ} :
        Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))), Commute a b :=
    fun a ha b hb => congrArg Subtype.val (mul_comm_of_mem_centralizer hδ ⟨a, ha⟩ ⟨b, hb⟩)

  obtain ⟨V, hV, hVP⟩ := exists_mem_nhds_forall_mem_centralizer_exists_eq_mul K L v σ δ
  obtain ⟨V₂, hV₂, hV₂V⟩ := exists_nhds_split_inv hV
  obtain ⟨O, hOV₂, hOo, hO1⟩ := mem_nhds_iff.1 (inv_mem_nhds_one _ hV₂)

  have hcov : D ⊆ ⋃ d : GL (Fin 2) (L ⊗[K] v.adicCompletion K), (fun x => d⁻¹ * x) ⁻¹' O := fun d _ =>
    Set.mem_iUnion.2 ⟨d, show d⁻¹ * d ∈ O by rwa [inv_mul_cancel]⟩
  obtain ⟨I, hI⟩ := hD.elim_finite_subcover (fun d : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
    (fun x => d⁻¹ * x) ⁻¹' O) (fun d => hOo.preimage (continuous_const_mul d⁻¹)) hcov

  obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      ∀ d, (∃ a ∈ Subgroup.centralizer ({normString K L (v.adicCompletion K) σ δ} :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))), d⁻¹ * (a⁻¹ * phi σ δ a) ∈ O) →
        r d ∈ Subgroup.centralizer ({normString K L (v.adicCompletion K) σ δ} :
          Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) ∧ d⁻¹ * ((r d)⁻¹ * phi σ δ (r d)) ∈ O := by
    refine ⟨fun d => if h : ∃ a ∈ Subgroup.centralizer ({normString K L (v.adicCompletion K) σ δ} :
        Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))), d⁻¹ * (a⁻¹ * phi σ δ a) ∈ O then h.choose else 1,
      fun d h => ?_⟩
    simp only [dif_pos h]
    exact h.choose_spec
  refine ⟨I.image r, fun z hz hzD => ?_⟩
  rw [twistedDisplacement_eq] at hzD
  obtain ⟨d, hdI, hd⟩ : ∃ d ∈ I, d⁻¹ * (z⁻¹ * phi σ δ z) ∈ O := by
    have h := hI hzD
    rw [Set.mem_iUnion₂] at h
    obtain ⟨d, hdI, hd⟩ := h
    exact ⟨d, hdI, hd⟩
  obtain ⟨ha, hda⟩ := hr d ⟨z, hz, hd⟩

  have hβ : (((r d)⁻¹ * z)⁻¹ * phi σ δ ((r d)⁻¹ * z)) ∈ V := by
    have key := hV₂V _ (Set.mem_inv.1 (hOV₂ hda)) _ (Set.mem_inv.1 (hOV₂ hd))
    rw [div_eq_mul_inv] at key
    have e : (d⁻¹ * ((r d)⁻¹ * phi σ δ (r d)))⁻¹ * (d⁻¹ * (z⁻¹ * phi σ δ z))⁻¹⁻¹ =
        ((r d)⁻¹ * phi σ δ (r d))⁻¹ * (z⁻¹ * phi σ δ z) := by group
    rw [e, ← inv_mul_mul_inv_mul_eq (phi σ δ z) (hcomm _ ha _ hz)
      (hcomm _ hz _ (phi_mem_centralizer σ hσn δ ha)) (hcomm _ ha _ (phi_mem_centralizer σ hσn δ ha)),
      ← map_inv, ← map_mul] at key
    exact key
  rw [← twistedDisplacement_eq] at hβ
  obtain ⟨t, ht, u, hu, htu⟩ := hVP ((r d)⁻¹ * z) (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hz) hβ
  refine ⟨r d, Finset.mem_image_of_mem r hdI, t, ht, u, hu, ?_⟩
  have hat : r d * t = t * r d := (hcomm _ ha _ (mem_centralizer_of_mem_twistedCentralizer σ hσn ht)).eq
  calc z = r d * ((r d)⁻¹ * z) := by rw [mul_inv_cancel_left]
    _ = r d * (t * u) := by rw [htu]
    _ = t * r d * u := by rw [← mul_assoc, hat]

end Averaging

private theorem exists_finset_forall_exists_inv_mul_mem {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] {U C : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) (hC : IsCompact C) :
    ∃ F : Finset G, ∀ g ∈ C, ∃ c ∈ F, c⁻¹ * g ∈ U := by
  have hcov : C ⊆ ⋃ c : G, (fun g => c⁻¹ * g) ⁻¹' U := fun g _ =>
    Set.mem_iUnion.2 ⟨g, show g⁻¹ * g ∈ U by rwa [inv_mul_cancel]⟩
  obtain ⟨F, hF⟩ := hC.elim_finite_subcover (fun c : G => (fun g => c⁻¹ * g) ⁻¹' U)
    (fun c => hU.preimage (continuous_const_mul c⁻¹)) hcov
  refine ⟨F, fun g hg => ?_⟩
  have h := hF hg
  rw [Set.mem_iUnion₂] at h
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, h⟩

section Places

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

private noncomputable def glEquiv :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) ≃* Π w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L) :=
  (Units.mapEquiv
    (((HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L)
      v).toAlgEquiv.toRingEquiv.mapMatrix.trans Matrix.piRingEquiv).toMulEquiv)).trans MulEquiv.piUnits

private noncomputable def atPlace (w : v.Extension (𝓞 L)) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L) :=
  (Pi.evalMonoidHom (fun w : v.Extension (𝓞 L) => GL (Fin 2) (w.1.adicCompletion L)) w).comp
    (glEquiv K L v).toMonoidHom

private theorem atPlace_apply (w : v.Extension (𝓞 L)) (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    atPlace K L v w g = glEquiv K L v g w := rfl

private theorem atPlace_apply_coe (w : v.Extension (𝓞 L)) (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (i j : Fin 2) :
    (atPlace K L v w g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j =
      semiLocalHomeomorph K L v ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j) w := rfl

private theorem atPlace_symm_apply (w : v.Extension (𝓞 L))
    (c : Π w : v.Extension (𝓞 L), GL (Fin 2) (w.1.adicCompletion L)) :
    atPlace K L v w ((glEquiv K L v).symm c) = c w := by
  rw [atPlace_apply, MulEquiv.apply_symm_apply]

private theorem eq_of_forall_atPlace_eq {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hgh : ∀ w, atPlace K L v w g = atPlace K L v w h) : g = h :=
  (glEquiv K L v).injective (funext hgh)

private theorem continuous_atPlace (w : v.Extension (𝓞 L)) : Continuous (atPlace K L v w) := by
  rw [Units.continuous_iff]
  have hρ : Continuous fun a : L ⊗[K] v.adicCompletion K => semiLocalHomeomorph K L v a w :=
    (continuous_apply w).comp (semiLocalHomeomorph K L v).continuous
  constructor
  · show Continuous fun g => (atPlace K L v w g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))
    refine continuous_matrix fun i j => ?_
    simp only [atPlace_apply_coe]
    exact hρ.comp (Units.continuous_val.matrix_elem i j)
  · simp_rw [← map_inv]
    refine continuous_matrix fun i j => ?_
    simp only [atPlace_apply_coe]
    exact hρ.comp (Units.continuous_coe_inv.matrix_elem i j)

private theorem isRegularSemisimple_atPlace (w : v.Extension (𝓞 L)) {γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hγ : IsRegularSemisimple γ) : IsRegularSemisimple (atPlace K L v w γ) := by
  have h := hγ.map ((Pi.evalRingHom (fun w : v.Extension (𝓞 L) => w.1.adicCompletion L) w).comp
    ((HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).toAlgEquiv.toRingEquiv.toRingHom))
  rw [map_sub, map_pow, map_mul, map_ofNat, Matrix.trace_fin_two, map_add, RingHom.map_det] at h
  rw [isRegularSemisimple_iff, Matrix.trace_fin_two]
  exact h

private theorem mem_semiLocalIntegralSet_iff_atPlace (u : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    u ∈ semiLocalIntegralSet K L v ↔ ∀ w, atPlace K L v w u ∈ localIntegralSet L w.1 := by
  have hO : ∀ a : L ⊗[K] v.adicCompletion K, a ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), semiLocalHomeomorph K L v a w ∈ w.1.adicCompletionIntegers L := fun a => by
    rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
    simp only [SetLike.mem_coe]
  constructor
  · rintro ⟨h₁, h₂⟩ w
    refine (mem_localIntegralSet L w.1).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [atPlace_apply_coe]
      exact (hO _).1 (h₁ i j) w
    · rw [← map_inv, atPlace_apply_coe]
      exact (hO _).1 (h₂ i j) w
  · intro h
    refine ⟨fun i j => (hO _).2 fun w => ?_, fun i j => (hO _).2 fun w => ?_⟩
    · rw [← atPlace_apply_coe]
      exact ((mem_localIntegralSet L w.1).1 (h w)).1 i j
    · rw [← atPlace_apply_coe, map_inv]
      exact ((mem_localIntegralSet L w.1).1 (h w)).2 i j

private theorem mem_centralizer_of_forall_atPlace {γ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (h : ∀ w, atPlace K L v w t ∈
      Subgroup.centralizer ({atPlace K L v w γ} : Set (GL (Fin 2) (w.1.adicCompletion L)))) :
    t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  refine eq_of_forall_atPlace_eq K L v fun w => ?_
  rw [map_mul, map_mul]
  exact (Subgroup.mem_centralizer_iff.1 (h w)) _ rfl

private theorem exists_finset_forall_exists_mem_centralizer_eq_mul_of_isCompact
    (γ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hγ : IsRegularSemisimple γ)
    (C : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (hC : IsCompact C) :
    ∃ P : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K), x⁻¹ * γ * x ∈ C →
        ∃ p ∈ P, ∃ z ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
          ∃ u ∈ semiLocalIntegralSet K L v, x = z * p * u := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI := Fintype.ofFinite (v.Extension (𝓞 L))

  have hw : ∀ w : v.Extension (𝓞 L), ∃ S : Finset (GL (Fin 2) (w.1.adicCompletion L)),
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K), x⁻¹ * γ * x ∈ C →
        ∃ s ∈ S, ∃ t ∈ Subgroup.centralizer ({atPlace K L v w γ} : Set (GL (Fin 2) (w.1.adicCompletion L))),
          ∃ u ∈ localIntegralSet L w.1, atPlace K L v w x = t * s * u := by
    intro w
    obtain ⟨F, hF⟩ := exists_finset_forall_exists_inv_mul_mem (isOpen_localIntegralSet L w.1)
      (one_mem_localIntegralSet L w.1) (hC.image (continuous_atPlace K L v w))
    obtain ⟨S, -, hS⟩ := AutomorphicForm.exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple L w.1
      (atPlace K L v w γ) (isRegularSemisimple_atPlace K L v w hγ)
      (fun g => if g ∈ atPlace K L v w '' C then 1 else 0)
      ⟨F, fun g hg => hF g (by
        by_contra h'
        exact hg (if_neg h'))⟩
    refine ⟨S, fun x hx => hS (atPlace K L v w x) ?_⟩
    have hmem : (atPlace K L v w x)⁻¹ * atPlace K L v w γ * atPlace K L v w x ∈ atPlace K L v w '' C :=
      ⟨x⁻¹ * γ * x, hx, by rw [map_mul, map_mul, map_inv]⟩
    show (if (atPlace K L v w x)⁻¹ * atPlace K L v w γ * atPlace K L v w x ∈ atPlace K L v w '' C
      then (1 : ℂ) else 0) ≠ 0
    rw [if_pos hmem]
    exact one_ne_zero
  choose S hS using hw
  refine ⟨(Fintype.piFinset S).image (glEquiv K L v).symm, fun x hx => ?_⟩
  choose s hs t ht u hu heq using fun w => hS w x hx
  refine ⟨(glEquiv K L v).symm s, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hs),
    (glEquiv K L v).symm t, mem_centralizer_of_forall_atPlace K L v fun w => ?_,
    (glEquiv K L v).symm u, (mem_semiLocalIntegralSet_iff_atPlace K L v _).2 fun w => ?_, ?_⟩
  · rw [atPlace_symm_apply]
    exact ht w
  · rw [atPlace_symm_apply]
    exact hu w
  · refine eq_of_forall_atPlace_eq K L v fun w => ?_
    rw [map_mul, map_mul, atPlace_symm_apply, atPlace_symm_apply, atPlace_symm_apply]
    exact heq w

end Places

section Extraction

variable {G : Type*} [Group G]

private theorem exists_finset_of_finset_forall_exists (T : Subgroup G) (U : Set G) (hU1 : (1 : G) ∈ U)
    (hUmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) (P : G → Prop) (S₀ : Finset G)
    (hcov₀ : ∀ x : G, P x → ∃ s ∈ S₀, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u) :
    ∃ S : Finset G,
      (∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ T, ∀ u ∈ U, s' = t * s * u → s' = s) ∧
      ∀ x : G, P x → ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, x = t * s * u := by
  classical
  set C : Finset (Finset G) :=
    S₀.powerset.filter (fun S => ∀ s₀ ∈ S₀, ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, s₀ = t * s * u) with hC
  have hS₀C : S₀ ∈ C := by
    rw [hC, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl S₀, fun s₀ hs₀ => ⟨s₀, hs₀, 1, T.one_mem, 1, hU1, by simp⟩⟩
  obtain ⟨S, hSC, hSmin⟩ := C.exists_min_image Finset.card ⟨S₀, hS₀C⟩
  rw [hC, Finset.mem_filter, Finset.mem_powerset] at hSC
  obtain ⟨hSsub, hScov⟩ := hSC
  refine ⟨S, ?_, ?_⟩
  · intro s hs s' hs' t ht u hu hs'eq
    by_contra hne
    have hmem : S.erase s' ∈ C := by
      rw [hC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.Subset.trans (Finset.erase_subset s' S) hSsub, fun s₀ hs₀ => ?_⟩
      obtain ⟨s₁, hs₁, t₁, ht₁, u₁, hu₁, hs₀eq⟩ := hScov s₀ hs₀
      by_cases h₁ : s₁ = s'
      · rw [h₁] at hs₀eq
        refine ⟨s, Finset.mem_erase.2 ⟨fun h => hne h.symm, hs⟩, t₁ * t, T.mul_mem ht₁ ht,
          u * u₁, hUmul u hu u₁ hu₁, ?_⟩
        rw [hs₀eq, hs'eq]
        simp only [mul_assoc]
      · exact ⟨s₁, Finset.mem_erase.2 ⟨h₁, hs₁⟩, t₁, ht₁, u₁, hu₁, hs₀eq⟩
    exact absurd (hSmin _ hmem) (not_le.2 (Finset.card_erase_lt_of_mem hs'))
  · intro x hx
    obtain ⟨s₀, hs₀, t, ht, u, hu, hxeq⟩ := hcov₀ x hx
    obtain ⟨s, hs, t', ht', u', hu', hs₀eq⟩ := hScov s₀ hs₀
    refine ⟨s, hs, t * t', T.mul_mem ht ht', u' * u, hUmul u' hu' u hu, ?_⟩
    rw [hxeq, hs₀eq]
    simp only [mul_assoc]

end Extraction

section Covering

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

open AutomorphicForm

private theorem mul_mem_semiLocalIntegralSet {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) (hh : h ∈ semiLocalIntegralSet K L v) :
    g * h ∈ semiLocalIntegralSet K L v := by
  have key : ∀ m n : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K),
      (∀ i j, m i j ∈ semiLocalIntegers K L v) → (∀ i j, n i j ∈ semiLocalIntegers K L v) →
        ∀ i j, (m * n) i j ∈ semiLocalIntegers K L v := fun m n hm hn i j => by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_semiLocalIntegers K L v (mul_mem_semiLocalIntegers K L v (hm i 0) (hn 0 j))
      (mul_mem_semiLocalIntegers K L v (hm i 1) (hn 1 j))
  obtain ⟨hg₁, hg₂⟩ := hg
  obtain ⟨hh₁, hh₂⟩ := hh
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul]
    exact key _ _ hg₁ hh₁ i j
  · rw [mul_inv_rev, Units.val_mul]
    exact key _ _ hh₂ hg₂ i j

private theorem continuous_sigmaPartialNorm (σ : L ≃ₐ[K] L) (r : ℕ) :
    Continuous fun y : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      LT.TwistedNorm.sigmaPartialNorm (sigmaGL K L (v.adicCompletion K) σ) y r := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  induction r with
  | zero =>
    simp only [LT.TwistedNorm.sigmaPartialNorm_zero]
    exact continuous_const
  | succ r ih =>
    simp only [LT.TwistedNorm.sigmaPartialNorm_succ']
    exact continuous_id.mul ((continuous_sigmaGL σ (v := v)).comp ih)

end Covering

end TwistedSupport

open AutomorphicForm in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (v.adicCompletion K) σ δ))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφs : ∃ F₀ : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K), φ g ≠ 0 →
        ∃ c ∈ F₀, c⁻¹ * g ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    ∃ S : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
     (
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
          ∀ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, s' = t * s * u → s' = s
     ) ∧
     (
      ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
          ∃ s ∈ S,
            ∃ t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ,
              ∃ u ∈ AutomorphicForm.semiLocalIntegralSet K L v, x = t * s * u
     ) := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  have hσn : ∀ z : L ⊗[K] v.adicCompletion K,
      (⇑(sigmaTensor K L (v.adicCompletion K) σ))^[Module.finrank K L] z = z :=
    fun z => TwistedSupport.iterate_sigmaTensor_finrank σ z
  have hU1 := one_mem_semiLocalIntegralSet K L v
  have hUc := isCompact_semiLocalIntegralSet K L v
  have hUo := isOpen_semiLocalIntegralSet K L v
  obtain ⟨F₀, hF₀⟩ := hφs

  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      C₀ = ⋃ c ∈ F₀, (fun u => c * u) '' semiLocalIntegralSet K L v := ⟨_, rfl⟩
  have hC₀c : IsCompact C₀ := by
    rw [hC₀]
    exact F₀.isCompact_biUnion fun c _ => hUc.image (continuous_const_mul c)
  have hφC₀ : ∀ g, φ g ≠ 0 → g ∈ C₀ := fun g hg => by
    obtain ⟨c, hc, hcg⟩ := hF₀ g hg
    rw [hC₀, Set.mem_iUnion₂]
    exact ⟨c, hc, c⁻¹ * g, hcg, mul_inv_cancel_left c g⟩

  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      C₁ = (fun y => LT.TwistedNorm.sigmaNormPow (sigmaGL K L (v.adicCompletion K) σ) (Module.finrank K L) y) ''
        C₀ := ⟨_, rfl⟩
  have hC₁c : IsCompact C₁ := by
    rw [hC₁]
    refine hC₀c.image ?_
    simp only [LT.TwistedNorm.sigmaNormPow_def]
    exact TwistedSupport.continuous_sigmaPartialNorm K L v σ (Module.finrank K L)
  have hxC₁ : ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0 →
        x⁻¹ * normString K L (v.adicCompletion K) σ δ * x ∈ C₁ := fun x hx => by
    rw [hC₁]
    refine ⟨x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x, hφC₀ _ hx, ?_⟩
    show LT.TwistedNorm.sigmaNormPow (sigmaGL K L (v.adicCompletion K) σ) (Module.finrank K L)
        (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) = x⁻¹ * normString K L (v.adicCompletion K) σ δ * x
    rw [LT.TwistedNorm.sigmaNormPow_sigmaConjElt _ _ (TwistedSupport.iterate_sigmaGL_eq_self σ hσn x),
      TwistedSupport.normString_eq_sigmaNormPow]

  obtain ⟨P, hP⟩ := TwistedSupport.exists_finset_forall_exists_mem_centralizer_eq_mul_of_isCompact K L v
    (normString K L (v.adicCompletion K) σ δ) hδ C₁ hC₁c

  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      D = fun p => (fun q : GL (Fin 2) (L ⊗[K] v.adicCompletion K) × GL (Fin 2) (L ⊗[K] v.adicCompletion K) ×
          GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        p * q.1 * q.2.1 * (sigmaGL K L (v.adicCompletion K) σ q.2.2)⁻¹ *
          (sigmaGL K L (v.adicCompletion K) σ p)⁻¹ * δ⁻¹) ''
        (semiLocalIntegralSet K L v ×ˢ C₀ ×ˢ semiLocalIntegralSet K L v) := ⟨_, rfl⟩
  have hDc : ∀ p, IsCompact (D p) := fun p => by
    rw [hDdef]
    exact (hUc.prod (hC₀c.prod hUc)).image
      ((((continuous_const.mul continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
        ((TwistedSupport.continuous_sigmaGL σ (v := v)).comp (continuous_snd.comp continuous_snd)).inv).mul
          continuous_const |>.mul continuous_const)
  have hR : ∀ p, ∃ R : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ z ∈ Subgroup.centralizer
          ({normString K L (v.adicCompletion K) σ δ} : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))),
        z⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹ ∈ D p →
          ∃ r ∈ R, ∃ t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ,
            ∃ u ∈ semiLocalIntegralSet K L v, z = t * r * u :=
    fun p => TwistedSupport.exists_finset_forall_mem_centralizer_exists_eq_mul_of_isCompact K L v σ δ hδ _ (hDc p)
  choose R hR using hR

  have hQ : ∀ p : GL (Fin 2) (L ⊗[K] v.adicCompletion K), ∃ Q : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g ∈ (fun q : GL (Fin 2) (L ⊗[K] v.adicCompletion K) × GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          q.1 * p * q.2) '' (semiLocalIntegralSet K L v ×ˢ semiLocalIntegralSet K L v),
        ∃ c ∈ Q, c⁻¹ * g ∈ semiLocalIntegralSet K L v :=
    fun p => TwistedSupport.exists_finset_forall_exists_inv_mul_mem hUo hU1
      ((hUc.prod hUc).image ((continuous_fst.mul continuous_const).mul continuous_snd))
  choose Q hQ using hQ

  refine TwistedSupport.exists_finset_of_finset_forall_exists (twistedCentralizer K L (v.adicCompletion K) σ δ)
    (semiLocalIntegralSet K L v) hU1 (fun a ha b hb => TwistedSupport.mul_mem_semiLocalIntegralSet K L v ha hb)
    (fun x => φ (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) ≠ 0)
    (P.biUnion fun p => (R p ×ˢ Q p).image fun rq => rq.1 * rq.2) fun x hx => ?_
  obtain ⟨p, hp, z, hz, u₀, hu₀, hxeq⟩ := hP x (hxC₁ x hx)
  have hβ : z⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹ ∈ D p := by
    rw [hDdef]
    refine ⟨(u₀, x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x, u₀), ⟨hu₀, hφC₀ _ hx, hu₀⟩, ?_⟩
    show p * u₀ * (x⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ x) * (sigmaGL K L (v.adicCompletion K) σ u₀)⁻¹ *
        (sigmaGL K L (v.adicCompletion K) σ p)⁻¹ * δ⁻¹ = z⁻¹ * δ * sigmaGL K L (v.adicCompletion K) σ z * δ⁻¹
    rw [hxeq, map_mul, map_mul]
    group
  obtain ⟨r, hr, t, ht, u₁, hu₁, hzeq⟩ := hR p z hz hβ
  obtain ⟨q, hq, hqU⟩ := hQ p (u₁ * p * u₀) ⟨(u₁, u₀), ⟨hu₁, hu₀⟩, rfl⟩
  refine ⟨r * q, ?_, t, ht, q⁻¹ * (u₁ * p * u₀), hqU, ?_⟩
  · rw [Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_image.2 ⟨(r, q), Finset.mem_product.2 ⟨hr, hq⟩, rfl⟩⟩
  · rw [hxeq, hzeq]
    group

end S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_eq_and_forall_exists_of_isRegularSemisimple_normString (solution)
