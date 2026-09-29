-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b2f38540-de54-5493-a0f8-162d90f889b2

import Theorems.Thm_AutomorphicForm_exists_isSectionFnOn_adeleRing_of_isRegularSemisimple
import Theorems.Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace NumberField
open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace P2mTwistedSectionAdelic

section Algebra

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
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

theorem isRegularSemisimple_map {B : Type*} [CommRing B] (f : A →+* B) {γ : GL (Fin 2) A}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map (n := Fin 2) f γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  have hval : ((Matrix.GeneralLinearGroup.map (n := Fin 2) f γ : GL (Fin 2) B) :
      Matrix (Fin 2) (Fin 2) B) = f.mapMatrix (γ : Matrix (Fin 2) (Fin 2) A) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have h := hγ.map f
  rwa [map_sub, map_pow, map_mul, map_ofNat] at h

end Algebra

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

theorem sigmaTensor_iterate (k : ℕ) (y : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[k] y =
      Algebra.TensorProduct.map (σ ^ k).toAlgHom (AlgHom.id K A) y := by
  induction k generalizing y with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul, pow_succ',
            AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem sigmaGL_iterate_finrank (hσ : σ ^ Module.finrank K L = 1) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[Module.finrank K L] x = x := by
  have hentry : ∀ (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      ((AutomorphicForm.sigmaGL K L A σ)^[k] x) i j =
        (AutomorphicForm.sigmaTensor K L A σ)^[k] (x i j) := by
    intro k
    induction k with
    | zero => intro x i j; rfl
    | succ k ih =>
        intro x i j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', AutomorphicForm.sigmaGL,
          Matrix.GeneralLinearGroup.map_apply, ← AutomorphicForm.sigmaGL, ih]
  apply Units.ext
  ext i j
  rw [hentry, sigmaTensor_iterate, hσ]
  induction (x i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem sigmaGL_iterate_mul (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] (x * y) =
      (AutomorphicForm.sigmaGL K L A σ)^[k] x * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem sigmaGL_iterate_inv (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) :
    (AutomorphicForm.sigmaGL K L A σ)^[k] x⁻¹ = ((AutomorphicForm.sigmaGL K L A σ)^[k] x)⁻¹ := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_inv]

theorem twistedCentralizer_le_centralizer_normString (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  set s := AutomorphicForm.sigmaGL K L A σ with hs
  have htδ : t * δ = δ * s t := by
    have h := (AutomorphicForm.mem_sigmaCentralizer_iff).1 ht
    rw [← hs] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hmul : ∀ (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)), s^[k] (x * y) = s^[k] x * s^[k] y :=
    fun k x y => sigmaGL_iterate_mul K L A σ k x y
  have hP : ∀ k : ℕ, t * ((List.range k).map fun i => s^[i] δ).prod =
      ((List.range k).map fun i => s^[i] δ).prod * s^[k] t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton, ← mul_assoc, ih, mul_assoc, mul_assoc]
        congr 1
        have h1 : s^[k] t * s^[k] δ = s^[k] (t * δ) := (hmul k t δ).symm
        rw [h1, htδ, hmul, ← Function.iterate_succ_apply s k t]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hP (Module.finrank K L)
  rw [sigmaGL_iterate_finrank K L A σ hσ] at h
  exact h

def pnorm (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range k).map fun i => (AutomorphicForm.sigmaGL K L A σ)^[i] y).prod

theorem pnorm_zero (y : GL (Fin 2) (L ⊗[K] A)) : pnorm K L A σ 0 y = 1 := by
  simp [pnorm]

theorem pnorm_succ (k : ℕ) (y : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ (k + 1) y = pnorm K L A σ k y * (AutomorphicForm.sigmaGL K L A σ)^[k] y := by
  simp [pnorm, List.range_succ, List.map_append, List.prod_append]

theorem normString_eq_pnorm (y : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ y = pnorm K L A σ (Module.finrank K L) y := rfl

theorem pnorm_twistedConj (k : ℕ) (δ x : GL (Fin 2) (L ⊗[K] A)) :
    pnorm K L A σ k (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) =
      x⁻¹ * pnorm K L A σ k δ * (AutomorphicForm.sigmaGL K L A σ)^[k] x := by
  induction k with
  | zero => simp [pnorm_zero]
  | succ k ih =>
      rw [pnorm_succ, ih, pnorm_succ, sigmaGL_iterate_mul, sigmaGL_iterate_mul, sigmaGL_iterate_inv,
        Function.iterate_succ_apply]
      group

theorem normString_twistedConj (hσ : σ ^ Module.finrank K L = 1) (δ x : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) =
      x⁻¹ * AutomorphicForm.normString K L A σ δ * x := by
  rw [normString_eq_pnorm, normString_eq_pnorm, pnorm_twistedConj, sigmaGL_iterate_finrank K L A σ hσ]

theorem pow_finrank_eq_one [FiniteDimensional K L] : σ ^ Module.finrank K L = 1 := by
  have h1 : orderOf σ ∣ Nat.card (L ≃ₐ[K] L) := orderOf_dvd_natCard σ
  have h2 : Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
    have h := IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (L ≃ₐ[K] L))
    rw [Subgroup.card_top] at h
    have := Module.finrank_mul_finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
    rw [h] at this
    exact Dvd.intro_left _ this
  exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans h2)

end Twist

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem secondCountableTopology_tensor [SecondCountableTopology A] :
    SecondCountableTopology (L ⊗[K] A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  let ι := Module.Free.ChooseBasisIndex A (L ⊗[K] A)
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A (L ⊗[K] A)
  let b : Module.Basis ι A (L ⊗[K] A) := Module.Free.chooseBasis A (L ⊗[K] A)
  let e : (L ⊗[K] A) ≃ₗ[A] (ι → A) := b.equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let eh : (L ⊗[K] A) ≃ₜ (ι → A) :=
    { toEquiv := e.toEquiv, continuous_toFun := h1, continuous_invFun := h2 }
  exact eh.isInducing.secondCountableTopology

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem continuous_sigmaGL_iterate (σ : L ≃ₐ[K] L) (k : ℕ) :
    Continuous ((AutomorphicForm.sigmaGL K L A σ)^[k]) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
      have h : ((AutomorphicForm.sigmaGL K L A σ)^[k + 1]) =
          (AutomorphicForm.sigmaGL K L A σ) ∘ ((AutomorphicForm.sigmaGL K L A σ)^[k]) :=
        Function.iterate_succ' _ _
      rw [h]
      exact (continuous_sigmaGL K L A σ).comp ih

theorem continuous_pnorm (σ : L ≃ₐ[K] L) (k : ℕ) : Continuous (pnorm K L A σ k) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  induction k with
  | zero =>
      have h : pnorm K L A σ 0 = fun _ => 1 := funext fun y => pnorm_zero K L A σ y
      rw [h]
      exact continuous_const
  | succ k ih =>
      have h : pnorm K L A σ (k + 1) =
          fun y => pnorm K L A σ k y * (AutomorphicForm.sigmaGL K L A σ)^[k] y :=
        funext fun y => pnorm_succ K L A σ k y
      rw [h]
      exact ih.mul (continuous_sigmaGL_iterate K L A σ k)

theorem continuous_normString (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.normString K L A σ) := by
  have h : AutomorphicForm.normString K L A σ = pnorm K L A σ (Module.finrank K L) :=
    funext fun y => normString_eq_pnorm K L A σ y
  rw [h]
  exact continuous_pnorm K L A σ _

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

end TensorTopology

section Untwisted

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_isCompact_conj_mem_subset_centralizer_mul_adeleRing
    (γ : GL (Fin 2) (AdeleRing (𝓞 L) L)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 L) L))} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (AdeleRing (𝓞 L) L)), IsCompact D ∧
      {x : GL (Fin 2) (AdeleRing (𝓞 L) L) | x⁻¹ * γ * x ∈ C} ⊆
        (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L))) :
          Set (GL (Fin 2) (AdeleRing (𝓞 L) L))) * D := by
  letI : MeasurableSpace (GL (Fin 2) (AdeleRing (𝓞 L) L)) :=
    NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 L) L)) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L)))) :=
    AutomorphicForm.centralizerBorel (AdeleRing (𝓞 L) L) γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L)))) := ⟨rfl⟩
  haveI : T2Space (GL (Fin 2) (AdeleRing (𝓞 L) L)) := t2Space_GL _
  haveI : LocallyCompactSpace (GL (Fin 2) (AdeleRing (𝓞 L) L)) := locallyCompactSpace_GL _
  have hZc : IsClosed ((Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L)))) :
      Set (GL (Fin 2) (AdeleRing (𝓞 L) L))) := by
    change IsClosed (Set.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L))))
    exact Set.isClosed_centralizer _
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L)))) :=
    hZc.locallyCompactSpace
  set τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L)))) :=
    Measure.haar with hτ
  set f : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ := C.indicator fun _ => (1 : ℂ) with hf_def
  have hf : HasCompactSupport f :=
    HasCompactSupport.intro hC fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨w, -, -, hwc, hw1⟩ :=
    AutomorphicForm.exists_isSectionFnOn_adeleRing_of_isRegularSemisimple L γ hγ τ f hf
  refine ⟨tsupport w, hwc, ?_⟩
  intro x hx
  have hx : x⁻¹ * γ * x ∈ C := hx
  have h1 : f (x⁻¹ * γ * x) ≠ 0 := by
    rw [hf_def, Set.indicator_of_mem hx]
    exact one_ne_zero
  have h2 := hw1 x h1
  have h3 : ∃ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L))),
      w ((t : GL (Fin 2) (AdeleRing (𝓞 L) L)) * x) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L))),
        w ((t : GL (Fin 2) (AdeleRing (𝓞 L) L)) * x) ∂τ = 0 := by
      simp [h]
    rw [h0] at h2
    exact zero_ne_one h2
  obtain ⟨t, ht⟩ := h3
  refine Set.mem_mul.2 ⟨((t⁻¹ : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 L) L)))) :
      GL (Fin 2) (AdeleRing (𝓞 L) L)), (t⁻¹).2, (t : GL (Fin 2) (AdeleRing (𝓞 L) L)) * x,
      subset_tsupport _ ht, ?_⟩
  simp

theorem exists_isCompact_conj_mem_subset_centralizer_mul_baseChange
    (γ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) | x⁻¹ * γ * x ∈ C} ⊆
        (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D := by
  set Φ := AutomorphicForm.baseChangeGLEquiv K L with hΦ
  have hγ' : AutomorphicForm.IsRegularSemisimple (Φ γ) := by
    rw [hΦ, AutomorphicForm.baseChangeGLEquiv_apply]
    exact isRegularSemisimple_map _ hγ
  have hC' : IsCompact (Φ '' C) := hC.image Φ.continuous
  obtain ⟨D', hD', hsub⟩ :=
    exists_isCompact_conj_mem_subset_centralizer_mul_adeleRing L (Φ γ) hγ' hC'
  refine ⟨Φ.symm '' D', hD'.image Φ.symm.continuous, ?_⟩
  intro x hx
  have hx' : (Φ x)⁻¹ * Φ γ * Φ x ∈ Φ '' C := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Set.mem_image_of_mem _ hx
  obtain ⟨t', ht', d', hd', htd⟩ := Set.mem_mul.1 (hsub hx')
  refine Set.mem_mul.2 ⟨Φ.symm t', ?_, Φ.symm d', Set.mem_image_of_mem _ hd', ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at ht' ⊢
    apply Φ.injective
    simpa using ht'
  · apply Φ.injective
    simpa using htd

end Untwisted

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (σ : L ≃ₐ[K] L)

theorem exists_isCompact_twistedConj_mem_subset_twistedCentralizer_mul
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    {C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ :
          Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  set s := AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ with hs
  set N := AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ with hN
  have hσ : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one K L σ

  have hC₁ : IsCompact (N '' C) := hC.image (continuous_normString K L (AdeleRing (𝓞 K) K) σ)

  obtain ⟨D₁, hD₁, hsub₁⟩ :=
    exists_isCompact_conj_mem_subset_centralizer_mul_baseChange K L (N δ) hδ hC₁

  have hsD₁ : IsCompact (s '' D₁) := hD₁.image (continuous_sigmaGL K L (AdeleRing (𝓞 K) K) σ)
  have hC₂ : IsCompact (D₁ * C * (s '' D₁)⁻¹) := (hD₁.mul hC).mul hsD₁.inv
  obtain ⟨D₂, hD₂, hsub₂⟩ :=
    AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul
      K L σ hσ δ hδ (D₁ * C * (s '' D₁)⁻¹) hC₂
  refine ⟨D₂ * D₁, hD₂.mul hD₁, ?_⟩
  intro x hx
  have hx' : x⁻¹ * N δ * x ∈ N '' C := by
    have h := normString_twistedConj K L (AdeleRing (𝓞 K) K) σ hσ δ x
    rw [← hN, ← hs] at h
    rw [← h]
    exact Set.mem_image_of_mem _ hx
  obtain ⟨z, hz, d₁, hd₁, hzd⟩ := Set.mem_mul.1 (hsub₁ hx')

  have hzconj : z⁻¹ * δ * s z = d₁ * (x⁻¹ * δ * s x) * (s d₁)⁻¹ := by
    rw [← hzd, map_mul]
    group
  have hz2 : z ∈ {z : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
      z ∈ Subgroup.centralizer ({N δ} : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∧
        z⁻¹ * δ * s z ∈ D₁ * C * (s '' D₁)⁻¹} := by
    refine ⟨hz, ?_⟩
    rw [hzconj]
    exact Set.mul_mem_mul (Set.mul_mem_mul hd₁ hx) (Set.inv_mem_inv.2 (Set.mem_image_of_mem _ hd₁))
  obtain ⟨t, ht, d₂, hd₂, htd⟩ := Set.mem_mul.1 (hsub₂ hz2)
  refine Set.mem_mul.2 ⟨t, ht, d₂ * d₁, Set.mul_mem_mul hd₂ hd₁, ?_⟩
  rw [← mul_assoc, htd, hzd]

theorem main
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ' φ w := by

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.t2Space_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (AdeleRing (𝓞 K) K)
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI := secondCountableTopology_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := secondCountableTopology_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) := ⟨rfl⟩
  haveI := hτ'

  have hσ : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one K L σ
  have hTc := isClosed_twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ
  have hle := twistedCentralizer_le_centralizer_normString K L (AdeleRing (𝓞 K) K) σ hσ δ
  have hcomm : ∀ a b : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
      a * b = b * a := fun a b =>
    Subtype.ext (mul_comm_of_mem_centralizer hδ (hle a.2) (hle b.2))
  haveI : τ'.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have h : (fun t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ => t * g) =
        fun t => g * t := funext fun t => hcomm t g
    rw [h]
    exact map_mul_left_eq_self τ' g

  obtain ⟨D, hD, hsub⟩ :=
    exists_isCompact_twistedConj_mem_subset_twistedCentralizer_mul K L σ δ hδ hφ
  have hE : {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
      φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) ≠ 0} ⊆
      (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ :
        Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D :=
    fun x hx => hsub (subset_tsupport φ hx)

  obtain ⟨w, hw0, hwm, hwc, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) hTc τ' hD hE
  exact ⟨w, hw0, hwm, hwc, fun x hx => hw1 x hx⟩

end Main

end P2mTwistedSectionAdelic

end

open MeasureTheory NumberField in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ' φ w :=
  P2mTwistedSectionAdelic.main K L σ δ hδ τ' hτ' φ hφ

end S_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString (solution)
