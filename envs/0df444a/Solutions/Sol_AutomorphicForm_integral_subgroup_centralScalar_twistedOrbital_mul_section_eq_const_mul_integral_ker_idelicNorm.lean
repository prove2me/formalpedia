-- Prove2me | solution 1 for AutomorphicForm.integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/22f45817-4aca-5c9a-9890-7a2bb1d8034b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

import Theorems.Thm_M4aHerbrand_GenuineDescent_isClosedEmbedding_unitsMap_genuineBaseChange
import Theorems.Thm_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_AutomorphicForm_isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

open TopologicalSpace

namespace TorusUnfoldAux

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
      ((AutomorphicForm.sigmaGL K L A σ)^[k] x) i j = (AutomorphicForm.sigmaTensor K L A σ)^[k] (x i j) := by
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
  have hmul : ∀ (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)), s^[k] (x * y) = s^[k] x * s^[k] y := by
    intro k
    induction k with
    | zero => intro x y; rfl
    | succ k ih => intro x y; simp only [Function.iterate_succ_apply', ih, map_mul]

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

theorem isInvInvariant_of_comm [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    (T : Subgroup (GL (Fin 2) A)) (hT : IsClosed (T : Set (GL (Fin 2) A)))
    (hcomm : ∀ s t : T, s * t = t * s) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [τ.IsHaarMeasure] : τ.IsInvInvariant := by
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  letI : CommGroup T := { mul_comm := hcomm }
  haveI : LocallyCompactSpace T := hT.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology T :=
    (Topology.IsInducing.subtypeVal : Topology.IsInducing (Subtype.val : T → GL (Fin 2) A)).secondCountableTopology
  haveI : PseudoMetrizableSpace T := PseudoMetrizableSpace.of_regularSpace_secondCountableTopology T
  haveI : SigmaCompactSpace T := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : τ.InnerRegular := inferInstance
  exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

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

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  haveI : T1Space (GL (Fin 2) (L ⊗[K] A)) := T2Space.t1Space
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

section Finrank

variable (K L : Type) [Field K] [Field L] [Algebra K L] (σ : L ≃ₐ[K] L)

theorem pow_finrank_eq_one [FiniteDimensional K L] : σ ^ Module.finrank K L = 1 := by
  have h1 : orderOf σ ∣ Nat.card (L ≃ₐ[K] L) := orderOf_dvd_natCard σ
  have h2 : Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
    have h := IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (L ≃ₐ[K] L))
    rw [Subgroup.card_top] at h
    have := Module.finrank_mul_finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
    rw [h] at this
    exact Dvd.intro_left _ this
  exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans h2)

end Finrank

section Diag

variable {A B : Type*} [CommRing A] [CommRing B]

def IsDiag (g : GL (Fin 2) A) : Prop :=
  (g : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) A) 0 1 = 0

theorem IsDiag.one : IsDiag (1 : GL (Fin 2) A) := by
  constructor <;> simp

theorem IsDiag.mul {g h : GL (Fin 2) A} (hg : IsDiag g) (hh : IsDiag h) : IsDiag (g * h) := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  constructor <;> simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg1, hg2, hh1, hh2]

theorem IsDiag.list_prod {l : List (GL (Fin 2) A)} (hl : ∀ g ∈ l, IsDiag g) : IsDiag l.prod := by
  induction l with
  | nil => simpa using IsDiag.one
  | cons a l ih =>
      rw [List.prod_cons]
      exact (hl a (by simp)).mul (ih fun g hg => hl g (by simp [hg]))

theorem IsDiag.map (f : A →+* B) {g : GL (Fin 2) A} (hg : IsDiag g) :
    IsDiag (Matrix.GeneralLinearGroup.map f g) := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, ?_⟩
  · show f ((g : Matrix (Fin 2) (Fin 2) A) 1 0) = 0
    rw [h1, map_zero]
  · show f ((g : Matrix (Fin 2) (Fin 2) A) 0 1) = 0
    rw [h2, map_zero]

theorem IsDiag.of_commute_of_isRegularSemisimple {γ X : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγd : IsDiag γ) (h : X * γ = γ * X) : IsDiag X := by
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hXg : (X : Matrix (Fin 2) (Fin 2) A) * g = g * (X : Matrix (Fin 2) (Fin 2) A) := by
    rw [hg, ← Units.val_mul, ← Units.val_mul, h]
  obtain ⟨h01, h10, -⟩ := entries_of_commute g (X : Matrix (Fin 2) (Fin 2) A) hXg u hu'
  obtain ⟨hγ10, hγ01⟩ := hγd
  refine ⟨?_, ?_⟩
  · rw [h10]; have : g 1 0 = 0 := by rw [hg]; exact hγ10
    rw [this, mul_zero]
  · rw [h01]; have : g 0 1 = 0 := by rw [hg]; exact hγ01
    rw [this, mul_zero]

theorem isRegularSemisimple_map' (f : A →+* B) {γ : GL (Fin 2) A}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map (n := Fin 2) f γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  have hval : ((Matrix.GeneralLinearGroup.map (n := Fin 2) f γ : GL (Fin 2) B) :
      Matrix (Fin 2) (Fin 2) B) = f.mapMatrix (γ : Matrix (Fin 2) (Fin 2) A) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have h := hγ.map f
  rwa [map_sub, map_pow, map_mul, map_ofNat] at h

end Diag

end TorusUnfoldAux

namespace TF

open AutomorphicForm TorusUnfoldAux

variable {A B : Type*} [CommRing A] [CommRing B]

theorem IsDiag.comm {g h : GL (Fin 2) A} (hg : IsDiag g) (hh : IsDiag h) : g * h = h * g := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hh1, hh2⟩ := hh
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg1, hg2, hh1, hh2, mul_comm]

theorem scalar_comm (n : Type*) [Fintype n] [DecidableEq n] (z : Aˣ) (g : GL n A) :
    Matrix.GeneralLinearGroup.scalar n z * g = g * Matrix.GeneralLinearGroup.scalar n z := by
  apply Units.ext
  simp only [Units.val_mul]
  have : ((Matrix.GeneralLinearGroup.scalar n z : GL n A) : Matrix n n A) = (z : A) • (1 : Matrix n n A) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.one_apply, Matrix.smul_apply]
  rw [this, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem isDiag_scalar (z : Aˣ) : IsDiag (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  constructor <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

theorem isDiag_diagUnits2 (x y : Aˣ) : IsDiag (diagUnits2 x y) := by
  constructor <;> simp [diagUnits2]

theorem map_scalar (n : Type*) [Fintype n] [DecidableEq n] (f : A →+* B) (z : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar n z) =
      Matrix.GeneralLinearGroup.scalar n (Units.map (f : A →* B) z) := by
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]
  split_ifs <;> simp

end TF

namespace TF

open AutomorphicForm TorusUnfoldAux

theorem sigmaGL_toTensorGL (K L A : Type) [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    [TopologicalSpace A] (σ : L ≃ₐ[K] L) (m : GL (Fin 2) A) :
    sigmaGL K L A σ (toTensorGL K L A m) = toTensorGL K L A m := by
  apply Units.ext
  ext i j
  simp only [sigmaGL, toTensorGL, Matrix.GeneralLinearGroup.map_apply, sigmaTensor, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one,
    AlgHom.coe_id, id_eq]

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  unfold sigmaAdelicAct centralScalar
  rw [map_scalar]
  congr 1

theorem sigmaAdelicAct_baseChangeGL_toTensorGL (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    sigmaAdelicAct K L D σ (baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) g)) =
      baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) g) := by
  have h1 := (map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).1 σ
    (toTensorGL K L (AdeleRing (𝓞 K) K) g)
  rw [← baseChangeGL_eq] at h1
  rw [← h1, sigmaGL_toTensorGL]

include D in
theorem baseChangeGL_toTensorGL_eq_map_beta (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g := by
  have h2 := (map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).2.1 g
  rw [← baseChangeGL_eq] at h2
  exact h2

theorem isDiag_globalPoints {t : GL (Fin 2) L} (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) : IsDiag (globalPoints (𝓞 L) L t) := by
  unfold globalPoints
  exact IsDiag.map _ ⟨ht₁, ht₂⟩

include D in
theorem isDiag_baseChangeGL_toTensorGL_diagUnits2 (x y : (AdeleRing (𝓞 K) K)ˣ) :
    IsDiag (baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 x y))) := by
  rw [baseChangeGL_toTensorGL_eq_map_beta K L D]
  exact IsDiag.map _ (isDiag_diagUnits2 x y)

theorem stepB (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (w z : (AdeleRing (𝓞 L) L)ˣ) (a : (AdeleRing (𝓞 K) K)ˣ) (q : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w *
      ((centralScalar (𝓞 L) L z * baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q)⁻¹ *
        globalPoints (𝓞 L) L t *
        sigmaAdelicAct K L D σ
          (centralScalar (𝓞 L) L z * baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q)) =
    q⁻¹ * globalPoints (𝓞 L) L t *
      (centralScalar (𝓞 L) L ((D.unitsAct σ z * z⁻¹) * w) * sigmaAdelicAct K L D σ q) := by
  set β := baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) with hβ
  have hβσ : sigmaAdelicAct K L D σ β = β := sigmaAdelicAct_baseChangeGL_toTensorGL K L D σ _
  have hβt : β * globalPoints (𝓞 L) L t = globalPoints (𝓞 L) L t * β :=
    IsDiag.comm (isDiag_baseChangeGL_toTensorGL_diagUnits2 K L D a 1) (isDiag_globalPoints L ht₁ ht₂)
  have hc : ∀ (u : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
      centralScalar (𝓞 L) L u * g = g * centralScalar (𝓞 L) L u := fun u g => scalar_comm (Fin 2) u g
  rw [map_mul, map_mul, sigmaAdelicAct_centralScalar, hβσ, mul_inv_rev, mul_inv_rev, map_mul, map_mul, map_inv]

  set cw := centralScalar (𝓞 L) L w with hcw
  set cz := centralScalar (𝓞 L) L z with hcz
  set cσ := centralScalar (𝓞 L) L (D.unitsAct σ z) with hcσ
  set ιt := globalPoints (𝓞 L) L t with hιt
  set σq := sigmaAdelicAct K L D σ q with hσq
  have hC : ∀ g : AdelicGL2 (𝓞 L) L, (cσ * cz⁻¹ * cw) * g = g * (cσ * cz⁻¹ * cw) := by
    intro g
    rw [hcσ, hcz, hcw, ← map_inv, ← map_mul, ← map_mul]
    exact hc _ g
  have hczi : ∀ g : AdelicGL2 (𝓞 L) L, cz⁻¹ * g = g * cz⁻¹ := by
    intro g; rw [hcz, ← map_inv]; exact hc _ g
  have hcσ' : ∀ g : AdelicGL2 (𝓞 L) L, cσ * g = g * cσ := fun g => hc _ g
  have hcw' : ∀ g : AdelicGL2 (𝓞 L) L, cw * g = g * cw := fun g => hc _ g

  have eR : q⁻¹ * ιt * (centralScalar (𝓞 L) L ((D.unitsAct σ z * z⁻¹) * w) * σq) =
      (cσ * cz⁻¹ * cw) * (q⁻¹ * ιt * σq) := by
    have : centralScalar (𝓞 L) L ((D.unitsAct σ z * z⁻¹) * w) = cσ * cz⁻¹ * cw := by
      rw [map_mul, map_mul, map_inv]
    rw [this, ← mul_assoc (q⁻¹ * ιt), ← hC (q⁻¹ * ιt)]
    simp only [mul_assoc]

  have eL : cw * (q⁻¹ * (β⁻¹ * cz⁻¹) * ιt * (cσ * β * σq)) = (cσ * cz⁻¹ * cw) * (q⁻¹ * ιt * σq) := by

    have s1 : q⁻¹ * (β⁻¹ * cz⁻¹) * ιt * (cσ * β * σq) = q⁻¹ * β⁻¹ * ιt * β * (cz⁻¹ * cσ) * σq := by
      have a1 : cz⁻¹ * ιt = ιt * cz⁻¹ := hczi ιt
      have a2 : (cz⁻¹ * cσ) * β = β * (cz⁻¹ * cσ) := by
        rw [mul_assoc, hcσ' β, ← mul_assoc, hczi β, mul_assoc]
      calc q⁻¹ * (β⁻¹ * cz⁻¹) * ιt * (cσ * β * σq)
          = q⁻¹ * β⁻¹ * (cz⁻¹ * ιt) * cσ * β * σq := by simp only [mul_assoc]
        _ = q⁻¹ * β⁻¹ * (ιt * cz⁻¹) * cσ * β * σq := by rw [a1]
        _ = q⁻¹ * β⁻¹ * ιt * ((cz⁻¹ * cσ) * β) * σq := by simp only [mul_assoc]
        _ = q⁻¹ * β⁻¹ * ιt * (β * (cz⁻¹ * cσ)) * σq := by rw [a2]
        _ = q⁻¹ * β⁻¹ * ιt * β * (cz⁻¹ * cσ) * σq := by simp only [mul_assoc]
    have s2 : q⁻¹ * β⁻¹ * ιt * β = q⁻¹ * ιt := by
      rw [mul_assoc (q⁻¹ * β⁻¹), ← hβt, ← mul_assoc, mul_assoc q⁻¹, inv_mul_cancel, mul_one]
    rw [s1, s2]

    have s3 : cz⁻¹ * cσ = cσ * cz⁻¹ := hczi cσ
    rw [s3]
    have s4 : q⁻¹ * ιt * (cσ * cz⁻¹) * σq = (cσ * cz⁻¹) * (q⁻¹ * ιt * σq) := by
      have hC' : ∀ g : AdelicGL2 (𝓞 L) L, (cσ * cz⁻¹) * g = g * (cσ * cz⁻¹) := by
        intro g; rw [hcσ, hcz, ← map_inv, ← map_mul]; exact hc _ g
      rw [← hC' (q⁻¹ * ιt)]
      simp only [mul_assoc]
    rw [s4, ← mul_assoc, hcw' (cσ * cz⁻¹)]
  rw [eL]
  conv_rhs => rw [← mul_assoc, ← hC (q⁻¹ * ιt)]
  simp only [mul_assoc]

end TF

namespace TF

open AutomorphicForm TorusUnfoldAux

variable {A B : Type*} [CommRing A] [CommRing B]

theorem diagUnits2_mul (x y x' y' : Aˣ) : diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagUnits2_self (x : Aˣ) : diagUnits2 x x = Matrix.GeneralLinearGroup.scalar (Fin 2) x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal]

theorem diagUnits2_one : diagUnits2 (1 : Aˣ) 1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2]

theorem map_diagUnits2 (f : A →+* B) (x y : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagUnits2 x y) = diagUnits2 (Units.map (f : A →* B) x) (Units.map (f : A →* B) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, diagUnits2]

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

include D in

theorem centralScalar_beta (a : (AdeleRing (𝓞 K) K)ˣ) :
    centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) =
      baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a a)) := by
  rw [baseChangeGL_toTensorGL_eq_map_beta K L D, map_diagUnits2, diagUnits2_self]
  rfl

include D in

theorem stepE_alg (u : (AdeleRing (𝓞 L) L)ˣ) (a' a : (AdeleRing (𝓞 K) K)ˣ) (q : AdelicGL2 (𝓞 L) L) :
    (baseChangeGLEquiv K L).symm
        (centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a' * u) *
          baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q) =
      toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 (a' * a) a') *
        (baseChangeGLEquiv K L).symm (centralScalar (𝓞 L) L u * q) := by
  rw [map_mul (centralScalar (𝓞 L) L), centralScalar_beta K L D, mul_assoc _ (centralScalar (𝓞 L) L u),
    scalar_comm_centralScalar, ← mul_assoc]
  rw [← map_mul (baseChangeGL K L), ← map_mul (toTensorGL K L (AdeleRing (𝓞 K) K)), diagUnits2_mul, mul_one,
    mul_assoc, map_mul ((baseChangeGLEquiv K L).symm)]
  congr 1
  rw [← baseChangeGLEquiv_apply, ContinuousMulEquiv.symm_apply_apply]
where
  scalar_comm_centralScalar : centralScalar (𝓞 L) L u * baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) =
      baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * centralScalar (𝓞 L) L u :=
    scalar_comm (Fin 2) u _

theorem stepE_guard (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (hδ : baseChangeGL K L δ = globalPoints (𝓞 L) L t)
    (w u : (AdeleRing (𝓞 L) L)ˣ) (q : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w *
        baseChangeGL K L
          (((baseChangeGLEquiv K L).symm (centralScalar (𝓞 L) L u * q))⁻¹ * δ *
            sigmaGL K L (AdeleRing (𝓞 K) K) σ ((baseChangeGLEquiv K L).symm (centralScalar (𝓞 L) L u * q))) =
      q⁻¹ * globalPoints (𝓞 L) L t *
        (centralScalar (𝓞 L) L ((D.unitsAct σ u * u⁻¹) * w) * sigmaAdelicAct K L D σ q) := by
  have hbcσ : ∀ y, baseChangeGL K L (sigmaGL K L (AdeleRing (𝓞 K) K) σ y) = sigmaAdelicAct K L D σ (baseChangeGL K L y) := by
    intro y
    have := (map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).1 σ y
    rw [← baseChangeGL_eq] at this
    exact this
  have hback : baseChangeGL K L ((baseChangeGLEquiv K L).symm (centralScalar (𝓞 L) L u * q)) = centralScalar (𝓞 L) L u * q := by
    rw [← baseChangeGLEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [map_mul, map_mul, map_inv, hbcσ, hback, hδ]
  have := TF.stepB K L D σ t ht₁ ht₂ w u 1 q
  rw [diagUnits2_one, map_one, map_one, mul_one] at this
  exact this

end TF

namespace TorusFibreNat

open Topology
open LanglandsTunnell.CubicInduction (diagUnits2)

section Diag

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def diagEmb (p : Rˣ × Rˣ) : GL (Fin 2) R := diagUnits2 p.1 p.2

theorem coe_diagEmb (p : Rˣ × Rˣ) :
    ((diagEmb R p : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![(p.1 : R), 0; 0, (p.2 : R)] := rfl

theorem coe_inv_diagEmb (p : Rˣ × Rˣ) :
    (((diagEmb R p)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![((p.1⁻¹ : Rˣ) : R), 0; 0, ((p.2⁻¹ : Rˣ) : R)] := rfl

theorem continuous_diagEmb : Continuous (diagEmb R) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact Units.continuous_val.comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_val.comp continuous_snd
  · fin_cases i <;> fin_cases j
    · exact Units.continuous_coe_inv.comp continuous_fst
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_coe_inv.comp continuous_snd

def entries (g : GL (Fin 2) R) : (R × Rᵐᵒᵖ) × (R × Rᵐᵒᵖ) :=
  (((g : Matrix (Fin 2) (Fin 2) R) 0 0, MulOpposite.op (((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0)),
   ((g : Matrix (Fin 2) (Fin 2) R) 1 1, MulOpposite.op (((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1)))

theorem continuous_entries : Continuous (entries R) := by
  have h1 : Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) := Units.continuous_val
  have h2 : Continuous fun g : GL (Fin 2) R => ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) :=
    Units.continuous_coe_inv
  unfold entries
  exact ((h1.matrix_elem 0 0).prodMk (MulOpposite.continuous_op.comp (h2.matrix_elem 0 0))).prodMk
    ((h1.matrix_elem 1 1).prodMk (MulOpposite.continuous_op.comp (h2.matrix_elem 1 1)))

theorem entries_comp_diagEmb :
    entries R ∘ diagEmb R = Prod.map (Units.embedProduct R) (Units.embedProduct R) := by
  funext p
  rfl

theorem isInducing_diagEmb : IsInducing (diagEmb R) := by
  refine IsInducing.of_comp (continuous_diagEmb R) (continuous_entries R) ?_
  rw [entries_comp_diagEmb]
  exact Units.isInducing_embedProduct.prodMap Units.isInducing_embedProduct

theorem injective_diagEmb : Function.Injective (diagEmb R) := by
  intro p q h
  have h00 := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0) h
  have h11 := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 1) h
  simp [coe_diagEmb] at h00 h11
  exact Prod.ext (Units.ext h00) (Units.ext h11)

theorem range_diagEmb :
    Set.range (diagEmb R) = {g : GL (Fin 2) R | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0} := by
  ext g
  constructor
  · rintro ⟨p, rfl⟩
    simp [coe_diagEmb]
  · rintro ⟨h10, h01⟩
    have hmul : (g : Matrix (Fin 2) (Fin 2) R) * ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hmul' : ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (g : Matrix (Fin 2) (Fin 2) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e00 := congr_fun (congr_fun hmul 0) 0
    have e11 := congr_fun (congr_fun hmul 1) 1
    have f00 := congr_fun (congr_fun hmul' 0) 0
    have f11 := congr_fun (congr_fun hmul' 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, h10, h01,
      mul_zero, zero_mul, add_zero, zero_add] at e00 e11 f00 f11

    refine ⟨(⟨(g : Matrix (Fin 2) (Fin 2) R) 0 0, ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0,
      e00, by rw [mul_comm]; exact e00⟩,
      ⟨(g : Matrix (Fin 2) (Fin 2) R) 1 1, ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1,
      e11, by rw [mul_comm]; exact e11⟩), ?_⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagEmb, h10, h01]

theorem isClosedEmbedding_diagEmb [T1Space R] : IsClosedEmbedding (diagEmb R) := by
  refine ⟨⟨isInducing_diagEmb R, injective_diagEmb R⟩, ?_⟩
  rw [range_diagEmb]
  have h1 : Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) := Units.continuous_val
  exact (isClosed_singleton.preimage (h1.matrix_elem 1 0)).inter (isClosed_singleton.preimage (h1.matrix_elem 0 1))

def shear [IsTopologicalRing R] : Rˣ × Rˣ ≃ₜ Rˣ × Rˣ :=
  (Homeomorph.shearMulRight Rˣ).trans (Homeomorph.prodComm Rˣ Rˣ)

theorem shear_apply (p : Rˣ × Rˣ) : shear R p = (p.1 * p.2, p.1) := rfl

end Diag

section Adelic

open Topology MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem bc_toTensorGL_diagUnits2 (a b : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a b)) =
      diagEmb (AdeleRing (𝓞 L) L) (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a, Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom b) := by
  apply Units.ext
  have hb : ∀ i j : Fin 2, ((AutomorphicForm.baseChangeGL K L
      (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a b)) : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β
        (((diagUnits2 a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) := by
    intro i j
    show AutomorphicForm.baseChangeEquiv K L ((Algebra.TensorProduct.includeRight :
        AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K)
          (((diagUnits2 a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)) = _
    rw [Algebra.TensorProduct.includeRight_apply, AutomorphicForm.baseChangeEquiv_one_tmul]
    rfl
  ext i j
  rw [hb]
  simp only [coe_diagEmb, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp

theorem isClosedEmbedding_bc_toTensorGL_diagUnits2 :
    IsClosedEmbedding (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2))) := by
  have h : (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2))) =
      diagEmb (AdeleRing (𝓞 L) L) ∘ Prod.map (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom) (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom) := by
    funext p; exact bc_toTensorGL_diagUnits2 K L p.1 p.2
  rw [h]
  exact (isClosedEmbedding_diagEmb (AdeleRing (𝓞 L) L)).comp
    ((M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange K L).prodMap
      (M4aHerbrand.GenuineDescent.isClosedEmbedding_unitsMap_genuineBaseChange K L))

theorem centralScalar_beta_mul_bc_diag (a' a : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a') *
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) =
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 (a' * a) a')) := by
  rw [bc_toTensorGL_diagUnits2, bc_toTensorGL_diagUnits2]
  apply Units.ext
  have hc : ((AutomorphicForm.centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a') : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = Matrix.scalar (Fin 2) ((Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a' : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) := rfl
  rw [Units.val_mul, hc, Matrix.scalar_apply, coe_diagEmb, coe_diagEmb]
  ext i j
  simp only [map_mul, map_one, Units.val_mul, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (X : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    X * AutomorphicForm.centralScalar (𝓞 L) L z = AutomorphicForm.centralScalar (𝓞 L) L z * X := by
  refine Units.ext ?_
  show (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) =
    Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) * (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 L) L) (fun r' => Commute.all _ r') _).eq.symm

theorem symm_centralScalar_beta_mul (u : (AdeleRing (𝓞 L) L)ˣ) (a' a : (AdeleRing (𝓞 K) K)ˣ)
    (q : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
    (AutomorphicForm.baseChangeGLEquiv K L).symm
        (AutomorphicForm.centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a' * u) *
          AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 (a' * a) a') *
        (AutomorphicForm.baseChangeGLEquiv K L).symm (AutomorphicForm.centralScalar (𝓞 L) L u * q) := by
  have hbcE : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K), AutomorphicForm.baseChangeGLEquiv K L x = AutomorphicForm.baseChangeGL K L x := fun x => rfl
  have h1 : AutomorphicForm.centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a' * u) *
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q =
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 (a' * a) a')) *
        (AutomorphicForm.centralScalar (𝓞 L) L u * q) := by
    rw [map_mul, mul_assoc (AutomorphicForm.centralScalar (𝓞 L) L _), ← centralScalar_comm L u, ← mul_assoc,
      centralScalar_beta_mul_bc_diag, mul_assoc]
  rw [h1, map_mul, ← hbcE, ContinuousMulEquiv.symm_apply_apply]

theorem fixed_AK [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ)
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ, z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (b : (AdeleRing (𝓞 L) L)ˣ) (hb : b ∈ AK) (u : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ (b * u) * (b * u)⁻¹ = D.unitsAct σ u * u⁻¹ := by
  obtain ⟨-, hfix, -, -⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
  obtain ⟨a, rfl⟩ := (hAK b).1 hb
  have hβ : D.unitsAct σ (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a := ((hfix _).2 ⟨a, rfl⟩) σ
  rw [map_mul, hβ, mul_inv_rev]
  calc Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a * D.unitsAct σ u * (u⁻¹ * (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)⁻¹)
      = D.unitsAct σ u * u⁻¹ * (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a * (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)⁻¹) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = D.unitsAct σ u * u⁻¹ := by rw [mul_inv_cancel, mul_one]

theorem H90_fold {X : Type*} [MeasurableSpace X] (ν : Measure X) {Y : Type*} [MeasurableSpace Y] (μN : Measure Y)
    (F : X → ℂ) (G : Y → ℂ) (cN : ℝ) (hcN : 0 < cN)
    (h : ∫ n, G n ∂μN = cN * ∫ x, F x ∂ν) :
    ∫ x, F x ∂ν = ((cN⁻¹ : ℝ) : ℂ) * ∫ n, G n ∂μN := by
  rw [h, ← mul_assoc]
  have : ((cN⁻¹ : ℝ) : ℂ) * (cN : ℂ) = 1 := by
    rw [Complex.ofReal_inv, inv_mul_cancel₀]
    exact_mod_cast hcN.ne'
  rw [this, one_mul]

theorem AK_unfold [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (G : (AdeleRing (𝓞 L) L)ˣ → ℂ) (hGm : Measurable G) (hGi : Integrable G νZL) :
    ∫ z, G z ∂νZL = ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
      (∫ b : AK, G ((b : (AdeleRing (𝓞 L) L)ˣ) * q.out) ∂μAK) ∂(HaarQuotient.measure νZL AK μAK) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite νZL := Measure.IsHaarMeasure.sigmaFinite _
  haveI : μAK.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have h : (fun t : AK => t * g) = fun t => g * t := funext fun t => mul_comm t g
    rw [h]
    exact map_mul_left_eq_self μAK g
  obtain ⟨-, -, h⟩ := HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
    νZL AK hAKc μAK G hGm hGi.2
  exact h

theorem isClosedEmbedding_toTensorGL_diagUnits2 :
    IsClosedEmbedding (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) := by
  have h : (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) =
      (AutomorphicForm.baseChangeGLEquiv K L).symm ∘ (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
        AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2))) := by
    funext p
    exact ((AutomorphicForm.baseChangeGLEquiv K L).symm_apply_apply _).symm
  rw [h]
  exact (AutomorphicForm.baseChangeGLEquiv K L).symm.toHomeomorph.isClosedEmbedding.comp
    (isClosedEmbedding_bc_toTensorGL_diagUnits2 K L)

theorem section_unfold
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (cτ : ℝ) (hcτ : 0 < cτ)
    (hτc : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
      ∫ r : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ, g (r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
        cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK))
    (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ) (hsc : Continuous s) (hss : HasCompactSupport s)
    (q : GL (Fin 2) (AdeleRing (𝓞 L) L)) (u : (AdeleRing (𝓞 L) L)ˣ)
    (h1 : ∫ r : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
      s ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * (AutomorphicForm.baseChangeGLEquiv K L).symm (AutomorphicForm.centralScalar (𝓞 L) L u * q)) ∂τ = 1) :
    ∫ a' : (AdeleRing (𝓞 K) K)ˣ, (∫ a : (AdeleRing (𝓞 K) K)ˣ,
      (s ((AutomorphicForm.baseChangeGLEquiv K L).symm
        (AutomorphicForm.centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a' * u) *
          AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q)) : ℂ)
      ∂νK) ∂νK = ((cτ⁻¹ : ℝ) : ℂ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  set x₀ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) := (AutomorphicForm.baseChangeGLEquiv K L).symm (AutomorphicForm.centralScalar (𝓞 L) L u * q) with hx₀
  set F : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ := fun p =>
    (s (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2) * x₀) : ℂ) with hF

  have hS : ∀ a' a : (AdeleRing (𝓞 K) K)ˣ,
      (s ((AutomorphicForm.baseChangeGLEquiv K L).symm
        (AutomorphicForm.centralScalar (𝓞 L) L (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a' * u) *
          AutomorphicForm.baseChangeGL K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q)) : ℂ) =
      F (a' * a, a') := by
    intro a' a
    simp only [hF, hx₀, symm_centralScalar_beta_mul]
  simp_rw [hS]

  have hemb := isClosedEmbedding_toTensorGL_diagUnits2 K L
  have hFc : Continuous F := by
    simp only [hF]
    exact Complex.continuous_ofReal.comp (hsc.comp (hemb.continuous.mul continuous_const))
  have hFs : HasCompactSupport F := by
    simp only [hF]
    have h2 : HasCompactSupport fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
        s (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2) * x₀) :=
      hss.comp_isClosedEmbedding ((Homeomorph.mulRight x₀).isClosedEmbedding.comp hemb)
    exact h2.comp_left Complex.ofReal_zero
  have hFi : Integrable F (νK.prod νK) := hFc.integrable_of_hasCompactSupport hFs

  have hinner : ∀ a' : (AdeleRing (𝓞 K) K)ˣ, ∫ a, F (a' * a, a') ∂νK = ∫ a, F (a, a') ∂νK := fun a' =>
    integral_mul_left_eq_self (fun a => F (a, a')) a'
  simp_rw [hinner]
  have hswap : ∫ a', (∫ a, F (a, a') ∂νK) ∂νK = ∫ p, F p ∂(νK.prod νK) := by
    rw [← integral_prod_swap F]
    exact (integral_prod (fun z : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => F z.swap) hFi.swap).symm
  rw [hswap]

  have h2 := hτc (fun y => (s (y * x₀) : ℂ))
  rw [integral_complex_ofReal, h1] at h2
  have hcτ' : (cτ : ℂ) ≠ 0 := by exact_mod_cast hcτ.ne'
  rw [Complex.ofReal_inv]
  have h3 : (cτ : ℂ) * ∫ p, F p ∂(νK.prod νK) = 1 := by simpa using h2.symm
  calc ∫ p, F p ∂(νK.prod νK) = (cτ : ℂ)⁻¹ * ((cτ : ℂ) * ∫ p, F p ∂(νK.prod νK)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcτ', one_mul]
    _ = (cτ : ℂ)⁻¹ := by rw [h3, mul_one]

end Adelic

end TorusFibreNat

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

open AutomorphicForm TorusUnfoldAux in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (cH : ℝ) (hcH : 0 < cH)
    (hHc : ∀ g : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ h : H, g (h : AdelicGL2 (𝓞 L) L) ∂μH =
        cH * ∫ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 L) L p.1 *
            AutomorphicForm.baseChangeGL K L
              (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) ∂(νZL.prod νK))
    (cτ : ℝ) (hcτ : 0 < cτ)
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t)
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ)
    (hτc : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
      ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
        cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (w : (AdeleRing (𝓞 L) L)ˣ)

    (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ) (hsc : Continuous s) (hs0 : ∀ x, 0 ≤ s x)
    (hss : HasCompactSupport s)
    (hsec : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      φ (AutomorphicForm.centralScalar (𝓞 L) L w *
          AutomorphicForm.baseChangeGL K L (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x)) ≠ 0 →
        ∫ r : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          s ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x) ∂τ = 1)
    (q : AdelicGL2 (𝓞 L) L) :
    ∫ h : H, φ (AutomorphicForm.centralScalar (𝓞 L) L w *
          (((h : AdelicGL2 (𝓞 L) L) * q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ ((h : AdelicGL2 (𝓞 L) L) * q))) *
        (s ((AutomorphicForm.baseChangeGLEquiv K L).symm ((h : AdelicGL2 (𝓞 L) L) * q)) : ℂ) ∂μH =
      ((cH / (cτ * cN) : ℝ) : ℂ) *
        ∫ n : N1, φ ((q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w) *
            AutomorphicForm.sigmaAdelicAct K L D σ q)) ∂μN := by
  classical

  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
    haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
    haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L

  set bcE := baseChangeGLEquiv K L with hbcE
  set θ : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 L) L := fun p =>
    centralScalar (𝓞 L) L p.1 * baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1)) with hθ
  set Ψ : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z =>
    φ (q⁻¹ * globalPoints (𝓞 L) L t *
      (centralScalar (𝓞 L) L ((D.unitsAct σ z * z⁻¹) * w) * sigmaAdelicAct K L D σ q)) with hΨ
  set S : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 K) K)ˣ → ℝ := fun z a =>
    s ((baseChangeGLEquiv K L).symm
      (centralScalar (𝓞 L) L z * baseChangeGL K L (toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 a 1)) * q)) with hS
  set A : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ∫ a, (S z a : ℂ) ∂νK with hA

  set F : AdelicGL2 (𝓞 L) L → ℂ := fun g =>
    φ (centralScalar (𝓞 L) L w * ((g * q)⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (g * q))) *
      (s ((baseChangeGLEquiv K L).symm (g * q)) : ℂ) with hF
  have hσc : Continuous (sigmaAdelicAct K L D σ) := continuous_glMap _ (D.continuous_act σ)
  have hFc : Continuous F := by
    simp only [hF]
    refine (hφ.comp ?_).mul (Complex.continuous_ofReal.comp (hsc.comp
      ((baseChangeGLEquiv K L).symm.continuous.comp (continuous_mul_const q))))
    exact (continuous_const.mul (((continuous_mul_const q).inv.mul continuous_const).mul
      (hσc.comp (continuous_mul_const q))))
  have hθc : Topology.IsClosedEmbedding θ := isClosedEmbedding_centralScalar_mul_baseChangeGL_toTensorGL_diagUnits2 K L

  have hStepA := hHc F
  simp only [hF] at hStepA
  rw [hStepA]

  have hB : (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => F (θ p)) = fun p => Ψ p.1 * (S p.1 p.2 : ℂ) := by
    funext p
    simp only [hF, hθ, hΨ, hS]
    rw [TF.stepB K L D σ t ht₁ ht₂ w p.1 p.2 q]
  have hB' : (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ =>
      φ (centralScalar (𝓞 L) L w * ((θ p * q)⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (θ p * q))) *
        (s ((baseChangeGLEquiv K L).symm (θ p * q)) : ℂ)) = fun p => Ψ p.1 * (S p.1 p.2 : ℂ) := hB
  change (cH : ℂ) * ∫ p, F (θ p) ∂(νZL.prod νK) = _
  rw [hB]

  have hsupp : HasCompactSupport (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => F (θ p)) := by
    set Kg : Set (AdelicGL2 (𝓞 L) L) := (fun g => g * q⁻¹) '' (bcE '' tsupport s) with hKg
    have hKgc : IsCompact Kg := (hss.image bcE.continuous).image (continuous_mul_const _)
    refine HasCompactSupport.intro (hθc.isCompact_preimage hKgc) fun p hp => ?_
    simp only [hF]
    have : s ((baseChangeGLEquiv K L).symm (θ p * q)) = 0 := by
      by_contra hne
      apply hp
      refine ⟨θ p * q, ⟨(baseChangeGLEquiv K L).symm (θ p * q), subset_tsupport _ hne, ?_⟩, by simp⟩
      simp [hbcE]
    rw [this]; simp
  have hI : Integrable (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => F (θ p)) (νZL.prod νK) :=
    (hFc.comp hθc.continuous).integrable_of_hasCompactSupport hsupp
  have hI' : Integrable (fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ => Ψ p.1 * (S p.1 p.2 : ℂ)) (νZL.prod νK) := by
    rw [← hB]; exact hI
  rw [integral_prod _ hI']
  have hC : ∀ z, ∫ a, Ψ z * (S z a : ℂ) ∂νK = Ψ z * A z := fun z => integral_const_mul _ _
  simp_rw [hC]

  have hΨA_int : Integrable (fun z => Ψ z * A z) νZL := by
    have := hI'.integral_prod_left
    simpa only [hC] using this
  have hSc : Continuous (Function.uncurry fun (z : (AdeleRing (𝓞 L) L)ˣ) (a : (AdeleRing (𝓞 K) K)ˣ) => Ψ z * (S z a : ℂ)) := by
    have : (Function.uncurry fun (z : (AdeleRing (𝓞 L) L)ˣ) (a : (AdeleRing (𝓞 K) K)ˣ) => Ψ z * (S z a : ℂ)) =
        fun p => F (θ p) := by rw [hB]; rfl
    rw [this]; exact hFc.comp hθc.continuous
  have hΨA_meas : Measurable (fun z => Ψ z * A z) := by
    have h1 := (hSc.stronglyMeasurable).integral_prod_right (ν := νK)
    have : (fun z => ∫ a, Ψ z * (S z a : ℂ) ∂νK) = fun z => Ψ z * A z := funext hC
    rw [← this]; exact h1.measurable

  have hD : ∫ z, Ψ z * A z ∂νZL =
      ∫ ū : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
        ∫ b : AK, Ψ ((b : (AdeleRing (𝓞 L) L)ˣ) * ū.out) * A ((b : (AdeleRing (𝓞 L) L)ˣ) * ū.out) ∂μAK
        ∂(HaarQuotient.measure νZL AK μAK) := by
    haveI : μAK.IsMulRightInvariant := ⟨fun g => by
      have : (fun x : AK => x * g) = fun x => g * x := funext fun x => mul_comm x g
      rw [this]; exact map_mul_left_eq_self μAK g⟩
    exact (HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
      νZL AK hAKc μAK (fun z => Ψ z * A z) hΨA_meas hΨA_int.2).2.2
  rw [hD]

  have hE0 : ∀ (b : (AdeleRing (𝓞 L) L)ˣ), b ∈ AK → ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      D.unitsAct σ (b * u) * (b * u)⁻¹ = D.unitsAct σ u * u⁻¹ := by
    intro b hb u
    obtain ⟨a', rfl⟩ := (hAK b).1 hb
    have hfix : D.unitsAct σ (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a') =
        Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a' :=
      ((M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D).2.1 _).2
        ⟨a', rfl⟩ σ
    rw [map_mul, hfix, mul_inv_rev]
    simp only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel_left]
  have hE : ∀ u : (AdeleRing (𝓞 L) L)ˣ, Ψ u ≠ 0 →
      ∫ b : AK, A ((b : (AdeleRing (𝓞 L) L)ˣ) * u) ∂μAK = ((cτ⁻¹ : ℝ) : ℂ) := by
    intro u hΨu
    have h1 : ∫ r : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
        s ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) *
          (baseChangeGLEquiv K L).symm (centralScalar (𝓞 L) L u * q)) ∂τ = 1 := by
      apply hsec
      rw [TF.stepE_guard K L D σ t ht₁ ht₂ δ hδ w u q]
      exact hΨu
    have h2 := hμAK (fun z => A (z * u))
    rw [h2]
    simp only [hA, hS]
    exact TorusFibreNat.section_unfold K L νK σ δ τ cτ hcτ hτc s hsc hss q u h1
  have hE' : ∀ ū : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
      ∫ b : AK, Ψ ((b : (AdeleRing (𝓞 L) L)ˣ) * ū.out) * A ((b : (AdeleRing (𝓞 L) L)ˣ) * ū.out) ∂μAK =
        Ψ ū.out * ((cτ⁻¹ : ℝ) : ℂ) := by
    intro ū
    have hΨb : ∀ b : AK, Ψ ((b : (AdeleRing (𝓞 L) L)ˣ) * ū.out) = Ψ ū.out := fun b => by
      simp only [hΨ]; rw [hE0 b b.2]
    simp_rw [hΨb]
    rw [integral_const_mul]
    by_cases h0 : Ψ ū.out = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [hE ū.out h0]
  simp_rw [hE']
  rw [integral_mul_const]

  have hF' : ∫ ū : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ, Ψ ū.out ∂(HaarQuotient.measure νZL AK μAK) =
      ((cN⁻¹ : ℝ) : ℂ) * ∫ n : N1, φ (q⁻¹ * globalPoints (𝓞 L) L t *
          (centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w) * sigmaAdelicAct K L D σ q)) ∂μN := by
    have := hNc (fun m => φ (q⁻¹ * globalPoints (𝓞 L) L t * (centralScalar (𝓞 L) L (m * w) * sigmaAdelicAct K L D σ q)))
    simp only [hΨ]
    rw [this, ← mul_assoc]
    rw [show ((cN⁻¹ : ℝ) : ℂ) * (cN : ℂ) = 1 by push_cast; field_simp [hcN.ne'], one_mul]
  rw [hF']
  push_cast
  field_simp

end S_AutomorphicForm_integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
end P2MW
export P2MW.S_AutomorphicForm_integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm (solution)
