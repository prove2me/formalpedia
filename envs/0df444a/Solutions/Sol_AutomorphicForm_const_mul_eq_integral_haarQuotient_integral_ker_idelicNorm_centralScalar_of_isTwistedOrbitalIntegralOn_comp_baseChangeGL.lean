-- Prove2me | solution 1 for AutomorphicForm.const_mul_eq_integral_haarQuotient_integral_ker_idelicNorm_centralScalar_of_isTwistedOrbitalIntegralOn_comp_baseChangeGL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/54ff50e0-a8e9-5d8d-abb3-d3a26420dc1e

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
import Theorems.Thm_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_AutomorphicForm_integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
import Theorems.Thm_AutomorphicForm_exists_continuous_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
import Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous
import Theorems.Thm_AutomorphicForm_isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_const_mul_eq_integral_haarQuotient_integral_ker_idelicNorm_centralScalar_of_isTwistedOrbitalIntegralOn_comp_baseChangeGL
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace
open scoped TensorProduct TensorProduct.RightActions

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

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

open AutomorphicForm TorusUnfoldAux in
theorem plain_part
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

    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)

    (cμ : ℝ) (hcμ : 0 < cμ)
    (hμc : ∀ F : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = cμ * ∫ g, F g ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
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
    (t : GL (Fin 2) L) (ht10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hnorm : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
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
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (w₀ : (AdeleRing (𝓞 L) L)ˣ)
    (I : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w₀ * g)) ∘
            AutomorphicForm.baseChangeGL K L) I) :
    ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * I =
        (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w₀) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) := by
  classical
  have hHcl : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) := by assumption

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI hGLHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 L) L) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : SFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := instSFiniteOfSigmaFinite

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.t2Space_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (AdeleRing (𝓞 K) K)
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI := secondCountableTopology_tensor K L (AdeleRing (𝓞 K) K)
  letI iG' : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := secondCountableTopology_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  letI iT : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) := ⟨rfl⟩
  haveI := hμ
  haveI := hτ
  have hσ : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one K L σ
  have hreg := AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
    K L σ hgen t ht10 ht01 hnorm δ hδ
  have hTc := isClosed_twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ
  have hle := twistedCentralizer_le_centralizer_normString K L (AdeleRing (𝓞 K) K) σ hσ δ
  have hcomm : ∀ a b : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ, a * b = b * a :=
    fun a b => Subtype.ext (mul_comm_of_mem_centralizer hreg (hle a.2) (hle b.2))
  haveI : τ.IsInvInvariant := isInvInvariant_of_comm (L ⊗[K] AdeleRing (𝓞 K) K) _ hTc hcomm τ

  have hbcE_apply : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K), AutomorphicForm.baseChangeGLEquiv K L x = AutomorphicForm.baseChangeGL K L x :=
    fun x => rfl
  have hbc_cont : Continuous (AutomorphicForm.baseChangeGL K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L) :=
    (AutomorphicForm.baseChangeGLEquiv K L).continuous.congr hbcE_apply
  have hbc_fun : ((AutomorphicForm.baseChangeGLEquiv K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L)) =
      (AutomorphicForm.baseChangeGL K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L) := funext hbcE_apply
  have hbc_ce : Topology.IsClosedEmbedding (AutomorphicForm.baseChangeGL K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L) :=
    hbc_fun ▸ (AutomorphicForm.baseChangeGLEquiv K L).toHomeomorph.isClosedEmbedding
  have hsymm : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (AutomorphicForm.baseChangeGLEquiv K L).symm (AutomorphicForm.baseChangeGL K L x) = x := fun x => by
    rw [← hbcE_apply]; exact (AutomorphicForm.baseChangeGLEquiv K L).symm_apply_apply x
  have hbcσ : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.baseChangeGL K L x) := by
    intro x
    obtain ⟨h1, -, -⟩ := AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D
    rw [AutomorphicForm.baseChangeGL_eq]
    exact h1 σ x
  have hconj : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.baseChangeGL K L (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
        (AutomorphicForm.baseChangeGL K L x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.baseChangeGL K L x) := by
    intro x; rw [map_mul, map_mul, map_inv, hδ, hbcσ]

  have hΦc : ∀ w : (AdeleRing (𝓞 L) L)ˣ, Continuous fun g : AdelicGL2 (𝓞 L) L =>
      φ (centralScalar (𝓞 L) L w * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) := fun w =>
    hφc.comp (continuous_const.mul ((continuous_inv.mul continuous_const).mul
      (AutomorphicForm.continuous_sigmaAdelicAct K L D σ)))

  have key : ∀ w₀ : (AdeleRing (𝓞 L) L)ˣ, ∃ s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ, Continuous s ∧
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ
        ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) s ∧
      (∀ q : AdelicGL2 (𝓞 L) L,
        ∫ h : H, φ (AutomorphicForm.centralScalar (𝓞 L) L w₀ *
            (((h : AdelicGL2 (𝓞 L) L) * q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
              AutomorphicForm.sigmaAdelicAct K L D σ ((h : AdelicGL2 (𝓞 L) L) * q))) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm ((h : AdelicGL2 (𝓞 L) L) * q)) : ℂ) ∂μH =
        ((cH / (cτ * cN) : ℝ) : ℂ) *
          ∫ n : N1, φ ((q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w₀) *
              AutomorphicForm.sigmaAdelicAct K L D σ q)) ∂μN) := by
    intro w₀
    have hφw : Continuous (fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) :=
      hφc.comp (continuous_const.mul continuous_id)
    have hφws : HasCompactSupport (fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) :=
      hφs.comp_homeomorph (Homeomorph.mulLeft (centralScalar (𝓞 L) L w₀))
    have hφ's : HasCompactSupport
        ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) :=
      hφws.comp_isClosedEmbedding hbc_ce
    obtain ⟨s, hsc, hsS⟩ :=
      AutomorphicForm.exists_continuous_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
        K L σ δ hreg τ hτ _ hφ's
    refine ⟨s, hsc, hsS, fun q => ?_⟩
    obtain ⟨hs0, -, hss, hsec⟩ := hsS
    exact AutomorphicForm.integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
      K L νZL D σ hgen H hHcl hH μH νK cH hcH hHc cτ hcτ AK hAKc hAK μAK hμAK N1 hN1c hN1 μN cN hcN hNc
      t ht10 ht01 hnorm δ hδ τ hτ hτc φ hφc hφs w₀ s hsc hs0 hss (fun x hx => hsec x hx) q
  obtain ⟨s, hsc, hsS, hfib⟩ := key w₀
  have hφw : Continuous (fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) :=
    hφc.comp (continuous_const.mul continuous_id)
  have hφ'm : Measurable
      ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) :=
    (hφw.comp hbc_cont).measurable
  have hφ'b : ∃ C : ℝ, ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      ‖((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) g‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hφs.comp_homeomorph (Homeomorph.mulLeft (centralScalar (𝓞 L) L w₀))).exists_bound_of_continuous hφw
    exact ⟨C, fun g => hC _⟩
  have hI' : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
      ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L)
      (∫ x, ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L)
        (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) * (s x : ℂ) ∂μ) := ⟨s, hsS, rfl⟩
  rw [AutomorphicForm.IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L
      (AdeleRing (𝓞 K) K) σ hσ μ hμ δ hreg τ hτ _ hφ'm hφ'b hI hI']

  have hint : (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘
        AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
        (s x : ℂ)) =
      fun x => (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) (AutomorphicForm.baseChangeGL K L x) := by
    funext x
    simp only [Function.comp_apply, hconj, hsymm]
  rw [hint]
  have step1 := hμc (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ))

  have hFc : Continuous (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) :=
    (hΦc w₀).mul (Complex.continuous_ofReal.comp (hsc.comp (AutomorphicForm.baseChangeGLEquiv K L).symm.continuous))
  have hFs : HasCompactSupport (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) := by
    have h1 : HasCompactSupport fun g : AdelicGL2 (𝓞 L) L =>
        (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ) :=
      (hsS.2.2.1.comp_homeomorph (AutomorphicForm.baseChangeGLEquiv K L).symm.toHomeomorph).comp_left
        Complex.ofReal_zero
    exact h1.mul_left
  obtain ⟨-, -, hC0⟩ :=
    HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
      (adelicGLHaar (Fin 2) (𝓞 L) L) H hHcl μH (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) hFc.measurable (hFc.integrable_of_hasCompactSupport hFs).2
  have hfibF : (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
      ∫ h : H, (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * q.out) ∂μH) =
      fun q => ((cH / (cτ * cN) : ℝ) : ℂ) *
        ∫ n : N1, φ ((q.out)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w₀) *
            AutomorphicForm.sigmaAdelicAct K L D σ q.out)) ∂μN := by
    funext q; exact hfib q.out
  rw [hfibF, integral_const_mul] at hC0
  rw [hC0] at step1
  refine (congrArg (fun z : ℂ => ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * z) step1).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  conv_rhs => rw [← one_mul (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), _ ∂_)]
  congr 1
  have hne : ((cN : ℂ) * cτ * cH * cμ) ≠ 0 := by
    have h0 : (cN * cτ * cH * cμ : ℝ) ≠ 0 := by positivity
    exact_mod_cast h0
  push_cast
  field_simp
  exact div_self hne

open AutomorphicForm TorusUnfoldAux in
theorem weighted_part
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

    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)

    (cμ : ℝ) (hcμ : 0 < cμ)
    (hμc : ∀ F : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = cμ * ∫ g, F g ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
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
    (t : GL (Fin 2) L) (ht10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hnorm : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
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
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (w₀ : (AdeleRing (𝓞 L) L)ˣ)
    (J : ℂ)
    (hJ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ
          (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
            -Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.baseChangeGL K L x))
              - Real.log (NumberField.AdelicHeight.adelicHeight L
                  (AutomorphicForm.adelicWeyl (𝓞 L) L * AutomorphicForm.baseChangeGL K L x)))
          δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w₀ * g)) ∘
            AutomorphicForm.baseChangeGL K L) J) :
    ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * J =
        (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) *
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w₀) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) := by
  classical
  have hHcl : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) := by assumption

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI hGLHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 L) L) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : SFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := instSFiniteOfSigmaFinite

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.t2Space_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (AdeleRing (𝓞 K) K)
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI := secondCountableTopology_tensor K L (AdeleRing (𝓞 K) K)
  letI iG' : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := secondCountableTopology_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  letI iT : MeasurableSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) := ⟨rfl⟩
  haveI := hμ
  haveI := hτ
  have hσ : σ ^ Module.finrank K L = 1 := pow_finrank_eq_one K L σ
  have hreg := AutomorphicForm.isRegularSemisimple_normString_of_baseChangeGL_eq_globalPoints_of_norm_ne_one
    K L σ hgen t ht10 ht01 hnorm δ hδ
  have hTc := isClosed_twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ
  have hle := twistedCentralizer_le_centralizer_normString K L (AdeleRing (𝓞 K) K) σ hσ δ
  have hcomm : ∀ a b : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ, a * b = b * a :=
    fun a b => Subtype.ext (mul_comm_of_mem_centralizer hreg (hle a.2) (hle b.2))
  haveI : τ.IsInvInvariant := isInvInvariant_of_comm (L ⊗[K] AdeleRing (𝓞 K) K) _ hTc hcomm τ

  have hbcE_apply : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K), AutomorphicForm.baseChangeGLEquiv K L x = AutomorphicForm.baseChangeGL K L x :=
    fun x => rfl
  have hbc_cont : Continuous (AutomorphicForm.baseChangeGL K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L) :=
    (AutomorphicForm.baseChangeGLEquiv K L).continuous.congr hbcE_apply
  have hbc_fun : ((AutomorphicForm.baseChangeGLEquiv K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L)) =
      (AutomorphicForm.baseChangeGL K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L) := funext hbcE_apply
  have hbc_ce : Topology.IsClosedEmbedding (AutomorphicForm.baseChangeGL K L : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → AdelicGL2 (𝓞 L) L) :=
    hbc_fun ▸ (AutomorphicForm.baseChangeGLEquiv K L).toHomeomorph.isClosedEmbedding
  have hsymm : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (AutomorphicForm.baseChangeGLEquiv K L).symm (AutomorphicForm.baseChangeGL K L x) = x := fun x => by
    rw [← hbcE_apply]; exact (AutomorphicForm.baseChangeGLEquiv K L).symm_apply_apply x
  have hbcσ : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.baseChangeGL K L (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.baseChangeGL K L x) := by
    intro x
    obtain ⟨h1, -, -⟩ := AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D
    rw [AutomorphicForm.baseChangeGL_eq]
    exact h1 σ x
  have hconj : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.baseChangeGL K L (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
        (AutomorphicForm.baseChangeGL K L x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.baseChangeGL K L x) := by
    intro x; rw [map_mul, map_mul, map_inv, hδ, hbcσ]

  have hΦc : ∀ w : (AdeleRing (𝓞 L) L)ˣ, Continuous fun g : AdelicGL2 (𝓞 L) L =>
      φ (centralScalar (𝓞 L) L w * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) := fun w =>
    hφc.comp (continuous_const.mul ((continuous_inv.mul continuous_const).mul
      (AutomorphicForm.continuous_sigmaAdelicAct K L D σ)))

  have key : ∀ w₀ : (AdeleRing (𝓞 L) L)ˣ, ∃ s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ, Continuous s ∧
      AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ
        ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) s ∧
      (∀ q : AdelicGL2 (𝓞 L) L,
        ∫ h : H, φ (AutomorphicForm.centralScalar (𝓞 L) L w₀ *
            (((h : AdelicGL2 (𝓞 L) L) * q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
              AutomorphicForm.sigmaAdelicAct K L D σ ((h : AdelicGL2 (𝓞 L) L) * q))) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm ((h : AdelicGL2 (𝓞 L) L) * q)) : ℂ) ∂μH =
        ((cH / (cτ * cN) : ℝ) : ℂ) *
          ∫ n : N1, φ ((q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w₀) *
              AutomorphicForm.sigmaAdelicAct K L D σ q)) ∂μN) := by
    intro w₀
    have hφw : Continuous (fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) :=
      hφc.comp (continuous_const.mul continuous_id)
    have hφws : HasCompactSupport (fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) :=
      hφs.comp_homeomorph (Homeomorph.mulLeft (centralScalar (𝓞 L) L w₀))
    have hφ's : HasCompactSupport
        ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) :=
      hφws.comp_isClosedEmbedding hbc_ce
    obtain ⟨s, hsc, hsS⟩ :=
      AutomorphicForm.exists_continuous_isTwistedSectionFnOn_adeleRing_of_isRegularSemisimple_normString
        K L σ δ hreg τ hτ _ hφ's
    refine ⟨s, hsc, hsS, fun q => ?_⟩
    obtain ⟨hs0, -, hss, hsec⟩ := hsS
    exact AutomorphicForm.integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
      K L νZL D σ hgen H hHcl hH μH νK cH hcH hHc cτ hcτ AK hAKc hAK μAK hμAK N1 hN1c hN1 μN cN hcN hNc
      t ht10 ht01 hnorm δ hδ τ hτ hτc φ hφc hφs w₀ s hsc hs0 hss (fun x hx => hsec x hx) q
  obtain ⟨s, hsc, hsS, hfib⟩ := key w₀
  obtain ⟨s', hs'S, rfl⟩ := hJ
  obtain ⟨hWinv, hWLcont⟩ :=
    NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous L
  have hφw : Continuous (fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) := hφc.comp (continuous_const.mul continuous_id)
  have hφws : HasCompactSupport (fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) := hφs.comp_homeomorph (Homeomorph.mulLeft (centralScalar (𝓞 L) L w₀))
  have hφ's : HasCompactSupport ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) := hφws.comp_isClosedEmbedding hbc_ce
  have htwc : Continuous fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) :=
    (continuous_inv.mul continuous_const).mul (continuous_sigmaGL K L (AdeleRing (𝓞 K) K) σ)

  have hiter : ∀ i : ℕ, IsDiag (AutomorphicForm.baseChangeGL K L
      ((AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ)^[i] δ)) := by
    intro i
    induction i with
    | zero =>
        rw [Function.iterate_zero, id_eq, hδ]
        exact IsDiag.map (algebraMap L (AdeleRing (𝓞 L) L)) ⟨ht10, ht01⟩
    | succ i ih =>
        rw [Function.iterate_succ_apply', hbcσ]
        exact ih.map _
  have hNd : IsDiag (AutomorphicForm.baseChangeGL K L (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ)) := by
    simp only [AutomorphicForm.normString, map_list_prod, List.map_map]
    refine IsDiag.list_prod fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact hiter i
  have hreg' : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.baseChangeGL K L (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ)) :=
    isRegularSemisimple_map' _ hreg
  have hTdiag : ∀ r : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
      IsDiag (AutomorphicForm.baseChangeGL K L (r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) := fun r => by
    have hc := hle r.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    refine IsDiag.of_commute_of_isRegularSemisimple hreg' hNd ?_
    rw [← map_mul, ← map_mul, hc]

  have hWT : ∀ (r : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      (fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x)) = (fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) := by
    intro r x
    simp only [map_mul]
    exact hWinv _ (hTdiag r).1 (hTdiag r).2 _
  have hWc : Continuous fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => (fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) := hWLcont.comp hbc_cont

  have hF₁m : Measurable fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
      (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) : ℝ) : ℂ) :=
    (((hφw.comp hbc_cont).comp htwc).mul (Complex.continuous_ofReal.comp hWc)).measurable
  have hF₁T : ∀ (r : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) (x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
        (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) : ℝ) : ℂ)) ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x) =
      (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
        (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) : ℝ) : ℂ)) x := by
    intro r x
    have key1 : (r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ r = δ :=
      (AutomorphicForm.mem_sigmaCentralizer_iff_inv).1 r.2
    have h1 : ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x)⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x) =
        x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x := by
      calc ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x)⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x)
          = x⁻¹ * ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ r) *
              AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x := by
            simp only [mul_inv_rev, map_mul, mul_assoc]
        _ = x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x := by rw [key1]
    simp only [h1, hWT]
  have hF₁b : ∃ C : ℝ, ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K), ‖((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
      (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) : ℝ) : ℂ)‖ ≤ C := by
    obtain ⟨Dc, hDc, hsub⟩ :=
      AutomorphicForm.exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul K L σ δ hreg
        (tsupport ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L)) hφ's
    obtain ⟨Cφ, hCφ⟩ := hφws.exists_bound_of_continuous hφw
    obtain ⟨CW, hCW⟩ := hDc.exists_bound_of_continuousOn hWc.continuousOn
    have h0 : 0 ≤ Cφ := le_trans (norm_nonneg _) (hCφ 1)
    refine ⟨Cφ * max CW 0, fun x => ?_⟩
    by_cases hx : ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) = 0
    · rw [hx, zero_mul, norm_zero]
      exact mul_nonneg h0 (le_max_right _ _)
    · have hxD : x ∈ (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * Dc :=
        hsub (subset_tsupport _ hx)
      obtain ⟨r, hr, d, hd, rfl⟩ := Set.mem_mul.1 hxD
      rw [norm_mul, hWT ⟨r, hr⟩ d]
      refine mul_le_mul (hCφ _) ?_ (norm_nonneg _) h0
      rw [Complex.norm_real]
      exact (hCW d hd).trans (le_max_left _ _)

  have hswap := MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) hTc μ τ
    (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
      (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) : ℝ) : ℂ)) hF₁m hF₁b hF₁T s' s
    ⟨hs'S.1, hs'S.2.1, hs'S.2.2.1, fun x hx => hs'S.2.2.2 x (left_ne_zero_of_mul hx)⟩
    ⟨hsS.1, hsS.2.1, hsS.2.2.1, fun x hx => hsS.2.2.2 x (left_ne_zero_of_mul hx)⟩
  refine (congrArg (fun z : ℂ => ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * z) hswap).trans ?_

  have hint : (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) => ((fun g : AdelicGL2 (𝓞 L) L => φ (centralScalar (𝓞 L) L w₀ * g)) ∘ AutomorphicForm.baseChangeGL K L) (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) *
        (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) (AutomorphicForm.baseChangeGL K L x) : ℝ) : ℂ)) x * (s x : ℂ)) =
      fun x => (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) * (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) g : ℝ) : ℂ) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) (AutomorphicForm.baseChangeGL K L x) := by
    funext x
    simp only [Function.comp_apply, hconj, hsymm]
  rw [hint]
  have step1 := hμc (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) * (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) g : ℝ) : ℂ) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ))
  have hGc : Continuous (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) * (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) g : ℝ) : ℂ) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) :=
    ((hΦc w₀).mul (Complex.continuous_ofReal.comp hWLcont)).mul
      (Complex.continuous_ofReal.comp (hsc.comp (AutomorphicForm.baseChangeGLEquiv K L).symm.continuous))
  have hGs : HasCompactSupport (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) * (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) g : ℝ) : ℂ) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) := by
    have h1 : HasCompactSupport fun g : AdelicGL2 (𝓞 L) L =>
        (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ) :=
      (hsS.2.2.1.comp_homeomorph (AutomorphicForm.baseChangeGLEquiv K L).symm.toHomeomorph).comp_left
        Complex.ofReal_zero
    refine h1.mono fun g hg => ?_
    rw [Function.mem_support] at hg ⊢
    exact fun h0 => hg (by rw [h0, mul_zero])
  obtain ⟨-, -, hC0⟩ :=
    HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
      (adelicGLHaar (Fin 2) (𝓞 L) L) H hHcl μH (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) * (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) g : ℝ) : ℂ) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) hGc.measurable (hGc.integrable_of_hasCompactSupport hGs).2

  have hfibG : (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
      ∫ h : H, (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) * (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) g : ℝ) : ℂ) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * q.out) ∂μH) =
      fun q => ((cH / (cτ * cN) : ℝ) : ℂ) * ((((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) q.out : ℝ) : ℂ) *
        ∫ n : N1, φ ((q.out)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w₀) *
            AutomorphicForm.sigmaAdelicAct K L D σ q.out)) ∂μN) := by
    funext q
    have hq : ∀ h : H, (fun g : AdelicGL2 (𝓞 L) L =>
        φ (centralScalar (𝓞 L) L w₀ * (g⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ g)) * (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) g : ℝ) : ℂ) *
          (s ((AutomorphicForm.baseChangeGLEquiv K L).symm g) : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * q.out) =
        (((fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) q.out : ℝ) : ℂ) *
          (φ (centralScalar (𝓞 L) L w₀ * (((h : AdelicGL2 (𝓞 L) L) * q.out)⁻¹ * globalPoints (𝓞 L) L t *
            sigmaAdelicAct K L D σ ((h : AdelicGL2 (𝓞 L) L) * q.out))) *
            (s ((AutomorphicForm.baseChangeGLEquiv K L).symm ((h : AdelicGL2 (𝓞 L) L) * q.out)) : ℂ)) := by
      intro h
      have hh := (hH h).1 h.2
      have hWq : (fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) ((h : AdelicGL2 (𝓞 L) L) * q.out) = (fun g : AdelicGL2 (𝓞 L) L => -Real.log (NumberField.AdelicHeight.adelicHeight L g) - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * g))) q.out :=
        hWinv (h : AdelicGL2 (𝓞 L) L) hh.1 hh.2.1 q.out
      beta_reduce
      beta_reduce at hWq
      rw [hWq]
      ring
    rw [funext hq, integral_const_mul, hfib q.out]
    ring
  rw [hfibG, integral_const_mul] at hC0
  rw [hC0] at step1
  refine (congrArg (fun z : ℂ => ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * z) step1).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  conv_rhs => rw [← one_mul (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), _ ∂_)]
  congr 1
  have hne : ((cN : ℂ) * cτ * cH * cμ) ≠ 0 := by
    have h0 : (cN * cτ * cH * cμ : ℝ) ≠ 0 := by positivity
    exact_mod_cast h0
  push_cast
  field_simp
  exact div_self hne

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

    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)

    (cμ : ℝ) (hcμ : 0 < cμ)
    (hμc : ∀ F : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ x, F (AutomorphicForm.baseChangeGL K L x) ∂μ = cμ * ∫ g, F g ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
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
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK)) :
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
    ∀ (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ →
      (∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
            g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
          cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK)) →
    ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ), Continuous φ → HasCompactSupport φ →

    (∀ (w : (AdeleRing (𝓞 L) L)ˣ) (I : ℂ),
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
            AutomorphicForm.baseChangeGL K L) I →
      ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * I =
        (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH))) ∧

    (∀ (w : (AdeleRing (𝓞 L) L)ˣ) (J : ℂ),
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ
          (fun x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) =>
            -Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.baseChangeGL K L x))
              - Real.log (NumberField.AdelicHeight.adelicHeight L
                  (AutomorphicForm.adelicWeyl (𝓞 L) L * AutomorphicForm.baseChangeGL K L x)))
          δ τ
          ((fun g : AdelicGL2 (𝓞 L) L => φ (AutomorphicForm.centralScalar (𝓞 L) L w * g)) ∘
            AutomorphicForm.baseChangeGL K L) J →
      ((cN * cτ / (cH * cμ) : ℝ) : ℂ) * J =
        (∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) *
            (∫ n : N1, φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w) *
                  AutomorphicForm.sigmaAdelicAct K L D σ ((q.out : AdelicGL2 (𝓞 L) L)))) ∂μN)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH))) := by
  intro t ht10 ht01 hnorm δ hδ τ hτ hτc φ hφc hφs
  have hHcl : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)) := by assumption
  exact ⟨fun w₀ I hI => plain_part K L νZL D σ hgen H hHcl hH μH μ hμ cμ hcμ hμc νK cH hcH hHc cτ hcτ
      AK hAKc hAK μAK hμAK N1 hN1c hN1 μN cN hcN hNc t ht10 ht01 hnorm δ hδ τ hτ hτc φ hφc hφs w₀ I hI,
    fun w₀ J hJ => weighted_part K L νZL D σ hgen H hHcl hH μH μ hμ cμ hcμ hμc νK cH hcH hHc cτ hcτ
      AK hAKc hAK μAK hμAK N1 hN1c hN1 μN cN hcN hNc t ht10 ht01 hnorm δ hδ τ hτ hτc φ hφc hφs w₀ J hJ⟩

end S_AutomorphicForm_const_mul_eq_integral_haarQuotient_integral_ker_idelicNorm_centralScalar_of_isTwistedOrbitalIntegralOn_comp_baseChangeGL
end P2MW
export P2MW.S_AutomorphicForm_const_mul_eq_integral_haarQuotient_integral_ker_idelicNorm_centralScalar_of_isTwistedOrbitalIntegralOn_comp_baseChangeGL (solution)
