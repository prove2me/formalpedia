-- Prove2me | solution 1 for AutomorphicForm.setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/91f16498-8fcf-55ee-83ce-271913d3390d

import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
import Theorems.Thm_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.cpowChar_apply_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "MeasureTheory TopologicalSpace NumberField AutomorphicForm~continuous_sigmaTensor"
open scoped TensorProduct TensorProduct.RightActions Pointwise NNReal ENNReal

noncomputable section

namespace P2mPerClassCentral

section GLGeneral

variable {A B : Type*} [CommRing A] [CommRing B]

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem map_scalar (f : A →+* B) (c : Aˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : A →* B) c) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : Aˣ → GL (Fin 2) A) := by
  intro a b h
  have := congrArg (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) 0 0) h
  refine Units.ext ?_
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this

theorem scalar_mul_comm (c : Aˣ) (g : GL (Fin 2) A) : sc c * g = g * sc c := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (c : A) * (g : Matrix (Fin 2) (Fin 2) A) =
    (g : Matrix (Fin 2) (Fin 2) A) * Matrix.scalar (Fin 2) (c : A)
  exact (Matrix.scalar_commute (c : A) (fun r => Commute.all _ r) _).eq

theorem conj_scalar (c : Aˣ) (h : GL (Fin 2) A) : h⁻¹ * sc c * h = sc c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem continuous_generalLinearGroup_map [TopologicalSpace A] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Continuous.matrix_map Units.continuous_val hf
  · exact Continuous.matrix_map Units.continuous_coe_inv hf

end GLGeneral

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

omit [IsTopologicalRing A] in
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
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

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

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def transportEquiv : (L ⊗[K] AdeleRing (𝓞 K) K) ≃+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L))

theorem continuous_transportEquiv :
    Continuous (transportEquiv K L) ∧ Continuous (transportEquiv K L).symm := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L
      (M4aHerbrand.Bridge.continuous_genuineβ K L) (M4aHerbrand.Bridge.genuineTensorEquiv K L)
  let eLin : (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
    (TensorProduct.RightActions.Module.TensorProduct.comm K (AdeleRing (𝓞 K) K) L).symm.trans
      (M4aHerbrand.Bridge.genuineTensorEquiv K L).toLinearEquiv
  have hfun : ∀ x, eLin x = transportEquiv K L x := by
    intro x
    rfl
  let eC := IsModuleTopology.continuousLinearEquiv eLin
  have h1 : Continuous (transportEquiv K L) := by
    have : Continuous eC := eC.continuous
    exact this.congr hfun
  have h2 : Continuous (transportEquiv K L).symm := by
    have hc : Continuous eC.symm := eC.symm.continuous
    refine hc.congr fun y => ?_
    apply (transportEquiv K L).injective
    rw [RingEquiv.apply_symm_apply]
    show transportEquiv K L (eLin.symm y) = y
    rw [← hfun, LinearEquiv.apply_symm_apply]
  exact ⟨h1, h2⟩

noncomputable abbrev GE :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) →* AutomorphicForm.AdelicGL2 (𝓞 L) L :=
  Matrix.GeneralLinearGroup.map (transportEquiv K L).toRingHom

noncomputable abbrev GEi :
    AutomorphicForm.AdelicGL2 (𝓞 L) L →* GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (transportEquiv K L).symm.toRingHom

noncomputable abbrev Eu : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (transportEquiv K L).toRingHom.toMonoidHom

noncomputable abbrev Eui : (AdeleRing (𝓞 L) L)ˣ →* (L ⊗[K] AdeleRing (𝓞 K) K)ˣ :=
  Units.map (transportEquiv K L).symm.toRingHom.toMonoidHom

theorem GEi_GE (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) : GEi K L (GE K L g) = g := by
  ext i j
  exact (transportEquiv K L).symm_apply_apply (g.val i j)

theorem GE_GEi (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) : GE K L (GEi K L g) = g := by
  ext i j
  exact (transportEquiv K L).apply_symm_apply (g.val i j)

theorem Eu_Eui (z : (AdeleRing (𝓞 L) L)ˣ) : Eu K L (Eui K L z) = z :=
  Units.ext ((transportEquiv K L).apply_symm_apply (z : AdeleRing (𝓞 L) L))

theorem Eui_Eu (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : Eui K L (Eu K L c) = c :=
  Units.ext ((transportEquiv K L).symm_apply_apply (c : L ⊗[K] AdeleRing (𝓞 K) K))

theorem GE_injective : Function.Injective (GE K L) :=
  Function.LeftInverse.injective (GEi_GE K L)

theorem Eu_injective : Function.Injective (Eu K L) :=
  Function.LeftInverse.injective (Eui_Eu K L)

theorem continuous_GE : Continuous (GE K L) :=
  continuous_generalLinearGroup_map _ (continuous_transportEquiv K L).1

theorem continuous_GEi : Continuous (GEi K L) :=
  continuous_generalLinearGroup_map _ (continuous_transportEquiv K L).2

theorem GE_scalar (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    GE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.centralScalar (𝓞 L) L (Eu K L c) :=
  map_scalar _ _

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem GE_sigmaGL (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    GE K L (AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ g) =
      AutomorphicForm.sigmaAdelicAct K L D σ (GE K L g) :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).1 σ g

theorem GE_toTensorGL (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    GE K L (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.1 g

theorem GE_map_includeLeft (δ : GL (Fin 2) L) :
    GE K L (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ) =
      AutomorphicForm.globalPoints (𝓞 L) L δ :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.2 δ

theorem Eu_sigma (σ : L ≃ₐ[K] L) (x : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Eu K L (Units.map (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ :
      L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] AdeleRing (𝓞 K) K) x) = D.unitsAct σ (Eu K L x) := by
  have h1 := GE_sigmaGL K L D σ (Matrix.GeneralLinearGroup.scalar (Fin 2) x)
  change GE K L (Matrix.GeneralLinearGroup.map (AutomorphicForm.sigmaTensor K L (AdeleRing (𝓞 K) K) σ)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) =
    Matrix.GeneralLinearGroup.map (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom
      (GE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) x)) at h1
  rw [map_scalar, map_scalar, map_scalar, map_scalar] at h1
  have h2 := scalar_injective h1
  refine (Units.ext ?_ : Eu K L _ = _)
  have h3 := congrArg (fun z : (AdeleRing (𝓞 L) L)ˣ => (z : AdeleRing (𝓞 L) L)) h2
  simp at h3
  exact h3

theorem Eu_includeRight (a : (AdeleRing (𝓞 K) K)ˣ) :
    Eu K L (Units.map (Algebra.TensorProduct.includeRight :
      AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom.toMonoidHom a) =
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a := by
  have h1 := GE_toTensorGL K L (Matrix.GeneralLinearGroup.scalar (Fin 2) a)
  change GE K L (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight :
      AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = _ at h1
  rw [map_scalar, map_scalar, map_scalar] at h1
  exact scalar_injective h1

end Transport

section NormString

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (θ : L ≃ₐ[K] L)

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

noncomputable abbrev sigmaUnits : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ :=
  Units.map (AutomorphicForm.sigmaTensor K L A θ : L ⊗[K] A →* L ⊗[K] A)

noncomputable def galNorm (n : ℕ) : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ where
  toFun x := ∏ i ∈ Finset.range n, (sigmaUnits K L A θ)^[i] x
  map_one' := by simp [iterate_map_one]
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => iterate_map_mul _ i x y

theorem galNorm_apply (n : ℕ) (x : (L ⊗[K] A)ˣ) :
    galNorm K L A θ n x = ∏ i ∈ Finset.range n, (sigmaUnits K L A θ)^[i] x := rfl

theorem list_prod_range_eq_finset_prod {M : Type*} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).prod = ∏ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

theorem sigmaGL_scalar (c : (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A θ (sc c) = sc (sigmaUnits K L A θ c) :=
  map_scalar _ _

theorem iterate_sigmaGL_scalar (i : ℕ) (c : (L ⊗[K] A)ˣ) :
    (AutomorphicForm.sigmaGL K L A θ)^[i] (sc c) = sc ((sigmaUnits K L A θ)^[i] c) := by
  induction i generalizing c with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sigmaGL_scalar, ih]

theorem list_prod_map_mul_of_comm {M : Type*} [Monoid M] (l : List ℕ) (f g : ℕ → M)
    (hg : ∀ i x, g i * x = x * g i) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih]

      have hcomm : g a * (l.map f).prod = (l.map f).prod * g a := hg a _
      calc f a * g a * ((l.map f).prod * (l.map g).prod)
          = f a * (g a * (l.map f).prod) * (l.map g).prod := by simp only [mul_assoc]
        _ = f a * ((l.map f).prod * g a) * (l.map g).prod := by rw [hcomm]
        _ = f a * (l.map f).prod * (g a * (l.map g).prod) := by simp only [mul_assoc]

theorem normString_mul_scalar (a : GL (Fin 2) (L ⊗[K] A)) (c : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A θ (a * sc c) =
      AutomorphicForm.normString K L A θ a * sc (galNorm K L A θ (Module.finrank K L) c) := by
  unfold AutomorphicForm.normString
  have hfun : (fun i => (⇑(AutomorphicForm.sigmaGL K L A θ))^[i] (a * sc c)) =
      fun i => (⇑(AutomorphicForm.sigmaGL K L A θ))^[i] a * sc ((sigmaUnits K L A θ)^[i] c) := by
    funext i
    rw [iterate_map_mul, iterate_sigmaGL_scalar]
  rw [hfun, list_prod_map_mul_of_comm _ _ _ (fun i x => scalar_mul_comm _ x)]
  congr 1
  rw [galNorm_apply, ← list_prod_range_eq_finset_prod, map_list_prod, List.map_map]
  rfl

theorem sigmaTensor_includeLeft (l : L) :
    AutomorphicForm.sigmaTensor K L A θ (l ⊗ₜ[K] (1 : A)) = θ l ⊗ₜ[K] (1 : A) := by
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem sigmaGL_map_includeLeft (g : GL (Fin 2) L) :
    AutomorphicForm.sigmaGL K L A θ (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) g) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (Matrix.GeneralLinearGroup.map (θ : L →+* L) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show AutomorphicForm.sigmaTensor K L A θ (Algebra.TensorProduct.includeLeftRingHom (g i j)) =
    Algebra.TensorProduct.includeLeftRingHom ((θ : L →+* L) (g i j))
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    sigmaTensor_includeLeft]
  rfl

theorem normString_map_includeLeft (δ₀ : GL (Fin 2) L) :
    AutomorphicForm.normString K L A θ (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (θ : L →+* L))
          (Module.finrank K L) δ₀) := by
  unfold AutomorphicForm.normString
  rw [← LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range, LT.TwistedNorm.sigmaNormPow_def]
  exact (LT.TwistedNorm.hom_sigmaPartialNorm (Matrix.GeneralLinearGroup.map (θ : L →+* L))
    (AutomorphicForm.sigmaGL K L A θ)
    (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A))
    (fun x => (sigmaGL_map_includeLeft K L A θ x).symm) δ₀ (Module.finrank K L)).symm

theorem toTensorGL_scalar (a : Aˣ) :
    AutomorphicForm.toTensorGL K L A (sc a) =
      sc (Units.map (Algebra.TensorProduct.includeRight :
        A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom a) := by
  unfold AutomorphicForm.toTensorGL
  rw [map_scalar]
  rfl

theorem map_includeLeft_scalar_algebraMap (b : Kˣ) :
    Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (sc (Units.map ((algebraMap K L : K →+* L) : K →* L) b)) =
      AutomorphicForm.toTensorGL K L A (sc (Units.map (algebraMap K A : K →* A) b)) := by
  rw [map_scalar, toTensorGL_scalar]
  congr 1
  refine Units.ext ?_
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.commutes,
    Algebra.TensorProduct.algebraMap_apply]

end NormString

section NormStringAdelic

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (θ : L ≃ₐ[K] L)

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

theorem Eu_iterate_sigma (i : ℕ) (x : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Eu K L ((sigmaUnits K L (AdeleRing (𝓞 K) K) θ)^[i] x) = (D.unitsAct θ)^[i] (Eu K L x) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      exact Eu_sigma K L D θ _

omit [FiniteDimensional K L] [IsGalois K L] in
theorem unitsAct_iterate (i : ℕ) (w : (AdeleRing (𝓞 L) L)ˣ) :
    (D.unitsAct θ)^[i] w = D.unitsAct (θ ^ i) w := by
  induction i generalizing w with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih, pow_succ', map_mul, MulAut.mul_apply]

theorem Eu_galNorm (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers θ)
    (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Eu K L (galNorm K L (AdeleRing (𝓞 K) K) θ (Module.finrank K L) c) =
      Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom
        ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (Eu K L c)) := by
  set D₀ := M4aHerbrand.GenuineDescent.genuineDescentDatum K L
  obtain ⟨-, -, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D₀
  rw [← hprod, LT.TwistedNorm.prod_algEquiv_eq_prod_range_of_generator hgen, galNorm_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Eu_iterate_sigma K L D₀, unitsAct_iterate]

theorem galNorm_eq_includeRight_idelicNorm (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers θ)
    (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    galNorm K L (AdeleRing (𝓞 K) K) θ (Module.finrank K L) c =
      Units.map (Algebra.TensorProduct.includeRight :
        AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K).toRingHom.toMonoidHom
        ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (Eu K L c)) := by
  apply Eu_injective K L
  rw [Eu_galNorm K L θ hgen, Eu_includeRight]

theorem idelicNorm_unitsAct (τ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (D.unitsAct τ z) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z := by
  obtain ⟨hβinj, -, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm K L D
  have h : ∏ ρ : L ≃ₐ[K] L, D.unitsAct ρ (D.unitsAct τ z) = ∏ ρ : L ≃ₐ[K] L, D.unitsAct ρ z := by
    refine (Fintype.prod_equiv (Equiv.mulRight τ) _ _ fun ρ => ?_)
    show D.unitsAct ρ (D.unitsAct τ z) = D.unitsAct (ρ * τ) z
    rw [map_mul, MulAut.mul_apply]
  rw [hprod, hprod] at h
  have h1 := congrArg (fun w : (AdeleRing (𝓞 L) L)ˣ => (w : AdeleRing (𝓞 L) L)) h
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h1
  exact Units.ext (hβinj h1)

theorem normString_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers θ)
    (δ₀ : GL (Fin 2) L) (b₀ : Kˣ)
    (hδ₀ : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (θ : L →+* L))
        (Module.finrank K L) δ₀ = sc (Units.map ((algebraMap K L : K →+* L) : K →* L) b₀))
    (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) θ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * sc c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b₀ *
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (Eu K L c))) := by
  rw [normString_mul_scalar, normString_map_includeLeft, hδ₀, map_includeLeft_scalar_algebraMap,
    galNorm_eq_includeRight_idelicNorm K L θ hgen, map_mul, map_mul]
  congr 1
  change _ = AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (sc _)
  rw [toTensorGL_scalar]

end NormStringAdelic

section CentralNorm

open LT.TwistedNorm

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)
local notation "σ'" => Matrix.GeneralLinearGroup.map (σ : L →+* L)
local notation "Nσ" => sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L)
local notation "ιF" => Units.map ((algebraMap F L : F →+* L) : F →* L)

omit [FiniteDimensional F L] [IsGalois F L] [Algebra F L] in

theorem eq_scalar_of_isConj {γ : GL (Fin 2) F} {b : Fˣ} (h : IsConj γ (sc b)) : γ = sc b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  calc γ = c⁻¹ * (c * γ * c⁻¹) * c := by group
    _ = sc b := by rw [hc, conj_scalar]

theorem sigmaNormPow_eq_scalar_of_normClassMap_eq (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {b : Fˣ}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk (sc b)) :
    Nσ δ = sc (ιF b) := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at h
  have hrep : normRep hgen δ = sc b := eq_scalar_of_isConj h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  rw [hrep, map_scalar] at hP
  calc Nσ δ = P * (P⁻¹ * Nσ δ * P) * P⁻¹ := by group
    _ = sc (ιF b) := by
        rw [hP]
        have := conj_scalar (Units.map ((algebraMap F L : F →+* L) : F →* L) b) P⁻¹
        rwa [inv_inv] at this

end CentralNorm

section Discrete

variable (F : Type) [Field F] [NumberField F]

theorem discreteTopology_globalPoints_range :
    DiscreteTopology ↥((AutomorphicForm.globalPoints (𝓞 F) F).range) := by
  set ι := algebraMap F (AdeleRing (𝓞 F) F) with hι
  have hιinj : Function.Injective ι := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
  obtain ⟨C₁, hC₁c, hC₁⟩ := exists_compact_mem_nhds (1 : AdeleRing (𝓞 F) F)
  obtain ⟨C₀, hC₀c, hC₀⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 F) F)
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F (hC₁c.union hC₀c)
  set R₁ : Set (AdeleRing (𝓞 F) F) := ι '' {ξ : F | ι ξ ∈ C₁ ∪ C₀ ∧ ξ ≠ 1} with hR₁
  set R₀ : Set (AdeleRing (𝓞 F) F) := ι '' {ξ : F | ι ξ ∈ C₁ ∪ C₀ ∧ ξ ≠ 0} with hR₀
  have hR₁f : R₁.Finite := (hfin.subset fun ξ hξ => hξ.1).image _
  have hR₀f : R₀.Finite := (hfin.subset fun ξ hξ => hξ.1).image _
  set U₁ : Set (AdeleRing (𝓞 F) F) := interior C₁ \ R₁ with hU₁
  set U₀ : Set (AdeleRing (𝓞 F) F) := interior C₀ \ R₀ with hU₀
  have hU₁o : IsOpen U₁ := isOpen_interior.sdiff hR₁f.isClosed
  have hU₀o : IsOpen U₀ := isOpen_interior.sdiff hR₀f.isClosed
  have h1U : (1 : AdeleRing (𝓞 F) F) ∈ U₁ := by
    refine ⟨mem_interior_iff_mem_nhds.2 hC₁, ?_⟩
    rintro ⟨ξ, ⟨-, hne⟩, h1⟩
    exact hne (hιinj (h1.trans (map_one _).symm))
  have h0U : (0 : AdeleRing (𝓞 F) F) ∈ U₀ := by
    refine ⟨mem_interior_iff_mem_nhds.2 hC₀, ?_⟩
    rintro ⟨ξ, ⟨-, hne⟩, h0⟩
    exact hne (hιinj (h0.trans (map_zero _).symm))

  have hdiag : ∀ ξ : F, ι ξ ∈ U₁ → ξ = 1 := by
    intro ξ hξ
    by_contra hne
    exact hξ.2 ⟨ξ, ⟨Or.inl (interior_subset hξ.1), hne⟩, rfl⟩
  have hoff : ∀ ξ : F, ι ξ ∈ U₀ → ξ = 0 := by
    intro ξ hξ
    by_contra hne
    exact hξ.2 ⟨ξ, ⟨Or.inr (interior_subset hξ.1), hne⟩, rfl⟩
  let ent : Fin 2 → Fin 2 → AutomorphicForm.AdelicGL2 (𝓞 F) F → AdeleRing (𝓞 F) F :=
    fun i j g => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
  have hent : ∀ i j, Continuous (ent i j) := fun i j => Units.continuous_val.matrix_elem i j
  set U : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F) :=
    ent 0 0 ⁻¹' U₁ ∩ ent 1 1 ⁻¹' U₁ ∩ ent 0 1 ⁻¹' U₀ ∩ ent 1 0 ⁻¹' U₀ with hU
  have hUo : IsOpen U :=
    (((hU₁o.preimage (hent 0 0)).inter (hU₁o.preimage (hent 1 1))).inter
      (hU₀o.preimage (hent 0 1))).inter (hU₀o.preimage (hent 1 0))
  apply discreteTopology_of_isOpen_singleton_one
  have hset : ({1} : Set ↥((AutomorphicForm.globalPoints (𝓞 F) F).range)) =
      (fun p : ↥((AutomorphicForm.globalPoints (𝓞 F) F).range) =>
        ((p : AutomorphicForm.AdelicGL2 (𝓞 F) F))) ⁻¹' U := by
    ext p
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · show ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0) ∈ U₁
        simpa using h1U
      · show ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) ∈ U₁
        simpa using h1U
      · show ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1) ∈ U₀
        simpa using h0U
      · show ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) ∈ U₀
        simpa using h0U
    · intro hp
      obtain ⟨γ, hγ⟩ := p.2
      have hval : ∀ i j, ent i j (p : AutomorphicForm.AdelicGL2 (𝓞 F) F) = ι (γ i j) := by
        intro i j
        rw [← hγ]
        rfl
      obtain ⟨⟨⟨h00, h11⟩, h01⟩, h10⟩ := hp
      have e00 : γ 0 0 = 1 := hdiag _ (by rw [← hval]; exact h00)
      have e11 : γ 1 1 = 1 := hdiag _ (by rw [← hval]; exact h11)
      have e01 : γ 0 1 = 0 := hoff _ (by rw [← hval]; exact h01)
      have e10 : γ 1 0 = 0 := hoff _ (by rw [← hval]; exact h10)
      have hγ1 : γ = 1 := by
        refine Units.ext (Matrix.ext fun i j => ?_)
        fin_cases i <;> fin_cases j
        · simpa using e00
        · simpa using e01
        · simpa using e10
        · simpa using e11
      apply Subtype.ext
      show (p : AutomorphicForm.AdelicGL2 (𝓞 F) F) = 1
      rw [← hγ, hγ1, map_one]
  rw [hset]
  exact hUo.preimage continuous_subtype_val

end Discrete

section Twisted

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin 2)

abbrev inclA : L →+* L ⊗[K] AdeleRing (𝓞 K) K := Algebra.TensorProduct.includeLeftRingHom

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

abbrev Tw (θ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) θ (δA K L δ₀ c)

abbrev ΓTw (θ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (Tw K L θ δ₀ c) :=
  ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (θ : L →+* L)) δ₀).map
    (Matrix.GeneralLinearGroup.map (inclA K L))).subgroupOf (Tw K L θ δ₀ c)

theorem exists_isTwistedSectionFnOn_of_forall_ne_scalar (h2 : Module.finrank K L = 2)
    (θ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers θ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) θ (δA K L δ₀ c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (zz : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (θ : L →+* L) x ≠ sc zz)
    (τ' : Measure (Tw K L θ δ₀ c)) [τ'.IsHaarMeasure] [τ'.IsMulRightInvariant]
    (ψ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (hψ : HasCompactSupport ψ) :
    ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
      IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) θ (δA K L δ₀ c) τ' ψ w := by
  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_tensor K L (AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_tensor K L (AdeleRing (𝓞 K) K)
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI := secondCountableTopology_tensor K L (AdeleRing (𝓞 K) K)
  haveI := isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := secondCountableTopology_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := locallyCompactSpace_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    borelSpace_glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (Tw K L θ δ₀ c) := ⟨rfl⟩
  have hTc := isClosed_twistedCentralizer K L (AdeleRing (𝓞 K) K) θ (δA K L δ₀ c)
  obtain ⟨D, hD, hsub⟩ :=
    AutomorphicForm.exists_isCompact_setOf_twistedConj_mem_subset_twistedCentralizer_mul_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 θ hgen δ₀ c u hN hns (tsupport ψ) hψ
  have hE : {x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
      ψ (x⁻¹ * δA K L δ₀ c * sigmaGL K L (AdeleRing (𝓞 K) K) θ x) ≠ 0} ⊆
      (Tw K L θ δ₀ c : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D :=
    fun x hx => hsub (subset_tsupport ψ hx)
  obtain ⟨w, hw0, hwm, hwc, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (Tw K L θ δ₀ c) hTc τ' hD hE
  exact ⟨w, hw0, hwm, hwc, fun x hx => hw1 x hx⟩

end Twisted

end P2mPerClassCentral

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain P2mPerClassCentral
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

set_option maxHeartbeats 8000000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h2 : Module.finrank K L = 2)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (c₀ : NNReal)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hcent : ∀ (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u) →
      ∀ (τ : Measure (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))))
        (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
        τ.IsHaarMeasure → τ'.IsHaarMeasure →
      ∀ C : ENNReal, C ≠ 0 → C ≠ ⊤ →
        (∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
          IsFundamentalDomain
            (((AutomorphicForm.sigmaCentralizer
                (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom :
                    L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
              (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
                (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom :
                      L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                  Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det
                (Matrix.GeneralLinearGroup.map
                  (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                    (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                  (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
              C * ENNReal.ofReal (Real.log (b / a))) →
        (∀ D : Set (Subgroup.centralizer
            ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))),
          IsFundamentalDomain
            (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
              (Subgroup.centralizer
                ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K)))).op D τ →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
              (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a))) →
      ∀ I I' : ℂ,
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ.symm
          (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
            (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
            (adelicGLHaar (Fin 2) (𝓞 L) L))
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
          (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I' →
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I' = I)
    (C_H : ℝ≥0∞) (hC0 : C_H ≠ 0) (hCt : C_H ≠ ⊤)
    (hC_H : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K),
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
      adelicGLHaar (Fin 2) (𝓞 K) K Φ = C_H * ENNReal.ofReal (Real.log (b / a)))
    (δ₀ : GL (Fin 2) L) (b₀ : Kˣ)
    (hδ₀ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) b₀))
    (hns : ∀ (x : GL (Fin 2) L) (e : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) e)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (((c₀ : ℝ) / (Module.finrank K L : ℝ) * (C_H * ENNReal.ofReal (Real.log (β / α))).toReal : ℝ) : ℂ) *
        f (AutomorphicForm.centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b₀ *
            (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) := by
  classical

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
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 K) K) :=
    NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

  set θ : L ≃ₐ[K] L := σ.symm with hθ
  set ℓ : ℕ := Module.finrank K L with hℓ
  set z' : (AdeleRing (𝓞 L) L)ˣ := D.unitsAct θ z with hz'
  set c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ := Eui K L z' with hc
  have hEc : Eu K L c = z' := Eu_Eui K L z'
  set u : (AdeleRing (𝓞 K) K)ˣ :=
    Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b₀ *
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z with hu

  have hN0 : LT.TwistedNorm.sigmaNormPow (Matrix.GeneralLinearGroup.map (θ : L →+* L)) ℓ δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((algebraMap K L : K →+* L) : K →* L) b₀) :=
    sigmaNormPow_eq_scalar_of_normClassMap_eq hgen hδ₀
  have hNz : (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z' =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z :=
    idelicNorm_unitsAct K L D θ z
  have hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) θ (δA K L δ₀ c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u) := by
    have h := normString_eq K L θ hgen δ₀ b₀ hN0 c
    rw [hEc, hNz] at h
    exact h

  have hTc := isClosed_twistedCentralizer K L (AdeleRing (𝓞 K) K) θ (δA K L δ₀ c)
  haveI : LocallyCompactSpace (Tw K L θ δ₀ c) := hTc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : BorelSpace (Tw K L θ δ₀ c) := ⟨rfl⟩
  set τ' : Measure (Tw K L θ δ₀ c) := Measure.haar with hτ'def
  haveI hτ'H : τ'.IsHaarMeasure := by rw [hτ'def]; infer_instance
  have hpack : τ'.IsMulRightInvariant ∧
      (∃ CB : ℝ≥0∞, CB ≠ 0 ∧ CB ≠ ⊤ ∧
        ∀ D' : Set (Tw K L θ δ₀ c), IsFundamentalDomain (ΓTw K L θ δ₀ c).op D' τ' →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det (GE K L
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
              CB * ENNReal.ofReal (Real.log (b / a))) ∧
      (∀ ψ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ, HasCompactSupport ψ →
        ∃ w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ,
          AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) θ (δA K L δ₀ c) τ' ψ w) := by
    have hns' : ∀ (x : GL (Fin 2) L) (zz : Lˣ),
        x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (θ : L →+* L) x ≠
          Matrix.GeneralLinearGroup.scalar (Fin 2) zz := hns
    haveI hri : τ'.IsMulRightInvariant :=
      AutomorphicForm.isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
        K L h2 θ hgen (δA K L δ₀ c) u hN τ' hτ'H
    refine ⟨hri, ?_, fun ψ hψ => ?_⟩
    · exact AutomorphicForm.exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
        K L h2 θ hgen δ₀ c u hN hns' τ'
    · exact exists_isTwistedSectionFnOn_of_forall_ne_scalar K L h2 θ hgen δ₀ c u hN hns' τ' ψ hψ
  obtain ⟨hri, ⟨CB, hCB0, hCBt, hcovL⟩, hsect⟩ := hpack
  haveI := hri

  haveI : DiscreteTopology (ΓTw K L θ δ₀ c) := by
    haveI := discreteTopology_globalPoints_range L
    have hmem : ∀ γ : ΓTw K L θ δ₀ c,
        GE K L ((γ : Tw K L θ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∈
          (AutomorphicForm.globalPoints (𝓞 L) L).range := by
      intro γ
      have hγ := γ.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
      obtain ⟨g₁, -, hg₁⟩ := hγ
      refine ⟨g₁, ?_⟩
      rw [← hg₁, GE_map_includeLeft]
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : ΓTw K L θ δ₀ c => (⟨GE K L ((γ : Tw K L θ δ₀ c) :
        GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), hmem γ⟩ :
          ↥((AutomorphicForm.globalPoints (𝓞 L) L).range))) ?_ ?_
    · exact ((continuous_GE K L).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    · intro a b hab
      have hab' := congrArg (fun p : ↥((AutomorphicForm.globalPoints (𝓞 L) L).range) =>
        (p : AutomorphicForm.AdelicGL2 (𝓞 L) L)) hab
      exact Subtype.ext (Subtype.ext (GE_injective K L hab'))
  haveI : SecondCountableTopology (Tw K L θ δ₀ c) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨D', -, -, hD'all⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology (ΓTw K L θ δ₀ c)
      inferInstance
  have hD' : IsFundamentalDomain (ΓTw K L θ δ₀ c).op D' τ' := hD'all τ'

  let eH : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ AutomorphicForm.AdelicGL2 (𝓞 L) L :=
    { toFun := GE K L
      invFun := GEi K L
      left_inv := GEi_GE K L
      right_inv := GE_GEi K L
      continuous_toFun := continuous_GE K L
      continuous_invFun := continuous_GEi K L }
  have hφE : HasCompactSupport (φ ∘ GE K L) := hφc.comp_homeomorph eH
  obtain ⟨w, hw⟩ := hsect (φ ∘ GE K L) hφE
  have hTU :=
    AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
      K L D θ δ₀ c τ' D' hD' α β hα Ψ hΨ φ hφ.measurable w hw

  have hℓpos : 0 < ℓ := Module.finrank_pos
  have hℓC0 : (ℓ : ℝ≥0∞) * CB ≠ 0 := mul_ne_zero (by exact_mod_cast hℓpos.ne') hCB0
  have hℓCt : (ℓ : ℝ≥0∞) * CB ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top ℓ) hCBt
  obtain ⟨τ, hτH, hτR, -, hcovK, hOI⟩ :=
    AutomorphicForm.exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
      K C_H hC0 hCt hC_H u ((ℓ : ℝ≥0∞) * CB) hℓC0 hℓCt

  set μL : Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    Measure.map (GEi K L) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) with hμL
  set I' : ℂ := ∫ y, (φ ∘ GE K L) (y⁻¹ * δA K L δ₀ c *
      AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) θ y) * (w y : ℂ) ∂μL with hI'
  set I : ℂ := (((c₀ : ℝ) * (C_H / ((ℓ : ℝ≥0∞) * CB)).toReal : ℝ) : ℂ) *
    f (AutomorphicForm.centralScalar (𝓞 K) K u) with hIdef
  have hTOI : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) θ μL (δA K L δ₀ c)
      τ' (φ ∘ GE K L) I' := ⟨w, hw, rfl⟩
  have hOI' : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K)
      (c₀ • NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
      (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I := (hOI c₀ f I).2 rfl
  have hII : I' = I :=
    hcent δ₀ c u hN τ τ' hτH hτ'H CB hCB0 hCBt hcovL hcovK I I' hTOI hOI'

  have hGEc : GE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.centralScalar (𝓞 L) L z' := by rw [GE_scalar, hEc]
  have hint : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D θ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) =
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D θ x * GE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := by
    intro x
    congr 1
    have hσz : AutomorphicForm.sigmaAdelicAct K L D θ (AutomorphicForm.centralScalar (𝓞 L) L z) =
        AutomorphicForm.centralScalar (𝓞 L) L z' := by
      ext i j
      change (D.act θ : RingAut (AdeleRing (𝓞 L) L)).toRingHom
          (((AutomorphicForm.centralScalar (𝓞 L) L z : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) =
        ((AutomorphicForm.centralScalar (𝓞 L) L z' : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
      simp only [AutomorphicForm.centralScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply]
      split_ifs
      · rfl
      · exact map_zero _
    rw [map_mul, hσz, hGEc]
    change x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z' * AutomorphicForm.sigmaAdelicAct K L D θ x) =
      x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D θ x *
        Matrix.GeneralLinearGroup.scalar (Fin 2) z'
    rw [scalar_mul_comm]
    simp only [mul_assoc]
  have hLHS : ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D θ x * GE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        ∂((NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
    rw [Measure.restrict_restrict_of_subset hΨs]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hint x)
  rw [hLHS]
  erw [hTU]

  have hvol : τ'.real (D' ∩ {t : Tw K L θ δ₀ c | NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (GE K L
        (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc α β}) =
      (CB * ENNReal.ofReal (Real.log (β / α))).toReal := by
    rw [measureReal_def, hcovL D' hD' α β hα hαβ.le]
  change ((τ'.real (D' ∩ {t : Tw K L θ δ₀ c | NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (GE K L
        (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc α β}) : ℝ) : ℂ) * I' = _
  rw [hvol, hII, hIdef, ← mul_assoc, ← Complex.ofReal_mul]

  have hCBr : 0 < CB.toReal := ENNReal.toReal_pos hCB0 hCBt
  have hℓr : (0 : ℝ) < ℓ := Nat.cast_pos.2 hℓpos
  have hreal : (CB * ENNReal.ofReal (Real.log (β / α))).toReal *
      ((c₀ : ℝ) * (C_H / ((ℓ : ℝ≥0∞) * CB)).toReal) =
      (c₀ : ℝ) / (ℓ : ℝ) * (C_H * ENNReal.ofReal (Real.log (β / α))).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_mul]
    field_simp
  rw [hreal]

end S_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_forall_ne_scalar_of_finrank_eq_two (solution)
