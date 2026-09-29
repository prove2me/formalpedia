-- Prove2me | solution 1 for AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a5d87794-9169-5274-8e1b-283addf37c4f

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
import Theorems.Thm_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf
import Theorems.Thm_AutomorphicForm_areMatchingArch_central_transfer_of_scalar
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicHaar NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArchHom tensorPlaceHom tensorArch tensorPlace baseChangeGL tensorArch_toTensorGL tensorPlace_toTensorGL tensorArchHom_sigmaTensor tensorPlaceHom_sigmaTensor semiLocalHomeomorph_eq isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel toTensorGL semiLocalIntegers semiLocalIntegers_eq_preimage IsSemiLocalTestFn semiLocalIntegralSet isOpen_semiLocalIntegralSet isSemiLocalTestFn_indicator_semiLocalIntegralSet semiLocalHaar sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer twistedCentralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsTwistedOrbitalIntegralOn Coupled IsTwistedOrbitalIntegral AreMatchingLocal archHaarK archHaarL archIdentGL AreMatchingArch IsSemiLocalFactorization IsUnitFactorization IsLocalTestFn localIntegralSet mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocalTestFn_indicator_localIntegralSet localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet localCentralizer IsSectionFn IsOrbitalIntegral AdelicGL2 centralScalar sigmaCentralizer mem_sigmaCentralizer_iff exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf areMatchingArch_central_transfer_of_scalar isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing"
namespace CentralCoupled
p2m_open "AutomorphicForm"

section LinearAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

abbrev sc (c : Rˣ) : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm (c : Rˣ) (g : GL (Fin 2) R) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem conj_scalar (c : Rˣ) (g : GL (Fin 2) R) : g⁻¹ * sc c * g = sc c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem centralizer_scalar_eq_top (c : Rˣ) :
    Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact (scalar_mul_comm c g).symm

theorem map_scalar (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : R →* S) c) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) R) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

def unipUpper : GL (Fin 2) R :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩

def unipLower : GL (Fin 2) R :=
  ⟨!![1, 0; 1, 1], !![1, 0; -1, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩

@[scoped simp] theorem coe_unipUpper : ((unipUpper : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![1, 1; 0, 1] := rfl

@[scoped simp] theorem coe_unipLower : ((unipLower : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![1, 0; 1, 1] := rfl

theorem entries_of_commute_unip (M : Matrix (Fin 2) (Fin 2) R)
    (h₁ : !![(1 : R), 1; 0, 1] * M = M * !![(1 : R), 1; 0, 1])
    (h₂ : !![(1 : R), 0; 1, 1] * M = M * !![(1 : R), 0; 1, 1]) :
    M 1 0 = 0 ∧ M 0 1 = 0 ∧ M 1 1 = M 0 0 := by
  have e00 := congrFun (congrFun h₁ 0) 0
  have e01 := congrFun (congrFun h₁ 0) 1
  have f11 := congrFun (congrFun h₂ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, mul_one, mul_zero,
    add_zero, zero_add] at e00 e01 f11
  have hc : M 1 0 = 0 := by linear_combination e00
  have hb : M 0 1 = 0 := by linear_combination f11
  exact ⟨hc, hb, by linear_combination e01⟩

theorem exists_eq_scalar_of_commute_unip (ε : GL (Fin 2) R)
    (h₁ : (unipUpper : GL (Fin 2) R) * ε = ε * unipUpper)
    (h₂ : (unipLower : GL (Fin 2) R) * ε = ε * unipLower) :
    ∃ d : Rˣ, ε = sc d := by
  have h₁' : !![(1 : R), 1; 0, 1] * (ε : Matrix (Fin 2) (Fin 2) R) = ε * !![(1 : R), 1; 0, 1] := by
    simpa using congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) h₁
  have h₂' : !![(1 : R), 0; 1, 1] * (ε : Matrix (Fin 2) (Fin 2) R) = ε * !![(1 : R), 0; 1, 1] := by
    simpa using congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) h₂
  obtain ⟨hc, hb, hd⟩ := entries_of_commute_unip (ε : Matrix (Fin 2) (Fin 2) R) h₁' h₂'
  have hinv : (ε : Matrix (Fin 2) (Fin 2) R) 0 0 * (ε⁻¹ : GL (Fin 2) R) 0 0 = 1 := by
    have h := congrFun (congrFun (ε.mul_inv) 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
    rw [hb, zero_mul, add_zero] at h
    exact h
  refine ⟨⟨(ε : Matrix (Fin 2) (Fin 2) R) 0 0, (ε⁻¹ : GL (Fin 2) R) 0 0, hinv, by rw [mul_comm]; exact hinv⟩, ?_⟩
  ext i j
  change (ε : Matrix (Fin 2) (Fin 2) R) i j = Matrix.scalar (Fin 2) ((ε : Matrix (Fin 2) (Fin 2) R) 0 0) i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using hb
  · simpa using hc
  · simpa using hd

end LinearAlgebra

section Tensor

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  simp [sigmaTensor]

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) : sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  ext i j
  change sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)
  exact sigmaTensor_includeRight K L σ A _

theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) A).map (fun a => (1 : L) ⊗ₜ[K] a) := rfl

theorem toTensorGL_unipUpper : toTensorGL K L A (unipUpper : GL (Fin 2) A) = (unipUpper : GL (Fin 2) (L ⊗[K] A)) := by
  ext i j
  rw [coe_toTensorGL, coe_unipUpper, coe_unipUpper]
  fin_cases i <;> fin_cases j <;> simp [Algebra.TensorProduct.one_def]

theorem toTensorGL_unipLower : toTensorGL K L A (unipLower : GL (Fin 2) A) = (unipLower : GL (Fin 2) (L ⊗[K] A)) := by
  ext i j
  rw [coe_toTensorGL, coe_unipLower, coe_unipLower]
  fin_cases i <;> fin_cases j <;> simp [Algebra.TensorProduct.one_def]

theorem toTensorGL_scalar (c : Aˣ) :
    toTensorGL K L A (sc c) =
      sc (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom : A →* L ⊗[K] A) c) :=
  map_scalar _ c

theorem map_normString {B : Type} [CommRing B] [Algebra K B] (f : L ⊗[K] A →+* L ⊗[K] B)
    (hf : ∀ z, f (sigmaTensor K L A σ z) = sigmaTensor K L B σ (f z)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.map f (normString K L A σ δ) =
      normString K L B σ (Matrix.GeneralLinearGroup.map f δ) := by
  have hcomm : ∀ x : GL (Fin 2) (L ⊗[K] A), Matrix.GeneralLinearGroup.map f (sigmaGL K L A σ x) =
      sigmaGL K L B σ (Matrix.GeneralLinearGroup.map f x) := fun x =>
    Matrix.GeneralLinearGroup.ext fun i j => hf _
  have hiter : ∀ (i : ℕ) (x : GL (Fin 2) (L ⊗[K] A)),
      Matrix.GeneralLinearGroup.map f ((⇑(sigmaGL K L A σ))^[i] x) =
        (⇑(sigmaGL K L B σ))^[i] (Matrix.GeneralLinearGroup.map f x) := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact hiter i δ

end Tensor

section Places

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Gad (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev Garch (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev Gv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)

abbrev Gt (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

abbrev Ht (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  GL (Fin 2) (L ⊗[K] v.adicCompletion K)

def uArch (u : (AdeleRing (𝓞 K) K)ˣ) : (InfiniteAdeleRing K)ˣ :=
  Units.map (adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) u

def uAt (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) : (v.adicCompletion K)ˣ :=
  Units.map (((finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K) u

theorem glArch_centralScalar (u : (AdeleRing (𝓞 K) K)ˣ) :
    glArch (𝓞 K) K (centralScalar (𝓞 K) K u) = sc (uArch K u) :=
  map_scalar _ u

theorem localAt_centralScalar (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) = sc (uAt K v u) := by
  rw [show finComponent (𝓞 K) K v (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) =
      Matrix.GeneralLinearGroup.map ((finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)) (centralScalar (𝓞 K) K u)
    from rfl]
  exact map_scalar _ u

def zArch (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ :=
  Units.map ((tensorArchHom K L).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] InfiniteAdeleRing K) ζ

def zAt (v : HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map ((tensorPlaceHom K L v).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] v.adicCompletion K) ζ

theorem tensorArch_scalar (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : tensorArch K L (sc ζ) = sc (zArch K L ζ) :=
  map_scalar _ ζ

theorem tensorPlace_scalar (v : HeightOneSpectrum (𝓞 K)) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    tensorPlace K L v (sc ζ) = sc (zAt K L v ζ) :=
  map_scalar _ ζ

theorem tensorArch_normString (σ : L ≃ₐ[K] L) (δ : Gt K L) :
    tensorArch K L (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ) :=
  map_normString K L σ (AdeleRing (𝓞 K) K) (tensorArchHom K L).toRingHom (tensorArchHom_sigmaTensor K L σ) δ

theorem tensorPlace_normString (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : Gt K L) :
    tensorPlace K L v (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) :=
  map_normString K L σ (AdeleRing (𝓞 K) K) (tensorPlaceHom K L v).toRingHom (tensorPlaceHom_sigmaTensor K L σ v) δ

theorem nonempty_extension (v : HeightOneSpectrum (𝓞 K)) : Nonempty (v.Extension (𝓞 L)) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := Ideal.sum_ramification_inertia_extensions (𝓞 K) K L (𝓞 L) v
  simp at this
  exact Module.finrank_pos.ne' this.symm

theorem one_tmul_mem_semiLocalIntegers_iff (v : HeightOneSpectrum (𝓞 K)) (a : v.adicCompletion K) :
    (1 : L) ⊗ₜ[K] a ∈ semiLocalIntegers K L v ↔ a ∈ v.adicCompletionIntegers K := by
  constructor
  · intro h
    rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_eq] at h
    obtain ⟨w⟩ := nonempty_extension K L v
    have hw := h w (Set.mem_univ w)
    change (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ[K] a)) w ∈
      (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) at hw
    rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul] at hw
    change HeightOneSpectrum.Extension.adicCompletionSemialgHom K L w a ∈ w.1.adicCompletionIntegers L at hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom] at hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact (pow_le_one_iff (HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 K) (𝓞 L)
      (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L) w.1)).1 hw
  · intro ha
    exact ⟨(1 : 𝓞 L) ⊗ₜ ⟨a, ha⟩, by rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, map_one]⟩

theorem toTensorGL_mem_semiLocalIntegralSet_iff (v : HeightOneSpectrum (𝓞 K)) (g : Gv K v) :
    toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v ↔ g ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet]
  show (∀ i j, ((toTensorGL K L (v.adicCompletion K) g : Gsl K L v) : Matrix (Fin 2) (Fin 2) _) i j ∈ semiLocalIntegers K L v) ∧
      (∀ i j, (((toTensorGL K L (v.adicCompletion K) g)⁻¹ : Gsl K L v) : Matrix (Fin 2) (Fin 2) _) i j ∈
        semiLocalIntegers K L v) ↔ _
  rw [← map_inv]
  simp only [coe_toTensorGL, Matrix.map_apply, one_tmul_mem_semiLocalIntegers_iff]

end Places

section Instances

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

scoped instance instSecondCountableCompletion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  show SecondCountableTopology ((w : InfinitePlace K) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X]
    [SecondCountableTopology X] : SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountable_gl (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instSecondCountableGarch : SecondCountableTopology (Garch K) := secondCountable_gl _
scoped instance instSecondCountableGv (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Gv K v) :=
  secondCountable_gl _
scoped instance instSecondCountableGad : SecondCountableTopology (Gad K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance instLocallyCompactGarch : LocallyCompactSpace (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
scoped instance instLocallyCompactGv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gv K v) :=
  locallyCompactSpace_localGL K v
scoped instance instT2Garch : T2Space (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isEmbedding_embedProduct.t2Space
scoped instance instT2Gv (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gv K v) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space
scoped instance instT2Gad : T2Space (Gad K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  exact Units.isEmbedding_embedProduct.t2Space

scoped instance instIsTopologicalRingSL (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalRing (L ⊗[K] v.adicCompletion K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2SL (v : HeightOneSpectrum (𝓞 K)) : T2Space (L ⊗[K] v.adicCompletion K) := t2Space_tensor K L _
scoped instance instLocallyCompactSL (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (L ⊗[K] v.adicCompletion K) :=
  locallyCompactSpace_tensor K L _
scoped instance instLocallyCompactGsl (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gsl K L v) :=
  locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalGroupGsl (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (Gsl K L v) :=
  isTopologicalGroup_tensorGL K L _
scoped instance instT2Gsl (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gsl K L v) := t2Space_tensorGL K L _
scoped instance instIsTopologicalRingTA : IsTopologicalRing (L ⊗[K] AdeleRing (𝓞 K) K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TA : T2Space (L ⊗[K] AdeleRing (𝓞 K) K) := t2Space_tensor K L _
scoped instance instLocallyCompactTA : LocallyCompactSpace (L ⊗[K] AdeleRing (𝓞 K) K) := locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupGt : IsTopologicalGroup (Gt K L) := isTopologicalGroup_tensorGL K L _
scoped instance instT2Gt : T2Space (Gt K L) := t2Space_tensorGL K L _
scoped instance instLocallyCompactGt : LocallyCompactSpace (Gt K L) := locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalRingTI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TI : T2Space (L ⊗[K] InfiniteAdeleRing K) := t2Space_tensor K L _
scoped instance instLocallyCompactTI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) := locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupHt : IsTopologicalGroup (Ht K L) := isTopologicalGroup_tensorGL K L _
scoped instance instLocallyCompactHt : LocallyCompactSpace (Ht K L) := locallyCompactSpace_tensorGL K L _
scoped instance instT2Ht : T2Space (Ht K L) := t2Space_tensorGL K L _

scoped instance instMeasurableSpaceGarch : MeasurableSpace (Garch K) := borel _
scoped instance instBorelSpaceGarch : BorelSpace (Garch K) := ⟨rfl⟩
scoped instance instMeasurableSpaceGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gv K v) := borel _
scoped instance instBorelSpaceGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gv K v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGad : MeasurableSpace (Gad K) := borel _
scoped instance instBorelSpaceGad : BorelSpace (Gad K) := ⟨rfl⟩
scoped instance instMeasurableSpaceHt : MeasurableSpace (Ht K L) := borel _
scoped instance instBorelSpaceHt : BorelSpace (Ht K L) := ⟨rfl⟩
scoped instance instMeasurableSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gsl K L v) := borel _
scoped instance instBorelSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gsl K L v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGt : MeasurableSpace (Gt K L) := borel _
scoped instance instBorelSpaceGt : BorelSpace (Gt K L) := ⟨rfl⟩

scoped instance (priority := 10000) instMeasurableSpaceSubgroupGad (H : Subgroup (Gad K)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGad (H : Subgroup (Gad K)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGarch (H : Subgroup (Garch K)) :
    MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGarch (H : Subgroup (Garch K)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gv K v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gv K v)) :
    BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGt (H : Subgroup (Gt K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGt (H : Subgroup (Gt K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupHt (H : Subgroup (Ht K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupHt (H : Subgroup (Ht K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gsl K L v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gsl K L v)) :
    BorelSpace H := ⟨rfl⟩

scoped instance instIsHaarLocalHaar (v : HeightOneSpectrum (𝓞 K)) : IsHaarMeasure (localHaar K v) := isHaarMeasure_localHaar K v
scoped instance instIsHaarArchHaarK : IsHaarMeasure (archHaarK K) := Measure.isHaarMeasure_haarMeasure _
scoped instance instIsHaarAdelicGLHaar : IsHaarMeasure (adelicGLHaar (Fin 2) (𝓞 K) K) := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

theorem isClosed_twistedCentralizer (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hcs : Continuous (sigmaGL K L A σ) := by
    refine Continuous.units_map _ ?_
    exact continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap)
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul hcs.inv
  have : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

scoped instance instLocallyCompactCentralizerGad (u : (AdeleRing (𝓞 K) K)ˣ) :
    LocallyCompactSpace (Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))) := by
  have h : IsClosed ((Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) : Set (Gad K))) := by
    rw [show centralScalar (𝓞 K) K u = sc u from rfl, centralizer_scalar_eq_top]
    exact isClosed_univ
  exact h.locallyCompactSpace
scoped instance instLocallyCompactCentralizerGarch (c : (InfiniteAdeleRing K)ˣ) :
    LocallyCompactSpace (Subgroup.centralizer ({sc c} : Set (Garch K))) := by
  have h : IsClosed ((Subgroup.centralizer ({sc c} : Set (Garch K))) : Set (Garch K)) := by
    rw [centralizer_scalar_eq_top]; exact isClosed_univ
  exact h.locallyCompactSpace
scoped instance instLocallyCompactCentralizerGv (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) :
    LocallyCompactSpace (Subgroup.centralizer ({sc c} : Set (Gv K v))) := by
  have h : IsClosed ((Subgroup.centralizer ({sc c} : Set (Gv K v))) : Set (Gv K v)) := by
    rw [centralizer_scalar_eq_top]; exact isClosed_univ
  exact h.locallyCompactSpace
scoped instance instLocallyCompactTwistedGt (σ : L ≃ₐ[K] L) (δ : Gt K L) :
    LocallyCompactSpace (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ).locallyCompactSpace
scoped instance instLocallyCompactTwistedHt (σ : L ≃ₐ[K] L) (δ : Ht K L) :
    LocallyCompactSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ).locallyCompactSpace
scoped instance instLocallyCompactTwistedGsl (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : Gsl K L v) :
    LocallyCompactSpace (twistedCentralizer K L (v.adicCompletion K) σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ).locallyCompactSpace

end Instances

section Transport

theorem isMulRightInvariant_map_equiv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (μ : Measure G) [μ.IsMulRightInvariant] :
    (Measure.map e μ).IsMulRightInvariant := by
  refine ⟨fun h => ?_⟩
  have hem : Measurable (e : G → H) := e.continuous.measurable
  rw [Measure.map_map (measurable_mul_const h) hem]
  obtain ⟨g, rfl⟩ : ∃ g, e g = h := ⟨e.symm h, e.apply_symm_apply h⟩
  conv_rhs => rw [← map_mul_right_eq_self μ g]
  rw [Measure.map_map hem (measurable_mul_const g)]
  congr 1
  funext x
  simp only [Function.comp_apply, map_mul]

def centralizerScalarEquiv {R : Type*} [CommRing R] [TopologicalSpace R] (c : Rˣ) :
    Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) ≃ₜ* GL (Fin 2) R :=
  { (MulEquiv.subgroupCongr (centralizer_scalar_eq_top c)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk continuous_id }

end Transport

section CouplingScalar

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
theorem continuous_toTensorGL' : Continuous (toTensorGL K L A) := by
  refine Continuous.units_map _ ?_
  have h : Continuous fun a : A => a • (1 : L ⊗[K] A) := continuous_id.fun_smul continuous_const
  have h' : Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    refine h.congr fun a => ?_
    rw [← Algebra.algebraMap_eq_smul_one]
    rfl
  change Continuous fun M : Matrix (Fin 2) (Fin 2) A => M.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
  exact continuous_id.matrix_map h'

theorem toTensorGL_mem_conj_twistedCentralizer [T2Space A] [NumberField K] [NumberField L]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = sc c)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ : @Measure.IsOpenPosMeasure _ _ (centralizerBorel A γ) τ)
    (hc : Coupled K L A σ γ δ y τ τ') (g : GL (Fin 2) A) :
    y * toTensorGL K L A g * y⁻¹ ∈ twistedCentralizer K L A σ δ := by
  haveI := isTopologicalGroup_tensorGL K L A
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  letI mC : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := centralizerBorel A γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  letI mT : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  set S : Set (GL (Fin 2) (L ⊗[K] A)) :=
    (fun x => y * x * y⁻¹) ⁻¹' (twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) with hS_def
  have hS : IsClosed S :=
    (isClosed_twistedCentralizer (K := K) (L := L) A σ δ).preimage ((continuous_const.mul continuous_id).mul continuous_const)
  set cj : twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A) :=
    fun t => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y with hcj_def
  set e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) (L ⊗[K] A) :=
    fun t => toTensorGL K L A (t : GL (Fin 2) A) with he_def
  have hc' : Measure.map cj τ' = Measure.map e τ := hc
  have hL : Measure.map cj τ' Sᶜ = 0 := by
    by_cases hm : AEMeasurable cj τ'
    · rw [Measure.map_apply_of_aemeasurable hm hS.measurableSet.compl]
      have hemp : cj ⁻¹' Sᶜ = ∅ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_compl_iff, hS_def, hcj_def, Set.mem_empty_iff_false, iff_false,
          not_not, SetLike.mem_coe]
        have : y * (y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) * y⁻¹ = t := by group
        rw [this]
        exact t.2
      rw [hemp, measure_empty]
    · rw [Measure.map_of_not_aemeasurable hm]
      rfl
  have he : Continuous e := (continuous_toTensorGL' K L A).comp continuous_subtype_val
  have hR : τ (e ⁻¹' Sᶜ) = 0 := by
    rw [← Measure.map_apply he.measurable hS.measurableSet.compl, ← hc']
    exact hL
  have hempty : e ⁻¹' Sᶜ = ∅ := (hS.isOpen_compl.preimage he).eq_empty_of_measure_zero hR
  obtain ⟨c, rfl⟩ := hγ
  have hg : g ∈ Subgroup.centralizer ({sc c} : Set (GL (Fin 2) A)) := by
    rw [centralizer_scalar_eq_top]; trivial
  have hmem : e ⟨g, hg⟩ ∈ S := by
    by_contra hnot
    have : (⟨g, hg⟩ : Subgroup.centralizer ({sc c} : Set (GL (Fin 2) A))) ∈ e ⁻¹' Sᶜ := hnot
    rw [hempty] at this
    exact this
  simpa [hS_def, he_def] using hmem

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem commute_of_mem (δ y : GL (Fin 2) (L ⊗[K] A)) (g : GL (Fin 2) A)
    (h : y * toTensorGL K L A g * y⁻¹ ∈ twistedCentralizer K L A σ δ) :
    toTensorGL K L A g * (y⁻¹ * δ * sigmaGL K L A σ y) = (y⁻¹ * δ * sigmaGL K L A σ y) * toTensorGL K L A g := by
  set eg := toTensorGL K L A g with heg
  set sy := sigmaGL K L A σ y with hsy
  have h1 : (y * eg * y⁻¹) * δ * (sigmaGL K L A σ (y * eg * y⁻¹))⁻¹ = δ := mem_sigmaCentralizer_iff.1 h
  rw [map_mul, map_mul, map_inv, sigmaGL_toTensorGL K L σ A g] at h1
  have h2 : y⁻¹ * δ * sy = eg * (y⁻¹ * δ * sy) * eg⁻¹ := by
    calc y⁻¹ * δ * sy = y⁻¹ * ((y * eg * y⁻¹) * δ * (sy * eg * sy⁻¹)⁻¹) * sy := by rw [h1]
      _ = eg * (y⁻¹ * δ * sy) * eg⁻¹ := by group
  calc eg * (y⁻¹ * δ * sy) = (eg * (y⁻¹ * δ * sy) * eg⁻¹) * eg := by group
    _ = (y⁻¹ * δ * sy) * eg := by rw [← h2]

theorem exists_conj_eq_scalar_of_coupled [T2Space A] [NumberField K] [NumberField L]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = sc c)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ : @Measure.IsOpenPosMeasure _ _ (centralizerBorel A γ) τ)
    (hc : Coupled K L A σ γ δ y τ τ') :
    ∃ ζ : (L ⊗[K] A)ˣ, y⁻¹ * δ * sigmaGL K L A σ y = sc ζ := by
  have hmem := toTensorGL_mem_conj_twistedCentralizer K L σ A γ hγ δ y τ τ' hτ hc
  have hU := commute_of_mem K L σ A δ y unipUpper (hmem unipUpper)
  have hLo := commute_of_mem K L σ A δ y unipLower (hmem unipLower)
  rw [toTensorGL_unipUpper] at hU
  rw [toTensorGL_unipLower] at hLo
  exact exists_eq_scalar_of_commute_unip (y⁻¹ * δ * sigmaGL K L A σ y) hU hLo

end CouplingScalar

section AdelicTransport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem mem_sigmaCentralizer_conj_iff {G : Type*} [Group G] (θ : G →* G) (d w t : G) :
    t ∈ sigmaCentralizer θ d ↔ w⁻¹ * t * w ∈ sigmaCentralizer θ (w⁻¹ * d * θ w) := by
  rw [mem_sigmaCentralizer_iff, mem_sigmaCentralizer_iff, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc w⁻¹ * t * w * (w⁻¹ * d * θ w) * ((θ w)⁻¹ * θ t * θ w)⁻¹
        = w⁻¹ * (t * d * (θ t)⁻¹) * θ w := by group
      _ = w⁻¹ * d * θ w := by rw [h]
  · intro h
    calc t * d * (θ t)⁻¹ = w * (w⁻¹ * t * w * (w⁻¹ * d * θ w) * ((θ w)⁻¹ * θ t * θ w)⁻¹) * (θ w)⁻¹ := by group
      _ = w * (w⁻¹ * d * θ w) * (θ w)⁻¹ := by rw [h]
      _ = d := by group

theorem conj_mem_twistedCentralizer_conj (σ : L ≃ₐ[K] L) (δ y : Gt K L)
    (t : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :
    y⁻¹ * (t : Gt K L) * y ∈ twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (y⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ y) :=
  (mem_sigmaCentralizer_conj_iff (sigmaGL K L (AdeleRing (𝓞 K) K) σ) δ y (t : Gt K L)).1 t.2

theorem conj_symm_mem_twistedCentralizer (σ : L ≃ₐ[K] L) (δ y : Gt K L)
    (s : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (y⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ y)) :
    y * (s : Gt K L) * y⁻¹ ∈ twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ := by
  refine (mem_sigmaCentralizer_conj_iff (sigmaGL K L (AdeleRing (𝓞 K) K) σ) δ y (y * (s : Gt K L) * y⁻¹)).2 ?_
  have : y⁻¹ * (y * (s : Gt K L) * y⁻¹) * y = s := by group
  rw [this]
  exact s.2

def conjIso (σ : L ≃ₐ[K] L) (δ y : Gt K L) :
    twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ ≃ₜ*
      twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (y⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ y) where
  toFun t := ⟨y⁻¹ * (t : Gt K L) * y, conj_mem_twistedCentralizer_conj σ δ y t⟩
  invFun s := ⟨y * (s : Gt K L) * y⁻¹, conj_symm_mem_twistedCentralizer σ δ y s⟩
  left_inv t := Subtype.ext (by simp only; group)
  right_inv s := Subtype.ext (by simp only; group)
  map_mul' s t := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

theorem coe_conjIso_apply (σ : L ≃ₐ[K] L) (δ y : Gt K L) (t : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :
    ((conjIso σ δ y t : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (y⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ y)) : Gt K L) =
      y⁻¹ * (t : Gt K L) * y := rfl

theorem isTwistedOrbitalIntegralOn_conj (σ : L ≃ₐ[K] L) (μ : Measure (Gt K L)) [μ.IsMulLeftInvariant]
    (δ y : Gt K L) (τ' : Measure (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)) (φ : Gt K L → ℂ) (I' : ℂ)
    (h : IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ' φ I') :
    IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ (y⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ y)
      (Measure.map (conjIso σ δ y) τ') φ I' := by
  obtain ⟨w, ⟨hw0, hwm, hwc, hsec⟩, rfl⟩ := h
  set A := AdeleRing (𝓞 K) K
  refine ⟨fun g => w (y * g), ⟨fun g => hw0 _, hwm.comp (measurable_const_mul y), ?_, ?_⟩, ?_⟩
  · refine (hwc.comp_homeomorph (Homeomorph.mulLeft y)).mono ?_
    intro g hg
    exact hg
  · intro x hx
    have hmeas : Measurable (fun t : twistedCentralizer K L A σ δ => conjIso σ δ y t) := (conjIso σ δ y).continuous.measurable
    have hx' : φ ((y * x)⁻¹ * δ * sigmaGL K L A σ (y * x)) ≠ 0 := by
      have : (y * x)⁻¹ * δ * sigmaGL K L A σ (y * x) = x⁻¹ * (y⁻¹ * δ * sigmaGL K L A σ y) * sigmaGL K L A σ x := by
        rw [map_mul]; group
      rw [this]; exact hx
    show ∫ t : twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y),
        w (y * (((t : twistedCentralizer K L A σ _) : Gt K L) * x)) ∂(Measure.map (conjIso σ δ y) τ') = 1
    have hF : Measurable (fun t : twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) =>
        w (y * (((t : twistedCentralizer K L A σ _) : Gt K L) * x))) :=
      hwm.comp ((continuous_const.mul (continuous_subtype_val.mul continuous_const)).measurable)
    rw [MeasureTheory.integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
    have heq : (fun s : twistedCentralizer K L A σ δ =>
          w (y * ((((conjIso σ δ y) s : twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y)) : Gt K L) * x))) =
        fun s : twistedCentralizer K L A σ δ => w ((s : Gt K L) * (y * x)) := by
      funext s
      rw [coe_conjIso_apply]
      congr 1
      group
    rw [heq]
    exact hsec (y * x) hx'
  · have heq : (fun x : Gt K L => φ (x⁻¹ * (y⁻¹ * δ * sigmaGL K L A σ y) * sigmaGL K L A σ x) * (((fun g => w (y * g)) x : ℝ) : ℂ)) =
        fun x => (fun g : Gt K L => φ (g⁻¹ * δ * sigmaGL K L A σ g) * ((w g : ℝ) : ℂ)) (y * x) := by
      funext x
      have : x⁻¹ * (y⁻¹ * δ * sigmaGL K L A σ y) * sigmaGL K L A σ x = (y * x)⁻¹ * δ * sigmaGL K L A σ (y * x) := by
        rw [map_mul]; group
      rw [this]
    rw [heq]
    exact (MeasureTheory.integral_mul_left_eq_self
      (fun g : Gt K L => φ (g⁻¹ * δ * sigmaGL K L A σ g) * ((w g : ℝ) : ℂ)) y).symm

theorem coupled_one_of_coupled (σ : L ≃ₐ[K] L) (γ : Gad K) (δ y : Gt K L)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (Gad K)))) (τ' : Measure (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    (hc : Coupled K L (AdeleRing (𝓞 K) K) σ γ δ y τ τ') :
    Coupled K L (AdeleRing (𝓞 K) K) σ γ (y⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ y) 1 τ
      (Measure.map (conjIso σ δ y) τ') := by
  have hc' : Measure.map (fun t : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ => y⁻¹ * (t : Gt K L) * y) τ' =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (Gad K)) => toTensorGL K L (AdeleRing (𝓞 K) K) (t : Gad K)) τ := hc
  show Measure.map (fun s : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (y⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ y) =>
      (1 : Gt K L)⁻¹ * (s : Gt K L) * 1) (Measure.map (conjIso σ δ y) τ') =
    Measure.map (fun t : Subgroup.centralizer ({γ} : Set (Gad K)) => toTensorGL K L (AdeleRing (𝓞 K) K) (t : Gad K)) τ
  rw [← hc', Measure.map_map]
  · congr 1
    funext t
    simp only [Function.comp_apply, coe_conjIso_apply, inv_one, one_mul, mul_one]
  · exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  · exact (conjIso σ δ y).continuous.measurable

theorem isHaarMeasure_map_conjIso (σ : L ≃ₐ[K] L) (δ y : Gt K L)
    (τ' : Measure (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)) [τ'.IsHaarMeasure] :
    (Measure.map (conjIso σ δ y) τ').IsHaarMeasure :=
  (conjIso σ δ y).isHaarMeasure_map τ'

def centralizerCsEquiv (u : (AdeleRing (𝓞 K) K)ˣ) :
    Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) ≃ₜ* Gad K :=
  { (MulEquiv.subgroupCongr (centralizer_scalar_eq_top (R := AdeleRing (𝓞 K) K) u)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk continuous_id }

theorem orbitalIntegral_scalar_eq (μK : Measure (Gad K)) [μK.IsHaarMeasure] (u : (AdeleRing (𝓞 K) K)ˣ)
    (τ : Measure (Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)))) [τ.IsHaarMeasure]
    (f : Gad K → ℂ) (I : ℂ) (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK (centralScalar (𝓞 K) K u) τ f I) :
    I = f (centralScalar (𝓞 K) K u) *
      (haarScalarFactor μK (Measure.map (centralizerCsEquiv u) τ) : ℝ) := by
  obtain ⟨w, ⟨hw0, hwm, hwc, hsec⟩, rfl⟩ := hI
  have hconj : ∀ x : Gad K, x⁻¹ * centralScalar (𝓞 K) K u * x = centralScalar (𝓞 K) K u := fun x =>
    conj_scalar (R := AdeleRing (𝓞 K) K) u x
  have hint : (fun x : Gad K => f (x⁻¹ * centralScalar (𝓞 K) K u * x) * ((w x : ℝ) : ℂ)) =
      fun x => f (centralScalar (𝓞 K) K u) * ((w x : ℝ) : ℂ) := funext fun x => by rw [hconj]
  show ∫ x, f (x⁻¹ * centralScalar (𝓞 K) K u * x) * ((w x : ℝ) : ℂ) ∂μK = _
  rw [hint, MeasureTheory.integral_const_mul]
  by_cases hf : f (centralScalar (𝓞 K) K u) = 0
  · rw [hf, zero_mul, zero_mul]
  congr 1
  set e := centralizerCsEquiv (K := K) u with he
  haveI : (Measure.map e τ).IsHaarMeasure := e.isHaarMeasure_map τ
  have hμ : μK = haarScalarFactor μK (Measure.map e τ) • Measure.map e τ := isMulLeftInvariant_eq_smul μK _
  have h1 : ∫ t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)), w ((t : Gad K) * 1) ∂τ = 1 :=
    hsec 1 (by rw [hconj]; exact hf)
  simp only [mul_one] at h1
  have h2 : ∫ x, ((w x : ℝ) : ℂ) ∂(Measure.map e τ) = 1 := by
    have hem : Measurable (fun t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)) => e t) :=
      e.continuous.measurable
    have hF : Measurable (fun x : Gad K => ((w x : ℝ) : ℂ)) := Complex.continuous_ofReal.measurable.comp hwm
    rw [MeasureTheory.integral_map hem.aemeasurable hF.aestronglyMeasurable]
    show ∫ t : Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K)), ((w (t : Gad K) : ℝ) : ℂ) ∂τ = 1
    rw [integral_complex_ofReal, h1, Complex.ofReal_one]
  conv_lhs => rw [hμ]
  rw [integral_smul_nnreal_measure, h2, NNReal.smul_def, Complex.real_smul, mul_one]

end AdelicTransport

section LocalScalar

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isOrbitalIntegral_scalar (c : (v.adicCompletion K)ˣ) (fv : Gv K v → ℂ) :
    IsOrbitalIntegral K v (sc c) (Measure.map (centralizerScalarEquiv c).symm (localHaar K v)) fv (fv (sc c)) := by
  set γ : Gv K v := sc c with hγ
  set e := centralizerScalarEquiv (R := v.adicCompletion K) c with he
  set τ : Measure (localCentralizer K v γ) := Measure.map e.symm (localHaar K v) with hτ
  haveI : (localHaar K v).IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two (localHaar K v)).1
  set A := localIntegralSet K v with hA
  have hAm : MeasurableSet A := (isOpen_localIntegralSet K v).measurableSet
  set w : Gv K v → ℝ := A.indicator fun _ => (1 : ℝ) with hw
  have hsec : IsSectionFn K v γ τ fv w := by
    refine ⟨fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x, measurable_const.indicator hAm,
      HasCompactSupport.intro (isCompact_localIntegralSet K v) fun x hx => Set.indicator_of_notMem hx _, fun x _ => ?_⟩
    have hmeas : (e.symm.toHomeomorph.toMeasurableEquiv : Gv K v → localCentralizer K v γ) = e.symm := rfl
    calc ∫ t : localCentralizer K v γ, w ((t : Gv K v) * x) ∂τ
        = ∫ g, w (((e.symm.toHomeomorph.toMeasurableEquiv g : localCentralizer K v γ) : Gv K v) * x) ∂(localHaar K v) := by
          rw [hτ, ← hmeas, integral_map_equiv]
      _ = ∫ g, ((fun g => g * x) ⁻¹' A).indicator 1 g ∂(localHaar K v) := by congr 1
      _ = (localHaar K v).real ((fun g => g * x) ⁻¹' A) := integral_indicator_one (hAm.preimage (measurable_mul_const x))
      _ = (localHaar K v).real A := by
          rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_mul_const x) hAm, map_mul_right_eq_self]
      _ = 1 := by rw [measureReal_def, hA, localHaar_localIntegralSet, ENNReal.toReal_one]
  refine ⟨w, hsec, ?_⟩
  have h1 : (fun x => fv (x⁻¹ * γ * x) * (w x : ℂ)) = fun x => A.indicator (fun _ => fv γ) x := by
    funext x
    rw [hγ, conj_scalar]
    by_cases hx : x ∈ A
    · simp [hw, hx]
    · simp [hw, hx]
  rw [h1, integral_indicator_const _ hAm, measureReal_def, hA, localHaar_localIntegralSet, ENNReal.toReal_one, one_smul]

end LocalScalar

section ArchScalar

variable (K : Type) [Field K] [NumberField K]

theorem isOrbitalIntegralOn_arch_scalar (hr : (archHaarK K).IsMulRightInvariant) (c : (InfiniteAdeleRing K)ˣ)
    (fa : Garch K → ℂ) :
    IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) (sc c)
      (Measure.map (centralizerScalarEquiv c).symm (archHaarK K)) fa (fa (sc c)) := by
  set γ : Garch K := sc c with hγ
  set e := centralizerScalarEquiv (R := InfiniteAdeleRing K) c with he
  set τ : Measure (Subgroup.centralizer ({γ} : Set (Garch K))) := Measure.map e.symm (archHaarK K) with hτ
  haveI := hr
  obtain ⟨k⟩ : Nonempty (PositiveCompacts (Garch K)) := inferInstance
  set A : Set (Garch K) := (k : Set (Garch K)) with hA
  have hAm : MeasurableSet A := k.isCompact.measurableSet
  have hApos : (archHaarK K).real A ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(measure_pos_of_nonempty_interior (archHaarK K) k.interior_nonempty).ne', k.isCompact.measure_lt_top.ne⟩
  set m : ℝ := (archHaarK K).real A with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set w : Garch K → ℝ := A.indicator fun _ => m⁻¹ with hw
  have hsec : IsSectionFnOn (InfiniteAdeleRing K) γ τ fa w := by
    refine ⟨fun x => Set.indicator_nonneg (fun _ _ => inv_nonneg.2 hm0) x, measurable_const.indicator hAm,
      HasCompactSupport.intro k.isCompact fun x hx => Set.indicator_of_notMem hx _, fun x _ => ?_⟩
    have hmeas : (e.symm.toHomeomorph.toMeasurableEquiv : Garch K → Subgroup.centralizer ({γ} : Set (Garch K))) = e.symm := rfl
    calc ∫ t : Subgroup.centralizer ({γ} : Set (Garch K)), w ((t : Garch K) * x) ∂τ
        = ∫ g, w (((e.symm.toHomeomorph.toMeasurableEquiv g : Subgroup.centralizer ({γ} : Set (Garch K))) : Garch K) * x)
            ∂(archHaarK K) := by
          rw [hτ, ← hmeas, integral_map_equiv]
      _ = ∫ g, ((fun g => g * x) ⁻¹' A).indicator (fun _ => m⁻¹) g ∂(archHaarK K) := by congr 1
      _ = (archHaarK K).real ((fun g => g * x) ⁻¹' A) • m⁻¹ := integral_indicator_const _ (hAm.preimage (measurable_mul_const x))
      _ = (archHaarK K).real A • m⁻¹ := by
          rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_mul_const x) hAm, map_mul_right_eq_self]
      _ = 1 := by rw [smul_eq_mul, ← hm, mul_inv_cancel₀ hApos]
  refine ⟨w, hsec, ?_⟩
  have h1 : (fun x => fa (x⁻¹ * γ * x) * (w x : ℂ)) = fun x => A.indicator (fun _ => (m⁻¹ : ℂ) * fa γ) x := by
    funext x
    rw [hγ, conj_scalar]
    by_cases hx : x ∈ A
    · simp [hw, hx, mul_comm]
    · simp [hw, hx]
  rw [h1, integral_indicator_const _ hAm, ← hm, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hApos, Complex.ofReal_one, one_mul]

end ArchScalar

section Plumbing

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev cpt (v : HeightOneSpectrum (𝓞 K)) (g : Gad K) : Gv K v := finComponent (𝓞 K) K v (glFin (𝓞 K) K g)

theorem eventually_cpt_mem (g : Gad K) : ∀ᶠ v in cofinite, cpt v g ∈ localIntegralSet K v := by
  set h := glFin (𝓞 K) K g with hh
  have h1 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite,
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) w ∈ w.adicCompletionIntegers K :=
    fun i j => ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j).2
  have h2 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite,
      (((h⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) w ∈
        w.adicCompletionIntegers K :=
    fun i j => (((h⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j).2
  have h1' : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ i j : Fin 2,
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) w ∈ w.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => h1 i j
  have h2' : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ i j : Fin 2,
      (((h⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) w ∈
        w.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => h2 i j
  filter_upwards [h1', h2'] with w hw1 hw2
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply]
    exact hw1 i j
  · rw [← map_inv, finComponent_apply]
    exact hw2 i j

theorem finite_setOf_cpt_not_mem (g : Gad K) : {v | cpt v g ∉ localIntegralSet K v}.Finite :=
  Filter.eventually_cofinite.1 (eventually_cpt_mem g)

theorem cpt_centralScalar (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) :
    cpt v (centralScalar (𝓞 K) K u) = sc (uAt K v u) :=
  localAt_centralScalar K v u

theorem eq_map_of_coupled_one (σ : L ≃ₐ[K] L) (γ : Gad K) (δ : Gt K L)
    (e : Subgroup.centralizer ({γ} : Set (Gad K)) ≃ₜ* twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
    (he : ∀ s : Subgroup.centralizer ({γ} : Set (Gad K)),
      ((e s : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) : Gt K L) = toTensorGL K L _ (s : Gad K))
    (τ : Measure (Subgroup.centralizer ({γ} : Set (Gad K)))) (τ' : Measure (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    (hC : Coupled K L (AdeleRing (𝓞 K) K) σ γ δ 1 τ τ') :
    τ' = Measure.map e τ := by
  set j : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ → Gt K L := fun t => (1 : Gt K L)⁻¹ * (t : Gt K L) * 1 with hj_def
  have hCj : Measure.map j τ' = Measure.map (fun s : Subgroup.centralizer ({γ} : Set (Gad K)) => toTensorGL K L _ (s : Gad K)) τ := hC
  have hjval : j = (Subtype.val : twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ → Gt K L) := by
    funext t
    simp only [hj_def, inv_one, one_mul, mul_one]
  have hcomp : (fun s : Subgroup.centralizer ({γ} : Set (Gad K)) => toTensorGL K L _ (s : Gad K)) = j ∘ e := by
    funext s
    simp only [Function.comp_apply, hjval, he]
  have hjce : IsClosedEmbedding j := hjval ▸ IsClosedEmbedding.subtypeVal (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ)
  have hjm : MeasurableEmbedding j := hjce.measurableEmbedding
  have hem : Measurable e := e.continuous.measurable
  rw [hcomp, ← Measure.map_map hjm.measurable hem] at hCj
  ext A hA
  rw [← Set.preimage_image_eq A hjm.injective, ← hjm.map_apply, hCj, hjm.map_apply]

theorem sigmaTensor_iterate (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A] (k : ℕ) (z : L ⊗[K] A) :
    (⇑(sigmaTensor K L A σ))^[k] z = (Algebra.TensorProduct.map ((σ ^ k : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) z := by
  induction k generalizing z with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul l a => rfl
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul l a =>
          rw [Algebra.TensorProduct.map_tmul, pow_succ']
          show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A)) (((σ ^ k : L ≃ₐ[K] L) : L →ₐ[K] L) l ⊗ₜ[K] a) = _
          rw [Algebra.TensorProduct.map_tmul]
          rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem sigmaGL_iterate_eq_self (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1) (A : Type) [CommRing A] [Algebra K A]
    (x : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] x = x := by
  have hent : ∀ (k : ℕ) (u : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      (((⇑(sigmaGL K L A σ))^[k] u : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
        (⇑(sigmaTensor K L A σ))^[k] ((u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) := by
    intro k
    induction k with
    | zero => intro u i j; rfl
    | succ k ih =>
        intro u i j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih u i j]
        rfl
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [hent, sigmaTensor_iterate, hσ]
  have : (Algebra.TensorProduct.map ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) = AlgHom.id K (L ⊗[K] A) := by
    ext <;> simp
  rw [this, AlgHom.id_apply]

theorem normString_conj (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1) (A : Type) [CommRing A] [Algebra K A]
    (δ y : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) = y⁻¹ * normString K L A σ δ * y := by
  have h1 : ∀ x : GL (Fin 2) (L ⊗[K] A), normString K L A σ x = LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) x := by
    intro x
    rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
    rfl
  rw [h1, h1, LT.TwistedNorm.sigmaNormPow_sigmaConjElt _ _ (sigmaGL_iterate_eq_self σ hσ A y)]

end Plumbing

section MainScalar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Tu (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (Gad K) :=
  Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (Gad K))

abbrev Tz (σ : L ≃ₐ[K] L) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : Subgroup (Gt K L) :=
  twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (sc ζ)
abbrev Tua (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (Garch K) := Subgroup.centralizer ({sc (uArch K u)} : Set (Garch K))
abbrev Tza (σ : L ≃ₐ[K] L) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : Subgroup (Ht K L) :=
  twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L (sc ζ))
abbrev Tuv (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gv K v) :=
  Subgroup.centralizer ({sc (uAt K v u)} : Set (Gv K v))
abbrev Tzv (σ : L ≃ₐ[K] L) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v (sc ζ))

section Iso

variable [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
  (u : (AdeleRing (𝓞 K) K)ˣ) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

include hgen in
theorem exists_psi : ∃ Ψ : Tu u ≃ₜ* Tz σ ζ, ∀ s : Tu u, ((Ψ s : Tz σ ζ) : Gt K L) = toTensorGL K L _ (s : Gad K) := by
  obtain ⟨e, he⟩ := AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar K L σ hgen
    (AdeleRing (𝓞 K) K) (centralScalar (𝓞 K) K u) ⟨u, rfl⟩ (sc ζ) 1 ζ (by rw [inv_one, one_mul, map_one, mul_one])
  exact ⟨e, fun s => by rw [he, one_mul, inv_one, mul_one]⟩

include hgen in
theorem exists_psi_a : ∃ Ψa : Tua u ≃ₜ* Tza σ ζ, ∀ s : Tua u, ((Ψa s : Tza σ ζ) : Ht K L) = toTensorGL K L _ (s : Garch K) := by
  obtain ⟨e, he⟩ := AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar K L σ hgen
    (InfiniteAdeleRing K) (sc (uArch K u)) ⟨_, rfl⟩ (tensorArch K L (sc ζ)) 1 (zArch K L ζ)
    (by rw [inv_one, one_mul, map_one, mul_one, tensorArch_scalar])
  exact ⟨e, fun s => by rw [he, one_mul, inv_one, mul_one]⟩

include hgen in
theorem exists_psi_v (v : HeightOneSpectrum (𝓞 K)) :
    ∃ Ψv : Tuv u v ≃ₜ* Tzv σ ζ v, ∀ s : Tuv u v, ((Ψv s : Tzv σ ζ v) : Gsl K L v) = toTensorGL K L _ (s : Gv K v) := by
  obtain ⟨e, he⟩ := AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar K L σ hgen
    (v.adicCompletion K) (sc (uAt K v u)) ⟨_, rfl⟩ (tensorPlace K L v (sc ζ)) 1 (zAt K L v ζ)
    (by rw [inv_one, one_mul, map_one, mul_one, tensorPlace_scalar])
  exact ⟨e, fun s => by rw [he, one_mul, inv_one, mul_one]⟩

end Iso

set_option maxHeartbeats 6400000 in

theorem main_scalar
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (μK : Measure (Gad K)) [hμK : μK.IsHaarMeasure]
    (μL : Measure (Gt K L)) [hμL : μL.IsHaarMeasure]
    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : Gad K → ℂ) (fa : Garch K → ℂ) (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ),
        AEStronglyMeasurable fa (archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable (fS v) (localHaar K v)) →
        (∀ g : Gad K, (∀ v ∉ S, cpt v g ∈ localIntegralSet K v) → f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt v g)) →
        (∀ g : Gad K, (∃ v ∉ S, cpt v g ∉ localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μK = cK * (∫ x, fa x ∂(archHaarK K)) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : Gt K L → ℂ) (Fa : Ht K L → ℂ) (FS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
        AEStronglyMeasurable Fa (archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable (FS v) (semiLocalHaar K L v)) →
        (∀ x : Gt K L, (∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
            F x = Fa (tensorArch K L x) * ∏ v ∈ S, FS v (tensorPlace K L v x)) →
        (∀ x : Gt K L, (∃ v ∉ S, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → F x = 0) →
          ∫ x, F x ∂μL = cL * (∫ y, Fa y ∂(archHaarL K L)) * ∏ v ∈ S, ∫ y, FS v y ∂(semiLocalHaar K L v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : Gad K → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)
    (fa : Garch K → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ)
    (hφ : IsSemiLocalFactorization K L S φ φa φf φS)
    (hf : IsUnitFactorization K S f fa ff fS)
    (hArch : AreMatchingArch K L σ φa fa)
    (hLoc : ∀ v ∈ S, AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AreMatchingLocal K L v σ
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (d : Gt K L) (ζ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (hd : d = sc ζ)
    (hN : normString K L (AdeleRing (𝓞 K) K) σ d = toTensorGL K L (AdeleRing (𝓞 K) K) (centralScalar (𝓞 K) K u))
    (τ : Measure (Tu u)) [hτ : τ.IsHaarMeasure]
    (τ₁ : Measure (twistedCentralizer K L (AdeleRing (𝓞 K) K) σ d)) [hτ₁ : τ₁.IsHaarMeasure]
    (hc : Coupled K L (AdeleRing (𝓞 K) K) σ (centralScalar (𝓞 K) K u) d 1 τ τ₁)
    (I I' : ℂ)
    (hI' : IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL d τ₁ (φ ∘ baseChangeGL K L) I')
    (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK (centralScalar (𝓞 K) K u) τ f I) :
    (cK : ℂ) * I' = cL * I := by
  subst hd
  classical

  obtain ⟨hgal, -, hzp⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  haveI := hgal
  have hgen : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ := fun θ => hzp ▸ Subgroup.mem_top θ

  obtain ⟨Ψ, hΨ⟩ := exists_psi σ hgen u ζ
  obtain ⟨Ψa, hΨa⟩ := exists_psi_a σ hgen u ζ
  have hΨv0 := fun v => exists_psi_v (K := K) (L := L) σ hgen u ζ v
  choose Ψv hΨv using hΨv0

  set e := centralizerCsEquiv (K := K) u with he_def
  set ea := centralizerScalarEquiv (R := InfiniteAdeleRing K) (uArch K u) with hea_def
  set ev := fun v : HeightOneSpectrum (𝓞 K) => centralizerScalarEquiv (R := v.adicCompletion K) (uAt K v u) with hev_def
  set Φ : Gad K ≃ₜ* Tz σ ζ := e.symm.trans Ψ with hΦ_def
  set Φa : Garch K ≃ₜ* Tza σ ζ := ea.symm.trans Ψa with hΦa_def
  set Φv : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v ≃ₜ* Tzv σ ζ v := fun v => (ev v).symm.trans (Ψv v) with hΦv_def
  have hΦ : ∀ g : Gad K, ((Φ g : Tz σ ζ) : Gt K L) = toTensorGL K L _ g := fun g => hΨ _
  have hΦa : ∀ g : Garch K, ((Φa g : Tza σ ζ) : Ht K L) = toTensorGL K L _ g := fun g => hΨa _
  have hΦv : ∀ v (g : Gv K v), ((Φv v g : Tzv σ ζ v) : Gsl K L v) = toTensorGL K L _ g := fun v g => hΨv v _
  have hmΦ : Measurable (Φ : Gad K → Tz σ ζ) := Φ.continuous.measurable
  have hmΦa : Measurable (Φa : Garch K → Tza σ ζ) := Φa.continuous.measurable
  have hmΦv : ∀ v, Measurable (Φv v : Gv K v → Tzv σ ζ v) := fun v => (Φv v).continuous.measurable
  have hmeas : Measurable (ea.symm : Garch K → Tua u) := ea.symm.continuous.measurable
  have hmevs : ∀ v, Measurable ((ev v).symm : Gv K v → Tuv u v) := fun v => (ev v).symm.continuous.measurable
  have hcj_a : Continuous (fun t : Tza σ ζ => (1 : Ht K L)⁻¹ * (t : Ht K L) * 1) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hcj_v : ∀ v, Continuous (fun t : Tzv σ ζ v => (1 : Gsl K L v)⁻¹ * (t : Gsl K L v) * 1) := fun v =>
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hct_a : Continuous (fun s : Tua u => toTensorGL K L (InfiniteAdeleRing K) (s : Garch K)) :=
    (continuous_toTensorGL' K L _).comp continuous_subtype_val
  have hct_v : ∀ v, Continuous (fun s : Tuv u v => toTensorGL K L (v.adicCompletion K) (s : Gv K v)) := fun v =>
    (continuous_toTensorGL' K L _).comp continuous_subtype_val

  set ν₀ : Measure (Gad K) := Measure.map e τ with hν₀_def
  haveI hν₀H : ν₀.IsHaarMeasure := e.isHaarMeasure_map τ
  set r : ℝ≥0 := haarScalarFactor ν₀ μK with hr_def
  have hr0 : 0 < r := haarScalarFactor_pos_of_isHaarMeasure ν₀ μK
  have hν₀ : ν₀ = r • μK := isMulLeftInvariant_eq_smul ν₀ μK

  have hτ₁Ψ : τ₁ = Measure.map Ψ τ := eq_map_of_coupled_one σ (centralScalar (𝓞 K) K u) (sc ζ) Ψ hΨ τ τ₁ hc
  have hme : Measurable (e : Tu u → Gad K) := e.continuous.measurable
  have hmes : Measurable (e.symm : Gad K → Tu u) := e.symm.continuous.measurable
  have hmΨ : Measurable (Ψ : Tu u → Tz σ ζ) := Ψ.continuous.measurable
  have hτν₀ : τ = Measure.map e.symm ν₀ := by
    rw [hν₀_def, Measure.map_map hmes hme]
    have : (e.symm : Gad K → Tu u) ∘ (e : Tu u → Gad K) = id := funext fun s => e.symm_apply_apply s
    rw [this, Measure.map_id]
  have hτ₁Φ : τ₁ = Measure.map Φ ν₀ := by
    rw [hτ₁Ψ, hτν₀, Measure.map_map hmΨ hmes]
    rfl

  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsMulRightInvariant := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  have hμKeq : μK = haarScalarFactor μK (adelicGLHaar (Fin 2) (𝓞 K) K) • adelicGLHaar (Fin 2) (𝓞 K) K :=
    isMulLeftInvariant_eq_smul μK _
  haveI hμKr : μK.IsMulRightInvariant := by rw [hμKeq]; infer_instance
  haveI hν₀r : ν₀.IsMulRightInvariant := by rw [hν₀]; infer_instance
  have hτ₁r : τ₁.IsMulRightInvariant := by rw [hτ₁Φ]; exact isMulRightInvariant_map_equiv Φ ν₀

  set τa : Measure (Tza σ ζ) := Measure.map Φa (archHaarK K) with hτa_def
  haveI hτaH : τa.IsHaarMeasure := Φa.isHaarMeasure_map _
  set τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tzv σ ζ v) := fun v => Measure.map (Φv v) (localHaar K v) with hτf_def
  have hτfH : ∀ v, (τf v).IsHaarMeasure := fun v => (Φv v).isHaarMeasure_map _
  have hτf1 : ∀ v : HeightOneSpectrum (𝓞 K), τf v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 := by
    intro v
    show Measure.map (Φv v) (localHaar K v) (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1
    rw [Measure.map_apply (hmΦv v)
      ((isOpen_semiLocalIntegralSet K L v).measurableSet.preimage continuous_subtype_val.measurable)]
    have hset : (Φv v) ⁻¹' (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = localIntegralSet K v := by
      ext g
      simp only [Set.mem_preimage, hΦv, toTensorGL_mem_semiLocalIntegralSet_iff]
    rw [hset, localHaar_localIntegralSet]

  set τKa : Measure (Tua u) := Measure.map ea.symm (archHaarK K) with hτKa_def
  haveI hτKaH : τKa.IsHaarMeasure := ea.symm.isHaarMeasure_map _
  set τKv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tuv u v) := fun v => Measure.map (ev v).symm (localHaar K v)
    with hτKv_def
  have hτKvH : ∀ v, (τKv v).IsHaarMeasure := fun v => (ev v).symm.isHaarMeasure_map _

  have hT : ∀ (S' : Finset (HeightOneSpectrum (𝓞 K))) (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
      (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
      AEStronglyMeasurable (fun t : Tza σ ζ => Wa t) τa →
      (∀ v ∈ S', AEStronglyMeasurable (fun t : Tzv σ ζ v => WS v t) (τf v)) →
      (∀ t : Tz σ ζ, (∀ v ∉ S', tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
          W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S', WS v (tensorPlace K L v (t : Gt K L))) →
      (∀ t : Tz σ ζ, (∃ v ∉ S', tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
        ∫ t, W t ∂τ₁ = ((r : ℝ) * cK : ℝ) * (∫ t, Wa t ∂τa) * ∏ v ∈ S', ∫ t, WS v t ∂(τf v) := by
    intro S' W Wa WS hWa hWS hfac hvan
    have hmeΦ : MeasurableEmbedding (Φ : Gad K → Tz σ ζ) := Φ.toHomeomorph.measurableEmbedding
    have hmeΦa : MeasurableEmbedding (Φa : Garch K → Tza σ ζ) := Φa.toHomeomorph.measurableEmbedding
    have hmeΦv : ∀ v, MeasurableEmbedding (Φv v : Gv K v → Tzv σ ζ v) := fun v => (Φv v).toHomeomorph.measurableEmbedding

    have h1 : ∫ t, W t ∂τ₁ = (r : ℂ) * ∫ g, W (Φ g) ∂μK := by
      rw [hτ₁Φ, hmeΦ.integral_map, hν₀, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

    have hfa' : AEStronglyMeasurable (fun x : Garch K => Wa (toTensorGL K L _ x)) (archHaarK K) := by
      have hWa' : AEStronglyMeasurable (fun t : Tza σ ζ => Wa t) (Measure.map Φa (archHaarK K)) := hWa
      have h' : AEStronglyMeasurable ((fun t : Tza σ ζ => Wa t) ∘ Φa) (archHaarK K) := hWa'.comp_measurable hmΦa
      refine h'.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Function.comp_apply, hΦa]
    have hfS' : ∀ v ∈ S', AEStronglyMeasurable (fun x : Gv K v => WS v (toTensorGL K L _ x)) (localHaar K v) := by
      intro v hv
      have hWS' : AEStronglyMeasurable (fun t : Tzv σ ζ v => WS v t) (Measure.map (Φv v) (localHaar K v)) := hWS v hv
      have h' : AEStronglyMeasurable ((fun t : Tzv σ ζ v => WS v t) ∘ Φv v) (localHaar K v) := hWS'.comp_measurable (hmΦv v)
      refine h'.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Function.comp_apply, hΦv]
    have hfacK : ∀ g : Gad K, (∀ v ∉ S', cpt v g ∈ localIntegralSet K v) →
        W (Φ g) = Wa (toTensorGL K L _ (glArch (𝓞 K) K g)) * ∏ v ∈ S', WS v (toTensorGL K L _ (cpt v g)) := by
      intro g hg
      have h := hfac (Φ g) (fun v hv => by
        rw [hΦ, tensorPlace_toTensorGL, toTensorGL_mem_semiLocalIntegralSet_iff]; exact hg v hv)
      rw [h, hΦ, tensorArch_toTensorGL]
      congr 1
    have hvanK : ∀ g : Gad K, (∃ v ∉ S', cpt v g ∉ localIntegralSet K v) → W (Φ g) = 0 := by
      rintro g ⟨v, hv, hgv⟩
      refine hvan (Φ g) ⟨v, hv, ?_⟩
      rw [hΦ, tensorPlace_toTensorGL, toTensorGL_mem_semiLocalIntegralSet_iff]
      exact hgv
    have h2 := hG S' (fun g => W (Φ g)) _ _ hfa' hfS' hfacK hvanK

    have h3 : ∫ t, Wa t ∂τa = ∫ x, Wa (toTensorGL K L _ x) ∂(archHaarK K) := by
      show ∫ t, Wa t ∂(Measure.map Φa (archHaarK K)) = _
      rw [hmeΦa.integral_map]
      simp only [hΦa]
    have h4 : ∀ v ∈ S', ∫ t, WS v t ∂(τf v) = ∫ x, WS v (toTensorGL K L _ x) ∂(localHaar K v) := by
      intro v _
      show ∫ t, WS v t ∂(Measure.map (Φv v) (localHaar K v)) = _
      rw [(hmeΦv v).integral_map]
      simp only [hΦv]
    rw [h1, h2, h3, Finset.prod_congr rfl h4]
    push_cast
    ring

  have hE := AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization_of_isMulRightInvariant
    K L σ μL hμL (archHaarL K L) cL hG' (sc ζ) τ₁ hτ₁ hτ₁r τa hτaH τf hτfH hτf1 ((r : ℝ) * cK) (by positivity) hT
    S φ φa φf φS hφ I' hI'

  obtain ⟨hφa, -, hφS, -, -, -⟩ := hφ
  obtain ⟨hfa, -, hfS, hprod, hzero, hfac⟩ := hf

  have hyv : ∀ v : HeightOneSpectrum (𝓞 K), IsNormConjugator K L (v.adicCompletion K) σ (sc (uAt K v u))
      (tensorPlace K L v (sc ζ)) 1 := by
    intro v
    unfold IsNormConjugator
    rw [inv_one, one_mul, mul_one, ← tensorPlace_normString, hN, tensorPlace_toTensorGL, localAt_centralScalar]
  have hcv : ∀ v : HeightOneSpectrum (𝓞 K), Coupled K L (v.adicCompletion K) σ (sc (uAt K v u))
      (tensorPlace K L v (sc ζ)) 1 (τKv v) (τf v) := by
    intro v
    show Measure.map (fun t : Tzv σ ζ v => (1 : Gsl K L v)⁻¹ * (t : Gsl K L v) * 1) (Measure.map (Φv v) (localHaar K v)) =
      Measure.map (fun s : Tuv u v => toTensorGL K L _ (s : Gv K v)) (Measure.map (ev v).symm (localHaar K v))
    rw [Measure.map_map (hcj_v v).measurable (hmΦv v), Measure.map_map (hct_v v).measurable (hmevs v)]
    congr 1
    funext g
    simp only [Function.comp_apply, hΦv, inv_one, one_mul, mul_one]
    rfl

  set φv : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ := fun v =>
    if v ∈ S then φS v else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) with hφv_def
  set fv : ∀ v : HeightOneSpectrum (𝓞 K), Gv K v → ℂ := fun v =>
    if v ∈ S then fS v else (localIntegralSet K v).indicator fun _ => (1 : ℂ) with hfv_def
  have hmv : ∀ v, AreMatchingLocal K L v σ (φv v) (fv v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hφv_def, hfv_def, hv, if_true]; exact hLoc v hv
    · simp only [hφv_def, hfv_def, hv, if_false]; exact hunit v hv
  have hφvt : ∀ v, IsSemiLocalTestFn K L v (φv v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hφv_def, hv, if_true]; exact hφS v hv
    · simp only [hφv_def, hv, if_false]; exact isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v
  have hfvt : ∀ v, IsLocalTestFn K v (fv v) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hfv_def, hv, if_true]; exact hfS v hv
    · simp only [hfv_def, hv, if_false]; exact isLocalTestFn_indicator_localIntegralSet K v

  have hlocal : ∀ (v : HeightOneSpectrum (𝓞 K)) (J : ℂ),
      IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v (sc ζ)) (τf v) (φv v) J → J = fv v (sc (uAt K v u)) := by
    intro v J hJ
    haveI := hτKvH v
    haveI := hτfH v
    exact (AutomorphicForm.areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf K L hprime σ hgen v
      (φv v) (hφvt v) (fv v) (hfvt v) (hmv v)).1 (sc (uAt K v u)) ⟨_, rfl⟩ (tensorPlace K L v (sc ζ)) 1 (hyv v)
      (τKv v) (τf v) (hτKvH v) (hτfH v) (hcv v) (fv v (sc (uAt K v u))) J hJ (isOrbitalIntegral_scalar K v (uAt K v u) (fv v))

  have hya : IsNormConjugator K L (InfiniteAdeleRing K) σ (sc (uArch K u)) (tensorArch K L (sc ζ)) 1 := by
    unfold IsNormConjugator
    rw [inv_one, one_mul, mul_one, ← tensorArch_normString, hN, tensorArch_toTensorGL, glArch_centralScalar]
  have hca : Coupled K L (InfiniteAdeleRing K) σ (sc (uArch K u)) (tensorArch K L (sc ζ)) 1 τKa τa := by
    show Measure.map (fun t : Tza σ ζ => (1 : Ht K L)⁻¹ * (t : Ht K L) * 1) (Measure.map Φa (archHaarK K)) =
      Measure.map (fun s : Tua u => toTensorGL K L _ (s : Garch K)) (Measure.map ea.symm (archHaarK K))
    rw [Measure.map_map hcj_a.measurable hmΦa, Measure.map_map hct_a.measurable hmeas]
    congr 1
    funext g
    simp only [Function.comp_apply, hΦa, inv_one, one_mul, mul_one]
    rfl
  have hrK : (archHaarK K).IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_generalLinearGroup_infiniteAdeleRing K (archHaarK K) inferInstance

  have harch : ∀ J : ℂ, IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L)
      (tensorArch K L (sc ζ)) τa (φa ∘ archIdentGL K L) J → J = fa (sc (uArch K u)) := by
    intro J hJ
    exact AutomorphicForm.areMatchingArch_central_transfer_of_scalar K L hprime σ hgen φa hφa fa hfa hArch (sc (uArch K u)) ⟨_, rfl⟩
      (tensorArch K L (sc ζ)) 1 hya τKa τa hτKaH hτaH hca (fa (sc (uArch K u))) J hJ
      (isOrbitalIntegralOn_arch_scalar K hrK (uArch K u) fa)

  have hIval : I = f (centralScalar (𝓞 K) K u) * ((r⁻¹ : ℝ≥0) : ℝ) := by
    rw [orbitalIntegral_scalar_eq μK u τ f I hI]
    congr 2
    have hmul := haarScalarFactor_eq_mul μK ν₀ μK
    rw [haarScalarFactor_self] at hmul
    show ((haarScalarFactor μK ν₀ : ℝ≥0) : ℝ) = ((r⁻¹ : ℝ≥0) : ℝ)
    rw [eq_inv_of_mul_eq_one_left hmul.symm]

  have hfu : f (centralScalar (𝓞 K) K u) = fa (sc (uArch K u)) * ff (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) := by
    rw [hfac, glArch_centralScalar]

  rcases hE with ⟨hI'0, hobs⟩ | ⟨S₁, hSS₁, Ia, Iv, hIa, hIvS, hIvnS, hprodT⟩
  ·
    rw [hI'0, mul_zero, hIval]
    suffices h0 : f (centralScalar (𝓞 K) K u) = 0 by rw [h0, zero_mul, mul_zero]
    rw [hfu]
    rcases hobs with harch0 | ⟨v, hvS, hv0⟩ | ⟨v, hvS, hv0⟩
    ·
      have h0 : IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) (tensorArch K L (sc ζ)) τa
          (φa ∘ archIdentGL K L) 0 :=
        ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => absurd (harch0 x) hx⟩, by simp⟩
      rw [← harch 0 h0, zero_mul]
    ·
      have h0 : IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v (sc ζ)) (τf v) (φv v) 0 := by
        refine ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => ?_⟩, by simp⟩
        simp only [hφv_def, hvS, if_true] at hx
        exact absurd (hv0 x) hx
      have hfv0 : fS v (sc (uAt K v u)) = 0 := by
        have := hlocal v 0 h0
        simp only [hfv_def, hvS, if_true] at this
        exact this.symm
      by_cases hint : ∀ w ∉ S, cpt w (centralScalar (𝓞 K) K u) ∈ localIntegralSet K w
      · rw [hprod _ hint, Finset.prod_eq_zero hvS (by rw [← cpt_centralScalar] at hfv0; exact hfv0), mul_zero]
      · push Not at hint
        obtain ⟨w, hw, hw'⟩ := hint
        rw [hzero _ ⟨w, hw, hw'⟩, mul_zero]
    ·
      have h0 : IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v (sc ζ)) (τf v) (φv v) 0 := by
        refine ⟨fun _ => 0, ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun x hx => ?_⟩, by simp⟩
        simp only [hφv_def, hvS, if_false] at hx
        exact absurd (Set.indicator_of_notMem (hv0 x) _) hx
      have hfv0 : (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (sc (uAt K v u)) = 0 := by
        have := hlocal v 0 h0
        simp only [hfv_def, hvS, if_false] at this
        exact this.symm
      have hnot : cpt v (centralScalar (𝓞 K) K u) ∉ localIntegralSet K v := by
        intro hmem
        rw [cpt_centralScalar] at hmem
        rw [Set.indicator_of_mem hmem] at hfv0
        exact one_ne_zero hfv0
      rw [hzero _ ⟨v, hvS, hnot⟩, mul_zero]
  ·
    set B : Finset (HeightOneSpectrum (𝓞 K)) := (finite_setOf_cpt_not_mem (centralScalar (𝓞 K) K u)).toFinset with hB
    set T : Finset (HeightOneSpectrum (𝓞 K)) := S₁ ∪ B with hT
    have hIT := hprodT T Finset.subset_union_left

    have hIaval : Ia = fa (sc (uArch K u)) := harch Ia hIa
    have hIvval : ∀ v, Iv v = fv v (sc (uAt K v u)) := by
      intro v
      by_cases hv : v ∈ S
      · have h := hIvS v hv
        have : φS v = φv v := by simp only [hφv_def, hv, if_true]
        rw [this] at h
        exact hlocal v _ h
      · have h := hIvnS v hv
        have : ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) = φv v := by simp only [hφv_def, hv, if_false]
        rw [this] at h
        exact hlocal v _ h

    have hprodT' : ∏ v ∈ T, Iv v = ff (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) := by
      rw [Finset.prod_congr rfl fun v _ => hIvval v]
      by_cases hint : ∀ w ∉ S, cpt w (centralScalar (𝓞 K) K u) ∈ localIntegralSet K w
      · rw [hprod _ hint]
        have hST : S ⊆ T := hSS₁.trans Finset.subset_union_left
        rw [← Finset.prod_sdiff hST]
        have h1 : ∏ v ∈ T \ S, fv v (sc (uAt K v u)) = 1 := by
          refine Finset.prod_eq_one fun v hv => ?_
          rw [Finset.mem_sdiff] at hv
          simp only [hfv_def, hv.2, if_false]
          rw [Set.indicator_of_mem]
          rw [← cpt_centralScalar]
          exact hint v hv.2
        rw [h1, one_mul]
        refine Finset.prod_congr rfl fun v hv => ?_
        simp only [hfv_def, hv, if_true, cpt_centralScalar]
      · push Not at hint
        obtain ⟨w, hw, hw'⟩ := hint
        rw [hzero _ ⟨w, hw, hw'⟩]
        have hwT : w ∈ T := by
          refine Finset.mem_union_right _ ?_
          rw [hB, Set.Finite.mem_toFinset]
          exact hw'
        refine Finset.prod_eq_zero hwT ?_
        simp only [hfv_def, hw, if_false]
        rw [Set.indicator_of_notMem]
        rw [← cpt_centralScalar]
        exact hw'

    rw [hIT, hIaval, hprodT', hIval, hfu]
    have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hcK0 : (cK : ℂ) ≠ 0 := by exact_mod_cast hcK.ne'
    push_cast
    field_simp

end MainScalar

end AutomorphicForm.CentralCoupled
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled.AutomorphicForm P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled.AutomorphicForm.CentralCoupled"
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled.AutomorphicForm P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled.AutomorphicForm.CentralCoupled"

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open AutomorphicForm.CentralCoupled in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (μK : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hμK : μK.IsHaarMeasure)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμL : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μL)
    (cK cL : ℝ) (hcK : 0 < cK) (hcL : 0 < cL)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa
          (AutomorphicForm.archHaarK K) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μK = cK * (∫ x, fa x ∂(AutomorphicForm.archHaarK K)) *
            ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (hG' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa
          (AutomorphicForm.archHaarL K L) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v)
          (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) *
              ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = 0) →
          ∫ x, F x ∂μL = cL * (∫ y, Fa y ∂(AutomorphicForm.archHaarL K L)) *
            ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ w : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (hArch : AutomorphicForm.AreMatchingArch K L σ φa fa)
    (hLoc : ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AutomorphicForm.AreMatchingLocal K L v σ
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (δ y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hy : AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ
      (AutomorphicForm.centralScalar (𝓞 K) K u) δ y)
    (τ : Measure (Subgroup.centralizer
      ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : τ.IsHaarMeasure) (hτ' : τ'.IsHaarMeasure)
    (hc : AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ
      (AutomorphicForm.centralScalar (𝓞 K) K u) δ y τ τ')
    (I I' : ℂ)
    (hI' : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μL δ τ'
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I')
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μK
      (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I) :
    (cK : ℂ) * I' = cL * I := by
  haveI := hμK
  haveI : μL.IsHaarMeasure := hμL
  haveI : τ.IsHaarMeasure := hτ
  haveI : τ'.IsHaarMeasure := hτ'

  obtain ⟨-, hord, -⟩ := AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  have hσpow : σ ^ Module.finrank K L = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ

  obtain ⟨ζ, hζ⟩ := exists_conj_eq_scalar_of_coupled K L σ (AdeleRing (𝓞 K) K)
    (AutomorphicForm.centralScalar (𝓞 K) K u) ⟨u, rfl⟩ δ y τ τ' inferInstance hc

  have h1 := isTwistedOrbitalIntegralOn_conj σ μL δ y τ' _ I' hI'
  have h2 := coupled_one_of_coupled σ (AutomorphicForm.centralScalar (𝓞 K) K u) δ y τ τ' hc
  haveI h3 := isHaarMeasure_map_conjIso σ δ y τ'

  have hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
      (y⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ y) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u) := by
    rw [normString_conj σ hσpow]
    exact hy.symm
  exact main_scalar hprime σ hσ μK μL cK cL hcK hcL hG hG' S φ f φa φf φS fa ff fS hφ hf hArch hLoc hunit u
    (y⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ y) ζ hζ hN τ _ h2 I I' h1 hI

end S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled
end P2MW
export P2MW.S_AutomorphicForm_mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_coupled (solution)
