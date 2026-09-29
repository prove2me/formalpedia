-- Prove2me | solution 1 for AutomorphicForm.apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/bd36d3ed-7198-51f1-b543-8b98b1b011f7

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AlgEquiv_isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one
import Theorems.Thm_AutomorphicForm_areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf
import Theorems.Thm_AutomorphicForm_exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open NumberField IsDedekindDomain TensorProduct
open scoped TensorProduct.RightActions Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "toTensorGL IsSemiLocalTestFn semiLocalIntegralSet isSemiLocalTestFn_indicator_semiLocalIntegralSet sigmaTensor sigmaGL normString IsNormConjugator IsNormOf AreMatchingLocal IsUnitFactorization IsLocalTestFn localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet isLocalTestFn_indicator_localIntegralSet localGLBorel borelSpace_localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet localCentralizer IsSectionFn IsOrbitalIntegral centralScalar areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two"
namespace CentralVanishing
p2m_open "AutomorphicForm"

section NormAlgebra

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

def sT : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ := Units.map (sigmaTensor K L A σ).toMonoidHom

def scalarNorm (z : (L ⊗[K] A)ˣ) : (L ⊗[K] A)ˣ :=
  ((List.range (Module.finrank K L)).map fun i => (⇑(sT (A := A) σ))^[i] z).prod

def ι : Aˣ →* (L ⊗[K] A)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom

theorem sigmaGL_scalar (z : (L ⊗[K] A)ˣ) :
    sigmaGL K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (sT σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show sigmaTensor K L A σ ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : Matrix (Fin 2) (Fin 2) _) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [sT]

theorem iterate_sigmaGL_scalar (i : ℕ) (z : (L ⊗[K] A)ˣ) :
    (⇑(sigmaGL K L A σ))^[i] (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) ((⇑(sT (A := A) σ))^[i] z) :=
  (Function.Semiconj.iterate_right (f := (Matrix.GeneralLinearGroup.scalar (Fin 2) : (L ⊗[K] A)ˣ → _))
    (ga := sT (A := A) σ) (gb := sigmaGL K L A σ) (fun x => (sigmaGL_scalar σ x).symm) i z).symm

theorem normString_scalar (z : (L ⊗[K] A)ˣ) :
    normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (scalarNorm σ z) := by
  unfold normString scalarNorm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact iterate_sigmaGL_scalar σ i z

theorem det_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.det (sigmaGL K L A σ g) = sT σ (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  show Matrix.det ((sigmaTensor K L A σ).mapMatrix (g : Matrix (Fin 2) (Fin 2) _)) = sigmaTensor K L A σ (Matrix.det _)
  rw [RingHom.map_det]

theorem det_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.det (normString K L A σ δ) = scalarNorm σ (Matrix.GeneralLinearGroup.det δ) := by
  unfold normString scalarNorm
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact Function.Semiconj.iterate_right (f := (Matrix.GeneralLinearGroup.det : GL (Fin 2) (L ⊗[K] A) → _))
    (ga := sigmaGL K L A σ) (gb := sT (A := A) σ) (fun x => det_sigmaGL σ x) i δ

theorem scalarNorm_mul (x y : (L ⊗[K] A)ˣ) :
    scalarNorm σ (x * y) = scalarNorm σ x * scalarNorm σ y := by
  unfold scalarNorm
  rw [show (fun i => (⇑(sT (A := A) σ))^[i] (x * y)) = fun i => (⇑(sT (A := A) σ))^[i] x * (⇑(sT (A := A) σ))^[i] y
    from funext fun i => iterate_map_mul (sT (A := A) σ) i x y]
  exact List.prod_map_mul (M := (L ⊗[K] A)ˣ)

theorem scalarNorm_one : scalarNorm (A := A) σ 1 = 1 := by
  unfold scalarNorm
  have : ((List.range (Module.finrank K L)).map fun i => (⇑(sT (A := A) σ))^[i] (1 : (L ⊗[K] A)ˣ)) =
      (List.range (Module.finrank K L)).map fun _ => (1 : (L ⊗[K] A)ˣ) :=
    List.map_congr_left fun i _ => iterate_map_one (sT (A := A) σ) i
  rw [this, List.prod_map_one]

def scalarNormHom : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ where
  toFun := scalarNorm σ
  map_one' := scalarNorm_one σ
  map_mul' := scalarNorm_mul σ

@[scoped simp] theorem scalarNormHom_apply (z : (L ⊗[K] A)ˣ) : scalarNormHom (A := A) σ z = scalarNorm σ z := rfl

theorem sT_ι (r : Aˣ) : sT σ (ι (K := K) (L := L) r) = ι r := by
  refine Units.ext ?_
  show sigmaTensor K L A σ ((1 : L) ⊗ₜ (r : A)) = (1 : L) ⊗ₜ (r : A)
  simp [sigmaTensor]

theorem scalarNorm_ι (r : Aˣ) : scalarNorm σ (ι (K := K) (L := L) r) = ι r ^ Module.finrank K L := by
  unfold scalarNorm
  have : ((List.range (Module.finrank K L)).map fun i => (⇑(sT (A := A) σ))^[i] (ι (K := K) (L := L) r)) =
      (List.range (Module.finrank K L)).map fun _ => ι (K := K) (L := L) r := by
    refine List.map_congr_left fun i _ => ?_
    exact Function.iterate_fixed (sT_ι σ r) i
  rw [this, List.map_const', List.prod_replicate, List.length_range]

theorem toTensorGL_scalar (r : Aˣ) :
    toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) r) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ι (K := K) (L := L) r) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) A) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [ι]

theorem det_toTensorGL (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (toTensorGL K L A g) = ι (K := K) (L := L) (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  show Matrix.det ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.mapMatrix
      (g : Matrix (Fin 2) (Fin 2) A)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom (Matrix.det (g : Matrix (Fin 2) (Fin 2) A))
  rw [RingHom.map_det]

theorem det_scalar_two {R : Type*} [CommRing R] (r : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) r) = r ^ 2 := by
  refine Units.ext ?_
  show Matrix.det (Matrix.scalar (Fin 2) (r : R)) = ((r ^ 2 : Rˣ) : R)
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp [pow_two]

theorem exists_scalar_of_isNormOf_scalar (hodd : Odd (Module.finrank K L)) (r : Aˣ)
    (δ : GL (Fin 2) (L ⊗[K] A)) (h : IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) r) δ) :
    ∃ z : (L ⊗[K] A)ˣ, normString K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) r) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨k, hk⟩ := hodd

  have hdet : ι (K := K) (L := L) r ^ 2 = scalarNorm σ (Matrix.GeneralLinearGroup.det δ) := by
    have := congrArg Matrix.GeneralLinearGroup.det hy
    rw [det_toTensorGL, det_scalar_two, map_pow, map_mul, map_mul, map_inv, det_normString,
      mul_comm ((Matrix.GeneralLinearGroup.det y)⁻¹) _, mul_assoc, inv_mul_cancel, mul_one] at this
    exact this
  refine ⟨ι (K := K) (L := L) r * ((Matrix.GeneralLinearGroup.det δ)⁻¹) ^ k, ?_⟩
  rw [normString_scalar, toTensorGL_scalar]
  congr 1
  show scalarNormHom σ _ = _
  rw [map_mul, map_pow, map_inv, scalarNormHom_apply, scalarNormHom_apply, scalarNorm_ι, ← hdet, hk,
    inv_pow, ← pow_mul, pow_succ, mul_comm (2 : ℕ) k, mul_comm _ ((ι (K := K) (L := L) r ^ (k * 2))⁻¹), ← mul_assoc,
    inv_mul_cancel, one_mul]

end NormAlgebra

section Central

variable {R : Type*} [CommRing R]

theorem scalar_mul_comm (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem conj_scalar (c : Rˣ) (g : GL (Fin 2) R) :
    g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem centralizer_scalar_eq_top (c : Rˣ) :
    Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) R)) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact (scalar_mul_comm c g).symm

def companion (u : Rˣ) : GL (Fin 2) R where
  val := !![0, (u : R); 1, 0]
  inv := !![0, 1; ((u⁻¹ : Rˣ) : R), 0]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem companion_mul_self (u : Rˣ) :
    companion u * companion u = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  refine Units.ext ?_
  show !![0, (u : R); 1, 0] * !![0, (u : R); 1, 0] = Matrix.scalar (Fin 2) (u : R)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]

end Central

section DegreeTwo

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable {A : Type} [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) : sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show sigmaTensor K L A σ ((1 : L) ⊗ₜ ((g : Matrix (Fin 2) (Fin 2) A) i j)) = (1 : L) ⊗ₜ ((g : Matrix (Fin 2) (Fin 2) A) i j)
  simp [sigmaTensor]

theorem isNormOf_scalar_of_finrank_eq_two (h2 : Module.finrank K L = 2) (u : Aˣ) :
    IsNormOf K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) (toTensorGL K L A (companion u)) := by
  refine ⟨1, ?_⟩
  unfold IsNormConjugator normString
  rw [h2, inv_one, one_mul, mul_one]
  show _ = ((List.range 2).map fun i => (⇑(sigmaGL K L A σ))^[i] (toTensorGL K L A (companion u))).prod
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, Function.iterate_zero, Function.iterate_one, id,
    List.singleton_append, sigmaGL_toTensorGL]
  rw [← map_mul, companion_mul_self]

end DegreeTwo

section LocalScalar

open MeasureTheory MeasureTheory.Measure

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

scoped instance instMeasurableSpaceGv : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
scoped instance instBorelSpaceGv : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
scoped instance instLocallyCompactGv : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := locallyCompactSpace_localGL K v
scoped instance instT2Gv : T2Space (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space
scoped instance instSecondCountableGv : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGv (H : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
    MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGv (H : Subgroup (GL (Fin 2) (v.adicCompletion K))) : BorelSpace H := ⟨rfl⟩
scoped instance instIsHaarLocalHaar : IsHaarMeasure (localHaar K v) := isHaarMeasure_localHaar K v

def centralizerScalarEquiv (c : (v.adicCompletion K)ˣ) :
    localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≃ₜ* GL (Fin 2) (v.adicCompletion K) :=
  { (MulEquiv.subgroupCongr (centralizer_scalar_eq_top c)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk continuous_id }

theorem centralizerScalarEquiv_symm_apply_coe (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    (((centralizerScalarEquiv K v c).symm g : localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
      GL (Fin 2) (v.adicCompletion K)) = g := rfl

theorem exists_isOrbitalIntegral_scalar_ne_zero (c : (v.adicCompletion K)ˣ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≠ 0) :
    ∃ (τ : Measure (localCentralizer K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
      (_ : IsHaarMeasure τ) (I : ℂ),
      IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ fv I ∧ I ≠ 0 := by
  set γ := Matrix.GeneralLinearGroup.scalar (Fin 2) c with hγ
  set e := centralizerScalarEquiv K v c with he
  set τ : Measure (localCentralizer K v γ) := Measure.map e.symm (localHaar K v) with hτ
  haveI hτH : IsHaarMeasure τ := e.symm.isHaarMeasure_map (localHaar K v)

  haveI : (localHaar K v).IsMulRightInvariant :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
      (localHaar K v)).1
  set A := localIntegralSet K v with hA
  have hAm : MeasurableSet A := (isOpen_localIntegralSet K v).measurableSet
  set w : GL (Fin 2) (v.adicCompletion K) → ℝ := A.indicator fun _ => (1 : ℝ) with hw
  have hsec : IsSectionFn K v γ τ fv w := by
    refine ⟨fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x,
      measurable_const.indicator hAm,
      HasCompactSupport.intro (isCompact_localIntegralSet K v) fun x hx => Set.indicator_of_notMem hx _,
      fun x _ => ?_⟩
    have hmeas : (e.symm.toHomeomorph.toMeasurableEquiv : GL (Fin 2) (v.adicCompletion K) → localCentralizer K v γ) = e.symm := rfl
    calc ∫ t : localCentralizer K v γ, w ((t : GL (Fin 2) (v.adicCompletion K)) * x) ∂τ
        = ∫ g, w (((e.symm.toHomeomorph.toMeasurableEquiv g : localCentralizer K v γ) :
            GL (Fin 2) (v.adicCompletion K)) * x) ∂(localHaar K v) := by
          rw [hτ, ← hmeas, integral_map_equiv]
      _ = ∫ g, ((fun g => g * x) ⁻¹' A).indicator 1 g ∂(localHaar K v) := by
          congr 1
      _ = (localHaar K v).real ((fun g => g * x) ⁻¹' A) := integral_indicator_one (hAm.preimage (measurable_mul_const x))
      _ = (localHaar K v).real A := by
          rw [measureReal_def, measureReal_def, ← Measure.map_apply (measurable_mul_const x) hAm,
            map_mul_right_eq_self]
      _ = 1 := by rw [measureReal_def, hA, localHaar_localIntegralSet, ENNReal.toReal_one]
  refine ⟨τ, hτH, ∫ x, fv (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v), ⟨w, hsec, rfl⟩, ?_⟩
  have hint : ∫ x, fv (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v) = fv γ := by
    have h1 : (fun x => fv (x⁻¹ * γ * x) * (w x : ℂ)) = fun x => A.indicator (fun _ => fv γ) x := by
      funext x
      rw [hγ, conj_scalar]
      by_cases hx : x ∈ A
      · simp [hw, hx]
      · simp [hw, hx]
    rw [h1, integral_indicator_const _ hAm, measureReal_def, hA, localHaar_localIntegralSet, ENNReal.toReal_one,
      one_smul]
  rw [hint]
  exact hfv

end LocalScalar

section Main

open MeasureTheory

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finComponent_glFin_centralScalar (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ c : (v.adicCompletion K)ˣ,
      AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine ⟨Units.map (((AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K)) :
      AdeleRing (𝓞 K) K →* v.adicCompletion K) u, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show ((AdelicLevel.finAdeleEval (𝓞 K) K v).comp (AdelicLevel.adeleFin (𝓞 K) K))
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem main
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : IsUnitFactorization K S f fa ff fS)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ S, IsSemiLocalTestFn K L v (φS v))
    (hLoc : ∀ v ∈ S, AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AreMatchingLocal K L v σ
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : ¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      IsNormOf K L (AdeleRing (𝓞 K) K) σ (centralScalar (𝓞 K) K u) δ) :
    f (centralScalar (𝓞 K) K u) = 0 := by
  obtain ⟨hGal, hord, htop⟩ :=
    AlgEquiv.isGalois_and_orderOf_eq_finrank_of_finrank_prime_of_ne_one K L hprime σ hσ
  haveI := hGal
  have hgen : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ := fun θ => by rw [htop]; exact Subgroup.mem_top θ
  by_cases h2 : Module.finrank K L = 2
  ·
    exact absurd ⟨_, isNormOf_scalar_of_finrank_eq_two (A := AdeleRing (𝓞 K) K) σ h2 u⟩ hu

  have hodd : Odd (Module.finrank K L) := hprime.odd_of_ne_two h2
  by_contra hne
  obtain ⟨-, -, hfS, hprod, hzero, hfac⟩ := hf

  have hint : ∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v
      (AdelicLevel.glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) ∈ localIntegralSet K v := by
    by_contra h
    push Not at h
    obtain ⟨v, hv, hv'⟩ := h
    exact hne (by rw [hfac, hzero _ ⟨v, hv, hv'⟩, mul_zero])
  have hSne : ∀ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v
      (AdelicLevel.glFin (𝓞 K) K (centralScalar (𝓞 K) K u))) ≠ 0 := by
    intro v hv h0
    exact hne (by rw [hfac, hprod _ hint, Finset.prod_eq_zero hv h0, mul_zero])

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
      normString K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
        toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (centralScalar (𝓞 K) K u))) := by
    intro v
    obtain ⟨c, hc⟩ := finComponent_glFin_centralScalar K v u
    rw [hc]

    set φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ :=
      if v ∈ S then φS v else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) with hφv_def
    set fv : GL (Fin 2) (v.adicCompletion K) → ℂ :=
      if v ∈ S then fS v else (localIntegralSet K v).indicator fun _ => (1 : ℂ) with hfv_def
    have hm : AreMatchingLocal K L v σ φv fv := by
      by_cases hv : v ∈ S
      · simp only [hφv_def, hfv_def, hv, if_true]; exact hLoc v hv
      · simp only [hφv_def, hfv_def, hv, if_false]; exact hunit v hv
    have hφv : IsSemiLocalTestFn K L v φv := by
      by_cases hv : v ∈ S
      · simp only [hφv_def, hv, if_true]; exact hφS v hv
      · simp only [hφv_def, hv, if_false]; exact isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v
    have hfv : IsLocalTestFn K v fv := by
      by_cases hv : v ∈ S
      · simp only [hfv_def, hv, if_true]; exact hfS v hv
      · simp only [hfv_def, hv, if_false]; exact isLocalTestFn_indicator_localIntegralSet K v
    have hval : fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ≠ 0 := by
      by_cases hv : v ∈ S
      · simp only [hfv_def, hv, if_true]; rw [← hc]; exact hSne v hv
      · simp only [hfv_def, hv, if_false]
        have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ localIntegralSet K v := by
          rw [← hc]; exact hint v hv
        rw [Set.indicator_of_mem hmem]
        exact one_ne_zero

    have key := (AutomorphicForm.areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf
      K L hprime σ hgen v φv hφv fv hfv hm).2 (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ⟨c, rfl⟩
    have hnorm : ∃ δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ := by
      by_contra hno
      obtain ⟨τ, hτ, I, hI, hI0⟩ := exists_isOrbitalIntegral_scalar_ne_zero K v c fv hval
      exact hI0 (key hno τ hτ I hI)
    obtain ⟨δ, hδ⟩ := hnorm
    exact exists_scalar_of_isNormOf_scalar σ hodd c δ hδ

  obtain ⟨z, hz⟩ :=
    AutomorphicForm.exists_normString_scalar_eq_toTensorGL_centralScalar_of_forall_of_finrank_ne_two
      K L hprime h2 σ hσ u hloc
  exact hu ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) z, 1, by
    rw [IsNormConjugator, inv_one, one_mul, mul_one, hz]⟩

end Main

end AutomorphicForm.CentralVanishing
p2m_reactivate "P2MW.S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime.AutomorphicForm P2MW.S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime.AutomorphicForm.CentralVanishing"
p2m_reactivate "P2MW.S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime.AutomorphicForm P2MW.S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime.AutomorphicForm.CentralVanishing"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ S, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))
    (hLoc : ∀ v ∈ S, AutomorphicForm.AreMatchingLocal K L v σ (φS v) (fS v))
    (hunit : ∀ v ∉ S, AutomorphicForm.AreMatchingLocal K L v σ
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : ¬ ∃ δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K u) δ) :
    f (AutomorphicForm.centralScalar (𝓞 K) K u) = 0 :=
  AutomorphicForm.CentralVanishing.main K L hprime σ hσ S f fa ff fS hf φS hφS hLoc hunit u hu

end S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime
end P2MW
export P2MW.S_AutomorphicForm_apply_centralScalar_eq_zero_of_not_exists_isNormOf_of_isUnitFactorization_of_prime (solution)
