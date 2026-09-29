-- Prove2me | solution 1 for AutomorphicForm.exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/29c22194-7b17-52e6-bf3c-70fcaf6b141f

import Mathlib
import Theorems.Thm_AutomorphicForm_archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2
import Theorems.Thm_LT_TwistedNorm_exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
import Theorems.Thm_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace R3OffFam

open LT.TwistedNorm LT.TwistedNorm.GL2

section Family

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

abbrev sc : Lˣ →* GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2)

abbrev σG (σ : L ≃ₐ[F] L) : GL (Fin 2) L →* GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

abbrev σU (σ : L ≃ₐ[F] L) : Lˣ →* Lˣ := Units.map ((σ : L →+* L) : L →* L)

theorem sc_comm (u : Lˣ) (g : GL (Fin 2) L) : sc u * g = g * sc u := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (u : L) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) L)).eq

theorem mul_sc_left (g k : GL (Fin 2) L) (u : Lˣ) : g * (sc u * k) = sc u * (g * k) := by
  rw [← mul_assoc, ← sc_comm, mul_assoc]

theorem σG_sc (σ : L ≃ₐ[F] L) (u : Lˣ) : σG σ (sc u) = sc (σU σ u) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change σ ((Matrix.scalar (Fin 2) (u : L)) i j) = Matrix.scalar (Fin 2) (σ (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem fam_of_transport_fam (σ : L ≃ₐ[F] L) (v : Lˣ) (γ δ : GL (Fin 2) L)
    (h : ∃ (h : GL (Fin 2) L) (u : Lˣ), sc v * (γ * δ * (σG σ γ)⁻¹) = sc u * (h⁻¹ * σG σ h)) :
    ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = sc u * (h⁻¹ * σG σ h) := by
  obtain ⟨h, u, hh⟩ := h
  refine ⟨h * γ, v⁻¹ * u, ?_⟩
  have h2 : γ * δ * (σG σ γ)⁻¹ = sc (v⁻¹ * u) * (h⁻¹ * σG σ h) := by
    have h4 := congrArg (fun g => (sc v)⁻¹ * g) hh
    simp only [inv_mul_cancel_left] at h4
    rw [h4, ← mul_assoc, ← map_inv, ← map_mul]
  have h3 : δ = γ⁻¹ * (γ * δ * (σG σ γ)⁻¹) * σG σ γ := by group
  rw [h3, h2, ← mul_assoc γ⁻¹, ← sc_comm, map_mul (σG σ), mul_inv_rev]
  simp only [mul_assoc]

theorem transport_injective (σ : L ≃ₐ[F] L) (v : Lˣ) (γ : GL (Fin 2) L) :
    Function.Injective fun δ : GL (Fin 2) L => sc v * (γ * δ * (σG σ γ)⁻¹) := by
  intro δ₁ δ₂ h
  have h' : sc v * (γ * δ₁ * (σG σ γ)⁻¹) = sc v * (γ * δ₂ * (σG σ γ)⁻¹) := h
  have := mul_left_cancel h'
  exact mul_left_cancel (mul_right_cancel this)

theorem sigmaPartialNorm_sc_mul (σ : L ≃ₐ[F] L) (u : Lˣ) (δ : GL (Fin 2) L) (r : ℕ) :
    sigmaPartialNorm (σG σ) (sc u * δ) r =
      sc (sigmaPartialNorm (σU σ) u r) * sigmaPartialNorm (σG σ) δ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul, map_mul,
        σG_sc]
      rw [mul_assoc (sc u), ← mul_assoc δ, ← sc_comm _ δ]
      simp only [mul_assoc]

theorem scalar_mul_mem_cells {γ : GL (Fin 2) F} (a : Fˣ)
    (hγ : γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ ∈ AutomorphicForm.ellipticCell F ∨
      Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ ∈ AutomorphicForm.centralCell F := by
  have hcoe : ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (a : F) • (γ : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul]
    change Matrix.scalar (Fin 2) (a : F) * _ = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rcases hγ with hγ | hγ
  · left
    rw [AutomorphicForm.mem_ellipticCell_iff, AutomorphicForm.IsEllipticType, hcoe]
    intro b hb
    apply hγ (b / a)
    rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at hb ⊢
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.trace_fin_two, Matrix.det_fin_two,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] at hb ⊢
    have ha : (a : F) ≠ 0 := a.ne_zero
    field_simp
    linear_combination hb
  · right
    obtain ⟨c, hc⟩ := AutomorphicForm.mem_centralCell_iff.mp hγ
    refine AutomorphicForm.mem_centralCell_iff.mpr ⟨a * c, ?_⟩
    rw [hcoe, hc, smul_smul]

variable [FiniteDimensional F L] [IsGalois F L]

theorem isNormRep_of_normClassMap_mk_eq {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (hN : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hN
  obtain ⟨Q, hQ⟩ := hN
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, ?_⟩
  rw [← hQ, map_mul, map_mul, map_inv, ← hP]
  group

theorem coe_sc_norm (σ : L ≃ₐ[F] L) (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    ((sc (sigmaNormPow (σU σ) (Module.finrank F L) u) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L (Algebra.norm F (u : L)) • (1 : Matrix (Fin 2) (Fin 2) L) := by
  rw [← coe_sigmaNormPow_units_eq_algebraMap_norm hgen u]
  ext i j
  change Matrix.scalar (Fin 2) _ i j = _
  rw [Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

def normUnit (u : Lˣ) : Fˣ :=
  Units.mk0 (Algebra.norm F (u : L)) (Algebra.norm_ne_zero_iff.mpr u.ne_zero)

theorem isNormRep_sc_mul {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) F} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (u : Lˣ) :
    IsNormRep σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (normUnit (F := F) u) * γ) (sc u * δ) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_def, sigmaPartialNorm_sc_mul, ← sigmaNormPow_def, ← sigmaNormPow_def, map_mul]
  have hnorm : P⁻¹ * (sc (sigmaNormPow (σU σ) (Module.finrank F L) u) *
      sigmaNormPow (σG σ) (Module.finrank F L) δ) * P =
      sc (sigmaNormPow (σU σ) (Module.finrank F L) u) *
        (P⁻¹ * sigmaNormPow (σG σ) (Module.finrank F L) δ * P) := by
    simp only [mul_assoc, mul_sc_left]
  rw [hnorm]
  erw [hP]
  congr 1
  apply Units.ext
  rw [coe_sc_norm σ hgen u]
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change _ = algebraMap F L (Matrix.scalar (Fin 2) _ i j)
  rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp [normUnit]
  · simp [hij]

theorem sc_mul_mem_I {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) (u : Lˣ) :
    ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ (sc u * δ)) = ConjClasses.mk γ := by
  obtain ⟨γ, hγ, hN⟩ := hδ
  refine ⟨_, scalar_mul_mem_cells (normUnit (F := F) u) hγ, ?_⟩
  exact normClassMap_mk_eq_of_isNormRep hgen (isNormRep_sc_mul hgen (isNormRep_of_normClassMap_mk_eq hgen hN) u)

theorem transport_mem_I {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L}
    (hδ : ∃ γ : GL (Fin 2) F, (γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) (v : Lˣ) (γ : GL (Fin 2) L) :
    ∃ γ' : GL (Fin 2) F, (γ' ∈ AutomorphicForm.ellipticCell F ∨ γ' ∈ AutomorphicForm.centralCell F) ∧
      normClassMap hgen (SigmaConjClasses.mk σ (sc v * (γ * δ * (σG σ γ)⁻¹))) = ConjClasses.mk γ' := by
  apply sc_mul_mem_I hgen
  have hmk : SigmaConjClasses.mk σ (γ * δ * (σG σ γ)⁻¹) = SigmaConjClasses.mk σ δ := by
    refine (SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨γ⁻¹, ?_⟩).symm
    rw [inv_inv, map_inv]
  rwa [hmk]

end Family

section Adelic

open MeasureTheory NumberField
open scoped ENNReal NNReal Pointwise

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem ideleNorm_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) =
      NumberField.TateGlobal.ideleNorm L z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph
  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne
  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* _) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b
  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl
  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s
    first | (funext a; exact θ.apply_symm_apply a) | exact θ.apply_symm_apply _
  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1
  have hcancel : distribHaarChar (AdeleRing (𝓞 L) L) w = distribHaarChar (AdeleRing (𝓞 L) L) z := by
    have := congrArg (fun t => t / μ s) h1
    rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this
  unfold NumberField.TateGlobal.ideleNorm
  rw [hw] at hcancel
  exact_mod_cast congrArg (fun t : ℝ≥0 => (t : ℝ)) hcancel

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

abbrev actU : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

abbrev cs : (AdeleRing (𝓞 L) L)ˣ →* AutomorphicForm.AdelicGL2 (𝓞 L) L :=
  AutomorphicForm.centralScalar (𝓞 L) L

theorem cs_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    cs L w * y = y * cs L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs_left (g y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (cs L w * y) = cs L w * (g * y) := by
  rw [← mul_assoc, ← cs_comm, mul_assoc]

theorem globalPoints_sc (u : Lˣ) :
    AutomorphicForm.globalPoints (𝓞 L) L (sc u) = cs L (princ L u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.globalPoints, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (u : L) i j) =
    Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem sigmaAdelicAct_cs (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (cs L z) = cs L (actU K L D σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L g) =
      AutomorphicForm.globalPoints (𝓞 L) L (σG σ g) :=
  AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ g

theorem sigmaAdelicAct_cs_princ (u : Lˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (cs L (princ L u)) = cs L (princ L (σU σ u)) := by
  rw [← globalPoints_sc, ← globalPoints_sc, sigmaAdelicAct_globalPoints', σG_sc]

theorem actU_actU_symm (w : (AdeleRing (𝓞 L) L)ˣ) : actU K L D σ (actU K L D σ⁻¹ w) = w := by
  apply Units.ext
  simp only [Units.coe_map, MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [← RingEquiv.coe_toRingHom, ← RingEquiv.coe_toRingHom]
  change ((D.act σ * D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L))) (w : AdeleRing (𝓞 L) L) = w
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

theorem continuous_cs : Continuous (cs L : (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar_apply]; try exact continuous_id
    · simp [Matrix.scalar_apply, hij]; try exact continuous_const
  exact Continuous.units_map _ hsc

theorem det_sigmaAdelicAct (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.sigmaAdelicAct K L D σ y) =
      actU K L D σ (Matrix.GeneralLinearGroup.det y) :=
  Matrix.GeneralLinearGroup.map_det _ y

theorem det_cs (z : (AdeleRing (𝓞 L) L)ˣ) : Matrix.GeneralLinearGroup.det (cs L z) = z ^ 2 := by
  have h : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      z ^ Fintype.card (Fin 2) := Matrix.GeneralLinearGroup.det_scalar z
  rw [Fintype.card_fin] at h
  exact h

theorem ideleNorm_one : NumberField.TateGlobal.ideleNorm L 1 = 1 := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := L) 1).ne' (h.symm.trans (mul_one _).symm)

theorem ideleNorm_inv (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L u⁻¹ = (NumberField.TateGlobal.ideleNorm L u)⁻¹ := by
  have h := NumberField.TateGlobal.ideleNorm_mul (F := L) u u⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem ideleNorm_pow_two (u : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (u ^ 2) = NumberField.TateGlobal.ideleNorm L u ^ 2 := by
  rw [pow_two, pow_two, NumberField.TateGlobal.ideleNorm_mul]

abbrev karg (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.AdelicGL2 (𝓞 L) L :=
  x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (cs L z * x)

theorem ideleNorm_det_karg (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (karg K L D σ x δ z)) =
      NumberField.TateGlobal.ideleNorm L z ^ 2 := by
  rw [map_mul, map_mul, map_inv, det_sigmaAdelicAct, map_mul, det_cs, map_mul, map_pow,
    NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, AutomorphicForm.ideleNorm_det_globalPoints,
    ideleNorm_pow_two, ideleNorm_unitsMap_act, ideleNorm_unitsMap_act, mul_one]
  have hx : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) ≠ 0 :=
    (NumberField.TateGlobal.ideleNorm_pos (F := L) _).ne'
  field_simp

theorem karg_normalise (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L)
    (z w : (AdeleRing (𝓞 L) L)ˣ) :
    karg K L D σ (cs L w * x) δ (actU K L D σ⁻¹ w * z * w⁻¹) = karg K L D σ x δ z := by
  simp only [karg]
  have h1 : cs L (actU K L D σ⁻¹ w * z * w⁻¹) * (cs L w * x) = cs L (actU K L D σ⁻¹ w) * (cs L z * x) := by
    rw [map_mul, map_mul, map_inv]
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [h1, map_mul (AutomorphicForm.sigmaAdelicAct K L D σ) (cs L _), sigmaAdelicAct_cs, actU_actU_symm,
    mul_inv_rev]

  simp only [mul_assoc]
  rw [mul_cs_left L (AutomorphicForm.globalPoints (𝓞 L) L δ), inv_mul_cancel_left]

theorem karg_globalPoints_inv_mul (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (γ δ : GL (Fin 2) L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    karg K L D σ (AutomorphicForm.globalPoints (𝓞 L) L γ⁻¹ * y) δ z =
      karg K L D σ y (γ * δ * (σG σ γ)⁻¹) z := by
  simp only [karg]
  have hcz : cs L z * (AutomorphicForm.globalPoints (𝓞 L) L γ⁻¹ * y) =
      AutomorphicForm.globalPoints (𝓞 L) L γ⁻¹ * (cs L z * y) := by
    rw [← mul_assoc, cs_comm, mul_assoc]
  rw [hcz, map_mul (AutomorphicForm.sigmaAdelicAct K L D σ) (AutomorphicForm.globalPoints (𝓞 L) L γ⁻¹),
    sigmaAdelicAct_globalPoints']
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]

theorem karg_princ_mul (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (δ : GL (Fin 2) L) (a : Lˣ)
    (κ : (AdeleRing (𝓞 L) L)ˣ) :
    karg K L D σ y δ (princ L a * κ) = karg K L D σ y (sc (σU σ a) * δ) κ := by
  simp only [karg]
  rw [map_mul (cs L), mul_assoc (cs L _), map_mul (AutomorphicForm.sigmaAdelicAct K L D σ),
    sigmaAdelicAct_cs_princ, ← globalPoints_sc, sc_comm (σU σ a) δ]
  simp only [map_mul, mul_assoc]

def transportC (zc : (AdeleRing (𝓞 L) L)ˣ) (t g : AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (κ : (AdeleRing (𝓞 L) L)ˣ) : AutomorphicForm.AdelicGL2 (𝓞 L) L :=
  t * (cs L zc)⁻¹ * (AutomorphicForm.sigmaAdelicAct K L D σ (cs L κ))⁻¹ * g *
    AutomorphicForm.sigmaAdelicAct K L D σ (cs L zc) * (AutomorphicForm.sigmaAdelicAct K L D σ t)⁻¹

theorem continuous_transportC (zc : (AdeleRing (𝓞 L) L)ˣ) (t : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      transportC K L D σ zc t p.1 p.2 := by
  unfold transportC
  have hκ : Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      AutomorphicForm.sigmaAdelicAct K L D σ (cs L p.2) :=
    (AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp ((continuous_cs L).comp continuous_snd)
  exact ((((continuous_const.mul hκ.inv).mul continuous_fst).mul continuous_const).mul continuous_const)

theorem transport_eq (s' t : AutomorphicForm.AdelicGL2 (𝓞 L) L) (zc κ : (AdeleRing (𝓞 L) L)ˣ)
    (δ : GL (Fin 2) L) :
    s'⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ s' =
      transportC K L D σ zc t (karg K L D σ (s' * t * (cs L zc)⁻¹) δ κ) κ := by
  set c₁ := AutomorphicForm.sigmaAdelicAct K L D σ (cs L κ) with hc₁
  have hc₁' : c₁ = cs L (actU K L D σ κ) := sigmaAdelicAct_cs K L D σ κ
  have hk : karg K L D σ (s' * t * (cs L zc)⁻¹) δ κ =
      c₁ * ((cs L zc * t⁻¹ * s'⁻¹) * AutomorphicForm.globalPoints (𝓞 L) L δ *
        (AutomorphicForm.sigmaAdelicAct K L D σ s' * AutomorphicForm.sigmaAdelicAct K L D σ t *
          (AutomorphicForm.sigmaAdelicAct K L D σ (cs L zc))⁻¹)) := by
    simp only [karg, map_mul, map_inv, mul_inv_rev, inv_inv]
    rw [← hc₁, hc₁']

    have hcomm : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L, g * cs L (actU K L D σ κ) = cs L (actU K L D σ κ) * g :=
      fun g => (cs_comm L _ g).symm
    simp only [mul_assoc]
    rw [← mul_assoc (AutomorphicForm.globalPoints (𝓞 L) L δ), hcomm, mul_assoc,
      ← mul_assoc s'⁻¹, hcomm, mul_assoc, ← mul_assoc t⁻¹, hcomm, mul_assoc, ← mul_assoc (cs L zc),
      hcomm, mul_assoc]
  unfold transportC
  rw [hk, ← hc₁]
  group

end Adelic

section Lift

open NumberField
open scoped NNReal Pointwise

variable (L : Type) [Field L] [NumberField L]

theorem mem_Icc_sqrt_of_sq_mem_Icc {t m₀ M₀ : ℝ} (ht : 0 ≤ t) (h : t ^ 2 ∈ Set.Icc m₀ M₀) :
    t ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) :=
  ⟨by rw [← Real.sqrt_sq ht]; exact Real.sqrt_le_sqrt h.1,
    (Real.le_sqrt ht (le_trans (sq_nonneg t) h.2)).mpr h.2⟩

theorem exists_isCompact_forall_mem_exists_princ_mul {m₁ M₁ : ℝ} (hm₁ : 0 < m₁) :
    ∃ C : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact C ∧
      ∀ z : (AdeleRing (𝓞 L) L)ˣ, NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc m₁ M₁ →
        ∃ (a : Lˣ) (c : (AdeleRing (𝓞 L) L)ˣ), c ∈ C ∧
          z = Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) a * c := by
  obtain ⟨C₁, hC₁c, -, hC₁⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
  obtain ⟨s, hs_cont, hs_norm, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L
  set S₁ : Set ℝ≥0ˣ := {r | ((r : ℝ≥0) : ℝ) ∈ Set.Icc m₁ M₁} with hS₁
  have hS₁c : IsCompact S₁ := by
    set a₀ : ℝ≥0 := ⟨m₁, hm₁.le⟩ with ha₀
    set b₀ : ℝ≥0 := Real.toNNReal M₁ with hb₀
    have ha₀pos : 0 < a₀ := hm₁
    have hpre : IsCompact (Units.embedProduct ℝ≥0 ⁻¹'
        (Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹))) :=
      Units.isClosedEmbedding_embedProduct.isCompact_preimage
        (isCompact_Icc.prod (isCompact_Icc.image MulOpposite.continuous_op))
    refine hpre.of_isClosed_subset (isClosed_Icc.preimage (NNReal.continuous_coe.comp Units.continuous_val)) ?_
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrpos : 0 < (r : ℝ≥0) := lt_of_lt_of_le ha₀pos hr1
    have h1 : a₀ ≤ (r : ℝ≥0) := hr1
    have h2 : (r : ℝ≥0) ≤ b₀ := (Real.le_toNNReal_iff_coe_le (le_trans (le_trans hm₁.le hr1) hr2)).mpr hr2
    show ((r : ℝ≥0), MulOpposite.op ((r⁻¹ : ℝ≥0ˣ) : ℝ≥0)) ∈
      Set.Icc a₀ b₀ ×ˢ (MulOpposite.op '' Set.Icc b₀⁻¹ a₀⁻¹)
    refine Set.mk_mem_prod ⟨h1, h2⟩ ⟨(r : ℝ≥0)⁻¹, ⟨inv_anti₀ hrpos h2, inv_anti₀ ha₀pos h1⟩, ?_⟩
    rw [Units.val_inv_eq_inv_val]
  refine ⟨C₁ * s '' S₁, hC₁c.mul (hS₁c.image hs_cont), fun z hz => ?_⟩
  have hzpos : 0 < NumberField.TateGlobal.ideleNorm L z := NumberField.TateGlobal.ideleNorm_pos (F := L) z
  set r : ℝ≥0ˣ := Units.mk0 (⟨NumberField.TateGlobal.ideleNorm L z, hzpos.le⟩ : ℝ≥0)
    (fun h => hzpos.ne' (congrArg Subtype.val h)) with hr
  have hrS : r ∈ S₁ := hz
  have hsr : NumberField.TateGlobal.ideleNorm L (s r) = NumberField.TateGlobal.ideleNorm L z := hs_norm r
  have hz₁ : z * (s r)⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_inv, hsr,
      mul_inv_cancel₀ hzpos.ne']
  obtain ⟨η, κ, hκ, hzκ⟩ := hC₁ _ hz₁
  refine ⟨η, κ * s r, Set.mul_mem_mul hκ ⟨r, hrS, rfl⟩, ?_⟩
  rw [← mul_assoc]
  exact mul_inv_eq_iff_eq_mul.mp hzκ

end Lift

section Cap

open NumberField NumberField.AdelicLevel AutomorphicForm.WindowedSiegel

variable (L : Type) [Field L] [NumberField L]

omit [NumberField L] in
theorem mult_le_two (w : InfinitePlace L) : w.mult ≤ 2 := by
  unfold InfinitePlace.mult; split_ifs <;> norm_num

theorem localHeight_le_of_archHeight_le (c T₁ : ℝ) (hc : 0 < c)
    (g : GL (Fin 2) (InfiniteAdeleRing L))
    (hfloor : ∀ w : InfinitePlace L, c ≤ localHeight (archComponent L w g)) (hcap : archHeight L g ≤ T₁)
    (w₀ : InfinitePlace L) :
    localHeight (archComponent L w₀ g) ≤
      max (T₁ / (min c 1) ^ (2 * Fintype.card (InfinitePlace L))) 1 := by
  classical
  set y : InfinitePlace L → ℝ := fun w => localHeight (archComponent L w g) with hy
  set q : ℝ := min c 1 with hq
  set n : ℕ := Fintype.card (InfinitePlace L) with hn
  have hq0 : 0 < q := lt_min hc one_pos
  have hq1 : q ≤ 1 := min_le_right _ _
  have hqc : q ≤ c := min_le_left _ _
  have hypos : ∀ w, 0 < y w := fun w => localHeight_pos _
  have harch : archHeight L g = ∏ w, y w ^ w.mult := rfl
  have h1 : y w₀ ^ w₀.mult * ∏ w ∈ Finset.univ.erase w₀, y w ^ w.mult = ∏ w, y w ^ w.mult :=
    Finset.mul_prod_erase Finset.univ (fun w => y w ^ w.mult) (Finset.mem_univ w₀)

  have hfac : ∀ w, q ^ 2 ≤ y w ^ w.mult := by
    intro w
    calc q ^ 2 ≤ q ^ w.mult := pow_le_pow_of_le_one hq0.le hq1 (mult_le_two L w)
      _ ≤ y w ^ w.mult := pow_le_pow_left₀ hq0.le (hqc.trans (hfloor w)) _
  have hlow : q ^ (2 * n) ≤ ∏ w ∈ Finset.univ.erase w₀, y w ^ w.mult := by
    calc q ^ (2 * n) ≤ q ^ (2 * (n - 1)) := pow_le_pow_of_le_one hq0.le hq1 (by omega)
      _ = ∏ _w ∈ Finset.univ.erase w₀, q ^ 2 := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ w₀), Finset.card_univ, ← pow_mul]
      _ ≤ ∏ w ∈ Finset.univ.erase w₀, y w ^ w.mult :=
          Finset.prod_le_prod (fun w _ => by positivity) (fun w _ => hfac w)
  have hqn : 0 < q ^ (2 * n) := pow_pos hq0 _
  have hpow : y w₀ ^ w₀.mult ≤ T₁ / q ^ (2 * n) := by
    rw [le_div_iff₀ hqn]
    calc y w₀ ^ w₀.mult * q ^ (2 * n) ≤ y w₀ ^ w₀.mult * ∏ w ∈ Finset.univ.erase w₀, y w ^ w.mult :=
          mul_le_mul_of_nonneg_left hlow (pow_nonneg (hypos w₀).le _)
      _ = archHeight L g := by rw [h1, harch]
      _ ≤ T₁ := hcap
  by_cases hy1 : y w₀ ≤ 1
  · exact hy1.trans (le_max_right _ _)
  · push Not at hy1
    have hm : w₀.mult ≠ 0 := (InfinitePlace.mult_pos).ne'
    calc y w₀ ≤ y w₀ ^ w₀.mult := le_self_pow₀ hy1.le hm
      _ ≤ T₁ / q ^ (2 * n) := hpow
      _ ≤ _ := le_max_left _ _

end Cap

section Main

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped NNReal Pointwise

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

theorem main
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ) :
    ∃ N : ℕ, ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      {δ : GL (Fin 2) L |
        (∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
            ConjClasses.mk γ) ∧
        (¬ ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
            (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) ∧
        φ (karg K L D σ x δ z) ≠ 0}.encard ≤ N := by
  classical
  haveI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  set σA := AutomorphicForm.sigmaAdelicAct K L D σ with hσA
  set ι := AutomorphicForm.globalPoints (𝓞 L) L with hι

  obtain ⟨T, c, hc, u₀, hcovAll⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet L
  have hcov := hcovAll 1 2 two_pos one_le_two
  obtain ⟨Zf, hZf⟩ :=
    AutomorphicForm.exists_finset_globalPoints_mul_mul_centralScalar_mem_of_coversModCentre_of_ideleNorm_det_mem_Icc
      L c u₀ 1 2 T one_pos one_lt_two hcov 1 1 one_pos le_rfl
  obtain ⟨sec, -, hsec_norm, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L

  have hSc : IsCompact (tsupport φ) := hφc
  obtain ⟨m₀, hm₀, hlo⟩ : ∃ m₀ > 0, ∀ g ∈ tsupport φ,
      m₀ ≤ NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
    by_cases hne : (tsupport φ).Nonempty
    · obtain ⟨g₀, -, hmin⟩ :=
        hSc.exists_isMinOn hne (NumberField.TateGlobal.continuous_ideleNorm_det L).continuousOn
      exact ⟨_, NumberField.TateGlobal.ideleNorm_pos (F := L) _, fun g hg => hmin hg⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      exact ⟨1, one_pos, fun g hg => by rw [hne] at hg; exact absurd hg (Set.notMem_empty g)⟩
  obtain ⟨M₀, hhi⟩ : ∃ M₀, ∀ g ∈ tsupport φ,
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ≤ M₀ := by
    obtain ⟨M, hM⟩ := (hSc.image (NumberField.TateGlobal.continuous_ideleNorm_det L)).bddAbove
    exact ⟨M, fun g hg => hM ⟨g, hg, rfl⟩⟩
  have hm₁pos : 0 < Real.sqrt m₀ := Real.sqrt_pos.mpr hm₀
  obtain ⟨C₁, hC₁c, hlift⟩ := exists_isCompact_forall_mem_exists_princ_mul L (M₁ := Real.sqrt M₀) hm₁pos

  set Csharp : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    ⋃ zc ∈ Zf, ⋃ t ∈ T, (fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      transportC K L D σ zc t p.1 p.2) '' (tsupport φ ×ˢ C₁) with hCsharp
  have hCsharpc : IsCompact Csharp := by
    refine Zf.finite_toSet.isCompact_biUnion fun zc _ => T.finite_toSet.isCompact_biUnion fun t _ => ?_
    exact (hSc.prod hC₁c).image (continuous_transportC K L D σ zc t)

  obtain ⟨T₀, hT₀⟩ :=
    AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem L hCsharpc
  set T₁ : ℝ := max T₀ 1 with hT₁
  set Ccap : ℝ := max (T₁ / (min c 1) ^ (2 * Fintype.card (InfinitePlace L))) 1 with hCcap
  set Kcap : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    centreCutSiegelSet L c u₀ 1 2 ∩
      {g | ∀ w : InfinitePlace L, localHeight (archComponent L w (glArch (𝓞 L) L g)) ≤ Ccap} with hKcap
  have hKcapc : IsCompact Kcap :=
    AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap L hc one_pos

  set Big : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
    (fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      p.1 * p.2 * (σA p.1)⁻¹) '' (Kcap ×ˢ Csharp) with hBig
  have hBigc : IsCompact Big := by
    refine (hKcapc.prod hCsharpc).image ?_
    exact (continuous_fst.mul continuous_snd).mul
      ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp continuous_fst).inv
  set Ent : Fin 2 → Fin 2 → Set (AdeleRing (𝓞 L) L) := fun i j =>
    (fun g : AutomorphicForm.AdelicGL2 (𝓞 L) L => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) '' Big
    with hEnt
  have hvalc : Continuous (Units.val : AutomorphicForm.AdelicGL2 (𝓞 L) L → Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    Units.continuous_val
  have hEntc : ∀ i j, IsCompact (Ent i j) := fun i j => hBigc.image (hvalc.matrix_elem i j)
  have hEfin : ∀ i j, {ξ : L | algebraMap L (AdeleRing (𝓞 L) L) ξ ∈ Ent i j}.Finite := fun i j =>
    NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L (hEntc i j)
  set FinL : Set (GL (Fin 2) L) := {δ | ι δ ∈ Big} with hFinL
  have hFinLfin : FinL.Finite := by
    set PiM : Set (Matrix (Fin 2) (Fin 2) L) :=
      {M | ∀ i j, algebraMap L (AdeleRing (𝓞 L) L) (M i j) ∈ Ent i j} with hPiM
    have hPiMfin : PiM.Finite := by
      have h := Set.Finite.pi' (κ := fun _ : Fin 2 => Fin 2 → L)
        (t := fun i => {row : Fin 2 → L | ∀ j, algebraMap L (AdeleRing (𝓞 L) L) (row j) ∈ Ent i j})
        (fun i => Set.Finite.pi' (κ := fun _ : Fin 2 => L)
          (t := fun j => {ξ : L | algebraMap L (AdeleRing (𝓞 L) L) ξ ∈ Ent i j}) (fun j => hEfin i j))
      exact h
    have hinj : Set.InjOn (Units.val : GL (Fin 2) L → Matrix (Fin 2) (Fin 2) L)
        ((Units.val : GL (Fin 2) L → Matrix (Fin 2) (Fin 2) L) ⁻¹' PiM) := Units.val_injective.injOn
    refine (hPiMfin.preimage hinj).subset ?_
    intro δ hδ i j
    exact ⟨ι δ, hδ, rfl⟩
  refine ⟨hFinLfin.toFinset.card, fun x z => ?_⟩

  set S : Set (GL (Fin 2) L) := {δ : GL (Fin 2) L |
        (∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
            ConjClasses.mk γ) ∧
        (¬ ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
            (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) ∧
        φ (karg K L D σ x δ z) ≠ 0} with hSdef
  show S.encard ≤ (hFinLfin.toFinset.card : ℕ∞)
  rcases Set.eq_empty_or_nonempty S with hS | ⟨δ₀, hδ₀⟩
  · rw [hS, Set.encard_empty]; exact bot_le
  obtain ⟨-, -, hδ₀ne⟩ := hδ₀

  have hr : 0 < NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.ideleNorm_pos (F := L) _
  set r : ℝ := NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x) with hrdef
  have hsr : 0 < (Real.sqrt r)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hr)
  set q : ℝ≥0ˣ := Units.mk0 (⟨(Real.sqrt r)⁻¹, hsr.le⟩ : ℝ≥0) (fun h => hsr.ne' (congrArg Subtype.val h))
    with hqdef
  set w : (AdeleRing (𝓞 L) L)ˣ := sec q with hwdef
  have hw : NumberField.TateGlobal.ideleNorm L w = (Real.sqrt r)⁻¹ := hsec_norm q
  set x₁ : AutomorphicForm.AdelicGL2 (𝓞 L) L := cs L w * x with hx₁def
  set z₁ : (AdeleRing (𝓞 L) L)ˣ := actU K L D σ⁻¹ w * z * w⁻¹ with hz₁def
  have hkarg : ∀ δ, karg K L D σ x δ z = karg K L D σ x₁ δ z₁ := fun δ =>
    (karg_normalise K L D σ x δ z w).symm
  have hx₁ : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x₁) ∈ Set.Icc (1 : ℝ) 1 := by
    have h1 : NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det x₁) = 1 := by
      rw [hx₁def, map_mul, det_cs, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_pow_two, hw, ← hrdef,
        inv_pow, Real.sq_sqrt hr.le, inv_mul_cancel₀ hr.ne']
    rw [h1]; exact ⟨le_rfl, le_rfl⟩

  obtain ⟨γ, zc, hzc, hmem⟩ := hZf x₁ hx₁
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨t, ht, s', hs', hst⟩ := hmem
  have hy : x₁ = ι γ⁻¹ * (s' * t * (cs L zc)⁻¹) := by
    have hst' : s' * t = ι γ * x₁ * cs L zc := hst
    rw [map_inv, hst']
    group

  have hz₁band : NumberField.TateGlobal.ideleNorm L z₁ ∈ Set.Icc (Real.sqrt m₀) (Real.sqrt M₀) := by
    have hmem₀ : karg K L D σ x₁ δ₀ z₁ ∈ tsupport φ := by
      rw [← hkarg δ₀]; exact subset_tsupport φ hδ₀ne
    have hz2 : NumberField.TateGlobal.ideleNorm L z₁ ^ 2 ∈ Set.Icc m₀ M₀ := by
      rw [← ideleNorm_det_karg K L D σ x₁ δ₀ z₁]
      exact ⟨hlo _ hmem₀, hhi _ hmem₀⟩
    exact mem_Icc_sqrt_of_sq_mem_Icc (NumberField.TateGlobal.ideleNorm_pos (F := L) z₁).le hz2
  obtain ⟨a, κ, hκ, hz₁⟩ := hlift z₁ hz₁band

  set ψ : GL (Fin 2) L → GL (Fin 2) L := fun δ => sc (σU σ a) * (γ * δ * (σG σ γ)⁻¹) with hψdef
  have hψinj : Function.Injective ψ := transport_injective σ (σU σ a) γ
  have hs'int : glFin (𝓞 L) L s' ∈ finiteIntegralGL2 (𝓞 L) L := (mem_centreCutSiegelSet_iff.mp hs').1
  have hs'floor : ∀ w : InfinitePlace L, c ≤ localHeight (archComponent L w (glArch (𝓞 L) L s')) :=
    (mem_centreCutSiegelSet_iff.mp hs').2.1
  obtain ⟨hHeq, hint⟩ :=
    AutomorphicForm.archHeight_glArch_sigmaAdelicAct_and_glFin_sigmaAdelicAct_mem_finiteIntegralGL2 K L D σ s'
  have hmaps : Set.MapsTo ψ S FinL := by
    intro δ hδ
    obtain ⟨hP, hnF, hne⟩ := hδ

    have hrel : s'⁻¹ * ι (ψ δ) * σA s' ∈ Csharp := by
      have e1 : karg K L D σ x δ z = karg K L D σ (s' * t * (cs L zc)⁻¹) (ψ δ) κ := by
        rw [hkarg δ, hy, karg_globalPoints_inv_mul, hz₁, karg_princ_mul]
      have e2 := transport_eq K L D σ s' t zc κ (ψ δ)
      rw [hι, hσA, e2, ← e1, hCsharp]
      refine Set.mem_iUnion₂.mpr ⟨zc, hzc, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
      exact ⟨(karg K L D σ x δ z, κ), ⟨subset_tsupport φ hne, hκ⟩, rfl⟩

    have hI : ∃ γ' : GL (Fin 2) K,
        (γ' ∈ AutomorphicForm.ellipticCell K ∨ γ' ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ (ψ δ)) = ConjClasses.mk γ' :=
      transport_mem_I hgen hP (σU σ a) γ
    have hnF' : ¬ ∃ (h : GL (Fin 2) L) (u : Lˣ), ψ δ = sc u * (h⁻¹ * σG σ h) := fun hF =>
      hnF (fam_of_transport_fam σ (σU σ a) γ δ hF)

    have hcapT : archHeight L (glArch (𝓞 L) L s') ≤ T₀ := by
      by_contra hlt
      push Not at hlt
      have hlt' : T₀ < archHeight L (glArch (𝓞 L) L (σA s')) := by rw [hσA, hHeq]; exact hlt
      have h10 := hT₀ s' (σA s') hs'int (hint hs'int) hlt hlt' (ψ δ) hrel
      obtain ⟨γK, hγK, hNK⟩ := hI
      exact hnF'
        (LT.TwistedNorm.exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk
          hgen (ψ δ) h10 γK hγK hNK)

    have hs'K : s' ∈ Kcap := by
      refine ⟨hs', fun w => ?_⟩
      exact localHeight_le_of_archHeight_le L c T₁ hc (glArch (𝓞 L) L s') hs'floor
        (hcapT.trans (le_max_left _ _)) w

    show ι (ψ δ) ∈ Big
    refine ⟨(s', s'⁻¹ * ι (ψ δ) * σA s'), ⟨hs'K, hrel⟩, ?_⟩
    show s' * (s'⁻¹ * ι (ψ δ) * σA s') * (σA s')⁻¹ = ι (ψ δ)
    group
  calc S.encard ≤ FinL.encard := Set.encard_le_encard_of_injOn hmaps hψinj.injOn
    _ = hFinLfin.toFinset.card := hFinLfin.encard_eq_coe_toFinset_card
    _ ≤ _ := le_rfl

end Main

end R3OffFam

end

open NumberField in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ) :
    ∃ N : ℕ, ∀ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      {δ : GL (Fin 2) L |
        (∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
            ConjClasses.mk γ) ∧
        (¬ ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
            (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) ∧
        φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.encard
        ≤ N :=
  R3OffFam.main K L hgen D φ hφc

end S_AutomorphicForm_exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_encard_setOf_twistedKernelSummand_ne_zero_not_identityFamily_le (solution)
