-- Prove2me | solution 1 for AutomorphicForm.exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8bc04e87-6810-5fe2-a391-56b06b636648

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Theorems.Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat
import Theorems.Thm_UnramifiedWhittaker_mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
import Theorems.Thm_AutomorphicForm_adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsEulerPoly_contragredient_twist_eq
import Theorems.Thm_AutomorphicForm_exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Mathlib.Analysis.MellinTransform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_sigmaCentralizer_iff AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

namespace DataRS

open ComplexConjugate

theorem ideleNorm_one : TateGlobal.ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) = 1 := by
  have h := TateGlobal.ideleNorm_mul (F := ℚ) 1 1
  rw [one_mul] at h
  have hp := TateGlobal.ideleNorm_pos (F := ℚ) (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ)

  have : TateGlobal.ideleNorm ℚ (1 : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * (TateGlobal.ideleNorm ℚ 1 - 1) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact absurd h0 hp.ne'
  · linarith

noncomputable def normRpowHom (σ : ℝ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂ where
  toFun z := ((TateGlobal.ideleNorm ℚ z ^ σ : ℝ) : ℂ)
  map_one' := by simp [ideleNorm_one]
  map_mul' x y := by
    rw [TateGlobal.ideleNorm_mul,
      Real.mul_rpow (TateGlobal.ideleNorm_pos x).le (TateGlobal.ideleNorm_pos y).le]
    push_cast
    rfl

noncomputable def normRpow (σ : ℝ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ := (normRpowHom σ).toHomUnits

theorem normRpow_apply (σ : ℝ) (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((normRpow σ z : ℂˣ) : ℂ) = ((TateGlobal.ideleNorm ℚ z ^ σ : ℝ) : ℂ) := rfl

theorem ideleNorm_principal (u : ℚˣ) :
    TateGlobal.ideleNorm ℚ (Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) u) = 1 := by
  unfold TateGlobal.ideleNorm
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap ℚ u
  rw [RingHom.toMonoidHom_eq_coe] at h
  first
    | (rw [h]; simp)
    | (erw [h]; simp)
    | (simp only [h]; simp)

theorem isIdeleClassChar_normRpow (σ : ℝ) : IsIdeleClassChar (𝓞 ℚ) ℚ (normRpow σ) := by
  intro u
  ext
  rw [normRpow_apply, ideleNorm_principal, Real.one_rpow]
  simp

theorem norm_archWeightCharℝ (n : ℤ) (κ : rowIsometrySubgroup₀ ℝ) :
    ‖((archWeightCharℝ n κ : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : ‖((archWeightOneℝ κ : ℂˣ) : ℂ)‖ = 1 := by
    have hsq := normSq_firstRowℂ_of_mem κ.2
    have : ‖firstRowℂ (κ : GL (Fin 2) ℝ)‖ = 1 := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, hsq, Real.sqrt_one]
    exact this
  show ‖(((zpowGroupHom n).comp archWeightOneℝ κ : ℂˣ) : ℂ)‖ = 1
  simp only [MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, norm_zpow, h1, one_zpow]

theorem bottom_row_finUnipotent_mul (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ) (j : Fin 2) :
    ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j =
      (((g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j := by
  obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.mp n.property
  have hn : (((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![1, x.toAdd; 0, 1] := by
    rw [← hx]; rfl
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hn]
  simp

theorem glFin_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ g := by
  show NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ
      ((archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 g))⁻¹ * g) = _
  rw [map_mul, map_inv,
    show NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ
        (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 g)) = 1 from
      glFin_adelicArchGLIncl ℚ _,
    inv_one, one_mul]

theorem finFactor_entry_snd (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    ((((finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 =
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 := by
  rw [← NumberField.AdelicLevel.glFin_apply, ← NumberField.AdelicLevel.glFin_apply, glFin_finFactor]

def FfC (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ) (g : AdelicGL2 (𝓞 ℚ) ℚ) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
      Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
    (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
      Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤ WithZero.exp (-(mS p : ℤ)) ∧
      Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤ WithZero.exp (-(mS p : ℤ)))

theorem localAt_apply (v : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2) :
    ((localAt ℚ v g : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v := rfl

theorem localAt_placeEmbed_self (v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ v (placeEmbed ℚ v x) = x := by
  show NumberField.AdelicLevel.finComponent (𝓞 ℚ) ℚ v
      (NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = x
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem localAt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show NumberField.AdelicLevel.finComponent (𝓞 ℚ) ℚ w
      (NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem snd_entry_mul_placeEmbed_of_ne (g : AdelicGL2 (𝓞 ℚ) ℚ) {v w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v)
    (x : GL (Fin 2) (v.adicCompletion ℚ)) (i j : Fin 2) :
    ((((g * placeEmbed ℚ v x : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) w =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) w := by
  rw [← localAt_apply, ← localAt_apply, map_mul, localAt_placeEmbed_of_ne hw, mul_one]

theorem snd_entry_mul_placeEmbed_self (g : AdelicGL2 (𝓞 ℚ) ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (x : GL (Fin 2) (v.adicCompletion ℚ)) (i j : Fin 2) :
    ((((g * placeEmbed ℚ v x : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v =
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 0).2) v * (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 0 j +
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i 1).2) v * (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 j := by
  rw [← localAt_apply, ← localAt_apply, ← localAt_apply, map_mul, localAt_placeEmbed_self, Units.val_mul,
    Matrix.mul_apply, Fin.sum_univ_two]

theorem FfC_finFactor (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) : FfC S mS (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) ↔ FfC S mS g := by
  simp only [FfC, finFactor_entry_snd]

theorem FfC.mul_placeEmbed {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {mS : HeightOneSpectrum (𝓞 ℚ) → ℕ}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ S) (x : GL (Fin 2) (v.adicCompletion ℚ))
    (hx : ∀ i j, Valued.v ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : FfC S mS g) : FfC S mS (g * placeEmbed ℚ v x) := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨fun p hp j => ?_, fun p hp => ?_⟩
  · by_cases hpv : p = v
    · subst hpv
      rw [snd_entry_mul_placeEmbed_self]
      refine le_trans (Valued.v.map_add _ _) (max_le ?_ ?_)
      · rw [Valued.v.map_mul]; exact mul_le_one' (h1 p hp 0) (hx 0 j)
      · rw [Valued.v.map_mul]; exact mul_le_one' (h1 p hp 1) (hx 1 j)
    · rw [snd_entry_mul_placeEmbed_of_ne g hpv]; exact h1 p hp j
  · have hpv : p ≠ v := fun h => hv (h ▸ hp)
    rw [snd_entry_mul_placeEmbed_of_ne g hpv, snd_entry_mul_placeEmbed_of_ne g hpv]
    exact h2 p hp

theorem FfC_mul_placeEmbed_iff {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {mS : HeightOneSpectrum (𝓞 ℚ) → ℕ}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ S) {x : GL (Fin 2) (v.adicCompletion ℚ)}
    (hx : x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    FfC S mS (g * placeEmbed ℚ v x) ↔ FfC S mS g := by
  rw [AdelicDock.mem_localLevelOne_iff] at hx
  have hxi : ∀ i j, Valued.v ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1 := fun i j =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx.1.integral i j)
  have hxi' : ∀ i j, Valued.v (((x⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1 :=
    fun i j => (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hx.2.integral i j)
  constructor
  · intro h
    have := FfC.mul_placeEmbed hv x⁻¹ hxi' h
    rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at this
  · exact FfC.mul_placeEmbed hv x hxi

section TorusMatrices
variable {K : Type*} [Field K]

theorem scalarPi_eq_scalar (π : K) (hπ : π ≠ 0) :
    scalarPi π hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 π hπ) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) K) i j = (Matrix.scalar (Fin 2) π) i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem val_scalarPi_zpow (π : K) (hπ : π ≠ 0) (n : ℤ) (i j : Fin 2) :
    ((scalarPi π hπ ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = if i = j then π ^ n else 0 := by
  rw [scalarPi_eq_scalar, ← map_zpow]
  show (Matrix.scalar (Fin 2) (((Units.mk0 π hπ) ^ n : Kˣ) : K)) i j = _
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem val_diagZ_mul_scalarPi_zpow_row_one (π : K) (hπ : π ≠ 0) (m n : ℤ) :
    ((diagZ π hπ m * scalarPi π hπ ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
    ((diagZ π hπ m * scalarPi π hπ ^ n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = π ^ n := by
  have hd : ∀ j, ((diagZ π hπ m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j = if (1 : Fin 2) = j then 1 else 0 := by
    intro j
    show (!![π ^ m, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) 1 j = _
    fin_cases j <;> simp
  constructor
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hd, hd, val_scalarPi_zpow, val_scalarPi_zpow]
    simp
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hd, hd, val_scalarPi_zpow, val_scalarPi_zpow]
    simp

end TorusMatrices

theorem FfC_mul_torus_iff {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {mS : HeightOneSpectrum (𝓞 ℚ) → ℕ}
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ S) {π : v.adicCompletion ℚ} (hπ : π ≠ 0)
    (hπv : Valued.v π = WithZero.exp (-1 : ℤ)) {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : localAt ℚ v g = 1) (m n : ℤ) :
    FfC S mS (g * placeEmbed ℚ v (diagZ π hπ m * scalarPi π hπ ^ n)) ↔ FfC S mS g ∧ 0 ≤ n := by
  have hg' : ∀ i j, (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) v =
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j := by
    intro i j; rw [← localAt_apply, hg, Units.val_one]
  obtain ⟨h10, h11⟩ := val_diagZ_mul_scalarPi_zpow_row_one π hπ m n
  have hev : ∀ j, ((((g * placeEmbed ℚ v (diagZ π hπ m * scalarPi π hπ ^ n) : AdelicGL2 (𝓞 ℚ) ℚ) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) v =
      ((diagZ π hπ m * scalarPi π hπ ^ n : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) 1 j := by
    intro j
    rw [snd_entry_mul_placeEmbed_self, hg', hg', Matrix.one_apply_ne (by decide), Matrix.one_apply_eq, zero_mul,
      one_mul, zero_add]
  have hπn : Valued.v (π ^ n) ≤ 1 ↔ 0 ≤ n := by
    rw [map_zpow₀, hπv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun p hp j => ?_, fun p hp => ?_⟩, ?_⟩
    · by_cases hpv : p = v
      · subst hpv
        rw [hg']
        obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
        · rw [Matrix.one_apply_ne (by decide), map_zero]; exact zero_le'
        · rw [Matrix.one_apply_eq, map_one]
      · have := h1 p hp j; rwa [snd_entry_mul_placeEmbed_of_ne g hpv] at this
    · have hpv : p ≠ v := fun h => hv (h ▸ hp)
      have := h2 p hp
      rwa [snd_entry_mul_placeEmbed_of_ne g hpv, snd_entry_mul_placeEmbed_of_ne g hpv] at this
    · have := h1 v hv 1
      rw [hev, h11] at this
      exact hπn.mp this
  · rintro ⟨⟨h1, h2⟩, hn⟩
    refine ⟨fun p hp j => ?_, fun p hp => ?_⟩
    · by_cases hpv : p = v
      · subst hpv
        rw [hev]
        obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
        · rw [h10, map_zero]; exact zero_le'
        · rw [h11]; exact hπn.mpr hn
      · rw [snd_entry_mul_placeEmbed_of_ne g hpv]; exact h1 p hp j
    · have hpv : p ≠ v := fun h => hv (h ▸ hp)
      rw [snd_entry_mul_placeEmbed_of_ne g hpv, snd_entry_mul_placeEmbed_of_ne g hpv]
      exact h2 p hp

theorem continuous_snd_entry (p : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 2) :
    Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) p := by
  have : (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2) p) =
      fun g => ((localAt ℚ p g : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j := by
    funext g; rw [localAt_apply]
  rw [this]
  exact (Units.continuous_val.comp (continuous_localAt ℚ p)).matrix_elem i j

theorem isClosed_le_one (p : HeightOneSpectrum (𝓞 ℚ)) : IsClosed {x : p.adicCompletion ℚ | Valued.v x ≤ 1} := by
  have : {x : p.adicCompletion ℚ | Valued.v x ≤ 1} = (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) := by
    ext x; exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  rw [this]
  exact Valued.isClosed_valuationSubring _

theorem isClosed_le_exp_neg (p : HeightOneSpectrum (𝓞 ℚ)) {π : p.adicCompletion ℚ} (hπv : Valued.v π = WithZero.exp (-1 : ℤ))
    (m : ℕ) : IsClosed {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(m : ℤ))} := by
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, map_zero] at hπv; exact WithZero.exp_ne_zero hπv.symm
  have hvm : Valued.v (π⁻¹ ^ m) = WithZero.exp (m : ℤ) := by
    rw [map_pow, map_inv₀, hπv, WithZero.exp_neg, inv_inv, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]
  have : {x : p.adicCompletion ℚ | Valued.v x ≤ WithZero.exp (-(m : ℤ))} =
      (fun x => x * π⁻¹ ^ m) ⁻¹' {x : p.adicCompletion ℚ | Valued.v x ≤ 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, map_mul, hvm]
    rw [WithZero.exp_neg, ← one_div, le_div_iff₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)]
  rw [this]
  exact (isClosed_le_one p).preimage (continuous_id.mul continuous_const)

theorem isClosed_FfC (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) :
    IsClosed {g : AdelicGL2 (𝓞 ℚ) ℚ | FfC S mS g} := by
  have h1 : IsClosed {g : AdelicGL2 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
      Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ => isClosed_iInter fun j =>
      (isClosed_le_one p).preimage (continuous_snd_entry p 1 j)
  have h2 : IsClosed {g : AdelicGL2 (𝓞 ℚ) ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
      Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤ WithZero.exp (-(mS p : ℤ)) ∧
      Valued.v ((((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤ WithZero.exp (-(mS p : ℤ))} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun p => isClosed_iInter fun _ => ?_
    exact ((isClosed_le_exp_neg p (hϖ p) (mS p)).preimage (continuous_snd_entry p 1 0)).inter
      ((isClosed_le_exp_neg p (hϖ p) (mS p)).preimage ((continuous_snd_entry p 1 1).sub continuous_const))
  exact h1.inter h2

open Classical in

theorem cell_const_assembly
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (Bc Fc : finiteAdelicGL2Subgroup ℚ → Prop)
    (Wf Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hFf1 : ∀ g, Fc g → Ff g = 1) (hFf0 : ∀ g, ¬Fc g → Ff g = 0)
    (hdet : ∀ g, Bc g → Wf g ≠ 0 → Fc g →
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1)
    (hint : Integrable ({g | Bc g ∧ Fc g}.indicator fun g => (Complex.normSq (Wf g) : ℂ))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)))
    (hpos : (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) {g | Bc g ∧ Fc g ∧ Wf g ≠ 0} ≠ 0) :
    ∃ (A : ℕ) (cf : ℤ → ℝ) (B : ℝ), 1 < B ∧ (∀ n, 0 ≤ cf n) ∧ (∃ n, -(A : ℤ) ≤ n ∧ n ≤ A ∧ 0 < cf n) ∧
      ∀ s : ℂ, RSCarrier.rsFinIntegral μ μN s ({g | Bc g}.indicator (fun g => Wf g))
          ({g | Bc g}.indicator (fun g => (starRingEnd ℂ) (Wf g) * Ff g)) =
        ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s) := by
  have hWF : ∀ g : finiteAdelicGL2Subgroup ℚ,
      {g | Bc g}.indicator (fun g => Wf g) g * {g | Bc g}.indicator (fun g => (starRingEnd ℂ) (Wf g) * Ff g) g =
        if (Bc g ∧ Fc g) then (Complex.normSq (Wf g) : ℂ) else 0 := by
    intro g
    by_cases hB : Bc g
    · have hB' : g ∈ {g | Bc g} := hB
      rw [Set.indicator_of_mem hB', Set.indicator_of_mem hB']
      by_cases hF : Fc g
      · rw [hFf1 g hF, if_pos ⟨hB, hF⟩, mul_one]
        exact Complex.mul_conj (Wf g)
      · rw [hFf0 g hF, if_neg (fun h => hF h.2), mul_zero, mul_zero]
    · have hB' : g ∉ {g | Bc g} := hB
      rw [Set.indicator_of_notMem hB', zero_mul, if_neg (fun h => hB h.1)]
  have hWF' : ∀ g : finiteAdelicGL2Subgroup ℚ,
      {g | Bc g}.indicator (fun g => Wf g) g * {g | Bc g}.indicator (fun g => (starRingEnd ℂ) (Wf g) * Ff g) g =
        {g | Bc g ∧ Fc g}.indicator (fun g => (Complex.normSq (Wf g) : ℂ)) g := by
    intro g
    rw [hWF g]
    by_cases hc : (Bc g ∧ Fc g)
    · rw [if_pos hc, Set.indicator_of_mem (show g ∈ {g | Bc g ∧ Fc g} from hc)]
    · rw [if_neg hc, Set.indicator_of_notMem (show g ∉ {g | Bc g ∧ Fc g} from hc)]
  have hset : {g : finiteAdelicGL2Subgroup ℚ |
      {g | Bc g}.indicator (fun g => Wf g) g * {g | Bc g}.indicator (fun g => (starRingEnd ℂ) (Wf g) * Ff g) g ≠ 0} =
      {g | Bc g ∧ Fc g ∧ Wf g ≠ 0} := by
    ext g
    simp only [Set.mem_setOf_eq, hWF g]
    constructor
    · intro h
      by_cases hc : (Bc g ∧ Fc g)
      · refine ⟨hc.1, hc.2, ?_⟩
        intro h0; apply h; rw [if_pos hc, h0, map_zero, Complex.ofReal_zero]
      · exact (h (if_neg hc)).elim
    · rintro ⟨h1, h2, h3⟩
      rw [if_pos ⟨h1, h2⟩]
      exact_mod_cast (Complex.normSq_pos.mpr h3).ne'
  obtain ⟨c₀, hc₀, hconst⟩ :=
    LanglandsTunnell.RankinSelberg.exists_pos_forall_rsFinIntegral_eq_const_of_ideleNorm_det_eq_one_of_nonneg
      μ μN ({g | Bc g}.indicator (fun g => Wf g)) ({g | Bc g}.indicator (fun g => (starRingEnd ℂ) (Wf g) * Ff g))
      (by
        intro g hg
        rw [hWF] at hg
        by_cases hc : (Bc g ∧ Fc g)
        · have hWf0 : Wf g ≠ 0 := by
            intro h0; apply hg; rw [if_pos hc, h0, map_zero, Complex.ofReal_zero]
          exact hdet g hc.1 hWf0 hc.2
        · exact (hg (if_neg hc)).elim)
      (by
        intro g
        rw [hWF]
        by_cases hc : (Bc g ∧ Fc g)
        · rw [if_pos hc]
          exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact Complex.normSq_nonneg _⟩
        · rw [if_neg hc]
          exact ⟨Complex.zero_im, le_of_eq Complex.zero_re.symm⟩)
      (by
        refine (hint).congr (Filter.Eventually.of_forall fun g => ?_)
        exact (hWF' g).symm)
      (by rw [hset]; exact hpos)
  refine ⟨0, fun n => if n = 0 then c₀ else 0, 2, one_lt_two, ?_, ⟨0, le_refl _, le_refl _, ?_⟩, ?_⟩
  · intro n
    show 0 ≤ (if n = 0 then c₀ else 0)
    by_cases hn : n = 0
    · rw [if_pos hn]; exact hc₀.le
    · rw [if_neg hn]
  · show 0 < (if (0 : ℤ) = 0 then c₀ else 0)
    rw [if_pos rfl]; exact hc₀
  · intro s
    rw [hconst s, Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton]
    show (c₀ : ℂ) = ((if (0 : ℤ) = 0 then c₀ else 0 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) ^ (-((0 : ℤ) : ℂ) * s)
    rw [if_pos rfl, Int.cast_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one]

theorem rescale_assembly (q σ₀ : ℝ) (hq : 0 < q) (a b : ℂ)
    (hrel : a * (starRingEnd ℂ) b = ((q ^ (1 - σ₀) : ℝ) : ℂ) * (starRingEnd ℂ) a) (hnb : ‖b‖ = q ^ (1 - σ₀)) (X : ℂ) :
    (rsEulerPoly ((((q ^ (σ₀ / 2) : ℝ) : ℂ) * a) / (q : ℂ)) ((((q ^ σ₀ : ℝ) : ℂ) * (b / (q : ℂ))) / (q : ℂ))
        ((starRingEnd ℂ) (((q ^ (σ₀ / 2) : ℝ) : ℂ) * a) / (q : ℂ))
        ((starRingEnd ℂ) (((q ^ σ₀ : ℝ) : ℂ) * (b / (q : ℂ))) / (q : ℂ)) 0).eval ((q : ℂ) * X) =
      (rsEulerPoly (a / b) b⁻¹ a b 0).eval X := by
  set t : ℝ := q ^ (σ₀ / 2) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hq _
  have ht2 : t ^ 2 = q ^ σ₀ := by
    rw [ht, pow_two, ← Real.rpow_add hq]; ring_nf
  have hq1 : q ^ σ₀ * q ^ (1 - σ₀) = q := by
    rw [← Real.rpow_add hq]; norm_num
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hnb; exact (Real.rpow_pos_of_pos hq _).ne hnb
  have htC : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hqC : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'

  set A : ℂ := (t : ℂ) * a with hA
  set B : ℂ := (t : ℂ) ^ 2 * b with hB
  have hB0 : B ≠ 0 := mul_ne_zero (pow_ne_zero _ htC) hb0
  have hnormB : ‖B‖ = q := by
    rw [hB, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, ht2, hnb, hq1]
  have hrel' : (starRingEnd ℂ) a * b = ((q ^ (1 - σ₀) : ℝ) : ℂ) * a := by
    have := congrArg (starRingEnd ℂ) hrel
    simpa [map_mul, Complex.conj_conj, Complex.conj_ofReal] using this
  have hconjB : (starRingEnd ℂ) A * B = ((q : ℝ) : ℂ) * A := by
    rw [hA, hB, map_mul, Complex.conj_ofReal]
    have : ((t : ℝ) : ℂ) * (starRingEnd ℂ) a * (((t : ℝ) : ℂ) ^ 2 * b) =
        ((t : ℝ) : ℂ) ^ 3 * ((starRingEnd ℂ) a * b) := by ring
    rw [this, hrel']
    have h3 : ((t : ℝ) : ℂ) ^ 3 * ((q ^ (1 - σ₀) : ℝ) : ℂ) = ((q : ℝ) : ℂ) * ((t : ℝ) : ℂ) := by
      have : t ^ 3 * q ^ (1 - σ₀) = q * t := by
        rw [pow_succ, ht2, mul_comm (q ^ σ₀) t, mul_assoc, hq1, mul_comm]
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this
    calc ((t : ℝ) : ℂ) ^ 3 * (((q ^ (1 - σ₀) : ℝ) : ℂ) * a)
        = (((t : ℝ) : ℂ) ^ 3 * ((q ^ (1 - σ₀) : ℝ) : ℂ)) * a := by ring
      _ = ((q : ℝ) : ℂ) * ((t : ℝ) : ℂ) * a := by rw [h3]
      _ = ((q : ℝ) : ℂ) * (((t : ℝ) : ℂ) * a) := by ring
  have key := LanglandsTunnell.RankinSelberg.rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
    q hq A B hB0 hnormB hconjB X
  rw [hA, hB, LanglandsTunnell.RankinSelberg.rsEulerPoly_contragredient_twist_eq a b _ hb0 htC] at key

  have ht2C : ((q ^ σ₀ : ℝ) : ℂ) = ((t : ℝ) : ℂ) ^ 2 := by rw [← ht2]; push_cast; rfl
  have e1 : (((q ^ (σ₀ / 2) : ℝ) : ℂ) * a) / (q : ℂ) = ((t : ℝ) : ℂ) * a / (q : ℂ) := by rw [ht]
  have e2 : (((q ^ σ₀ : ℝ) : ℂ) * (b / (q : ℂ))) / (q : ℂ) = ((t : ℝ) : ℂ) ^ 2 * b / (q : ℂ) ^ 2 := by
    rw [ht2C]; field_simp
  have e3 : (starRingEnd ℂ) (((q ^ (σ₀ / 2) : ℝ) : ℂ) * a) / (q : ℂ) = (starRingEnd ℂ) (((t : ℝ) : ℂ) * a) / (q : ℂ) := by
    rw [ht]
  have e4 : (starRingEnd ℂ) (((q ^ σ₀ : ℝ) : ℂ) * (b / (q : ℂ))) / (q : ℂ) =
      (starRingEnd ℂ) (((t : ℝ) : ℂ) ^ 2 * b) / (q : ℂ) ^ 2 := by
    rw [ht2C, map_mul, map_mul, map_div₀, map_pow, Complex.conj_ofReal, Complex.conj_ofReal]
    field_simp
  rw [e1, e2, e3, e4]
  exact key

end DataRS

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (WA WA' FA : GL (Fin 2) ℝ → ℂ)
      (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
      (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
      (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
      (P : ℝ → ℝ) (x₀ xH : ℝ) (Hinf : ℂ → ℂ)
      (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
      (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
      (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
      (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (e₁ e₂ cS uS : ℝ) (tS : Finset (AdelicGL2 (𝓞 ℚ) ℚ)),
      Continuous φ ∧ Continuous φ' ∧
      IsRapidlyDecreasingOnSiegelSets ℚ φ ∧ IsRapidlyDecreasingOnSiegelSets ℚ φ' ∧
      (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (globalPoints (𝓞 ℚ) ℚ γ * g) = φ' g) ∧
      IsIdeleClassChar (𝓞 ℚ) ℚ ω ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ω z : ℂˣ) : ℂ) * φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (centralScalar (𝓞 ℚ) ℚ z * g) = ((ω⁻¹ z : ℂˣ) : ℂ) * φ' g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ a g‖) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' a g‖) ∧
      Φ ∈ schwartzBruhat2 ℚ ∧
      0 < e₁ ∧ e₁ < e₂ ∧ 0 < cS ∧ MeasurableSet D ∧ adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ D < ⊤ ∧
      D ⊆ {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
        ((adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).restrict
          {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      D ⊆ ⋃ t ∈ tS, (· * t) '' integralWindowedSiegelSet ℚ cS uS ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 g = WA (ratArchGL2 g) * Wf (finFactor g)) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' 1 g = WA' (ratArchGL2 g) * Wf' (finFactor g)) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g)) ∧
      (∀ g : GL (Fin 2) ℝ, FA g = Complex.exp (-(Real.pi *
          (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))) ∧
      Measurable WA ∧ Measurable WA' ∧ Measurable P ∧
      Measurable Wf ∧ Measurable Wf' ∧ Measurable Ff ∧
      (∀ n ∈ realUnipotent, ∀ g : GL (Fin 2) ℝ, WA (n * g) * WA' (n * g) = WA g * WA' g) ∧
      (∀ κ' ∈ rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det κ' = 1 →
        ∀ g : GL (Fin 2) ℝ, WA (g * κ') * WA' (g * κ') = WA g * WA' g) ∧
      (∀ (a₁ a₂ : ℝ) (h₁ : a₁ ≠ 0) (h₂ : 0 < a₂),
        WA (upperUnit a₁ 0 a₂ h₁ h₂.ne') * WA' (upperUnit a₁ 0 a₂ h₁ h₂.ne') = ((P (a₁ / a₂) : ℝ) : ℂ)) ∧
      (∀ y : ℝ, 0 ≤ P y) ∧ (¬ ∀ᵐ y : ℝ, P y = 0) ∧
      (∀ σ' : ℝ, x₀ < σ' → Integrable (fun y : ℝ => P y * |y| ^ (σ' - 2))) ∧
      xH < 0 ∧ (∀ σ' : ℝ, xH < σ' → AnalyticAt ℂ Hinf (σ' : ℂ)) ∧ Hinf 0 = 0 ∧
      (∀ s : ℂ, max x₀ 0 < s.re →
        Hinf s * ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
          ∫ y : ℝ, ((P y : ℝ) : ℂ) * ((|y| : ℝ) : ℂ) ^ (s - 2)) = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
        Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * (Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) * Ff ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
          Wf g * (Wf' g * Ff g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ →
          Wf' (finFactor (g * placeEmbed ℚ v x)) * Ff (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) * Ff (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Wf (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
          (Wf' (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n))) *
            Ff (finFactor (g * placeEmbed ℚ v
              (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)))) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (Wf (finFactor g) * (Wf' (finFactor g) * Ff (finFactor g)))) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ X : ℂ,
        (rsEulerPoly (lam v / (Ideal.absNorm v.asIdeal : ℂ)) (om v / (Ideal.absNorm v.asIdeal : ℂ))
            (lam' v / (Ideal.absNorm v.asIdeal : ℂ)) (om' v / (Ideal.absNorm v.asIdeal : ℂ)) 0).eval
          ((Ideal.absNorm v.asIdeal : ℂ) * X) =
        (rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval X) ∧
      (∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
        (∀ g : finiteAdelicGL2Subgroup ℚ, ‖Wf g * (Wf' g * Ff g)‖ ≤ B₀) ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf g * (Wf' g * Ff g) ≠ 0 →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      (∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
        ∃ (A : ℕ) (cf : ℤ → ℝ) (B : ℝ), 1 < B ∧ (∀ n, 0 ≤ cf n) ∧ (∃ n, -(A : ℤ) ≤ n ∧ n ≤ A ∧ 0 < cf n) ∧
          ∀ s : ℂ, RSCarrier.rsFinIntegral μf μNFin s
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k'}.indicator (fun g => Wf g))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k'}.indicator (fun g => Wf' g * Ff g)) =
            ∑ n ∈ Finset.Icc (-(A : ℤ)) A, ((cf n : ℝ) : ℂ) * ((B : ℝ) : ℂ) ^ (-(n : ℂ) * s)) := by
  classical

  have hunif : ∃ ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ,
      ∀ v : HeightOneSpectrum (𝓞 ℚ),
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ) := by
    have h : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ϖv : v.adicCompletionIntegers ℚ,
        Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖv) = WithZero.exp (-1 : ℤ) := by
      intro v
      obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer ℚ
      refine ⟨⟨(((WithVal.equiv (v.valuation ℚ)).symm π : WithVal (v.valuation ℚ)) : v.adicCompletion ℚ), ?_⟩, ?_⟩
      · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← WithZero.exp_zero]
        exact WithZero.exp_le_exp.mpr (by norm_num)
      · change Valued.v ((((WithVal.equiv (v.valuation ℚ)).symm π : WithVal (v.valuation ℚ)) : v.adicCompletion ℚ)) = _
        rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
    exact ⟨fun v => (h v).choose, fun v => (h v).choose_spec⟩
  obtain ⟨ϖ, hϖ⟩ := hunif
  have hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0 := by
    intro v h0
    have h1 := hϖ v
    rw [h0, map_zero] at h1
    first
      | exact WithZero.exp_ne_zero h1.symm
      | exact WithZero.coe_ne_zero h1.symm
      | (revert h1; decide)

  obtain ⟨S, σ₀, k₀, ω, φ, WA, Wf, mS, P, x₀, Hinf, hωicc', hωunit, hφc, hφrd, hφleft, hφcen, hφcusp, hφsum, hφfac,
      hWAN, hWAwt, hWAc, hWfmeas, hWfN, hWfψ, hWfK, hWfKu, hWfT, hWfZ, hom0, hκ', hunitrel, hWfbdd, hWfsupp, hWfdet,
      hWfint, hPmeas, hPtorus, hPnn, hPne, hPint, hHan, hH0, hHinv⟩ :=
    AutomorphicForm.exists_unitaryShapedVector_whittakerFactorization_torusProfile_of_isArithGenuineCuspRealizable_rat
      c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ ϖ hϖ hπall
  have hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0 := fun v _ => hπall v

  let lam : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun v => ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (σ₀ / 2) : ℝ) : ℂ) * Θ.a v
  let om : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun v =>
    ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ σ₀ : ℝ) : ℂ) * (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))
  let lam' : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun v => (starRingEnd ℂ) (lam v)
  let om' : HeightOneSpectrum (𝓞 ℚ) → ℂ := fun v => (starRingEnd ℂ) (om v)
  have hκ : ∃ κ : ℝ, (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ) := by
    obtain ⟨κ, hκ⟩ := hκ'
    refine ⟨κ, fun v hv => ?_⟩
    obtain ⟨h1, h2⟩ := hκ v hv
    refine ⟨h1, h2, ?_, ?_⟩
    · show ‖(starRingEnd ℂ) (lam v)‖ ≤ _
      rw [Complex.norm_conj]; exact h1
    · show ‖(starRingEnd ℂ) (om v)‖ ≤ _
      rw [Complex.norm_conj]; exact h2
  obtain ⟨κ, hκ⟩ := hκ

  let φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g => (starRingEnd ℂ) (φ g)
  let WA' : GL (Fin 2) ℝ → ℂ := fun h => (starRingEnd ℂ) (WA h)
  let Wf' : finiteAdelicGL2Subgroup ℚ → ℂ := fun g => (starRingEnd ℂ) (Wf g)

  obtain ⟨Φ, hΦmem, hΦrow⟩ :=
    NumberField.AdelicFourier.exists_mem_schwartzBruhat2_apply_bottomRowVec_eq_gaussian_mul_indicator_rat S mS
  let FA : GL (Fin 2) ℝ → ℂ := fun g =>
    Complex.exp (-(Real.pi * (((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) : ℝ))
  let Ff : finiteAdelicGL2Subgroup ℚ → ℂ := fun h =>
    if DataRS.FfC S mS (h : AdelicGL2 (𝓞 ℚ) ℚ) then (1 : ℂ) else 0

  obtain ⟨cS, uS, tS, D, hcS, hDmeas, hDslab, hDfd, hDcov⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre
      ℚ c u d₁ d₂ T hc hd₁ hd hcov 1 2 one_pos one_lt_two

  have hψnorm : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ‖NumberField.StandardAddChar.psiQ x‖ = 1 :=
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ NumberField.StandardAddChar.isGlobalAddChar_psiQ
  have hWconj : ∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ⁻¹ φ' a g =
        (starRingEnd ℂ) (whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ a g) := by
    intro a g
    have h := AutomorphicForm.whittakerCoefficient_inv_star_mul_apply_det_eq_star_whittakerCoefficient_mul ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      NumberField.StandardAddChar.psiQ hψnorm φ (fun _ => 1) a g
    simp only [mul_one] at h
    exact h

  refine ⟨S, φ, φ', WA, WA', FA, Wf, Wf', Ff, Φ, ω, P, x₀, -1, Hinf, ϖ, hπ, lam, om, lam', om', κ, D, 1, 2, cS, uS, tS,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact hφc
  ·
    exact (continuous_star).comp hφc
  ·
    exact hφrd
  ·
    intro c₁ u₁ t₁ hc₁ N₁
    obtain ⟨C₁, hC₁⟩ := hφrd c₁ u₁ t₁ hc₁ N₁
    refine ⟨C₁, fun g hg => ?_⟩
    show ‖(starRingEnd ℂ) (φ (g * t₁))‖ * _ ≤ C₁
    rw [Complex.norm_conj]
    exact hC₁ g hg
  ·
    exact hφleft
  ·
    intro γ g
    show (starRingEnd ℂ) (φ _) = (starRingEnd ℂ) (φ g)
    rw [hφleft]
  ·
    exact hωicc'
  ·
    exact hφcen
  ·
    intro z g
    show (starRingEnd ℂ) (φ _) = _ * (starRingEnd ℂ) (φ g)
    rw [hφcen, map_mul]
    congr 1
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, starRingEnd_apply, Complex.star_def]
    exact (Complex.inv_eq_conj (hωunit z)).symm
  ·
    intro g
    rw [hWconj, hφcusp g, map_zero]
  ·
    exact hφsum
  ·
    intro g
    simp only [hWconj, Complex.norm_conj]
    exact hφsum g
  ·
    exact hΦmem
  ·
    norm_num
  ·
    norm_num
  ·
    exact hcS
  ·
    exact hDmeas
  ·
    have hsub : D ⊆ ⋃ t ∈ tS, (((· * t) '' integralWindowedSiegelSet ℚ cS uS) ∩
        {g | TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (1 : ℝ) 2}) := by
      intro g hg
      have h1 := hDcov hg
      have h2 := hDslab hg
      simp only [Set.mem_iUnion, exists_prop] at h1 ⊢
      obtain ⟨t, ht, hgt⟩ := h1
      exact ⟨t, ht, hgt, h2⟩
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    refine lt_of_le_of_lt (measure_biUnion_finset_le tS _) ?_
    first
      | exact ENNReal.sum_lt_top.mpr fun t _ =>
          AutomorphicForm.adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat cS uS hcS t 1 2 one_pos
      | exact ENNReal.sum_lt_top fun t _ =>
          (AutomorphicForm.adelicGLHaar_image_mul_right_integralWindowedSiegelSet_inter_slab_lt_top_rat cS uS hcS t 1 2
            one_pos).ne
  ·
    exact hDslab
  ·
    exact hDfd
  ·
    exact hDcov
  ·
    exact hφfac
  ·
    intro g
    rw [hWconj, hφfac g, map_mul]
  ·
    intro g
    rw [hΦrow g]
    congr 1
    · show ((Real.exp _ : ℝ) : ℂ) = Complex.exp _
      rw [Complex.ofReal_exp, Complex.ofReal_neg]
    · simp only [Ff, DataRS.FfC, DataRS.finFactor_entry_snd]
  ·
    intro g; rfl
  ·
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
    exact hWAc.measurable
  ·
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    haveI : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩
    exact (continuous_star.comp hWAc).measurable
  ·
    exact hPmeas
  ·
    exact hWfmeas
  ·
    exact (continuous_star.measurable).comp hWfmeas
  ·
    refine Measurable.ite ?_ measurable_const measurable_const
    exact ((DataRS.isClosed_FfC S mS ϖ hϖ).preimage continuous_subtype_val).measurableSet
  ·
    intro n hn g
    obtain ⟨x, rfl⟩ := hn
    show WA _ * (starRingEnd ℂ) (WA _) = WA g * (starRingEnd ℂ) (WA g)
    rw [Complex.mul_conj, Complex.mul_conj]
    congr 1
    have h := hWAN x.toAdd g
    have he : Complex.normSq (Complex.exp (2 * Real.pi * Complex.I * (x.toAdd : ℝ))) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
      simp
    change Complex.normSq (WA (unipotentGL2 x.toAdd * g)) = Complex.normSq (WA g)
    rw [h, map_mul, he, one_mul]
  ·
    intro κ' hκ' hdet g
    have hκ₀ : κ' ∈ rowIsometrySubgroup₀ ℝ := ⟨by simpa [MonoidHom.mem_ker] using hdet, hκ'⟩
    show WA _ * (starRingEnd ℂ) (WA _) = WA g * (starRingEnd ℂ) (WA g)
    rw [Complex.mul_conj, Complex.mul_conj]
    congr 1
    rw [hWAwt κ' hκ₀ g, map_mul, Complex.normSq_eq_norm_sq ((archWeightCharℝ _ _ : ℂˣ) : ℂ),
      DataRS.norm_archWeightCharℝ, one_pow, one_mul]
  ·
    exact hPtorus
  ·
    exact hPnn
  ·
    exact hPne
  ·
    exact hPint
  ·
    norm_num
  ·
    exact hHan
  ·
    exact hH0
  ·
    exact hHinv
  ·
    intro v _; exact hϖ v
  ·
    exact hκ
  ·
    intro n g
    have hFf : Ff ((n : finiteAdelicGL2Subgroup ℚ) * g) = Ff g := by
      have e : DataRS.FfC S mS (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
          DataRS.FfC S mS (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        simp only [DataRS.FfC, DataRS.bottom_row_finUnipotent_mul]
      show (if DataRS.FfC S mS (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)
          then (1 : ℂ) else 0) = (if DataRS.FfC S mS (g : AdelicGL2 (𝓞 ℚ) ℚ) then (1 : ℂ) else 0)
      simp only [e]
    have h1 : Wf ((n : finiteAdelicGL2Subgroup ℚ) * g) * Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g) = Wf g * Wf' g := by
      show Wf _ * (starRingEnd ℂ) (Wf _) = Wf g * (starRingEnd ℂ) (Wf g)
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hWfN]
    rw [← mul_assoc, ← mul_assoc, h1, hFf]
  ·
    intro v hv
    obtain ⟨ψv, -, h0, h1, h2⟩ := hWfψ v hv
    exact ⟨ψv, h0, h1, h2⟩
  ·
    exact hWfK
  ·
    intro v hv x g hx
    have h1 : Wf' (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g) := by
      show (starRingEnd ℂ) (Wf _) = (starRingEnd ℂ) (Wf _)
      rw [hWfK v hv x g hx]
    have h2 : Ff (finFactor (g * placeEmbed ℚ v x)) = Ff (finFactor g) := by
      show (if DataRS.FfC S mS (finFactor (g * placeEmbed ℚ v x) : AdelicGL2 (𝓞 ℚ) ℚ) then (1 : ℂ) else 0) =
        (if DataRS.FfC S mS (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) then (1 : ℂ) else 0)
      have e : DataRS.FfC S mS (finFactor (g * placeEmbed ℚ v x) : AdelicGL2 (𝓞 ℚ) ℚ) =
          DataRS.FfC S mS (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) :=
        propext ((DataRS.FfC_finFactor S mS _).trans ((DataRS.FfC_mul_placeEmbed_iff hv hx g).trans
          (DataRS.FfC_finFactor S mS g).symm))
      simp only [e]
    rw [h1, h2]
  ·
    intro v hv g m n hg
    obtain ⟨ψv, hψu, hψ0, hψ1, hψN⟩ := hWfψ v hv
    obtain ⟨b, hb⟩ := hWfT v hv
    have hNpos : 0 < Ideal.absNorm v.asIdeal :=
      Nat.pos_of_ne_zero (fun h => v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h))
    haveI : Nonempty (Fin (Ideal.absNorm v.asIdeal)) := ⟨⟨0, hNpos⟩⟩
    have hψinv : ∀ x : v.adicCompletion ℚ, ψv⁻¹ x = (starRingEnd ℂ) (ψv x) := by
      intro x
      rw [AddChar.inv_apply', Complex.inv_eq_conj (hψu x)]

    have hψ'0 : ∀ r : v.adicCompletionIntegers ℚ,
        ψv⁻¹ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1 := by
      intro r; rw [hψinv, hψ0 r, map_one]
    have hψ'1 : ∃ r : v.adicCompletionIntegers ℚ,
        ψv⁻¹ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
          algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1 := by
      obtain ⟨r, hr⟩ := hψ1
      refine ⟨r, fun h => hr ?_⟩
      rw [hψinv] at h
      have := congrArg (starRingEnd ℂ) h
      rwa [Complex.conj_conj, map_one] at this
    have hN' : ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf' (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψv⁻¹ x * Wf' (finFactor g) := by
      intro x g
      show (starRingEnd ℂ) (Wf _) = _ * (starRingEnd ℂ) (Wf _)
      rw [hψN x g, map_mul, hψinv]
    have hK' : ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf' (finFactor (g * placeEmbed ℚ v
          (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf' (finFactor g) := by
      intro r g
      show (starRingEnd ℂ) (Wf _) = (starRingEnd ℂ) (Wf _)
      rw [hWfKu v hv r g]
    have hT' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        (∑ i, Wf' (finFactor (g * placeEmbed ℚ v
            (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
              (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
          Wf' (finFactor (g * placeEmbed ℚ v
            (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
        lam' v * Wf' (finFactor g) := by
      intro g
      have := congrArg (starRingEnd ℂ) (hb g)
      rw [map_add, map_sum, map_mul] at this
      exact this
    have hZ' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf' (finFactor (g * placeEmbed ℚ v
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
        om' v * Wf' (finFactor g) := by
      intro g
      have := congrArg (starRingEnd ℂ) (hWfZ v hv g)
      rw [map_mul] at this
      exact this
    have hom' : om' v ≠ 0 := by
      show (starRingEnd ℂ) (om v) ≠ 0
      exact (map_ne_zero _).mpr (hom0 v hv)
    have hF : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
        Ff (finFactor (g * placeEmbed ℚ v
          (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v) m *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v) ^ n))) =
        (if 0 ≤ n then Ff (finFactor g) else 0) := by
      intro g m n hg
      have e := (DataRS.FfC_finFactor S mS _).trans
        ((DataRS.FfC_mul_torus_iff (S := S) (mS := mS) hv (hπall v) (hϖ v) hg m n).trans
          (and_congr_left' (DataRS.FfC_finFactor S mS g).symm))
      show (if DataRS.FfC S mS (finFactor (g * placeEmbed ℚ v
          (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v) m *
            scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v) ^ n)) :
              AdelicGL2 (𝓞 ℚ) ℚ) then (1 : ℂ) else 0) =
        (if 0 ≤ n then (if DataRS.FfC S mS (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) then (1 : ℂ) else 0) else 0)
      rw [propext e]
      by_cases hn : 0 ≤ n
      · by_cases hc : DataRS.FfC S mS (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)
        · rw [if_pos ⟨hc, hn⟩, if_pos hn, if_pos hc]
        · rw [if_neg (fun h => hc h.1), if_pos hn, if_neg hc]
      · rw [if_neg (fun h => hn h.2), if_neg hn]
    exact UnramifiedWhittaker.mul_mul_apply_mul_placeEmbed_diagZ_mul_scalarPi_zpow_eq_of_torus_data_rat v (hπall v) b
      (Fintype.card_fin _) (fun g => Wf (finFactor g)) (fun g => Wf' (finFactor g)) (fun g => Ff (finFactor g))
      ψv ψv⁻¹ (lam v) (om v) (lam' v) (om' v) hψ0 hψ1 hψ'0 hψ'1 hψN hN' (hWfKu v hv) hK' hb hT' (hWfZ v hv) hZ'
      (hom0 v hv) hom' hF g m n hg
  ·
    intro v hv X
    obtain ⟨hrel, hnb⟩ := hunitrel v hv
    have hq0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp h))
    have key := DataRS.rescale_assembly ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) σ₀ hq0 (Θ.a v) (Θ.b v) hrel hnb X
    simp only [Complex.ofReal_natCast] at key
    exact key
  ·
    obtain ⟨B₁, hB₁⟩ := hWfbdd
    obtain ⟨Cpt, hCpt, hsupp⟩ := hWfsupp
    have hB0 : 0 ≤ B₁ := le_trans (norm_nonneg _) (hB₁ 1)
    refine ⟨Cpt, B₁ * (B₁ * 1), hCpt, ?_, ?_⟩
    · intro g
      rw [norm_mul, norm_mul]
      have hFf1 : ‖Ff g‖ ≤ 1 := by
        show ‖(if DataRS.FfC S mS (g : AdelicGL2 (𝓞 ℚ) ℚ) then (1 : ℂ) else 0)‖ ≤ 1
        by_cases h : DataRS.FfC S mS (g : AdelicGL2 (𝓞 ℚ) ℚ)
        · rw [if_pos h, norm_one]
        · rw [if_neg h, norm_zero]; exact zero_le_one
      have hWf' : ‖Wf' g‖ ≤ B₁ := by
        show ‖(starRingEnd ℂ) (Wf g)‖ ≤ B₁
        rw [Complex.norm_conj]; exact hB₁ g
      exact mul_le_mul (hB₁ g) (mul_le_mul hWf' hFf1 (norm_nonneg _) hB0) (by positivity) hB0
    · intro g hcell hne
      have hWf : Wf g ≠ 0 := by intro h; apply hne; rw [h, zero_mul]
      have hFf : Ff g ≠ 0 := by intro h; apply hne; rw [h, mul_zero, mul_zero]
      have hcond : DataRS.FfC S mS (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        by_contra hc
        apply hFf
        simp only [Ff, hc, if_false]
      exact hsupp g hcell hWf hcond
  ·
    intro μf _ μNFin _
    haveI : SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ) :=
      NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo ℚ
    haveI : SecondCountableTopology (finiteAdelicGL2Subgroup ℚ) :=
      TopologicalSpace.Subtype.secondCountableTopology (finiteAdelicGL2Subgroup ℚ : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    exact DataRS.cell_const_assembly μf μNFin
      (fun g => (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k'))
      (fun g => ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
                    Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
                  (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
                    Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                        WithZero.exp (-(mS p : ℤ)) ∧
                    Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                        WithZero.exp (-(mS p : ℤ)))))
      Wf Ff (fun g h => if_pos h) (fun g h => if_neg h) hWfdet (hWfint μf μNFin).1 (hWfint μf μNFin).2

end S_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat
end P2MW
export P2MW.S_AutomorphicForm_exists_rankinSelberg_testData_of_isArithGenuineCuspRealizable_rat (solution)
