-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d423c485-e88e-5c76-abcb-cfbeb26c709b

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_norm_centralChar_eq_ideleNorm_rpow_of_forall_norm_b_eq
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal Polynomial
open AutomorphicForm MeasureTheory NumberField.AdelicHaar AdelicDock
open scoped Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace UnitarityPack

variable (F : Type) [Field F] [NumberField F]

private theorem _root_.UnitarityPack.ideleNorm_uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) :
    ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ :=
  NumberField.TateGlobal.ideleNorm_uniformizerIdele F v

p2m_export "UnitarityPack" "ideleNorm_uniformizerIdele"

private theorem det_heckeGen (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal
    ![((Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v)) : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F), 1]) = _
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp [uniformizerIdele]

private theorem unit_det_norm (N : Ideal (𝓞 F)) :
    ∀ u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := fun u hu =>
  NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem F _
    (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup F N) u hu

private theorem exists_finset_level (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ¬ N ≤ v.asIdeal := by
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ N}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot])
  refine ⟨hfin.toFinset, fun v hv hle => hv ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le]
  exact hle

private noncomputable def weyl (v : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (v.adicCompletion F) where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem weyl_inv (v : HeightOneSpectrum (𝓞 F)) : (weyl F v)⁻¹ = weyl F v := rfl

private theorem coe_weyl (v : HeightOneSpectrum (𝓞 F)) :
    ((weyl F v : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![0, 1; 1, 0] :=
  rfl

private theorem isLocalLevelOne_weyl (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (v : HeightOneSpectrum (𝓞 F))
    (hv : ¬ v.asIdeal ∣ N) :
    IsLocalLevelOne (𝓞 F) F v N ((weyl F v : GL (Fin 2) (v.adicCompletion F)) : Matrix _ _ _) := by
  rw [coe_weyl]
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp
  · simp [idealBound_eq_one_of_not_dvd hN hv]
  · simp [idealBound_eq_one_of_not_dvd hN hv]

private theorem weyl_mem (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ N) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (weyl F v)) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [finEmbed_mem_levelOne_iff, mem_finiteLevelOne_iff, ← map_inv, weyl_inv, coe_localEmbed,
      isLevelOneMatrix_localMat_iff]
    exact ⟨isLocalLevelOne_weyl F N hN v hv, isLocalLevelOne_weyl F N hN v hv⟩
  · rw [mem_finiteAdelicGL2Subgroup_iff, glArch_finEmbed]

private theorem diagOne_inv_eq (v : HeightOneSpectrum (𝓞 F)) :
    diagOne (uniformizerUnit F v)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (uniformizerUnit F v)⁻¹ *
        (weyl F v * diagOne (uniformizerUnit F v) * (weyl F v)⁻¹) := by
  rw [weyl_inv]
  refine Units.ext ?_
  show Matrix.diagonal ![(((uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), 1] =
    Matrix.scalar (Fin 2) (((uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      (!![0, 1; 1, 0] * Matrix.diagonal ![((uniformizerUnit F v : (v.adicCompletion F)ˣ) : v.adicCompletion F), 1] *
        !![0, 1; 1, 0])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem heckeGen_eq (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagOne (uniformizerUnit F v))) := by
  refine Units.ext ?_
  rw [coe_finEmbed, coe_localEmbed]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [mapMatrix_arch_finMat]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, heckeGen]
    exact heckeGenAt_fst (uniformizerUnit F v) i j
  · rw [mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply, adeleFin_apply, heckeGen]
      rw [heckeGenAt_snd_apply_self, diagOne_coe_apply]
    · rw [mapMatrix_localMat_of_ne (𝓞 F) F v _ hw]
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply, adeleFin_apply, heckeGen]
      exact heckeGenAt_snd_apply_of_ne (uniformizerUnit F v) hw i j

private theorem centralScalar_inv_eq (v : HeightOneSpectrum (𝓞 F)) :
    centralScalar (𝓞 F) F (uniformizerIdele F v)⁻¹ =
      finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (Matrix.GeneralLinearGroup.scalar (Fin 2) (uniformizerUnit F v)⁻¹)) := by
  set u : (AdeleRing (𝓞 F) F)ˣ :=
    Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v)⁻¹) with hu
  have hidele : (uniformizerIdele F v)⁻¹ = u := by
    rw [hu, uniformizerIdele, ← map_inv, ← map_inv]
  have h1 : ((u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
    rw [hu]
    exact finIncl_apply_fst (𝓞 F) F _
  have hv : ((u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v =
      (((uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
    rw [hu]
    exact localUnit_apply_self (𝓞 F) F v _
  have hw' : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → ((u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w = 1 := by
    intro w hw
    rw [hu]
    exact localUnit_apply_of_ne (𝓞 F) F v _ hw
  refine Units.ext ?_
  rw [coe_finEmbed, coe_localEmbed, NumberField.AdelicVolume.centralScalar_val, hidele]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [mapMatrix_arch_finMat]
    ext i j
    rcases eq_or_ne i j with hij | hij
    · subst hij
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact h1
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij,
        map_zero]
  · rw [mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    by_cases hw : w = v
    · rw [hw, mapMatrix_localMat_self]
      ext i j
      rcases eq_or_ne i j with hij | hij
      · subst hij
        change _ = Matrix.scalar (Fin 2)
          (((uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) i i
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.scalar_apply]
        rw [adeleFin_apply, finAdeleEval_apply]
        exact hv
      · change _ = Matrix.scalar (Fin 2)
          (((uniformizerUnit F v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hij, Matrix.scalar_apply,
          map_zero]
    · rw [mapMatrix_localMat_of_ne (𝓞 F) F v _ hw]
      ext i j
      rcases eq_or_ne i j with hij | hij
      · subst hij
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        rw [adeleFin_apply, finAdeleEval_apply]
        exact hw' w hw
      · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij,
          map_zero]

private theorem inverse_class_datum (N : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ N ≤ v.asIdeal) :
    ∃ u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      ∃ u' ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
        (heckeGen (𝓞 F) F v)⁻¹ =
          centralScalar (𝓞 F) F ((uniformizerIdele F v)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) *
            (u * heckeGen (𝓞 F) F v * u') := by
  have hN : N ≠ ⊥ := fun h => hv (h ▸ bot_le)
  have hdvd : ¬ v.asIdeal ∣ N := fun h => hv (Ideal.dvd_iff_le.mp h)
  refine ⟨_, weyl_mem F N hN v hdvd, _, Subgroup.inv_mem _ (weyl_mem F N hN v hdvd), ?_⟩
  rw [heckeGen_eq, centralScalar_inv_eq]
  simp only [← map_inv, ← map_mul]
  rw [diagOne_inv_eq]

private theorem memLp_two_FD (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) (𝓕 : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})) :
    MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict 𝓕) := by
  have _ := hR
  have hls := (lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _).mp R.smoothCusp.1.1
  have h := (exists_forall_memLp_two_comp_mul_right_restrict_and_eLpNorm_le_of_isFundamentalDomain F c u d₁ d₂ T
    hd hcov R.toFun (fun n => ((R.centralChar ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)) (fun n => Units.ne_zero _)
    hls.2 hls.1.left_invariant (fun n w => hls.1.central_transform ⟨n, Subgroup.mem_top n⟩ w) e₁ e₂ he₁ he 𝓕
    h𝓕s h𝓕).1 1
  simpa using h

private theorem exists_finset_conj_a_eq (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ)
    (r : ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hb : ∀ v ∉ S, ‖Φ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r)) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S ∪ S₂,
      starRingEnd ℂ (Φ.a v) =
        Φ.a v * starRingEnd ℂ (Φ.b v) / ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ) := by
  obtain ⟨R, hR⟩ := hΦ
  obtain ⟨𝓕, h𝓕s, h𝓕⟩ := exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F 1 2
  have he₁ : (0 : ℝ) < 1 := one_pos
  have he : (1 : ℝ) < 2 := one_lt_two
  obtain ⟨SN, hSN⟩ := exists_finset_level F Φ.level Φ.level_ne_bot

  have hraw : ∀ v ∉ S, ‖Φ.toRawCentral.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(1 - 2 * r)) := by
    intro v hv
    have hN : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    simp only [HeckeEigensystem.toRawCentral, norm_mul, norm_inv, HeckeEigensystem.cNorm, Complex.norm_natCast,
      hb v hv]
    rw [Real.rpow_neg hN.le, Real.rpow_sub hN, Real.rpow_one]
    field_simp

  have hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ),
      ‖((R.centralChar z : ℂˣ) : ℂ)‖ = ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ (1 - 2 * r) :=
    SmoothCuspRealizationAt.norm_centralChar_eq_ideleNorm_rpow_of_forall_norm_b_eq F _ _ Φ.toRawCentral R hR
      (1 - 2 * r) S hraw

  have hP := (exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain
    F c u d₁ d₂ T hd hcov Φ Φ R R hR (1 - 2 * r) (fun x => hσ ⟨x, Subgroup.mem_top x⟩) 1 2 he₁ he 𝓕 h𝓕s h𝓕).2.1
  refine ⟨SN ∪ R.exceptionalSet, fun v hv => ?_⟩
  have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
  have hvN : v ∉ SN := fun h => hv (Finset.mem_union_right _ (Finset.mem_union_left _ h))
  have hvE : v ∉ R.exceptionalSet := fun h => hv (Finset.mem_union_right _ (Finset.mem_union_right _ h))

  obtain ⟨reps, hsys, heig⟩ := R.hecke_eigen v hvE
  obtain ⟨u₀, hu₀, u₁, hu₁, hinv⟩ := inverse_class_datum F Φ.level v (hSN v hvN)
  have hφ : IsLsXiFunction (𝓞 F) F ⊤ R.centralChar R.toFun :=
    ((lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _).mp R.smoothCusp.1.1).1
  have hU : ∀ w ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F,
      ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (1 - 2 * r) = 1 := by
    intro w hw
    rw [unit_det_norm F Φ.level w hw, Real.one_rpow]
  have hreps : ∀ i, ∃ a ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F,
      ∃ a' ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F, reps i = a * heckeGen (𝓞 F) F v * a' := by
    intro i
    obtain ⟨a, ha, a', ha', h⟩ := (HeckePair.mem_doubleCoset_iff).mp (hsys.mem_doubleCoset i)
    exact ⟨a, ha, a', ha', h.symm⟩
  have hc : ∃ a ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F,
      ∃ a' ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F,
        (heckeGen (𝓞 F) F v)⁻¹ =
          centralScalar (𝓞 F) F
            ((⟨(uniformizerIdele F v)⁻¹, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) :
              (AdeleRing (𝓞 F) F)ˣ) * (a * heckeGen (𝓞 F) F v * a') :=
    ⟨u₀, hu₀, u₁, hu₁, hinv⟩
  have h₂ := memLp_two_FD F c u d₁ d₂ T hd hcov Φ R hR 1 2 he₁ he 𝓕 h𝓕s h𝓕
  have hadj := (cosetSum_adjoint_weightedPairing_of_isLsXiFunction F 1 2 he₁ 𝓕 h𝓕s h𝓕 R.centralChar
    (1 - 2 * r) hσ (levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F) hU R.toFun R.toFun hφ hφ hR hR h₂ h₂
    (R.level_invariant) (R.level_invariant) (heckeGen (𝓞 F) F v) _ reps hreps _ hc).2.2

  have hsum : ∀ x, (∑ i, R.toFun (x * reps i)) = Φ.a v * R.toFun x := fun x => heig x

  have hcent : ((R.centralChar ⟨(uniformizerIdele F v)⁻¹, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * (Φ.b v)⁻¹ := by
    obtain ⟨g₀, hg₀⟩ := R.exists_ne_zero
    have h1 := R.central_eigen v hvE g₀
    have h2 := hφ.central_transform
      ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v), Subgroup.mem_top _⟩ g₀
    have h3 : ((R.centralChar ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v), Subgroup.mem_top _⟩ : ℂˣ) :
        ℂ) = Φ.toRawCentral.b v :=
      mul_right_cancel₀ hg₀ (h2.symm.trans h1)
    have h4 : (⟨(uniformizerIdele F v)⁻¹, Subgroup.mem_top _⟩ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) =
        (⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v), Subgroup.mem_top _⟩)⁻¹ := by
      ext
      simp [det_heckeGen]
    erw [h4, map_inv, Units.val_inv_eq_inv_val, h3]
    simp only [HeckeEigensystem.toRawCentral, HeckeEigensystem.cNorm]
    rw [mul_inv, inv_inv]

  have hL : (∫ x in 𝓕, (∑ i, R.toFun (x * reps i)) * starRingEnd ℂ (R.toFun x) *
      ((ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-(1 - 2 * r)) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F))
      = Φ.a v * peterssonIntegral F (1 - 2 * r) 𝓕 R.toFun R.toFun := by
    simp only [hsum, mul_assoc (Φ.a v)]
    rw [integral_const_mul]
    rfl
  have hRt : (∫ x in 𝓕, R.toFun x * starRingEnd ℂ (∑ i, R.toFun (x * reps i)) *
      ((ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-(1 - 2 * r)) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F))
      = starRingEnd ℂ (Φ.a v) * peterssonIntegral F (1 - 2 * r) 𝓕 R.toFun R.toFun := by
    simp only [hsum, map_mul]
    have : ∀ x, R.toFun x * (starRingEnd ℂ (Φ.a v) * starRingEnd ℂ (R.toFun x)) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-(1 - 2 * r)) : ℝ) : ℂ) =
        starRingEnd ℂ (Φ.a v) * (R.toFun x * starRingEnd ℂ (R.toFun x) *
          ((ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-(1 - 2 * r)) : ℝ) : ℂ)) := fun x => by ring
    simp only [this]
    rw [integral_const_mul]
    rfl
  rw [hL, hRt, det_heckeGen, ideleNorm_uniformizerIdele] at hadj
  erw [hcent] at hadj

  have hNr : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hb0 : Φ.b v ≠ 0 := by
    intro h
    have := hb v hvS
    rw [h, norm_zero] at this
    exact (Real.rpow_pos_of_pos hNr _).ne this
  have hmain : Φ.a v = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ (1 - 2 * r) : ℝ) : ℂ) *
      starRingEnd ℂ (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * (Φ.b v)⁻¹) * starRingEnd ℂ (Φ.a v) := by
    have h := hadj
    rw [← mul_assoc] at h
    exact mul_right_cancel₀ hP (by rw [h])
  rw [Real.inv_rpow hNr.le, Real.rpow_sub hNr, Real.rpow_one, map_mul, map_inv₀, Complex.conj_natCast] at hmain
  have hNc : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
  have hcb : starRingEnd ℂ (Φ.b v) ≠ 0 := (_root_.map_ne_zero _).mpr hb0
  have hN2 : ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hNr _).ne'

  rw [eq_div_iff hN2]
  have hcast : ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ) =
      (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r))⁻¹ : ℝ) : ℂ) *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
    push_cast
    field_simp
  rw [hcast]
  calc starRingEnd ℂ (Φ.a v) *
        ((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r))⁻¹ : ℝ) : ℂ) *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ))
      = ((((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r))⁻¹ : ℝ) : ℂ) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * (starRingEnd ℂ (Φ.b v))⁻¹) * starRingEnd ℂ (Φ.a v)) *
          starRingEnd ℂ (Φ.b v) := by
        field_simp
    _ = Φ.a v * starRingEnd ℂ (Φ.b v) := by rw [← hmain]

end UnitarityPack

open UnitarityPack in
open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (hnorm : ∀ v ∉ S₁, IsUnramifiedCharAt χ v →
      ‖(((χ (uniformizerIdele F v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v‖ = 1) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S₁ ∪ S₂, IsUnramifiedCharAt χ v →
      starRingEnd ℂ (((χ (uniformizerIdele F v) : ℂˣ) : ℂ) * Φ.a v) =
        (((χ (uniformizerIdele F v) : ℂˣ) : ℂ) * Φ.a v) /
          ((((χ (uniformizerIdele F v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v) := by

  obtain ⟨r, hr⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F χ hχ hχc
  obtain ⟨Sram, hSram⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous F χ hχc

  have hN : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := fun v => by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hχv : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((χ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-r) := by
    intro v
    rw [hr, UnitarityPack.ideleNorm_uniformizerIdele, Real.inv_rpow (hN v).le, ← Real.rpow_neg (hN v).le]
  have hb : ∀ v ∉ S₁ ∪ Sram, ‖Φ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) := by
    intro v hv
    have h1 := hnorm v (fun h => hv (Finset.mem_union_left _ h)) (hSram v (fun h => hv (Finset.mem_union_right _ h)))
    rw [norm_mul, Units.val_pow_eq_pow_val, norm_pow, hχv] at h1
    have hpos' : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r := Real.rpow_pos_of_pos (hN v) _
    have hinv : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-r) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r)⁻¹ :=
      Real.rpow_neg (hN v).le r
    have h2 : ‖Φ.b v‖ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r) ^ (2 : ℕ) := by
      rw [hinv, inv_pow] at h1
      have h4 : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hpos'.ne'
      calc ‖Φ.b v‖ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r) ^ (2 : ℕ) *
              (((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r) ^ (2 : ℕ))⁻¹ * ‖Φ.b v‖) := by
            rw [← mul_assoc, mul_inv_cancel₀ h4, one_mul]
        _ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ r) ^ (2 : ℕ) := by rw [h1, mul_one]
    rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul (hN v).le]
    congr 1
    push_cast
    ring
  obtain ⟨S₂, hS₂⟩ := UnitarityPack.exists_finset_conj_a_eq F c u d₁ d₂ T hd hcov Φ hΦ r (S₁ ∪ Sram) hb
  refine ⟨Sram ∪ S₂, fun v hv hunr => ?_⟩
  have hv' : v ∉ (S₁ ∪ Sram) ∪ S₂ := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hv (Finset.mem_union_left _ h)
      · exact hv (Finset.mem_union_right _ (Finset.mem_union_left _ h))
    · exact hv (Finset.mem_union_right _ (Finset.mem_union_right _ h))
  have hkey := hS₂ v hv'
  have hbv := hb v (fun h => hv' (Finset.mem_union_left _ h))
  have hnv := hnorm v (fun h => hv (Finset.mem_union_left _ h)) hunr

  set x : ℂ := ((χ (uniformizerIdele F v) : ℂˣ) : ℂ) with hxdef
  have hx0 : x ≠ 0 := Units.ne_zero _
  have hb0 : Φ.b v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hbv
    exact (Real.rpow_pos_of_pos (hN v) _).ne hbv
  have hN2 : ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (hN v) _).ne'
  have hxx : starRingEnd ℂ x * x = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-r) : ℝ) : ℂ) ^ (2 : ℕ) := by
    rw [Complex.conj_mul', hχv]
  have hbb : starRingEnd ℂ (Φ.b v) * Φ.b v = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ) ^ (2 : ℕ) := by
    rw [Complex.conj_mul', hbv]
  have hmod : starRingEnd ℂ x * x * (starRingEnd ℂ (Φ.b v) * Φ.b v) =
      ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ) := by
    rw [hxx, hbb]
    have : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-r)) ^ (2 : ℕ) *
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r)) ^ (2 : ℕ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (hN v).le, ← Real.rpow_mul (hN v).le,
        ← Real.rpow_add (hN v)]
      congr 1
      push_cast
      ring
    exact_mod_cast this
  rw [map_mul, hkey, Units.val_pow_eq_pow_val]
  change starRingEnd ℂ x * (Φ.a v * starRingEnd ℂ (Φ.b v) / ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ))
    = x * Φ.a v / (x ^ 2 * Φ.b v)
  rw [mul_div_assoc', div_eq_div_iff hN2 (mul_ne_zero (pow_ne_zero 2 hx0) hb0)]
  calc starRingEnd ℂ x * (Φ.a v * starRingEnd ℂ (Φ.b v)) * (x ^ 2 * Φ.b v)
      = x * Φ.a v * (starRingEnd ℂ x * x * (starRingEnd ℂ (Φ.b v) * Φ.b v)) := by ring
    _ = x * Φ.a v * ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 * r) : ℝ) : ℂ) := by rw [hmod]

end S_AutomorphicForm_exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one (solution)
