-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cfd3b538-ac0f-56ea-bd9e-ef0c67518c63

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Theorems.Thm_AutomorphicForm_RankinSelberg_lintegral_torus_pair_lt_top_of_ball_surgery
import Theorems.Thm_AutomorphicForm_RankinSelberg_whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
import Theorems.Thm_NumberField_Idele_exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty
import Theorems.Thm_AutomorphicForm_exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty
import Theorems.Thm_NumberField_Idele_measurePreserving_mul_right_sPartMeasure
import Theorems.Thm_NumberField_Idele_integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace P6E43

open Filter Topology

variable (K : Type) [Field K] [NumberField K]

scoped instance : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

scoped instance secondCountableTopology_maxCpt : SecondCountableTopology (adelicMaximalCompact K) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance secondCountableTopology_maxCpt0 : SecondCountableTopology (maximalCompactAt K ∅) :=
  TopologicalSpace.Subtype.secondCountableTopology _

scoped instance : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K

scoped instance secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 K) K)ˣ → AdelicGL2 (𝓞 K) K) := by
  have hval : Continuous fun u : (AdeleRing (𝓞 K) K)ˣ =>
      ((diagOne u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    change Continuous fun u : (AdeleRing (𝓞 K) K)ˣ => Matrix.diagonal ![(u : AdeleRing (𝓞 K) K), 1]
    refine (continuous_pi fun i => ?_).matrix_diagonal
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

scoped instance locallyCompactSpace_idele : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar K) := by
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  infer_instance

scoped instance sFinite_sPartMeasure (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SFinite (NumberField.Idele.sPartMeasure K S) := by
  unfold NumberField.Idele.sPartMeasure; infer_instance

variable {K}

theorem continuous_finMat : Continuous (AdelicDock.finMat (𝓞 K) K) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
    ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : (AdeleRing (𝓞 K) K)))
  exact continuous_const.prodMk ((continuous_apply j).comp (continuous_apply i))

theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 K) K) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      AdelicDock.finMat (𝓞 K) K (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    exact continuous_finMat.comp Units.continuous_val
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      AdelicDock.finMat (𝓞 K) K ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    exact continuous_finMat.comp Units.continuous_coe_inv

def kinf (g : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K := g * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K g))⁻¹

theorem continuous_kinf : Continuous (kinf (K := K)) :=
  continuous_id.mul ((continuous_finEmbed.comp (continuous_glFin (𝓞 K) K)).inv)

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K g = glArch (𝓞 K) K h)
    (h₂ : glFin (𝓞 K) K g = glFin (𝓞 K) K h) : g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h₁) i) j
    beta_reduce at this
    rwa [glArch_apply, glArch_apply] at this
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) h₂) i) j
    beta_reduce at this
    rwa [glFin_apply, glFin_apply] at this

theorem kinf_eq (g : AdelicGL2 (𝓞 K) K) : kinf g = adelicArchGLIncl K (glArch (𝓞 K) K g) := by
  refine gl_ext ?_ ?_
  · rw [kinf, map_mul, map_inv, AdelicDock.glArch_finEmbed, inv_one, mul_one, glArch_adelicArchGLIncl]
  · rw [kinf, map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel, glFin_adelicArchGLIncl]

theorem glFin_kinf (g : AdelicGL2 (𝓞 K) K) : glFin (𝓞 K) K (kinf g) = 1 := by
  rw [kinf, map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]

theorem glArch_kinf (g : AdelicGL2 (𝓞 K) K) : glArch (𝓞 K) K (kinf g) = glArch (𝓞 K) K g := by
  rw [kinf, map_mul, map_inv, AdelicDock.glArch_finEmbed, inv_one, mul_one]

theorem kinf_eq_self_of_glFin_eq_one {g : AdelicGL2 (𝓞 K) K} (hg : glFin (𝓞 K) K g = 1) : kinf g = g := by
  rw [kinf, hg, map_one, inv_one, mul_one]

theorem kinf_mul_of_glArch_eq_one (g k' : AdelicGL2 (𝓞 K) K) (hk' : glArch (𝓞 K) K k' = 1) : kinf (g * k') = kinf g := by
  rw [kinf_eq, kinf_eq, map_mul, hk', mul_one]

theorem glFin_eq_one_of_mem_maximalCompactAt_empty {g : AdelicGL2 (𝓞 K) K} (hg : g ∈ maximalCompactAt K ∅) :
    glFin (𝓞 K) K g = 1 := by
  have h := (mem_maximalCompactAt_iff.1 hg).2
  refine Matrix.GeneralLinearGroup.ext fun i j => RestrictedProduct.ext _ _ fun v => ?_
  have hv := congrArg (fun m : GL (Fin 2) (v.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j)
    (h v (Finset.notMem_empty v))
  beta_reduce at hv
  rw [finComponent_apply] at hv
  refine hv.trans ?_
  rw [Units.val_one, Units.val_one]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]; rfl

section Meas

theorem ae_partAt_eq (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ᵐ t ∂(NumberField.Idele.sPartMeasure K S), NumberField.Idele.partAt K S t = t := by
  have hmeas : MeasurableSet {t : (AdeleRing (𝓞 K) K)ˣ | NumberField.Idele.partAt K S t = t} :=
    (isClosed_eq (NumberField.Idele.continuous_partAt K S) continuous_id).measurableSet
  rw [ae_iff]
  have : {t : (AdeleRing (𝓞 K) K)ˣ | ¬ NumberField.Idele.partAt K S t = t} = {t | NumberField.Idele.partAt K S t = t}ᶜ := rfl
  rw [this, NumberField.Idele.sPartMeasure, Measure.map_apply (NumberField.Idele.measurable_partAt K S) hmeas.compl]
  have hpre : NumberField.Idele.partAt K S ⁻¹' {t : (AdeleRing (𝓞 K) K)ˣ | NumberField.Idele.partAt K S t = t}ᶜ = ∅ := by
    ext a
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]

    refine Units.ext (Prod.ext rfl (RestrictedProduct.ext _ _ fun v => ?_))
    by_cases hv : v ∈ S
    · exact NumberField.Idele.partAt_snd_of_mem K S _ hv
    · exact (NumberField.Idele.partAt_snd_of_not_mem K S _ hv).trans (NumberField.Idele.partAt_snd_of_not_mem K S a hv).symm
  rw [hpre, measure_empty]

theorem ae_snd_eq_one (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ᵐ t : (AdeleRing (𝓞 K) K)ˣ ∂(NumberField.Idele.sPartMeasure K S),
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (((t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by
  filter_upwards [ae_partAt_eq S] with t ht
  intro v hv
  rw [← ht]
  exact NumberField.Idele.partAt_snd_of_not_mem K S t hv

end Meas

section SNorm

theorem norm_eq_of_valued_eq {v : HeightOneSpectrum (𝓞 K)} {x y : v.adicCompletion K} (h : Valued.v x = Valued.v y) :
    ‖x‖ = ‖y‖ :=
  le_antisymm (Valued.toNormedField.norm_le_iff.mpr h.le) (Valued.toNormedField.norm_le_iff.mpr h.ge)

theorem ideleNorm_eq_prod_mul_finprod (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K t =
      (∏ pl : InfinitePlace K, ‖((t : AdeleRing (𝓞 K) K)).1 pl‖ ^ pl.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((t : AdeleRing (𝓞 K) K)).2 v‖ :=
  NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K t

def Qf (t : (AdeleRing (𝓞 K) K)ˣ) : ℝ := ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖((t : AdeleRing (𝓞 K) K)).2 v‖

theorem snd_ne_zero (t : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ((t : AdeleRing (𝓞 K) K)).2 v ≠ 0 :=
  (Valuation.ne_zero_iff _).mp (NumberField.Idele.valued_snd_ne_zero K v t)

theorem Qf_pos (t : (AdeleRing (𝓞 K) K)ˣ) : 0 < Qf t :=
  finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos) fun v => norm_pos_iff.mpr (snd_ne_zero t v)

theorem prod_archnorm_pos (t : (AdeleRing (𝓞 K) K)ˣ) : 0 < ∏ pl : InfinitePlace K, ‖((t : AdeleRing (𝓞 K) K)).1 pl‖ ^ pl.mult := by
  have h := NumberField.TateGlobal.ideleNorm_pos (F := K) t
  rw [ideleNorm_eq_prod_mul_finprod] at h
  exact pos_of_mul_pos_left h (Qf_pos t).le

theorem ideleNorm_partAt_empty (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K ∅ t) = ∏ pl : InfinitePlace K, ‖((t : AdeleRing (𝓞 K) K)).1 pl‖ ^ pl.mult := by
  rw [ideleNorm_eq_prod_mul_finprod]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((NumberField.Idele.partAt K ∅ t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    fun v => NumberField.Idele.partAt_snd_of_not_mem K ∅ t (Finset.notMem_empty v)
  simp_rw [h2, norm_one, finprod_one, mul_one]
  rfl

theorem ideleNorm_eq_partAt_mul_Qf (t : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K t = NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K ∅ t) * Qf t := by
  rw [ideleNorm_partAt_empty, ideleNorm_eq_prod_mul_finprod]; rfl

theorem Qf_eq_prod_of_partAt_eq (S : Finset (HeightOneSpectrum (𝓞 K))) {t : (AdeleRing (𝓞 K) K)ˣ}
    (hmem : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1) :
    Qf t = ∏ v ∈ S, ‖((t : AdeleRing (𝓞 K) K)).2 v‖ := by
  classical
  unfold Qf
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvS
  exact hv (show (fun v => ‖((t : AdeleRing (𝓞 K) K)).2 v‖) v = 1 by simp only [hmem v (by simpa using hvS), norm_one])

theorem fst_ne_zero (t : (AdeleRing (𝓞 K) K)ˣ) (pl : InfinitePlace K) : ((t : AdeleRing (𝓞 K) K)).1 pl ≠ 0 := by
  intro h0
  have h : (((t : AdeleRing (𝓞 K) K)) * ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl = 1 := by rw [t.mul_inv]; rfl
  rw [show (((t : AdeleRing (𝓞 K) K)) * ((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl =
      ((t : AdeleRing (𝓞 K) K)).1 pl * (((t⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl from rfl, h0, zero_mul] at h
  exact zero_ne_one h

theorem partAt_empty_snd (t : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((NumberField.Idele.partAt K ∅ t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
  NumberField.Idele.partAt_snd_of_not_mem K ∅ t (Finset.notMem_empty v)

theorem partAt_empty_snd' (t : (AdeleRing (𝓞 K) K)ˣ) : ((NumberField.Idele.partAt K ∅ t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 :=
  RestrictedProduct.ext _ _ fun v => partAt_empty_snd t v

theorem partAt_empty_mul_of_fst_eq_one (t ρ : (AdeleRing (𝓞 K) K)ˣ) (hρ : ((ρ : AdeleRing (𝓞 K) K)).1 = 1) :
    NumberField.Idele.partAt K ∅ (t * ρ) = NumberField.Idele.partAt K ∅ t := by
  rw [map_mul]
  suffices h : NumberField.Idele.partAt K ∅ ρ = 1 by rw [h, mul_one]
  apply Units.ext
  refine Prod.ext ?_ (RestrictedProduct.ext _ _ fun v => ?_)
  · rw [NumberField.Idele.partAt_fst]; exact hρ
  · exact partAt_empty_snd ρ v

theorem ideleNorm_eq_one_of_fst_eq_one_of_norm_snd (ρ : (AdeleRing (𝓞 K) K)ˣ) (hρ : ((ρ : AdeleRing (𝓞 K) K)).1 = 1)
    (hρv : ∀ v : HeightOneSpectrum (𝓞 K), ‖((ρ : AdeleRing (𝓞 K) K)).2 v‖ = 1) :
    NumberField.TateGlobal.ideleNorm K ρ = 1 := by
  rw [ideleNorm_eq_prod_mul_finprod]
  have h1 : ∀ pl : InfinitePlace K, ‖((ρ : AdeleRing (𝓞 K) K)).1 pl‖ ^ pl.mult = 1 := fun pl => by
    rw [hρ]
    show ‖(1 : pl.Completion)‖ ^ pl.mult = 1
    rw [norm_one, one_pow]
  simp_rw [h1, hρv, finprod_one, Finset.prod_const_one, one_mul]

theorem ideleNorm_eq_mul_of_ball (S : Finset (HeightOneSpectrum (𝓞 K))) (nb : ℕ) (hnb : 0 < nb) (t t₀ : (AdeleRing (𝓞 K) K)ˣ)
    (ht : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
    (ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
    (hball : (∀ v ∈ S, Valued.v ((((t) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))) :
    NumberField.TateGlobal.ideleNorm K t = NumberField.TateGlobal.ideleNorm K t₀ * NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K ∅ t) := by
  have hval : ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) := by
    intro v hv
    have h0 : Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≠ 0 := (Valuation.ne_zero_iff _).mpr (snd_ne_zero t₀ v)
    have hlt1 : ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    have hlt : Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) <
        Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) :=
      (hball v hv).trans_lt (mul_lt_of_lt_one_right (zero_lt_iff.mpr h0) hlt1)
    have := Valuation.map_add_eq_of_lt_left (v := Valued.v) hlt
    rwa [add_sub_cancel] at this
  have hQ : Qf t = Qf t₀ := by
    rw [Qf_eq_prod_of_partAt_eq S ht, Qf_eq_prod_of_partAt_eq S ht₀]
    exact Finset.prod_congr rfl fun v hv => norm_eq_of_valued_eq (hval v hv)
  have h0 : NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K ∅ t₀) = 1 := by
    rw [ideleNorm_partAt_empty, ht₀inf]
    exact Finset.prod_eq_one fun pl _ => by
      show ‖(1 : pl.Completion)‖ ^ pl.mult = 1
      rw [norm_one, one_pow]
  rw [ideleNorm_eq_partAt_mul_Qf t, hQ, mul_comm, ideleNorm_eq_partAt_mul_Qf t₀, h0, one_mul]

end SNorm

namespace P6ENV

open NumberField.Idele Set

variable {K : Type} [Field K] [NumberField K]

theorem fst_apply_ne_zero (a : (AdeleRing (𝓞 K) K)ˣ) (pl : InfinitePlace K) : ((a : AdeleRing (𝓞 K) K)).1 pl ≠ 0 := by
  intro h
  have h1 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl = 1 := by rw [mul_inv_cancel]; rfl
  have : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl =
      ((a : AdeleRing (𝓞 K) K)).1 pl * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 pl := rfl
  rw [this, h, zero_mul] at h1
  exact zero_ne_one h1

theorem continuous_norm_fst_apply (pl : InfinitePlace K) :
    Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ :=
  continuous_norm.comp (((continuous_apply pl).comp continuous_fst).comp Units.continuous_val)

theorem measurable_rpow_norm_fst (pl : InfinitePlace K) (e : ℝ) :
    Measurable fun a : (AdeleRing (𝓞 K) K)ˣ => ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ e :=
  (continuous_norm_fst_apply pl).measurable.pow_const e

theorem measurable_ideleNorm_rpow (e : ℝ) :
    Measurable fun a : (AdeleRing (𝓞 K) K)ˣ => NumberField.TateGlobal.ideleNorm K a ^ e :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable.pow_const e

theorem exists_envelope
    (S : Finset (HeightOneSpectrum (𝓞 K))) (D₀ : Set (AdelicGL2 (𝓞 K) K)) (w : ℝ) (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (κ : AdelicGL2 (𝓞 K) K) (y : AdelicGL2 (𝓞 K) K → ℂ)
    (Cx δx Cy δy : ℝ) (hδx : 0 < δx) (hδy : 0 < δy)
    (hCx : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
            Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
    (hCy : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * (diagOne t₀))‖ ≤
            Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy))
    (hxlarge' : ∀ M : ℕ, ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
            Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))
    (s : ℂ) (hs : 1 / 2 - (δx + δy) / 2 < s.re) :
    ∃ env : (AdeleRing (𝓞 K) K)ˣ → ℝ, Integrable env (NumberField.Idele.sPartMeasure K ∅) ∧
      ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K g))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * g * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * g * diagOne t₀)))‖ ≤ env a := by
  classical
  set σ : ℝ := s.re with hσ
  set cc : ℝ := σ - 1 / 2 with hcc
  have hN0 : ∀ a : (AdeleRing (𝓞 K) K)ˣ, 0 < NumberField.TateGlobal.ideleNorm K a := fun a => NumberField.TateGlobal.ideleNorm_pos a
  have hadm_one : glFin (𝓞 K) K (1 : AdelicGL2 (𝓞 K) K) = 1 ∧
      ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (1 : AdelicGL2 (𝓞 K) K))) :=
    ⟨map_one _, ((mem_adelicMaximalCompact_iff (K := K)).1 (one_mem _)).2⟩
  choose CxM hCxM using hxlarge'

  set Px : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun a => ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
    (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx) with hPx
  set Py : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun a => ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
    (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy) with hPy
  set Lx : ℕ × InfinitePlace K → (AdeleRing (𝓞 K) K)ˣ → ℝ := fun p a =>
    CxM p.1 * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 p.2‖ ^ (-(p.1 : ℝ)) with hLx
  set Ex : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun a => ENNReal.ofReal (Cx * Px a) ⊓ ⨅ p : ℕ × InfinitePlace K, ENNReal.ofReal (Lx p a)
    with hEx
  set Ey : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞ := fun a => ENNReal.ofReal (Cy * Py a) with hEy
  have hPmeas : ∀ δ : ℝ, Measurable fun a : (AdeleRing (𝓞 K) K)ˣ => ∏ pl : InfinitePlace K,
      (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ) := by
    intro δ
    refine Finset.measurable_prod _ fun pl _ => ?_
    exact (measurable_rpow_norm_fst pl _).mul ((measurable_const.min (continuous_norm_fst_apply pl).measurable).pow_const δ)
  have hExm : Measurable Ex := by
    refine (Measurable.ennreal_ofReal (measurable_const.mul (hPmeas δx))).inf (Measurable.iInf fun p => ?_)
    exact Measurable.ennreal_ofReal ((measurable_const.mul (measurable_ideleNorm_rpow _)).mul (measurable_rpow_norm_fst _ _))
  have hEym : Measurable Ey := Measurable.ennreal_ofReal (measurable_const.mul (hPmeas δy))
  have hExdom : ∀ kk : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K kk = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K kk))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * kk * (diagOne t₀ * κ))‖ₑ ≤ Ex a := by
    intro kk hk1 hk2 a ha
    rw [← ofReal_norm_eq_enorm]
    refine le_inf (ENNReal.ofReal_le_ofReal (hCx kk hk1 hk2 a ha)) (le_iInf fun p => ENNReal.ofReal_le_ofReal ?_)
    exact hCxM p.1 kk hk1 hk2 a ha p.2
  have hEydom : ∀ kk : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K kk = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K kk))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * kk * (diagOne t₀))‖ₑ ≤ Ey a := by
    intro kk hk1 hk2 a ha
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hCy kk hk1 hk2 a ha)
  have hExfin : ∀ a, Ex a ≠ ⊤ := fun a => ne_top_of_le_ne_top ENNReal.ofReal_ne_top inf_le_left
  have hEyfin : ∀ a, Ey a ≠ ⊤ := fun a => ENNReal.ofReal_ne_top
  have hPpos : ∀ (δ : ℝ) (a : (AdeleRing (𝓞 K) K)ˣ), 0 < ∏ pl : InfinitePlace K,
      (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ) := by
    intro δ a
    refine Finset.prod_pos fun pl _ => mul_pos (Real.rpow_pos_of_pos ?_ _) (Real.rpow_pos_of_pos (lt_min one_pos ?_) _) <;>
      exact norm_pos_iff.2 (fst_apply_ne_zero a pl)
  have hCx0 : 0 ≤ Cx := by
    have h := hCx 1 hadm_one.1 hadm_one.2 1 rfl
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (hPpos δx 1)
  have hCy0 : 0 ≤ Cy := by
    have h := hCy 1 hadm_one.1 hadm_one.2 1 rfl
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (hPpos δy 1)
  have hLx0 : ∀ (p : ℕ × InfinitePlace K) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 → 0 ≤ Lx p a :=
    fun p a ha => (norm_nonneg _).trans (hCxM p.1 1 hadm_one.1 hadm_one.2 a ha p.2)

  set F : (AdeleRing (𝓞 K) K)ˣ → ℝ := fun a => NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * (Ex a).toReal * (Ey a).toReal
    with hF
  have hFm : Measurable F :=
    ((measurable_ideleNorm_rpow _).mul (ENNReal.measurable_toReal.comp hExm)).mul (ENNReal.measurable_toReal.comp hEym)
  have hF0 : ∀ a, 0 ≤ F a := fun a => mul_nonneg (mul_nonneg (Real.rpow_nonneg (hN0 a).le _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
  have hnormF : ∀ a, ‖F a‖ = F a := fun a => Real.norm_of_nonneg (hF0 a)
  have hprodN : ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ ex : ℝ,
      ∏ pl : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * ex) = NumberField.TateGlobal.ideleNorm K a ^ ex := by
    intro a ha ex
    rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K a ha,
      ← Real.finset_prod_rpow _ _ (fun pl _ => pow_nonneg (norm_nonneg _) _)]
    refine Finset.prod_congr rfl fun pl _ => ?_
    rw [Real.rpow_natCast_mul (norm_nonneg _)]
  have hPsplit : ∀ (δ : ℝ) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ) =
        NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ := by
    intro δ a ha
    rw [Finset.prod_mul_distrib, ← hprodN a ha (w / 2)]
    congr 1
    exact Finset.prod_congr rfl fun pl _ => by rw [mul_div_assoc]
  have hminle : ∀ (δ : ℝ), 0 ≤ δ → ∀ a : (AdeleRing (𝓞 K) K)ˣ, ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ ≤ 1 :=
    fun δ hδ a => Finset.prod_le_one (fun pl _ => Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _)
      fun pl _ => Real.rpow_le_one (le_min zero_le_one (norm_nonneg _)) (min_le_left _ _) hδ
  have hsmall : ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ‖F a‖ ≤ (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ cc *
        ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) := by
    intro a ha
    rw [hnormF]
    have hx : (Ex a).toReal ≤ Cx * Px a :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCx0 (hPpos δx a).le) inf_le_left
    have hy : (Ey a).toReal ≤ Cy * Py a := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCy0 (hPpos δy a).le) le_rfl
    have hNp := hN0 a
    calc F a ≤ NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * (Cx * Px a) * (Cy * Py a) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hNp.le _)) hy ENNReal.toReal_nonneg
            (mul_nonneg (Real.rpow_nonneg hNp.le _) (mul_nonneg hCx0 (hPpos δx a).le))
      _ = (Cx * Cy) * NumberField.TateGlobal.ideleNorm K a ^ cc *
            ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) := by
          rw [hPx, hPy]
          simp only []
          rw [hPsplit δx a ha, hPsplit δy a ha]
          have hmin : ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ (δx + δy) =
              (∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx) *
                ∏ pl : InfinitePlace K, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy := by
            rw [← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun pl _ => ?_
            rw [Real.rpow_add (lt_min one_pos (norm_pos_iff.2 (fst_apply_ne_zero a pl)))]
          rw [hmin]
          have hNN : NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
              NumberField.TateGlobal.ideleNorm K a ^ (w / 2) = NumberField.TateGlobal.ideleNorm K a ^ cc := by
            rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; ring_nf
          calc NumberField.TateGlobal.ideleNorm K a ^ (cc - w) *
                (Cx * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx)) *
                (Cy * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy))
              = (Cx * Cy) * (NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
                  NumberField.TateGlobal.ideleNorm K a ^ (w / 2)) *
                  ((∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy) := by
                ring
            _ = _ := by rw [hNN]
  have hlarge : ∀ M : ℕ, ∃ B : ℝ, ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      ∀ pl : InfinitePlace K,
        ‖F a‖ ≤ B * NumberField.TateGlobal.ideleNorm K a ^ cc * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by
    intro M
    refine ⟨CxM M * Cy, fun a ha pl => ?_⟩
    rw [hnormF]
    have hNp := hN0 a
    have hx : (Ex a).toReal ≤ Lx (M, pl) a :=
      ENNReal.toReal_le_of_le_ofReal (hLx0 (M, pl) a ha) (inf_le_right.trans (iInf_le _ (M, pl)))
    have hy : (Ey a).toReal ≤ Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) := by
      refine (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCy0 (hPpos δy a).le) le_rfl).trans ?_
      show Cy * Py a ≤ _
      rw [hPy]; simp only []
      rw [hPsplit δy a ha]
      calc Cy * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ∏ pl, (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy)
          ≤ Cy * (NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hminle δy hδy.le a) (Real.rpow_nonneg hNp.le _)) hCy0
        _ = Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) := by rw [mul_one]
    calc F a ≤ NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * Lx (M, pl) a * (Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hNp.le _)) hy ENNReal.toReal_nonneg
            (mul_nonneg (Real.rpow_nonneg hNp.le _) (hLx0 (M, pl) a ha))
      _ = CxM M * Cy * NumberField.TateGlobal.ideleNorm K a ^ cc * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by
          rw [hLx]; simp only []
          have hNN : NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
              NumberField.TateGlobal.ideleNorm K a ^ (w / 2) = NumberField.TateGlobal.ideleNorm K a ^ cc := by
            rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; ring_nf
          calc NumberField.TateGlobal.ideleNorm K a ^ (cc - w) *
                (CxM M * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))) *
                (Cy * NumberField.TateGlobal.ideleNorm K a ^ (w / 2))
              = CxM M * Cy * (NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) *
                  NumberField.TateGlobal.ideleNorm K a ^ (w / 2)) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)) := by ring
            _ = _ := by rw [hNN]
  have hδc : 0 < (δx + δy) + cc := by rw [hcc]; linarith
  have hδc₂ : 0 < (δx + δy) + 2 * cc := by rw [hcc]; linarith
  have hint : Integrable F (NumberField.Idele.sPartMeasure K ∅) :=
    NumberField.Idele.integrable_sPartMeasure_empty_of_norm_le_ideleNorm_rpow_mul_prod_min_one_rpow_of_norm_le_rpow_neg K F
      hFm.aestronglyMeasurable (δx + δy) cc (Cx * Cy) hδc hδc₂ hsmall hlarge

  refine ⟨F, hint, fun g hg1 hg2 a ha => ?_⟩
  have hNp := hN0 a
  have h1 : ‖((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2)‖ = NumberField.TateGlobal.ideleNorm K a ^ (σ + 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNp]; simp [hσ]
  have h2 : ‖((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hNp.le _)]
  have hx : ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * g * (diagOne t₀ * κ))‖ ≤ (Ex a).toReal := by
    have h := hExdom g hg1 hg2 a ha
    rw [← ofReal_norm_eq_enorm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal (hExfin a)).1 h
  have hy : ‖(starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * g * diagOne t₀))‖ ≤ (Ey a).toReal := by
    rw [Complex.norm_conj]
    have h := hEydom g hg1 hg2 a ha
    rw [← ofReal_norm_eq_enorm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal (hEyfin a)).1 h
  have hpow : NumberField.TateGlobal.ideleNorm K a ^ (σ + 1 / 2) * NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) =
      NumberField.TateGlobal.ideleNorm K a ^ (cc - w) := by
    rw [← Real.rpow_add hNp, hcc]; ring_nf
  rw [norm_mul, norm_mul, norm_mul, h1, h2, hpow, hF]
  simp only []
  calc NumberField.TateGlobal.ideleNorm K a ^ (cc - w) *
        (‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * g * (diagOne t₀ * κ))‖ *
          ‖(starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * g * diagOne t₀))‖)
      ≤ NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * ((Ex a).toReal * (Ey a).toReal) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hx hy (norm_nonneg _) ENNReal.toReal_nonneg) (Real.rpow_nonneg hNp.le _)
    _ = NumberField.TateGlobal.ideleNorm K a ^ (cc - w) * (Ex a).toReal * (Ey a).toReal := by ring

end P6ENV

theorem integral_ite_bottomRow_mul_eq
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (κ₃ : ℝ)
    (hP3 : ∀ F : AdelicGL2 (𝓞 K) K → ℂ,
        AEStronglyMeasurable (fun k : ↥(adelicMaximalCompact K) => F k) (maximalCompactHaar K) →
        AEStronglyMeasurable (fun k : ↥(maximalCompactAt K ∅) => F k) (maximalCompactAtHaar K ∅) →
        (∃ B : ℝ, ∀ k, ‖F k‖ ≤ B) →
        (∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k) →
        (∫ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) ∂(maximalCompactHaar K)) =
          (κ₃ : ℂ) * ∫ k, F k ∂(maximalCompactAtHaar K ∅))
    (B : AdelicGL2 (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ → ℂ) (hBc : Continuous (Function.uncurry B))
    (hBint : ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = 1 → (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (g)))) →
      Integrable (B g) (NumberField.Idele.sPartMeasure K ∅))
    (IΛ : ℝ) (hΛbd : ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = 1 → (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (g)))) →
      ‖∫ a, B g a ∂(NumberField.Idele.sPartMeasure K ∅)‖ ≤ IΛ)
    (finf : AdelicGL2 (𝓞 K) K → ℂ) (hfc : Continuous finf) :
    (∫ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then
            finf (kinf (k : AdelicGL2 (𝓞 K) K)) * ∫ a, B (kinf (k : AdelicGL2 (𝓞 K) K)) a ∂(NumberField.Idele.sPartMeasure K ∅) else 0)
        ∂(maximalCompactHaar K)) =
      (κ₃ : ℂ) * ∫ k, finf (k : AdelicGL2 (𝓞 K) K) * (∫ a, B (k : AdelicGL2 (𝓞 K) K) a ∂(NumberField.Idele.sPartMeasure K ∅))
        ∂(maximalCompactAtHaar K ∅) := by
  classical

  set Λ : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∫ a, B g a ∂(NumberField.Idele.sPartMeasure K ∅) with hΛ
  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
    if (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K g))) then finf (kinf g) * Λ (kinf g) else 0
    with hF

  have hkinfK : ∀ g : AdelicGL2 (𝓞 K) K, (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K g))) →
      kinf g ∈ maximalCompactAt K ∅ := by
    intro g hg
    rw [mem_maximalCompactAt_iff]
    refine ⟨(mem_adelicMaximalCompact_iff (K := K)).2 ⟨?_, fun pl => ?_⟩, fun v _ => ?_⟩
    · rw [glFin_kinf]; exact one_mem _
    · rw [glArch_kinf]; exact hg pl
    · rw [glFin_kinf, map_one]
  have hrowK : ∀ k : AdelicGL2 (𝓞 K) K, k ∈ adelicMaximalCompact K →
      ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k)) :=
    fun k hk => ((mem_adelicMaximalCompact_iff (K := K)).1 hk).2
  have hFK : ∀ k : AdelicGL2 (𝓞 K) K, k ∈ adelicMaximalCompact K → F k = finf (kinf k) * Λ (kinf k) :=
    fun k hk => by rw [hF]; exact if_pos (hrowK k hk)
  have hFzero : ∀ k : AdelicGL2 (𝓞 K) K, k ∈ maximalCompactAt K ∅ → F k = finf k * Λ k := by
    intro k hk
    obtain ⟨hkK, hfin⟩ := (mem_maximalCompactAt_iff (K := K) (S := ∅)).1 hk
    have hg1 : glFin (𝓞 K) K k = 1 := by
      ext i j v
      have := hfin v (Finset.notMem_empty v)
      have h := congrArg (fun M : GL (Fin 2) (v.adicCompletion K) => (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) this
      simp only [finComponent_apply, Units.val_one] at h
      rw [Units.val_one]
      have h1 : ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
        rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      exact h.trans h1.symm
    rw [hFK k hkK, kinf_eq_self_of_glFin_eq_one hg1]

  obtain ⟨Cf, hCf⟩ := (isCompact_maximalCompactAt K ∅).exists_bound_of_continuousOn hfc.continuousOn
  have hbound : ∃ Bd : ℝ, ∀ g, ‖F g‖ ≤ Bd := by
    refine ⟨max Cf 0 * max IΛ 0, fun g => ?_⟩
    rw [hF]; simp only []
    split_ifs with hg
    · rw [norm_mul]
      refine mul_le_mul ((hCf _ (hkinfK g hg)).trans (le_max_left _ _)) ?_ (norm_nonneg _) (le_max_right _ _)
      exact (hΛbd (kinf g) (glFin_kinf g) (by intro pl; rw [glArch_kinf]; exact hg pl)).trans (le_max_left _ _)
    · rw [norm_zero]; exact mul_nonneg (le_max_right _ _) (le_max_right _ _)

  have hinv : ∀ k k' : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K k' = 1 → F (k * k') = F k := by
    intro k k' hk'
    rw [hF]; simp only []
    rw [map_mul, hk', mul_one, kinf_mul_of_glArch_eq_one k k' hk']

  have hBm : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
      (ι : X → AdelicGL2 (𝓞 K) K), Continuous ι →
      StronglyMeasurable (fun p : X × (AdeleRing (𝓞 K) K)ˣ => B (kinf (ι p.1)) p.2) := by
    intro X _ _ _ _ ι hι
    have hc : Continuous (fun p : X × (AdeleRing (𝓞 K) K)ˣ => B (kinf (ι p.1)) p.2) :=
      hBc.comp ((continuous_kinf.comp (hι.comp continuous_fst)).prodMk continuous_snd)
    exact hc.stronglyMeasurable
  have hΛm : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
      (ι : X → AdelicGL2 (𝓞 K) K), Continuous ι → StronglyMeasurable (fun x : X => Λ (kinf (ι x))) := by
    intro X _ _ _ _ ι hι
    have h := (hBm ι hι).integral_prod_right' (ν := NumberField.Idele.sPartMeasure K ∅)
    exact h
  have hm1 : AEStronglyMeasurable (fun k : ↥(adelicMaximalCompact K) => F k) (maximalCompactHaar K) := by
    have hfun : (fun k : ↥(adelicMaximalCompact K) => F k) =
        fun k : ↥(adelicMaximalCompact K) => finf (kinf (k : AdelicGL2 (𝓞 K) K)) * Λ (kinf (k : AdelicGL2 (𝓞 K) K)) := by
      funext k; exact hFK k k.property
    rw [hfun]
    refine ((hfc.comp (continuous_kinf.comp continuous_subtype_val)).stronglyMeasurable.mul
      (hΛm (fun k : ↥(adelicMaximalCompact K) => (k : AdelicGL2 (𝓞 K) K)) continuous_subtype_val)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun k : ↥(maximalCompactAt K ∅) => F k) (maximalCompactAtHaar K ∅) := by
    have hfun : (fun k : ↥(maximalCompactAt K ∅) => F k) =
        fun k : ↥(maximalCompactAt K ∅) => finf (kinf (k : AdelicGL2 (𝓞 K) K)) * Λ (kinf (k : AdelicGL2 (𝓞 K) K)) := by
      funext k; exact hFK k (maximalCompactAt_le K ∅ k.property)
    rw [hfun]
    refine ((hfc.comp (continuous_kinf.comp continuous_subtype_val)).stronglyMeasurable.mul
      (hΛm (fun k : ↥(maximalCompactAt K ∅) => (k : AdelicGL2 (𝓞 K) K)) continuous_subtype_val)).aestronglyMeasurable

  have hmain := hP3 F hm1 hm2 hbound hinv
  have hL : (fun k : ↥(adelicMaximalCompact K) =>
      (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
          Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
            ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then
        finf (kinf (k : AdelicGL2 (𝓞 K) K)) * ∫ a, B (kinf (k : AdelicGL2 (𝓞 K) K)) a ∂(NumberField.Idele.sPartMeasure K ∅) else 0)) =
      fun k : ↥(adelicMaximalCompact K) => (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
          Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
            ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then F k else 0) := by
    funext k
    rw [hFK k k.property]
  have hR : (fun k : ↥(maximalCompactAt K ∅) => finf (k : AdelicGL2 (𝓞 K) K) *
      (∫ a, B (k : AdelicGL2 (𝓞 K) K) a ∂(NumberField.Idele.sPartMeasure K ∅))) = fun k : ↥(maximalCompactAt K ∅) => F k := by
    funext k
    rw [hFzero k k.property]
  rw [hL, hR]
  exact hmain

theorem main
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))

      (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (_hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hx₀c : Continuous x₀)
      (nb : ℕ) (_hnb : 0 < nb)
      (_hx₀cong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x₀ (g * k) = x₀ g)
      (_hxlarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
      (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (m : ℕ)
      (_ht₀box : ∀ v ∈ S, Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
        ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))

      (r : ℕ) (u : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ)
      (_husupp : ∀ i, (u i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (u i).2 v = 0)
      (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (u i) = unipotentGL2 (u i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (u i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
      (_hμball : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
      (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (u i) * κ)))
      (_hxc : Continuous x)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (y : AdelicGL2 (𝓞 K) K → ℂ) (_hyc : Continuous y)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (_hyKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, y (g * k) = y g)
      (_hycong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * k) = y g)
      (_hylow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * lowerUnipotentGL2 γ) = y g)
      (_hylarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (_hφval : ∀ (s : ℂ) (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf)

      (δx Cx : ℝ) (_hδx : 0 < δx)
      (_hCx : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
            Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
      (δy Cy : ℝ) (_hδy : 0 < δy)
      (_hCy : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * (diagOne t₀))‖ ≤
            Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy)),
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ s : ℂ, 1 / 2 - (δx + δy) / 2 < s.re →
      (∫ t, ∫ k,
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
              φ s (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) =
        (κ₀ : ℂ) * (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) *
            ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) *
          ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅) := by
  classical
  intro α hα S D₀ ωx ωy w hωx hωy ν hων x₀ hx₀c nb hnb hx₀cong hxlarge t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan x hxsum hxc hxG hxZ hxKS n hn hxlow y hyc hyG hyZ hyKS hycong hylow hylarge finf hfc φ hφ hφjc hφKS hφsupp hφval δx Cx hδx hCx δy Cy hδy hCy

  have hP5 := AutomorphicForm.RankinSelberg.lintegral_torus_pair_lt_top_of_ball_surgery K hα S D₀ ωx ωy w hωx hωy ν hων x₀ nb hnb hx₀cong hxlarge t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan x hxsum hxG hxZ hxKS n hn hxlow y hyG hyZ hyKS hycong hylow hylarge finf φ hφ hφjc hφKS hφsupp hφval δx Cx hδx hCx δy Cy hδy hCy
  have hP4 := fun (s : ℂ) (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K) =>
    AutomorphicForm.RankinSelberg.whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery K hα S D₀ ωx ωy w ν hων x₀ nb hnb hx₀cong t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan x hxsum hxG hxZ hxKS n hn hxlow y hyG hyZ hyKS hycong hylow finf φ hφ hφKS hφsupp hφval s k hk
  obtain ⟨κ₂, hκ₂pos, -, hP2⟩ := NumberField.Idele.exists_lintegral_ite_ball_comp_partAt_sPartMeasure_eq_mul_lintegral_sPartMeasure_empty K S t₀ ht₀ nb hnb
  obtain ⟨κ₃, hκ₃pos, -, hP3⟩ := AutomorphicForm.exists_lintegral_ite_bottomRow_maximalCompactHaar_eq_mul_lintegral_maximalCompactAtHaar_empty K S n
  refine ⟨κ₂ * κ₃, mul_pos hκ₂pos hκ₃pos, fun s hs => ?_⟩

  have hψc : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous
  have hWc : ∀ (θ : AdelicGL2 (𝓞 K) K → ℂ), Continuous θ → Continuous (fun g : AdelicGL2 (𝓞 K) K => whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) θ 1
          (g)) :=
    fun θ hθ => AutomorphicForm.continuous_whittakerCoefficient K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K) hψc θ hθ 1
  have hnpos : ∀ t : (AdeleRing (𝓞 K) K)ˣ, 0 < NumberField.TateGlobal.ideleNorm K t := fun t => NumberField.TateGlobal.ideleNorm_pos t
  have hcpowc : ∀ z : ℂ, Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ z := fun z =>
    Continuous.cpow (Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm K)) continuous_const
      fun t => Or.inl (by simpa using hnpos t)
  have hrpowc : ∀ r : ℝ, Continuous fun t : (AdeleRing (𝓞 K) K)ˣ => ((NumberField.TateGlobal.ideleNorm K t ^ r : ℝ) : ℂ) := fun r =>
    Complex.continuous_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm K).rpow_const fun t => Or.inl (hnpos t).ne')
  have hglArchg₀ : glArch (𝓞 K) K (diagOne t₀ * κ) = 1 := by
    rw [map_mul, hκ, AdelicDock.glArch_finEmbed, mul_one]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glArch_apply, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [diagOne_coe_apply, ht₀inf] <;> rfl

  set μK : Measure (adelicMaximalCompact K) := maximalCompactHaar K with hμK
  set μ0 : Measure (maximalCompactAt K ∅) := maximalCompactAtHaar K ∅ with hμ0
  set νS : Measure (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.sPartMeasure K S with hνS
  set ν0 : Measure (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.sPartMeasure K ∅ with hν0
  set Fn : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K → ℂ := fun p =>
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
      (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
      φ s (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) *
      ((NumberField.TateGlobal.ideleNorm K p.1 ^ (-w - 1) : ℝ) : ℂ) with hFn

  have hdk : Continuous fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K => diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K) :=
    ((continuous_diagOne K).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hφc : Continuous (φ s) := hφjc.comp (Continuous.prodMk continuous_const continuous_id)
  have hFnc : Continuous Fn := by
    exact ((((hWc x hxc).comp hdk).mul (Complex.continuous_conj.comp ((hWc y hyc).comp hdk))).mul (hφc.comp hdk)).mul
      ((hrpowc (-w - 1)).comp continuous_fst)
  have hBc : Continuous fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ => (((NumberField.TateGlobal.ideleNorm K p.2 : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K p.2 ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne p.2 * p.1 * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne p.2 * p.1 * diagOne t₀)))) := by
    have h1 : Continuous fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ => diagOne p.2 * p.1 * (diagOne t₀ * κ) :=
      (((continuous_diagOne K).comp continuous_snd).mul continuous_fst).mul continuous_const
    have h2 : Continuous fun p : AdelicGL2 (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ => diagOne p.2 * p.1 * diagOne t₀ :=
      (((continuous_diagOne K).comp continuous_snd).mul continuous_fst).mul continuous_const
    exact (((hcpowc (s + 1 / 2)).comp continuous_snd).mul ((hrpowc (-w - 1)).comp continuous_snd)).mul
      (((hWc x₀ hx₀c).comp h1).mul (Complex.continuous_conj.comp ((hWc y hyc).comp h2)))
  have hBgc : ∀ g : AdelicGL2 (𝓞 K) K, Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * g * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * g * diagOne t₀)))) := fun g => by
    have h1 : Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => diagOne a * g * (diagOne t₀ * κ) :=
      ((continuous_diagOne K).mul continuous_const).mul continuous_const
    have h2 : Continuous fun a : (AdeleRing (𝓞 K) K)ˣ => diagOne a * g * diagOne t₀ :=
      ((continuous_diagOne K).mul continuous_const).mul continuous_const
    exact ((hcpowc (s + 1 / 2)).mul (hrpowc (-w - 1))).mul
      (((hWc x₀ hx₀c).comp h1).mul (Complex.continuous_conj.comp ((hWc y hyc).comp h2)))

  obtain ⟨env, henv_int, hdom⟩ := P6ENV.exists_envelope S D₀ w x₀ t₀ κ y Cx δx Cy δy hδx hδy hCx hCy
    (fun M : ℕ => hxlarge (diagOne t₀ * κ) hglArchg₀ M) s hs
  have hB_int : ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = 1 → (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (g)))) → Integrable (fun a : (AdeleRing (𝓞 K) K)ˣ => (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * g * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * g * diagOne t₀))))) ν0 := by
    intro g hg1 hgiso
    refine henv_int.mono' (hBgc g).aestronglyMeasurable ?_
    filter_upwards [ae_snd_eq_one (K := K) ∅] with a ha
    exact hdom g hg1 hgiso a (RestrictedProduct.ext _ _ fun v => ha v (Finset.notMem_empty v))
  have hΛbd : ∀ g : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K g = 1 → (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (g)))) → ‖(∫ a, (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * g * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * g * diagOne t₀)))) ∂ν0)‖ ≤ ∫ a, env a ∂ν0 := by
    intro g hg1 hgiso
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae (hB_int g hg1 hgiso).norm henv_int ?_)
    filter_upwards [ae_snd_eq_one (K := K) ∅] with a ha
    exact hdom g hg1 hgiso a (RestrictedProduct.ext _ _ fun v => ha v (Finset.notMem_empty v))

  have hFint : Integrable Fn (νS.prod μK) := by
    refine ⟨hFnc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFnc.measurable.enorm.aemeasurable]
    refine lt_of_le_of_lt (le_of_eq ?_) (hP5 s hs)
    refine lintegral_congr fun t => lintegral_congr fun k => ?_
    simp only [hFn, enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hnpos _).le _)]
  have hswap : (∫ t, ∫ k, Fn (t, k) ∂μK ∂νS) = ∫ k, ∫ t, Fn (t, k) ∂νS ∂μK := by
    rw [← MeasureTheory.integral_prod _ hFint, MeasureTheory.integral_prod_symm _ hFint]

  have hinner : ∀ k : adelicMaximalCompact K, (∫ t, Fn (t, k) ∂νS) =
      (κ₂ : ℂ) * (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) * (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then finf (kinf (k : AdelicGL2 (𝓞 K) K)) * (∫ a, (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))) ∂ν0) else 0) := by
    intro k
    have hrowk : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (kinf (k : AdelicGL2 (𝓞 K) K)))) := fun pl => by
      rw [glArch_kinf]; exact (mem_adelicMaximalCompact_iff.mp k.2).2 pl
    obtain ⟨ρ, hρ1, hρS, hρu, hpt⟩ := hP4 s k k.2
    have hρnorm : NumberField.TateGlobal.ideleNorm K ρ = 1 := by
      refine ideleNorm_eq_one_of_fst_eq_one_of_norm_snd ρ hρ1 fun v => ?_
      by_cases hv : v ∈ S
      · have h := norm_eq_of_valued_eq (K := K) (x := ((ρ : AdeleRing (𝓞 K) K)).2 v) (y := (1 : v.adicCompletion K))
          (by rw [hρu v hv, Valuation.map_one])
        rwa [norm_one] at h
      · rw [hρS v hv, norm_one]
    by_cases hck : (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    · rw [if_pos hck]

      have ha : (∫ t, Fn (t, k) ∂νS) = ∫ t, finf (kinf (k : AdelicGL2 (𝓞 K) K)) *
          (((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ) * (if (∀ v ∈ S, Valued.v ((((t * ρ) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀))) else 0)) ∂νS := by
        refine integral_congr_ae ?_
        filter_upwards [ae_snd_eq_one (K := K) S] with t ht
        have h4 := hpt t ht
        rw [if_pos hck, ← kinf_eq] at h4
        simp only [hFn]
        rw [h4]
        ring

      have hmp := NumberField.Idele.measurePreserving_mul_right_sPartMeasure K S ρ hρS
      have hb : (∫ t, ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ) * (if (∀ v ∈ S, Valued.v ((((t * ρ) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀))) else 0) ∂νS) =
          ∫ t, ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ) * (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀))) else 0) ∂νS := by
        rw [← hmp.integral_comp (show MeasurableEmbedding (fun t : (AdeleRing (𝓞 K) K)ˣ => t * ρ) from (Homeomorph.mulRight ρ).measurableEmbedding)
          (fun t : (AdeleRing (𝓞 K) K)ˣ => ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ) * (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀))) else 0))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        beta_reduce
        simp only [Units.val_mul]
        rw [NumberField.TateGlobal.ideleNorm_mul, hρnorm, mul_one, partAt_empty_mul_of_fst_eq_one t ρ hρ1]

      have hc : (∫ t, ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ) * (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀))) else 0) ∂νS) =
          ∫ t, (if (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) * (((NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K ∅ t) : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K ∅ t) ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))) else 0) ∂νS := by
        refine integral_congr_ae ?_
        filter_upwards [ae_snd_eq_one (K := K) S] with t ht
        by_cases hbt : (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
        · rw [if_pos hbt, if_pos hbt, ideleNorm_eq_mul_of_ball S nb hnb t t₀ ht ht₀ ht₀inf hbt]
          push_cast
          rw [Complex.mul_cpow_ofReal_nonneg (hnpos t₀).le (hnpos _).le,
            Real.mul_rpow (hnpos t₀).le (hnpos _).le]
          push_cast
          ring
        · rw [if_neg hbt, if_neg hbt, mul_zero]

      have hfk : Integrable (fun a : (AdeleRing (𝓞 K) K)ˣ => (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) * (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀))))) ν0 :=
        (hB_int (kinf (k : AdelicGL2 (𝓞 K) K)) (glFin_kinf _) hrowk).const_mul _
      have hd := (hP2 _ hfk).2
      rw [ha, integral_const_mul, hb, hc, hd, integral_const_mul]
      ring
    · rw [if_neg hck, mul_zero]
      have ha : (∫ t, Fn (t, k) ∂νS) = ∫ t, (0 : ℂ) ∂νS := by
        refine integral_congr_ae ?_
        filter_upwards [ae_snd_eq_one (K := K) S] with t ht
        have h4 := hpt t ht
        rw [if_neg hck] at h4
        simp only [hFn]
        rw [h4, zero_mul]
      rw [ha, integral_zero]

  have hP3app : (∫ k, (if (∀ v ∈ S, Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((((k : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then
            finf (kinf (k : AdelicGL2 (𝓞 K) K)) * (∫ a, (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * kinf (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * kinf (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))) ∂ν0) else 0) ∂μK) =
      (κ₃ : ℂ) * ∫ k, finf (k : AdelicGL2 (𝓞 K) K) * (∫ a, (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))) ∂ν0) ∂μ0 :=
    integral_ite_bottomRow_mul_eq S n κ₃ hP3
      (fun (g : AdelicGL2 (𝓞 K) K) (a : (AdeleRing (𝓞 K) K)ˣ) => (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * g * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * g * diagOne t₀)))))
      hBc hB_int (∫ a, env a ∂ν0) hΛbd finf hfc

  show (∫ t, ∫ k, Fn (t, k) ∂μK ∂νS) = ((κ₂ * κ₃ : ℝ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) * ∫ k, finf (k : AdelicGL2 (𝓞 K) K) * (∫ a, (((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) * ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
      (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))) ∂ν0) ∂μ0
  rw [hswap, integral_congr_ae (Filter.Eventually.of_forall hinner), integral_const_mul, hP3app]
  push_cast
  ring

end P6E43
p2m_reactivate "P2MW.S_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery.P6E43"

end
p2m_reactivate "P2MW.S_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery.P6E43"

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))

      (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (_hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hx₀c : Continuous x₀)
      (nb : ℕ) (_hnb : 0 < nb)
      (_hx₀cong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x₀ (g * k) = x₀ g)
      (_hxlarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
      (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (m : ℕ)
      (_ht₀box : ∀ v ∈ S, Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
        ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))

      (r : ℕ) (u : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ)
      (_husupp : ∀ i, (u i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (u i).2 v = 0)
      (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (u i) = unipotentGL2 (u i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (u i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
      (_hμball : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
      (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (u i) * κ)))
      (_hxc : Continuous x)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (y : AdelicGL2 (𝓞 K) K → ℂ) (_hyc : Continuous y)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (_hyKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, y (g * k) = y g)
      (_hycong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * k) = y g)
      (_hylow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * lowerUnipotentGL2 γ) = y g)
      (_hylarge : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (finf : AdelicGL2 (𝓞 K) K → ℂ) (_hfc : Continuous finf)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (_hφval : ∀ (s : ℂ) (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf)

      (δx Cx : ℝ) (_hδx : 0 < δx)
      (_hCx : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
            Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
      (δy Cy : ℝ) (_hδy : 0 < δy)
      (_hCy : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * (diagOne t₀))‖ ≤
            Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
              (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy)),
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ s : ℂ, 1 / 2 - (δx + δy) / 2 < s.re →
      (∫ t, ∫ k,
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K))) *
              φ s (diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            ((NumberField.TateGlobal.ideleNorm K t ^ (-w - 1) : ℝ) : ℂ)
          ∂(maximalCompactHaar K) ∂(NumberField.Idele.sPartMeasure K S)) =
        (κ₀ : ℂ) * (((NumberField.TateGlobal.ideleNorm K t₀ : ℝ) : ℂ) ^ (s + 1 / 2) *
            ((NumberField.TateGlobal.ideleNorm K t₀ ^ (-w - 1) : ℝ) : ℂ)) *
          ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅) :=
  P6E43.main K

end S_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_exists_integral_torus_pair_eq_mul_integral_archTorus_of_ball_surgery (solution)
