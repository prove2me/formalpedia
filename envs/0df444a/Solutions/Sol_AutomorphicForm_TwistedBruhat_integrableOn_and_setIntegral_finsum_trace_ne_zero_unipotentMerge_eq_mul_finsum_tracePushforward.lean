-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/64085ace-189a-5ccc-b4a5-744cec37e449

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_TraceFibrePushforward_setLIntegral_tsum_actSubId_eq_mul_measure_mul_tsum
import Theorems.Thm_AutomorphicForm_AdelicTracePushforward_trace_traceFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ArchcX3

open Filter Topology Function

theorem measurable_finsum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℂ} (hf : ∀ i, Measurable (f i)) :
    Measurable fun a => ∑ᶠ i, f i a := by
  classical
  have hA : ∀ T : Finset ι, MeasurableSet {a | (Function.support fun i => f i a) ⊆ ↑T} := by
    intro T
    have hset : {a | (Function.support fun i => f i a) ⊆ ↑T} = ⋂ i, {a | i ∉ T → f i a = 0} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Function.support_subset_iff', Finset.mem_coe]
    rw [hset]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ T
    · have : {a | i ∉ T → f i a = 0} = Set.univ := by
        ext a; simp [hi]
      rw [this]; exact MeasurableSet.univ
    · have : {a | i ∉ T → f i a = 0} = (f i) ⁻¹' {0} := by
        ext a; simp [hi]
      rw [this]; exact hf i (measurableSet_singleton 0)
  let g : Finset ι → α → ℂ := fun T a =>
    if (Function.support fun i => f i a) ⊆ ↑T then ∑ i ∈ T, f i a else 0
  have hg : ∀ T, Measurable (g T) := fun T =>
    Measurable.ite (hA T) (Finset.measurable_sum T fun i _ => hf i) measurable_const
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι)) hg ?_
  rw [tendsto_pi_nhds]
  intro a
  by_cases h : (Function.support fun i => f i a).Finite
  · apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop h.toFinset] with T hT
    have hsub : (Function.support fun i => f i a) ⊆ ↑T := by
      intro i hi
      exact hT (h.mem_toFinset.mpr hi)
    simp only [g, if_pos hsub]
    exact (finsum_eq_sum_of_support_subset (fun i => f i a) hsub).symm
  · have hne : ∀ T : Finset ι, ¬ (Function.support fun i => f i a) ⊆ ↑T :=
      fun T hsub => h (T.finite_toSet.subset hsub)
    have hg0 : (fun T => g T a) = fun _ => 0 := by
      funext T; simp only [g, if_neg (hne T)]
    rw [hg0, finsum_of_infinite_support h]
    exact tendsto_const_nhds

section Trace

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

@[reducible] noncomputable def adeleAlgebra : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  (M4aHerbrand.Bridge.genuineβ K L).toAlgebra

attribute [local instance] adeleAlgebra

theorem isModuleTopology_adele : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
  M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L
    (M4aHerbrand.Bridge.continuous_genuineβ K L) (M4aHerbrand.Bridge.genuineTensorEquiv K L)

theorem continuous_adelicTrace :
    Continuous (Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)) := by
  haveI := isModuleTopology_adele K L
  exact IsModuleTopology.continuous_of_linearMap _

theorem adelicTrace_algebraMap (b : L) :
    Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (algebraMap L (AdeleRing (𝓞 L) L) b) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.trace K L b) := by
  rw [← M4aHerbrand.Bridge.genuineTensorEquiv_one_tmul K L b, Algebra.trace_eq_of_algEquiv,
    Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem adelicTrace_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (y : AdeleRing (𝓞 L) L) :
    Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (D.act g y) =
      Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) y := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act]
  exact Algebra.trace_eq_of_algEquiv
    ((M4aHerbrand.Bridge.genuineTensorEquiv K L).symm.trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl g).trans (M4aHerbrand.Bridge.genuineTensorEquiv K L))) y

theorem adelicTrace_actSubId (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (g : L ≃ₐ[K] L)
    (x : AdeleRing (𝓞 L) L) :
    Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (actSubId K L D g x) = 0 := by
  unfold actSubId
  rw [map_sub, adelicTrace_act, sub_self]

theorem adelicTrace_traceFibre (r : AdeleRing (𝓞 K) K)
    (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (traceFibre K L r w) = r :=
  AutomorphicForm.AdelicTracePushforward.trace_traceFibre K L r w

end Trace

section Core

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] adeleAlgebra

theorem exists_card_le_of_isCompact (C : Set (AdeleRing (𝓞 L) L)) (hC : IsCompact C) :
    ∃ N : ℕ, ∀ y : AdeleRing (𝓞 L) L,
      ∃ T : Finset L, T.card ≤ N ∧ ∀ b : L, algebraMap L (AdeleRing (𝓞 L) L) b + y ∈ C → b ∈ T := by
  classical
  have hD : IsCompact ((fun p : AdeleRing (𝓞 L) L × AdeleRing (𝓞 L) L => p.1 - p.2) '' (C ×ˢ C)) :=
    (hC.prod hC).image (continuous_fst.sub continuous_snd)
  have hfinD := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hD
  refine ⟨hfinD.toFinset.card, fun y => ?_⟩
  have hCy : IsCompact ((fun w : AdeleRing (𝓞 L) L => w - y) '' C) :=
    hC.image (continuous_id.sub continuous_const)
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hCy
  refine ⟨hfin.toFinset, ?_, fun b hb => hfin.mem_toFinset.mpr ⟨_, hb, by simp⟩⟩
  rcases Finset.eq_empty_or_nonempty hfin.toFinset with hT | ⟨b₀, hb₀⟩
  · rw [hT, Finset.card_empty]; exact Nat.zero_le _
  · obtain ⟨w₀, hw₀, hwb₀⟩ := hfin.mem_toFinset.mp hb₀
    refine Finset.card_le_card_of_injOn (fun b => b - b₀) ?_ (sub_left_injective.injOn)
    intro b hb
    obtain ⟨w, hw, hwb⟩ := hfin.mem_toFinset.mp (Finset.mem_coe.mp hb)
    refine Finset.mem_coe.mpr (hfinD.mem_toFinset.mpr ⟨(w, w₀), ⟨hw, hw₀⟩, ?_⟩)
    show w - w₀ = algebraMap L (AdeleRing (𝓞 L) L) (b - b₀)
    rw [map_sub, ← hwb, ← hwb₀]
    exact (sub_sub_sub_cancel_right w w₀ y).symm

theorem core [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (G : AdeleRing (𝓞 L) L → ℂ) (hGc : Continuous G) (hGs : HasCompactSupport G)
    (X : Set (AdeleRing (𝓞 L) L))
    (hX : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK) :
    IntegrableOn (fun x : AdeleRing (𝓞 L) L =>
        ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0}, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x))
      X (adelicAddHaar (𝓞 L) L) ∧
    (∫ x in X, ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0}, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)
        ∂(adelicAddHaar (𝓞 L) L)) =
      (c.toReal : ℂ) * ∑ᶠ η : Kˣ, tracePushforward K L G (algebraMap K (AdeleRing (𝓞 K) K) (η : K)) := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 L) L) :=
    Function.Surjective.countable
      (f := fun l : L => (⟨algebraMap L (AdeleRing (𝓞 L) L) l, l, rfl⟩ : AdeleRing.principalSubgroup (𝓞 L) L))
      (by rintro ⟨_, l, rfl⟩; exact ⟨l, rfl⟩)

  obtain ⟨S, hS⟩ : ∃ S : Set L, S = {b : L | Algebra.trace K L b ≠ 0} := ⟨_, rfl⟩
  obtain ⟨Tr, hTr⟩ : ∃ Tr : AdeleRing (𝓞 L) L →ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 K) K,
      Tr = Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : AdeleRing (𝓞 L) L → ℂ, F = fun w => if Tr w = 0 then 0 else G w := ⟨_, rfl⟩
  rw [← hS]
  have h_injK : Function.Injective (algebraMap K (AdeleRing (𝓞 K) K)) :=
    NumberField.AdeleRing.algebraMap_injective (𝓞 K) K
  have hTrc : Continuous Tr := hTr ▸ continuous_adelicTrace K L
  have hact : Continuous (actSubId K L D σ) := by
    unfold actSubId
    exact (D.continuous_act σ).sub continuous_id

  have hTrF : ∀ (b : L) (x : AdeleRing (𝓞 L) L),
      Tr (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) =
        algebraMap K (AdeleRing (𝓞 K) K) (Algebra.trace K L b) := by
    intro b x
    rw [hTr, map_add, adelicTrace_algebraMap, adelicTrace_actSubId, add_zero]
  have hFpt : ∀ (b : L) (x : AdeleRing (𝓞 L) L),
      F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) =
        S.indicator (fun b => G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)) b := by
    intro b x
    simp only [hF, hTrF, hS, Set.indicator_apply, Set.mem_setOf_eq, map_eq_zero_iff _ h_injK]
    by_cases hb : Algebra.trace K L b = 0 <;> simp [hb]

  have hFmeas : Measurable F := by
    rw [hF]
    exact Measurable.ite (hTrc.measurable (measurableSet_singleton (0 : AdeleRing (𝓞 K) K)))
      measurable_const hGc.measurable

  obtain ⟨N, hN⟩ := exists_card_le_of_isCompact L (tsupport G) hGs
  choose T hTcard hTmem using hN
  obtain ⟨M, hM⟩ := hGs.exists_bound_of_continuous hGc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsupp : ∀ x : AdeleRing (𝓞 L) L,
      (Function.support fun b : L =>
        S.indicator (fun b => G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)) b) ⊆
        ↑(T (actSubId K L D σ x)) := by
    intro x b hb
    rw [Function.mem_support, Set.indicator_apply_ne_zero] at hb
    exact Finset.mem_coe.mpr (hTmem _ b (subset_tsupport _ hb.2))
  have hfx_eq : ∀ x : AdeleRing (𝓞 L) L,
      ∑ᶠ b ∈ S, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) =
        ∑ b ∈ T (actSubId K L D σ x),
          S.indicator (fun b => G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)) b := by
    intro x
    rw [finsum_mem_def]
    exact finsum_eq_sum_of_support_subset _ (hsupp x)
  have hfx_bound : ∀ x : AdeleRing (𝓞 L) L,
      ‖∑ᶠ b ∈ S, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)‖ ≤ N * M := by
    intro x
    rw [hfx_eq x]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ M fun b _ => ?_).trans ?_
    · rw [Set.indicator_apply]
      split_ifs
      · exact hM _
      · simpa using hM0
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hTcard _)) hM0
  have hFx_eq : ∀ x : AdeleRing (𝓞 L) L,
      ∑' b : L, F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) =
        ∑ᶠ b ∈ S, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) := by
    intro x
    rw [tsum_congr fun b => hFpt b x, tsum_eq_sum' (hsupp x), hfx_eq x]
  have hFx_enorm : ∀ x : AdeleRing (𝓞 L) L,
      ∑' b : L, ‖F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)‖ₑ ≤ (N : ℝ≥0∞) * ENNReal.ofReal M := by
    intro x
    have hsupp' : (Function.support fun b : L =>
        ‖F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)‖ₑ) ⊆ ↑(T (actSubId K L D σ x)) := by
      intro b hb
      apply hsupp x
      rw [Function.mem_support] at hb ⊢
      rw [← hFpt]
      exact fun h => hb (by rw [h, enorm_zero])
    rw [tsum_eq_sum' hsupp']
    refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal M) fun b _ => ?_).trans ?_
    · rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hFpt, Set.indicator_apply]
      split_ifs
      · exact hM _
      · simpa using hM0
    · rw [nsmul_eq_mul]
      gcongr
      exact_mod_cast hTcard _

  have hmeas_f : Measurable fun x : AdeleRing (𝓞 L) L =>
      ∑ᶠ b ∈ S, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) := by
    have hfun : (fun x : AdeleRing (𝓞 L) L =>
        ∑ᶠ b ∈ S, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)) =
        fun x => ∑ᶠ b : L, S.indicator (fun b => G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)) b :=
      funext fun x => finsum_mem_def _ _
    rw [hfun]
    refine measurable_finsum fun b => ?_
    by_cases hb : b ∈ S
    · simp only [Set.indicator_of_mem hb]
      exact (hGc.comp (continuous_const.add hact)).measurable
    · simp only [Set.indicator_of_notMem hb]
      exact measurable_const

  have hμX : adelicAddHaar (𝓞 L) L X < ∞ := by
    rw [hX.measure_eq (NumberField.AdelicBox.isAddFundamentalDomain_adelicBox L _)]
    exact NumberField.AdelicBox.measure_adelicBox_lt_top L _
  refine ⟨?_, ?_⟩
  ·
    exact Measure.integrableOn_of_bounded hμX.ne hmeas_f.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hfx_bound x)
  ·
    have hfin : ∫⁻ x in X, ∑' b : L, ‖F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)‖ₑ
        ∂(adelicAddHaar (𝓞 L) L) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const fun x _ => hFx_enorm x)
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top) hμX.ne
    have hmerge := (TraceFibrePushforward.setLIntegral_tsum_actSubId_eq_mul_measure_mul_tsum K L μK
      (adelicAddHaar (𝓞 L) L) D σ hgen c hc).2 X hX (NumberField.AdelicBox.adelicBox K)
      (NumberField.AdelicBox.isAddFundamentalDomain_adelicBox K μK) F hFmeas hfin
    have hfun : (fun x : AdeleRing (𝓞 L) L =>
        ∑ᶠ b ∈ S, G (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x)) =
        fun x => ∑' b : L, F (algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) :=
      funext fun x => (hFx_eq x).symm
    rw [hfun, hmerge, hμK1, mul_one]
    congr 1

    have hTP : ∀ r : K, tracePushforward K L F (algebraMap K (AdeleRing (𝓞 K) K) r) =
        if r = 0 then 0 else tracePushforward K L G (algebraMap K (AdeleRing (𝓞 K) K) r) := by
      intro r
      by_cases hr : r = 0
      · rw [if_pos hr, hr, map_zero]
        unfold tracePushforward
        have h0 : ∀ w, F (traceFibre K L 0 w) = 0 := fun w => by
          rw [hF]
          simp only [hTr, adelicTrace_traceFibre]
          simp
        simp [h0]
      · rw [if_neg hr]
        unfold tracePushforward
        congr 1
        funext w
        rw [hF]
        simp only [hTr, adelicTrace_traceFibre, map_eq_zero_iff _ h_injK, if_neg hr]
    rw [tsum_congr hTP]
    have hsuppK : (Function.support fun r : K =>
        if r = 0 then 0 else tracePushforward K L G (algebraMap K (AdeleRing (𝓞 K) K) r)) ⊆
        Set.range (Units.val : Kˣ → K) := by
      intro r hr
      rw [Function.mem_support] at hr
      have hr0 : r ≠ 0 := fun h => hr (by rw [if_pos h])
      exact ⟨Units.mk0 r hr0, rfl⟩
    rw [← (Units.val_injective : Function.Injective (Units.val : Kˣ → K)).tsum_eq hsuppK]
    simp only [Units.ne_zero, if_false]

    refine tsum_eq_finsum ?_
    have hCK : IsCompact (Tr '' tsupport G) := hGs.image hTrc
    have hfinK := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hCK
    refine (hfinK.preimage (Units.val_injective.injOn)).subset ?_
    intro η hη
    change algebraMap K (AdeleRing (𝓞 K) K) (η : K) ∈ Tr '' tsupport G
    by_contra hnot
    apply hη
    unfold tracePushforward
    have h0 : ∀ w, G (traceFibre K L (algebraMap K (AdeleRing (𝓞 K) K) (η : K)) w) = 0 := fun w => by
      by_contra hw
      exact hnot ⟨_, subset_tsupport _ hw, by rw [hTr]; exact adelicTrace_traceFibre K L _ w⟩
    simp [h0]

end Core

end ArchcX3

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (X : Set (AdeleRing (𝓞 L) L))
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)]
    [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K))
    [μK.IsAddHaarMeasure]
    (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    (c : ℝ≥0∞)
    (hc0 : c ≠ 0)
    (hcT : c ≠ ⊤)
    (hc : ∀ G : AdeleRing (𝓞 L) L → ℝ≥0∞, @Measurable _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) _ G →
      ∫⁻ x, G x ∂(adelicAddHaar (𝓞 L) L) =
        c * ∫⁻ r, ∫⁻ w, G (traceFibre K L r w)
          ∂(@Measure.pi (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L)))) (fun _ => AdeleRing (𝓞 K) K) _
            (fun _ => NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (fun _ => adelicAddHaar (𝓞 K) K)) ∂μK)
    (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : ↥(adelicMaximalCompact L)) :
    IntegrableOn (fun x : AdeleRing (𝓞 L) L =>
        ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
          φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
      X (adelicAddHaar (𝓞 L) L) ∧
    (∫ x in X, ∑ᶠ b ∈ {b : L | Algebra.trace K L b ≠ 0},
          φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 ((algebraMap L (AdeleRing (𝓞 L) L) b + actSubId K L D σ x) * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))
        ∂(adelicAddHaar (𝓞 L) L)) =
      (c.toReal : ℂ) * ∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K)) := by
  obtain rfl : ‹MeasurableSpace (AdeleRing (𝓞 K) K)› = NumberField.AdelicHaar.adeleBorel (𝓞 K) K :=
    BorelSpace.measurable_eq
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  have hGc : Continuous fun w : AdeleRing (𝓞 L) L =>
      φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) :=
    hφc.comp ((((continuous_const.mul (AutomorphicForm.continuous_unipotentGL2.comp
      (continuous_id.mul continuous_const))).mul continuous_const).mul continuous_const).mul continuous_const)
  have hGs : HasCompactSupport fun w : AdeleRing (𝓞 L) L =>
      φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) := by
    have hm : Continuous fun g : AdelicGL2 (𝓞 L) L =>
        (k : AdelicGL2 (𝓞 L) L) * g * (AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))⁻¹ *
          (centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ))⁻¹ *
          (diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹))⁻¹ :=
      (((continuous_const.mul continuous_id).mul continuous_const).mul continuous_const).mul continuous_const
    have hf : Continuous fun g : AdelicGL2 (𝓞 L) L =>
        (t : AdeleRing (𝓞 L) L) *
          (((k : AdelicGL2 (𝓞 L) L) * g * (AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))⁻¹ *
            (centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ))⁻¹ *
            (diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹))⁻¹ : AdelicGL2 (𝓞 L) L) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 :=
      continuous_const.mul ((Units.continuous_val.comp hm).matrix_elem 0 1)
    refine HasCompactSupport.intro (hφs.image hf) ?_
    intro w hw
    by_contra hGw
    apply hw
    refine ⟨(k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L), subset_tsupport _ hGw, ?_⟩
    have hgrp : (k : AdelicGL2 (𝓞 L) L) * ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
            unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
            diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
            AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) *
          (AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))⁻¹ *
          (centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ))⁻¹ *
          (diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹))⁻¹ =
        unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) := by
      group
    simp only [hgrp, AutomorphicForm.unipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    rw [mul_comm, mul_assoc, Units.inv_mul, mul_one]
  exact ArchcX3.core K L D σ hgen _ hGc hGs X hX μK hμK1 c hc

end S_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_integrableOn_and_setIntegral_finsum_trace_ne_zero_unipotentMerge_eq_mul_finsum_tracePushforward (solution)
