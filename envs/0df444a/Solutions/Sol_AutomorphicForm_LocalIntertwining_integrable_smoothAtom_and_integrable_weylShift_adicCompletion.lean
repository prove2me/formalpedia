-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9938817b-f7ad-5081-b58c-8ef811c0ee1b

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal Topology

noncomputable section

namespace AutomorphicForm
namespace LocalIntertwining
namespace IntV

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem exists_uniformizer :
    ∃ ϖ : (v.adicCompletion F)ˣ, Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
  obtain ⟨r, hr⟩ := v.valuation_exists_uniformizer' F
  obtain ⟨x, hx⟩ : ∃ x : v.adicCompletion F, Valued.v x = WithZero.exp (-1 : ℤ) :=
    ⟨_, (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v r).trans hr⟩
  have hne : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hne, hx⟩

private theorem two_le_absNorm : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private theorem isCompact_integers : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  isCompact_iff_compactSpace.mpr (show CompactSpace (v.adicCompletionIntegers F) from inferInstance)

private theorem isOpen_ball {r0 : v.adicCompletion F} (hr0v : Valued.v r0 ≠ 0) :
    IsOpen {y : v.adicCompletion F | Valued.v y ≤ Valued.v r0} := by
  have hr : Valued.v.restrict r0 ≠ 0 := fun h0 => hr0v ((Valuation.restrict_eq_zero_iff Valued.v).1 h0)
  have hset : {y : v.adicCompletion F | Valued.v y ≤ Valued.v r0}
      = {y | Valued.v.restrict y ≤ Valued.v.restrict r0} :=
    Set.ext fun y => (Valuation.restrict_le_iff Valued.v (x := y) (y := r0)).symm
  rw [hset]
  exact (Valued.isClopen_closedBall (v.adicCompletion F) hr).isOpen

private theorem integrableOn_of_locallyConstantOn
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (m : ℕ) (A : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x) :
    IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ := by
  refine ContinuousOn.integrableOn_compact (isCompact_integers F v) ?_
  intro x hx
  set r0 : v.adicCompletion F := (ϖ : v.adicCompletion F) ^ m with hr0
  have hvr0 : Valued.v r0 = Multiplicative.ofAdd (-(m : ℤ)) := by
    rw [hr0, map_pow, hϖ, ← WithZero.coe_pow, ← ofAdd_nsmul, smul_neg, nsmul_eq_mul, mul_one]
  have hr0v : Valued.v r0 ≠ 0 := by rw [hvr0]; exact WithZero.coe_ne_zero
  have hU : {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v r0} ∈ 𝓝 x :=
    ((isOpen_ball F v hr0v).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  refine (continuousWithinAt_const (b := A x)).congr_of_eventuallyEq ?_ rfl
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with y hy hyO
  exact hA x hx y hyO (by rw [← hvr0]; exact hy)

private theorem integrable_atom
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x) μ := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer F v
  have hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v 1, (1 : (v.adicCompletion F)ˣ →* ℂˣ) u = 1 :=
    fun _ _ => rfl
  have h2 := two_le_absNorm F v
  have hN : 1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast (lt_of_lt_of_le one_lt_two h2)
  have hs' : ‖(((1 : (v.adicCompletion F)ˣ →* ℂˣ) ϖ : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
    rw [MonoidHom.one_apply, Units.val_one, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    refine Real.rpow_lt_one_of_one_lt_of_neg hN ?_
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h := EisensteinGeneral.LocalRam.integrable_twisted_smooth F v μ ϖ hϖ 1 1 le_rfl hχ m hm A hA B hB s hs'
    (1 : AddChar (v.adicCompletion F) ℂ) 0 (fun _ _ => AddChar.one_apply _) 0
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [AddChar.one_apply, mul_one]
  congr 1
  by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (zero_mem _)
    rw [LanglandsTunnell.TateLocal.charExt_of_ne_zero _ hx0, MonoidHom.inv_apply, MonoidHom.one_apply, inv_one,
      Units.val_one, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

private theorem mem_O_iff (x : v.adicCompletion F) : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ↔ Valued.v x ≤ 1 := Iff.rfl

private theorem mem_O_iff' (x : v.adicCompletion F) : x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := Iff.rfl

private theorem modulus_eq_one_of_v_eq_one {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    LanglandsTunnell.TateLocal.modulus x = 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v x, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one,
    NumberField.FinitePlace.norm_def (K := F) (v := v) x, hx, map_one, NNReal.coe_one]

private theorem modulus_mul_modulus_inv {x : v.adicCompletion F} (hx : x ≠ 0) :
    LanglandsTunnell.TateLocal.modulus x * LanglandsTunnell.TateLocal.modulus x⁻¹ = 1 := by
  rw [← LanglandsTunnell.TateLocal.modulus_mul, mul_inv_cancel₀ hx, LanglandsTunnell.TateLocal.modulus_one]

private theorem ofAdd_neg_lt_one {m : ℕ} (hm : 1 ≤ m) :
    ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  omega

private theorem v_lt_one_of_close {m : ℕ} (hm : 1 ≤ m) {x y : v.adicCompletion F}
    (hxy : Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ))) (hx : Valued.v x < 1) : Valued.v y < 1 := by
  have : y = y - x + x := by ring
  rw [this]
  exact lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt (lt_of_le_of_lt hxy (ofAdd_neg_lt_one hm)) hx)

private theorem v_le_one_of_close {m : ℕ} (hm : 1 ≤ m) {x y : v.adicCompletion F}
    (hxy : Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ))) (hx : Valued.v x ≤ 1) : Valued.v y ≤ 1 := by
  have : y = y - x + x := by ring
  rw [this]
  exact le_trans (Valued.v.map_add _ _) (max_le (le_trans hxy (ofAdd_neg_lt_one hm).le) hx)

private theorem v_sub_comm (x y : v.adicCompletion F) : Valued.v (x - y) = Valued.v (y - x) := by
  rw [← neg_sub, Valuation.map_neg]

private theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer F v
  have hnorm : ‖(ϖ : v.adicCompletion F)‖ < 1 := by
    rw [NumberField.FinitePlace.norm_def (K := F) (v := v), hϖ]
    have h1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    exact_mod_cast (WithZeroMulInt.toNNReal_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr h1
  have ht := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hmem : (0 : v.adicCompletion F) ∈ closure ({0}ᶜ : Set (v.adicCompletion F)) :=
    mem_closure_of_tendsto ht (Filter.Eventually.of_forall fun n => pow_ne_zero n ϖ.ne_zero)
  exact mem_closure_iff_nhdsWithin_neBot.mp hmem

theorem main
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : 0 < s.re) :
    let a : v.adicCompletion F → ℂ := fun x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x
    Integrable a μ ∧
    Integrable (fun x =>
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹) μ := by
  intro a
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer F v
  have hAint := integrableOn_of_locallyConstantOn F v μ ϖ hϖ m A hA
  refine ⟨integrable_atom F v μ m hm A B hAint hB s hs, ?_⟩

  classical
  let A2 : v.adicCompletion F → ℂ := fun x => if Valued.v x < 1 then B x else A x⁻¹
  let B2 : v.adicCompletion F → ℂ := (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A
  have hA2 : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A2 y = A2 x := by
    intro x hx y hy hxy
    by_cases hvx : Valued.v x < 1
    · have hvy : Valued.v y < 1 := v_lt_one_of_close F v hm hxy hvx
      simp only [A2, if_pos hvx, if_pos hvy]
      exact hB x y hxy
    · have hx1 : Valued.v x = 1 := le_antisymm ((mem_O_iff' F v x).mp hx) (not_lt.mp hvx)
      have hvy : ¬ Valued.v y < 1 := by
        intro hvy
        exact hvx (v_lt_one_of_close F v hm (by rwa [v_sub_comm]) hvy)
      have hy1 : Valued.v y = 1 := le_antisymm ((mem_O_iff' F v y).mp hy) (not_lt.mp hvy)
      simp only [A2, if_neg hvx, if_neg hvy]
      have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hx1; exact zero_ne_one hx1
      have hy0 : y ≠ 0 := by rintro rfl; rw [map_zero] at hy1; exact zero_ne_one hy1
      have hval : Valued.v (y⁻¹ - x⁻¹) = Valued.v (y - x) := by
        have : y⁻¹ - x⁻¹ = (x - y) * (x⁻¹ * y⁻¹) := by field_simp
        rw [this, Valuation.map_mul, Valuation.map_mul, map_inv₀, map_inv₀, hx1, hy1, v_sub_comm F v x y]
        simp
      refine hA x⁻¹ ?_ y⁻¹ ?_ ?_
      · exact (mem_O_iff' F v _).mpr (by rw [map_inv₀, hx1, inv_one])
      · exact (mem_O_iff' F v _).mpr (by rw [map_inv₀, hy1, inv_one])
      · rw [hval]; exact hxy
  have hB2 : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B2 y = B2 x := by
    intro x y hxy
    by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · have hy : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := (mem_O_iff F v y).mpr (v_le_one_of_close F v hm hxy ((mem_O_iff F v x).mp hx))
      simp only [B2, Set.indicator_of_mem hx, Set.indicator_of_mem hy]
      exact hA x hx y hy hxy
    · have hy : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        intro hy
        exact hx ((mem_O_iff F v x).mpr
          (v_le_one_of_close F v hm (by rwa [v_sub_comm]) ((mem_O_iff F v y).mp hy)))
      simp only [B2, Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  have hA2int := integrableOn_of_locallyConstantOn F v μ ϖ hϖ m A2 hA2
  have h2 := integrable_atom F v μ m hm A2 B2 hA2int hB2 s hs

  have hpt : ∀ x : v.adicCompletion F, x ≠ 0 →
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹ =
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A2 x + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B2 y⁻¹) x := by
    intro x hx0
    have hmm := modulus_mul_modulus_inv F v hx0
    by_cases hxO : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · rw [Set.indicator_of_mem hxO, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hxO), add_zero]
      by_cases hvx : Valued.v x < 1
      ·
        have hxinv : x⁻¹ ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
          rw [mem_O_iff, map_inv₀, not_le]
          exact one_lt_inv_iff₀.mpr ⟨(Valuation.pos_iff _).mpr hx0, hvx⟩
        simp only [a, A2, if_pos hvx, Set.indicator_of_notMem hxinv, Set.indicator_of_mem (Set.mem_compl hxinv),
          zero_add, inv_inv]
        rw [← mul_assoc, ← Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
          ← Complex.ofReal_mul, ← NNReal.coe_mul, hmm, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul]
      ·
        have hx1 : Valued.v x = 1 := le_antisymm ((mem_O_iff F v x).mp hxO) (not_lt.mp hvx)
        have hxinv : x⁻¹ ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by rw [mem_O_iff, map_inv₀, hx1, inv_one]
        simp only [a, A2, if_neg hvx, Set.indicator_of_mem hxinv,
          Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hxinv), add_zero]
        rw [modulus_eq_one_of_v_eq_one F v hx1, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul]
    ·
      have hvx : 1 < Valued.v x := not_le.mp (fun h => hxO ((mem_O_iff F v x).mpr h))
      have hxinv : x⁻¹ ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [mem_O_iff, map_inv₀]
        exact inv_le_one_of_one_le₀ hvx.le
      rw [Set.indicator_of_notMem hxO, Set.indicator_of_mem (Set.mem_compl hxO), zero_add]
      simp only [a, B2, Set.indicator_of_mem hxinv, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hxinv),
        add_zero]

  haveI := nhdsNE_zero_neBot F v
  have hae : (fun x => (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹) =ᵐ[μ]
      fun x => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A2 x + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B2 y⁻¹) x := by
    have h0 : μ {(0 : v.adicCompletion F)} = 0 := measure_singleton 0
    refine (ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0))
    simp only [Set.mem_setOf_eq] at hx
    by_contra hx0
    exact hx (hpt x hx0)
  exact h2.congr hae.symm

end AutomorphicForm.LocalIntertwining.IntV

end

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (_hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (_hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (_hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (_hs : 0 < s.re) :
    let a : v.adicCompletion F → ℂ := fun x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x
    Integrable a μ ∧
    Integrable (fun x =>
      (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1)) * a x⁻¹) μ :=
  AutomorphicForm.LocalIntertwining.IntV.main F v μ m _hm A B _hA _hB s _hs

end S_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion (solution)
