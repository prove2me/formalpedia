-- Prove2me | solution 1 for AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f0e27717-2868-53a9-8551-2427d2d8c1d3

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Theorems.Thm_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open scoped NNReal

noncomputable section

namespace AutomorphicForm
namespace LocalIntertwining
namespace W3

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

private theorem modulus_le_one_of_mem {u : v.adicCompletion F} (hu : u ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    ((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ≤ 1 := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v u, coe_nnnorm,
    NumberField.FinitePlace.norm_def (K := F) (v := v) u]
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).mpr ((mem_O_iff F v u).mp hu)

private theorem one_lt_modulus_of_not_mem {u : v.adicCompletion F} (hu : u ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    1 < ((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v u, coe_nnnorm,
    NumberField.FinitePlace.norm_def (K := F) (v := v) u]
  have hv : 1 < Valued.v u := not_le.mp (fun h => hu ((mem_O_iff F v u).mpr h))
  have hmono := WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)
  have := hmono hv
  rw [map_one] at this
  exact_mod_cast this

private theorem modulus_pos_real {u : v.adicCompletion F} (hu : u ≠ 0) :
    0 < ((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) := by
  exact_mod_cast LanglandsTunnell.TateLocal.modulus_pos hu

private theorem ne_zero_of_not_mem {u : v.adicCompletion F} (hu : u ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) : u ≠ 0 := by
  rintro rfl
  exact hu (zero_mem _)

private theorem inv_mem_of_not_mem {u : v.adicCompletion F} (hu : u ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) : u⁻¹ ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hv : 1 < Valued.v u := not_le.mp (fun h => hu ((mem_O_iff F v u).mpr h))
  rw [mem_O_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ hv.le

private theorem continuous_modulus : Continuous fun u : v.adicCompletion F => LanglandsTunnell.TateLocal.modulus u := by
  have : (fun u : v.adicCompletion F => LanglandsTunnell.TateLocal.modulus u) = fun u => ‖u‖₊ :=
    funext fun u => LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm F v u
  rw [this]
  exact continuous_nnnorm

private theorem exists_bound_on_integers
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (m : ℕ) (B : v.adicCompletion F → ℂ)
    (hB : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖B y‖ ≤ M := by
  have hcont : ContinuousOn B (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro x hx
    set r0 : v.adicCompletion F := (ϖ : v.adicCompletion F) ^ m with hr0
    have hvr0 : Valued.v r0 = Multiplicative.ofAdd (-(m : ℤ)) := by
      rw [hr0, map_pow, hϖ, ← WithZero.coe_pow, ← ofAdd_nsmul, smul_neg, nsmul_eq_mul, mul_one]
    have hr0v : Valued.v r0 ≠ 0 := by rw [hvr0]; exact WithZero.coe_ne_zero
    have hU : {y : v.adicCompletion F | Valued.v (y - x) ≤ Valued.v r0} ∈ 𝓝 x :=
      ((isOpen_ball F v hr0v).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
    refine (continuousWithinAt_const (b := B x)).congr_of_eventuallyEq ?_ rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with y hy hyO
    exact hB x hx y hyO (by rw [← hvr0]; exact hy)
  obtain ⟨M, hM⟩ := (isCompact_integers F v).exists_bound_of_continuousOn hcont
  exact ⟨max M 0, le_max_right _ _, fun y hy => (hM y hy).trans (le_max_left _ _)⟩

private theorem norm_modulus_cpow {u : v.adicCompletion F} (hu : u ≠ 0) (z : ℂ) :
    ‖(((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) : ℂ) ^ z‖ =
      ((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ^ z.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (modulus_pos_real F v hu) z

theorem main
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    let a : ℝ → v.adicCompletion F → ℂ := fun σ x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * B y⁻¹) x
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, a σ x ∂μ‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x, (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ x⁻¹ ∂μ)
          - ∫ x, a σ x ∂μ)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  intro a
  haveI hLC : LocallyCompactSpace (v.adicCompletion F) := inferInstance
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer F v
  have hAint := integrableOn_of_locallyConstantOn F v μ ϖ hϖ m A hA
  obtain ⟨MB, hMB0, hMB⟩ := exists_bound_on_integers F v ϖ hϖ m B (fun x _ y _ h => hB x y h)
  haveI := nhdsNE_zero_neBot F v
  have hO_meas : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := (isCompact_integers F v).isClosed.measurableSet

  set r : v.adicCompletion F → ℝ := fun u => ((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) with hr
  have hr_meas : Measurable fun u => ((r u : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (NNReal.continuous_coe.measurable.comp (continuous_modulus F v).measurable)

  have ha_int : ∀ σ : ℝ, 0 < σ → Integrable (a σ) μ := fun σ hσ =>
    integrable_atom F v μ m hm A B hAint hB (σ : ℂ) (by simpa using hσ)

  have htail : Integrable (fun x => (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (0 : ℂ)) x + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
      (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (((1 / 2 : ℝ) : ℂ)) + 1)) *
        (fun _ => (1 : ℂ)) y⁻¹) x) μ :=
    integrable_atom F v μ m hm (fun _ => 0) (fun _ => 1) integrableOn_zero (fun _ _ _ => rfl) ((1 / 2 : ℝ) : ℂ)
      (by simp)
  set g : v.adicCompletion F → ℝ := fun u => ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A u‖ + MB * ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (0 : ℂ)) u +
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (((1 / 2 : ℝ) : ℂ)) + 1)) *
        (fun _ => (1 : ℂ)) y⁻¹) u‖ with hg
  have hg_int : Integrable g μ := ((hAint.integrable_indicator hO_meas).norm).add ((htail.norm).const_mul MB)
  have htail_eval : ∀ u, u ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) → ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (0 : ℂ)) u +
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (((1 / 2 : ℝ) : ℂ)) + 1)) *
        (fun _ => (1 : ℂ)) y⁻¹) u‖ = r u ^ (-(2 : ℝ)) := by
    intro u hu
    rw [Set.indicator_of_notMem hu, Set.indicator_of_mem (Set.mem_compl hu), zero_add, mul_one,
      norm_modulus_cpow F v (ne_zero_of_not_mem F v hu)]
    congr 1
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.one_re]
    norm_num
  have hg_off : ∀ u, u ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) → g u = MB * r u ^ (-(2 : ℝ)) := by
    intro u hu
    rw [hg]
    beta_reduce
    rw [htail_eval u hu, Set.indicator_of_notMem hu, norm_zero, zero_add]
  have hg_on : ∀ u, u ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) → ‖A u‖ ≤ g u := by
    intro u hu
    rw [hg]
    beta_reduce
    rw [Set.indicator_of_mem hu]
    exact le_add_of_nonneg_right (mul_nonneg hMB0 (norm_nonneg _))

  have ha_off : ∀ σ : ℝ, 1 / 2 ≤ σ → ∀ u, u ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) → ‖a σ u‖ ≤ MB * r u ^ (-(2 : ℝ)) := by
    intro σ hσ u hu
    have hu0 := ne_zero_of_not_mem F v hu
    have hr1 : 1 < r u := one_lt_modulus_of_not_mem F v hu
    simp only [a, Set.indicator_of_notMem hu, Set.indicator_of_mem (Set.mem_compl hu), zero_add, norm_mul,
      norm_modulus_cpow F v hu0]
    have hre : (-(2 * (σ : ℂ) + 1)).re = -(2 * σ + 1) := by simp
    rw [hre]
    have hpow : r u ^ (-(2 * σ + 1)) ≤ r u ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hr1.le (by linarith)
    have hBu : ‖B u⁻¹‖ ≤ MB := hMB u⁻¹ (inv_mem_of_not_mem F v hu)
    calc r u ^ (-(2 * σ + 1)) * ‖B u⁻¹‖ ≤ r u ^ (-(2 : ℝ)) * MB :=
          mul_le_mul hpow hBu (norm_nonneg _) (Real.rpow_nonneg (lt_trans zero_lt_one hr1).le _)
      _ = MB * r u ^ (-(2 : ℝ)) := mul_comm _ _
  have ha_bound : ∀ σ : ℝ, 1 / 2 ≤ σ → ∀ u, ‖a σ u‖ ≤ g u := by
    intro σ hσ u
    by_cases hu : u ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · simp only [a, Set.indicator_of_mem hu, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hu), add_zero]
      exact hg_on u hu
    · rw [hg_off u hu]
      exact ha_off σ hσ u hu

  refine ⟨⟨∫ u, g u ∂μ, fun σ hσ _ => norm_integral_le_of_norm_le hg_int (Eventually.of_forall (ha_bound σ hσ.le))⟩, ?_⟩

  set w : ℝ → v.adicCompletion F → ℂ := fun σ u => ((r u : ℝ) : ℂ) ^ (2 * (σ : ℂ) - 1) with hw
  have hw_meas : ∀ σ, Measurable (w σ) := fun σ => hr_meas.pow_const _
  have hT2 : ∀ σ : ℝ,
      ∫ x, (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ x⁻¹ ∂μ =
        ∫ u, ((((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) •
          ((((LanglandsTunnell.TateLocal.modulus u⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ u) ∂μ := by
    intro σ
    have h := LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion F v μ
      (fun u => (((LanglandsTunnell.TateLocal.modulus u⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ u)
    simpa only [inv_inv] using h
  have hsimp : ∀ σ : ℝ, 1 / 2 < σ → ∀ u,
      ((((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) •
          ((((LanglandsTunnell.TateLocal.modulus u⁻¹ : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ u) =
        w σ u * a σ u := by
    intro σ hσ u
    by_cases hu0 : u = 0
    · subst hu0
      have hexp : (2 * (σ : ℂ) - 1) ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hw0 : w σ 0 = 0 := by
        simp only [hw, hr, LanglandsTunnell.TateLocal.modulus_zero, NNReal.coe_zero, Complex.ofReal_zero]
        exact Complex.zero_cpow hexp
      rw [hw0, zero_mul, LanglandsTunnell.TateLocal.modulus_zero, NNReal.coe_zero]
      simp
    · have hr0 : 0 < r u := modulus_pos_real F v hu0
      have hinv : ((LanglandsTunnell.TateLocal.modulus u⁻¹ : ℝ≥0) : ℝ) = (r u)⁻¹ := by
        have h1 := modulus_mul_modulus_inv F v hu0
        have h' : r u * ((LanglandsTunnell.TateLocal.modulus u⁻¹ : ℝ≥0) : ℝ) = 1 := by
          show ((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) * ((LanglandsTunnell.TateLocal.modulus u⁻¹ : ℝ≥0) : ℝ) = 1
          exact_mod_cast h1
        exact eq_inv_of_mul_eq_one_right h'
      have hne : ((r u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
      have harg : ((r u : ℝ) : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hr0.le]
        exact Real.pi_ne_zero.symm
      rw [hinv, Complex.real_smul, ← mul_assoc]
      congr 1
      change ((((r u : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * (((r u)⁻¹ : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) =
        ((r u : ℝ) : ℂ) ^ (2 * (σ : ℂ) - 1)
      rw [Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_pow, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg,
        neg_neg, show (((r u : ℝ) : ℂ) ^ 2)⁻¹ = ((r u : ℝ) : ℂ) ^ (-2 : ℂ) by rw [Complex.cpow_neg, Complex.cpow_two],
        ← Complex.cpow_add _ _ hne]
      congr 1
      ring

  have hwa_bound : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ∀ u, ‖w σ u * a σ u‖ ≤ g u := by
    intro σ hσ hσ1 u
    by_cases hu : u ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    · have hw1 : ‖w σ u‖ ≤ 1 := by
        by_cases hu0 : u = 0
        · have hexp : (2 * (σ : ℂ) - 1) ≠ 0 := by
            intro h
            have := congrArg Complex.re h
            simp at this
            linarith
          simp only [hw, hr, hu0, LanglandsTunnell.TateLocal.modulus_zero, NNReal.coe_zero, Complex.ofReal_zero,
            Complex.zero_cpow hexp, norm_zero]
          exact zero_le_one
        · rw [hw, norm_modulus_cpow F v hu0]
          have hre : (2 * (σ : ℂ) - 1).re = 2 * σ - 1 := by simp
          rw [hre]
          exact Real.rpow_le_one (modulus_pos_real F v hu0).le (modulus_le_one_of_mem F v hu) (by linarith)
      calc ‖w σ u * a σ u‖ = ‖w σ u‖ * ‖a σ u‖ := norm_mul _ _
        _ ≤ 1 * ‖a σ u‖ := mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
        _ = ‖a σ u‖ := one_mul _
        _ ≤ g u := ha_bound σ hσ.le u
    · have hu0 := ne_zero_of_not_mem F v hu
      have hr1 := one_lt_modulus_of_not_mem F v hu
      rw [hg_off u hu]
      simp only [a, Set.indicator_of_notMem hu, Set.indicator_of_mem (Set.mem_compl hu), zero_add, norm_mul, hw, hr,
        norm_modulus_cpow F v hu0]
      have hre1 : (2 * (σ : ℂ) - 1).re = 2 * σ - 1 := by simp
      have hre2 : (-(2 * (σ : ℂ) + 1)).re = -(2 * σ + 1) := by simp
      rw [hre1, hre2, ← mul_assoc, ← Real.rpow_add (lt_trans zero_lt_one hr1),
        show 2 * σ - 1 + -(2 * σ + 1) = -(2 : ℝ) by ring]
      calc r u ^ (-(2 : ℝ)) * ‖B u⁻¹‖ ≤ r u ^ (-(2 : ℝ)) * MB :=
            mul_le_mul_of_nonneg_left (hMB _ (inv_mem_of_not_mem F v hu)) (Real.rpow_nonneg (lt_trans zero_lt_one hr1).le _)
        _ = MB * r u ^ (-(2 : ℝ)) := mul_comm _ _
  have hwa_int : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → Integrable (fun u => w σ u * a σ u) μ := fun σ hσ hσ1 =>
    Integrable.mono' hg_int ((hw_meas σ).aestronglyMeasurable.mul (ha_int σ (by linarith)).aestronglyMeasurable)
      (Eventually.of_forall (hwa_bound σ hσ hσ1))

  set Fσ : ℝ → v.adicCompletion F → ℂ := fun σ u => (w σ u - 1) * a σ u with hF
  have hdiff : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 →
      (∫ x, (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ x⁻¹ ∂μ)
          - ∫ x, a σ x ∂μ = ∫ u, Fσ σ u ∂μ := by
    intro σ hσ hσ1
    rw [hT2 σ, integral_congr_ae (Eventually.of_forall (hsimp σ hσ)),
      ← integral_sub (hwa_int σ hσ hσ1) (ha_int σ (by linarith))]
    congr 1
    funext u
    simp only [hF]
    ring

  have hF_bound : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ∀ u, ‖Fσ σ u‖ ≤ 2 * g u := by
    intro σ hσ hσ1 u
    have h1 : Fσ σ u = w σ u * a σ u - a σ u := by simp only [hF]; ring
    calc ‖Fσ σ u‖ = ‖w σ u * a σ u - a σ u‖ := by rw [h1]
      _ ≤ ‖w σ u * a σ u‖ + ‖a σ u‖ := norm_sub_le _ _
      _ ≤ g u + g u := add_le_add (hwa_bound σ hσ hσ1 u) (ha_bound σ hσ.le u)
      _ = 2 * g u := by ring
  have hF_meas : ∀ σ : ℝ, 0 < σ → AEStronglyMeasurable (Fσ σ) μ := fun σ hσ =>
    ((hw_meas σ).aestronglyMeasurable.sub aestronglyMeasurable_const).mul (ha_int σ hσ).aestronglyMeasurable
  have hF_lim : ∀ u, u ≠ 0 → Tendsto (fun σ : ℝ => Fσ σ u) (𝓝 (1 / 2 : ℝ)) (𝓝 0) := by
    intro u hu0
    have hne : ((r u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (modulus_pos_real F v hu0).ne'
    have hlin : Continuous fun σ : ℝ => 2 * (σ : ℂ) - 1 := by fun_prop
    have hlin' : Continuous fun σ : ℝ => -(2 * (σ : ℂ) + 1) := by fun_prop
    have hcw : Continuous fun σ : ℝ => w σ u := by
      simp only [hw]
      exact hlin.const_cpow (Or.inl hne)
    have hca : Continuous fun σ : ℝ => a σ u := by
      by_cases hu : u ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      · simp only [a, Set.indicator_of_mem hu, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hu), add_zero]
        exact continuous_const
      · simp only [a, Set.indicator_of_notMem hu, Set.indicator_of_mem (Set.mem_compl hu), zero_add]
        exact (hlin'.const_cpow (Or.inl hne)).mul continuous_const
    have hcF : Continuous fun σ : ℝ => Fσ σ u := by
      simp only [hF]
      exact (hcw.sub continuous_const).mul hca
    have h0 : Fσ (1 / 2) u = 0 := by
      simp only [hF, hw]
      have : (2 * (((1 / 2 : ℝ)) : ℂ) - 1) = 0 := by push_cast; ring
      rw [this, Complex.cpow_zero, sub_self, zero_mul]
    have ht := hcF.tendsto (1 / 2)
    rwa [h0] at ht
  have hDCT : Tendsto (fun σ : ℝ => ∫ u, Fσ σ u ∂μ) (𝓝[>] (1 / 2 : ℝ)) (𝓝 (∫ u, (fun _ => (0 : ℂ)) u ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => 2 * g u) ?_ ?_ (hg_int.const_mul 2) ?_
    · filter_upwards [Ioc_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with σ hσ
      exact hF_meas σ (by linarith [hσ.1])
    · filter_upwards [Ioc_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with σ hσ
      exact Eventually.of_forall (hF_bound σ hσ.1 hσ.2)
    · have h0 : μ {(0 : v.adicCompletion F)} = 0 := measure_singleton 0
      filter_upwards [compl_mem_ae_iff.mpr h0] with u hu
      exact (hF_lim u (Set.mem_compl_singleton_iff.mp hu)).mono_left nhdsWithin_le_nhds
  rw [integral_zero] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (show (1 / 2 : ℝ) < 1 by norm_num)] with σ hσ
  exact (hdiff σ hσ.1 hσ.2).symm

end AutomorphicForm.LocalIntertwining.W3

end

theorem solution
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (_hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (_hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (_hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    let a : ℝ → v.adicCompletion F → ℂ := fun σ x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * B y⁻¹) x
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, a σ x ∂μ‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x, (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ x⁻¹ ∂μ)
          - ∫ x, a σ x ∂μ)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) :=
  AutomorphicForm.LocalIntertwining.W3.main F v μ m _hm A B _hA _hB

end S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
end P2MW
export P2MW.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion (solution)
