-- Prove2me | Definitions.Def_OAIQ021F002
-- name    : OAIQ021F002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T18:08:28.720049+00:00
-- url     : https://prove2.me/theorems/abab3696-3e2a-4fe8-a9fb-856c86f0d03f
-- title:
--   Definitions bundle OAIQ021F002 of the split of OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FKCRT.finite_fk_maps_converge_to_brownian_crt`, carved from OpenAI's openai/math development (OpenAI, *Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211)*, OpenAI Math Release, September 24, 2026, result family 211, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 742 declarations of OpenAI's Lean: 149 definitions, 2 inductive types or structures, 16 instances and 575 theorems. The definitions and types are `OAI.FKCRT.Inventory.CoreLabel.markLaw`, `OAI.FKCRT.Inventory.CoreLabel.rootLaw`, `OAI.FKCRT.Inventory.CoreTree`, `OAI.FKCRT.Inventory.CoreTree.Dart`, `OAI.FKCRT.Inventory.CoreTree.LabelExcursion`, `OAI.FKCRT.Inventory.CoreTree.MarkedCode`, `OAI.FKCRT.Inventory.CoreTree.Node`, `OAI.FKCRT.Inventory.CoreTree.Sized`, `OAI.FKCRT.Inventory.CoreTree.SizedWord`, `OAI.FKCRT.Inventory.CoreTree.VertexConstant`, `OAI.FKCRT.Inventory.CoreTree.after`, `OAI.FKCRT.Inventory.CoreTree.assemble`, `OAI.FKCRT.Inventory.CoreTree.before`, `OAI.FKCRT.Inventory.CoreTree.build`, `OAI.FKCRT.Inventory.CoreTree.childDart`, `OAI.FKCRT.Inventory.CoreTree.childPole`, `OAI.FKCRT.Inventory.CoreTree.coreDart`, `OAI.FKCRT.Inventory.CoreTree.dartLabel`, `OAI.FKCRT.Inventory.CoreTree.darts`, `OAI.FKCRT.Inventory.CoreTree.labels`, `OAI.FKCRT.Inventory.CoreTree.matching`, `OAI.FKCRT.Inventory.CoreTree.nextSlot`, `OAI.FKCRT.Inventory.CoreTree.nodeIndex`, `OAI.FKCRT.Inventory.CoreTree.pole`, `OAI.FKCRT.Inventory.CoreTree.word`, `OAI.FKCRT.Inventory.D`, `OAI.FKCRT.Inventory.Dsum`, `OAI.FKCRT.Inventory.Evaluation.flip`, `OAI.FKCRT.Inventory.FixedWord`, `OAI.FKCRT.Inventory.FlexiblePrefix`, `OAI.FKCRT.Inventory.GoodLeft`, `OAI.FKCRT.Inventory.GoodRight`, `OAI.FKCRT.Inventory.K`, `OAI.FKCRT.Inventory.LeftCut`, `OAI.FKCRT.Inventory.Letter.flip`, `OAI.FKCRT.Inventory.Letter.typeNet`, `OAI.FKCRT.Inventory.NonemptyPieces`, `OAI.FKCRT.Inventory.PieceBuffer`, `OAI.FKCRT.Inventory.RightCut`, `OAI.FKCRT.Inventory.StackMatching.distance` and 111 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability/FKMaps, in whole or in part: `FKMaps_BlockCritical`, `FKMaps_BlockLaw`, `FKMaps_ConditionedTrees`, `FKMaps_CoreCompression`, `FKMaps_CoreMetric`, `FKMaps_CornerMass`, `FKMaps_ExcursionKernel`, `FKMaps_Inventory`, `FKMaps_InventoryDrift`, `FKMaps_InventoryRenewal`, `FKMaps_InventoryStopping`, `FKMaps_LadderCuts`, `FKMaps_NodeMetric`, `FKMaps_NodeOrder`, `FKMaps_Offspring`, `FKMaps_PieceLaws`, `FKMaps_PieceWalks`, `FKMaps_PlaneTrees`, `FKMaps_SeamLengths`, `FKMaps_SimpleWalk`, `FKMaps_SpineMoments`, `FKMaps_StationaryCuts`, `FKMaps_TreeCode`, `FKMaps_UniformSeams`, `FKMaps_WordCoefficients`, `FKMaps_WordLaw`.
--
--   **Imports.** It imports the bundles `OAIQ021F000` and `OAIQ021F001` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ021F004`; the statement `OAI_FKCRT_Inventory_metricBad_limit`; the proof of `OAI_FKCRT_Inventory_metricBad_limit`.
-- source:
--   OpenAI, Brownian continuum random tree limits of finite Fortuin–Kasteleyn maps above four (result family 211), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 211; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brownian-continuum-random-tree-limits-of-finite-Fortuin-Kasteleyn-maps-above-four-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/FKMaps at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ021F000
import Definitions.Def_OAIQ021F001

section
-- module Solutions.OAIQ021_FK.FKMaps_Offspring
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


def CriticalEvenOffspring.variance (p : CriticalEvenOffspring) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) - 1)^2 * p.mass k


def CriticalEvenOffspring.sigma (p : CriticalEvenOffspring) : ℝ :=
  Real.sqrt p.variance


lemma CriticalEvenOffspring.summable_variance (p : CriticalEvenOffspring) :
    Summable (fun k : ℕ => ((k : ℝ) - 1)^2 * p.mass k) := by
  apply Summable.of_nonneg_of_le (fun k : ℕ => mul_nonneg (sq_nonneg _) (p.nonneg k))
    (f := fun k : ℕ => (k : ℝ)^2 * p.mass k + p.mass k)
  · intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [p.nonneg k, mul_nonneg hk (p.nonneg k)]
  · exact p.second.add p.total.summable


lemma CriticalEvenOffspring.variance_pos (p : CriticalEvenOffspring) : 0 < p.variance := by
  have hle := p.summable_variance.le_tsum 0
    (fun k _ => mul_nonneg (sq_nonneg _) (p.nonneg k))
  simp only [Nat.cast_zero, zero_sub, neg_sq, one_pow, one_mul] at hle
  exact p.zero_pos.trans_le hle


lemma CriticalEvenOffspring.sigma_pos (p : CriticalEvenOffspring) : 0 < p.sigma :=
  Real.sqrt_pos.mpr p.variance_pos


lemma CriticalEvenOffspring.integrable_iff {E : Type*} [NormedAddCommGroup E]
    (p : CriticalEvenOffspring) (f : ℕ → E) :
    Integrable f p.law.toMeasure ↔ Summable (fun k => p.mass k * ‖f k‖) := by
  rw [← Measure.sum_smul_dirac p.law.toMeasure, integrable_sum_dirac_iff]
  · simp only [p.law_singleton, ENNReal.toReal_ofReal (p.nonneg _)]
  · intro k
    simp


lemma CriticalEvenOffspring.integral_eq_tsum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : CriticalEvenOffspring) (f : ℕ → E)
    (hf : Summable (fun k => p.mass k * ‖f k‖)) :
    ∫ k, f k ∂p.law.toMeasure = ∑' k, p.mass k • f k := by
  rw [integral_countable ((p.integrable_iff f).mpr hf)]
  simp only [p.law_real_singleton]


lemma CriticalEvenOffspring.integrable_id (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k : ℝ)) p.law.toMeasure := by
  apply (p.integrable_iff _).mpr
  simpa [Real.norm_natCast, mul_comm] using p.mean.summable


lemma CriticalEvenOffspring.integral_id (p : CriticalEvenOffspring) :
    ∫ k : ℕ, (k : ℝ) ∂p.law.toMeasure = 1 := by
  rw [integral_countable p.integrable_id]
  simpa [mul_comm] using p.mean.tsum_eq


lemma CriticalEvenOffspring.integral_step (p : CriticalEvenOffspring) :
    ∫ k : ℕ, ((k : ℝ) - 1) ∂p.law.toMeasure = 0 := by
  rw [integral_sub p.integrable_id (integrable_const 1), p.integral_id]
  simp


lemma CriticalEvenOffspring.integrable_step_sq (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => ((k : ℝ) - 1)^2) p.law.toMeasure := by
  apply (p.integrable_iff _).mpr
  simpa [Real.norm_eq_abs, abs_sq, mul_comm] using p.summable_variance


lemma CriticalEvenOffspring.integral_step_sq (p : CriticalEvenOffspring) :
    ∫ k : ℕ, ((k : ℝ) - 1)^2 ∂p.law.toMeasure = p.variance := by
  rw [integral_countable p.integrable_step_sq]
  simp only [p.law_real_singleton, smul_eq_mul, variance, mul_comm]


def CriticalEvenOffspring.standardStep (p : CriticalEvenOffspring) (k : ℕ) : ℝ :=
  ((k : ℝ) - 1) / p.sigma


lemma CriticalEvenOffspring.integral_standardStep (p : CriticalEvenOffspring) :
    ∫ k, p.standardStep k ∂p.law.toMeasure = 0 := by
  simp [standardStep, integral_div, p.integral_step]


lemma CriticalEvenOffspring.integral_standardStep_sq (p : CriticalEvenOffspring) :
    ∫ k, p.standardStep k ^ 2 ∂p.law.toMeasure = 1 := by
  simp only [standardStep, div_pow, integral_div, p.integral_step_sq, sigma,
    Real.sq_sqrt p.variance_pos.le, div_self p.variance_pos.ne']


lemma CriticalEvenOffspring.charFun_power_limit (p : CriticalEvenOffspring) (t : ℝ) :
    Tendsto (fun n : ℕ =>
      (charFun (p.law.toMeasure.map p.standardStep) ((Real.sqrt n)⁻¹ * t)) ^ n)
      atTop (𝓝 (Complex.exp (- (t : ℂ)^2 / 2))) := by
  exact tendsto_charFun_inv_sqrt_mul_pow
    (by fun_prop) p.integral_standardStep p.integral_standardStep_sq t


lemma CriticalEvenOffspring.charFun_gaussian_bound (p : CriticalEvenOffspring) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| ≤ δ →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ Real.exp (-t^2/4) := by
  have ho := taylor_charFun_two (P := p.law.toMeasure) (X := p.standardStep)
    (by fun_prop) p.integral_standardStep p.integral_standardStep_sq
  have hb := ho.bound (by norm_num : (0 : ℝ) < 1/4)
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨min (r/2) 1, lt_min (by positivity) zero_lt_one, ?_⟩
  intro t ht
  have ht1 : |t| ≤ 1 := ht.trans (min_le_right _ _)
  have htr : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero]
    exact (ht.trans (min_le_left _ _)).trans_lt (by linarith)
  have hsq : t^2 ≤ 1 := (sq_le_one_iff_abs_le_one t).mpr ht1
  have he := hbound htr
  have hn : ‖(1 - (t : ℂ)^2 / 2)‖ = 1 - t^2/2 := by
    have heq : (1 - (t : ℂ)^2 / 2) = ((1 - t^2/2 : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at he
  calc
    ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤
        ‖charFun (p.law.toMeasure.map p.standardStep) t - (1 - (t : ℂ)^2/2)‖ +
          ‖1 - (t : ℂ)^2/2‖ := by
      simpa only [add_comm] using (norm_le_insert'
        (charFun (p.law.toMeasure.map p.standardStep) t) (1 - (t : ℂ)^2/2))
    _ ≤ 1 - t^2/4 := by rw [hn]; linarith
    _ ≤ Real.exp (-t^2/4) := by
      linarith [Real.add_one_le_exp (-t^2/4)]


def CriticalEvenOffspring.iidLaw (p : CriticalEvenOffspring) (N : ℕ) :
    Measure (Fin N → ℕ) := Measure.pi (fun _ : Fin N => p.law.toMeasure)


instance instIsProbabilityMeasureForallFinNatIidLaw (p : CriticalEvenOffspring) (N : ℕ) : IsProbabilityMeasure (p.iidLaw N) := by
  unfold CriticalEvenOffspring.iidLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)


lemma CriticalEvenOffspring.ae_even (p : CriticalEvenOffspring) :
    ∀ᵐ k ∂p.law.toMeasure, Even k := by
  rw [ae_iff, p.law.toMeasure_apply_eq_zero_iff (by measurability), Set.disjoint_left]
  intro k hk hn
  have hzero : p.law k = 0 := by
    rw [p.law_apply, p.even_support k (Nat.not_even_iff_odd.mp hn), ENNReal.ofReal_zero]
  exact (p.law.mem_support_iff k).mp hk hzero


lemma CriticalEvenOffspring.iid_ae_even (p : CriticalEvenOffspring) (N : ℕ) :
    ∀ᵐ d ∂p.iidLaw N, ∀ i, Even (d i) := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin N => p.law.toMeasure) i).quasiMeasurePreserving.ae p.ae_even


lemma CriticalEvenOffspring.iid_totalStep_parity (p : CriticalEvenOffspring) (N : ℕ)
    {j : ℤ} (hj : Even ((N : ℤ) + j)) :
    ∀ᵐ d ∂p.iidLaw N, Even (totalStep d - j) := by
  filter_upwards [p.iid_ae_even N] with d hd
  rw [totalStep_eq_sum_sub, sub_sub]
  apply Even.sub _ hj
  exact_mod_cast Finset.even_sum d (fun i _ => hd i)


lemma CriticalEvenOffspring.iid_marginal_map (p : CriticalEvenOffspring) (N : ℕ)
    (i : Fin N) (f : ℕ → ℝ) :
    (p.iidLaw N).map (fun d => f (d i)) = p.law.toMeasure.map f := by
  have hf : Measurable f := measurable_of_countable f
  rw [← (measurePreserving_eval (fun _ : Fin N => p.law.toMeasure) i).map_eq,
    Measure.map_map hf (measurable_pi_apply i)]
  rfl


lemma CriticalEvenOffspring.charFun_step_scale (p : CriticalEvenOffspring) (t : ℝ) :
    charFun (p.law.toMeasure.map (fun k : ℕ => (k : ℝ) - 1)) t =
      charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t) := by
  rw [charFun_apply_real, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
  congr 1
  ext k
  congr 2
  simp only [standardStep]
  push_cast
  field_simp [p.sigma_pos.ne']


lemma CriticalEvenOffspring.iid_charFun (p : CriticalEvenOffspring) (N : ℕ) (t : ℝ) :
    charFun ((p.iidLaw N).map (fun d => (totalStep d : ℝ))) t =
      (charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t))^N := by
  have heq : (fun d : Fin N → ℕ => (totalStep d : ℝ)) =
      fun d => ∑ i, ((d i : ℝ) - 1) := by
    ext d
    simp [totalStep]
  rw [heq]
  have hind : iIndepFun (fun i (d : Fin N → ℕ) => (d i : ℝ) - 1) (p.iidLaw N) :=
    iIndepFun_pi (μ := fun _ : Fin N => p.law.toMeasure)
      (X := fun _ k => (k : ℝ) - 1) (fun _ => by fun_prop)
  have hm (i : Fin N) : AEMeasurable (fun d : Fin N → ℕ => (d i : ℝ) - 1) (p.iidLaw N) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ) - 1)).comp
      (measurable_pi_apply i)).aemeasurable
  rw [congrFun (hind.charFun_map_fun_sum_eq_prod hm) t]
  simp only [Finset.prod_apply]
  simp_rw [p.iid_marginal_map N _ (fun k : ℕ => (k : ℝ) - 1), p.charFun_step_scale]
  simp


lemma CriticalEvenOffspring.charFun_tsum (p : CriticalEvenOffspring) (t : ℝ) :
    charFun (p.law.toMeasure.map p.standardStep) t =
      ∑' k, p.mass k • Complex.exp ((t * p.standardStep k : ℝ) * Complex.I) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  simp only [← Complex.ofReal_mul]
  apply p.integral_eq_tsum
  simpa only [Complex.norm_exp_ofReal_mul_I, mul_one] using p.total.summable


lemma CriticalEvenOffspring.charFun_lt_one (p : CriticalEvenOffspring) {t : ℝ}
    (ht : t ≠ 0) (hbound : |t| ≤ p.sigma * Real.pi / 2) :
    ‖charFun (p.law.toMeasure.map p.standardStep) t‖ < 1 := by
  rw [p.charFun_tsum]
  apply norm_tsum_smul_lt_one p.mass p.nonneg p.total
    (fun k => Complex.exp ((t * p.standardStep k : ℝ) * Complex.I))
    (fun k => Complex.norm_exp_ofReal_mul_I _) (by norm_num : (0 : ℕ) ≠ 2)
    p.zero_pos p.two_pos
  intro he
  have hts : |t / p.sigma| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos p.sigma_pos, div_le_iff₀ p.sigma_pos]
    nlinarith [hbound]
  have hli : -Real.pi < -(t / p.sigma) := by
    have := (abs_le.mp hts).2
    linarith [Real.pi_pos]
  have hui : -(t / p.sigma) ≤ Real.pi := by
    have := (abs_le.mp hts).1
    linarith [Real.pi_pos]
  have hlj : -Real.pi < t / p.sigma := by
    have := (abs_le.mp hts).1
    linarith [Real.pi_pos]
  have huj : t / p.sigma ≤ Real.pi := by
    have := (abs_le.mp hts).2
    linarith [Real.pi_pos]
  have h0 : t * p.standardStep 0 = -(t / p.sigma) := by simp [standardStep, div_eq_mul_inv]
  have h2 : t * p.standardStep 2 = t / p.sigma := by norm_num [standardStep, div_eq_mul_inv]
  rw [h0, h2] at he
  have hx := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hli) (by simpa using hui)
    (by simpa using hlj) (by simpa using huj) he
  have hi := congrArg Complex.im hx
  simp only [Complex.mul_I_im, Complex.ofReal_re] at hi
  have hz : t / p.sigma = 0 := by linarith
  exact ht ((div_eq_zero_iff).mp hz |>.resolve_right p.sigma_pos.ne')


lemma CriticalEvenOffspring.charFun_compact_gap (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ t : ℝ,
      ε ≤ |t| → |t| ≤ p.sigma * Real.pi / 2 →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ ρ := by
  let K := {t : ℝ | ε ≤ |t| ∧ |t| ≤ p.sigma * Real.pi / 2}
  have hcompact : IsCompact K := by
    apply (isCompact_Icc (a := -(p.sigma * Real.pi / 2))
      (b := p.sigma * Real.pi / 2)).of_isClosed_subset
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · intro t ht
      exact abs_le.mp ht.2
  by_cases hne : K.Nonempty
  · obtain ⟨t, ht, hmax⟩ := hcompact.exists_isMaxOn hne
      ((continuous_charFun (μ := p.law.toMeasure.map p.standardStep)).norm.continuousOn)
    refine ⟨‖charFun (p.law.toMeasure.map p.standardStep) t‖, norm_nonneg _, ?_, ?_⟩
    · apply p.charFun_lt_one _ ht.2
      intro hz
      have := ht.1
      simp only [hz, abs_zero] at this
      linarith
    · intro u hu hu'
      exact hmax ⟨hu, hu'⟩
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro t ht ht'
    exact (hne ⟨t, ht, ht'⟩).elim


lemma CriticalEvenOffspring.charFun_global_gaussian (p : CriticalEvenOffspring) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |t| ≤ p.sigma * Real.pi / 2 →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ Real.exp (-c * t^2) := by
  obtain ⟨δ, hδ, hlocal⟩ := p.charFun_gaussian_bound
  obtain ⟨ρ, _, hρ, hgap⟩ := p.charFun_compact_gap hδ
  let a := p.sigma * Real.pi / 2
  have ha : 0 < a := div_pos (mul_pos p.sigma_pos Real.pi_pos) (by norm_num)
  let c := min (1/4 : ℝ) ((1-ρ)/a^2)
  have hc : 0 < c := lt_min (by norm_num) (div_pos (sub_pos.mpr hρ) (sq_pos_of_pos ha))
  refine ⟨c, hc, ?_⟩
  intro t ht
  by_cases hsmall : |t| ≤ δ
  · refine (hlocal t hsmall).trans (Real.exp_le_exp.mpr ?_)
    have := mul_le_mul_of_nonneg_right (min_le_left (1/4 : ℝ) ((1-ρ)/a^2)) (sq_nonneg t)
    change c * t^2 ≤ (1/4 : ℝ) * t^2 at this
    linarith
  · have hta : t^2 ≤ a^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) ha.le).mpr ht
    have hca : c * a^2 ≤ 1-ρ := by
      have h := min_le_right (1/4 : ℝ) ((1-ρ)/a^2)
      exact (le_div_iff₀ (sq_pos_of_pos ha)).mp h
    have hct := mul_le_mul_of_nonneg_left hta hc.le
    refine (hgap t (le_of_lt (lt_of_not_ge hsmall)) ht).trans ?_
    have hexp := Real.add_one_le_exp (-c*t^2)
    linarith


def CriticalEvenOffspring.fourierCutoff (p : CriticalEvenOffspring) (n : ℕ) (t : ℝ) : ℂ :=
  if |t| ≤ (p.sigma * Real.pi / 2) * Real.sqrt (n+1) then
    (charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1)))^(n+1)
  else 0


lemma CriticalEvenOffspring.cutoff_measurable (p : CriticalEvenOffspring) (n : ℕ) :
    Measurable (p.fourierCutoff n) := by
  apply Measurable.ite (measurableSet_le measurable_abs measurable_const)
  · exact ((continuous_charFun.comp (continuous_id.div_const _)).pow _).measurable
  · exact measurable_const


lemma CriticalEvenOffspring.cutoff_pointwise (p : CriticalEvenOffspring) (t : ℝ) :
    Tendsto (fun n => p.fourierCutoff n t) atTop
      (𝓝 (Complex.exp (-(t:ℂ)^2/2))) := by
  have ha : 0 < p.sigma * Real.pi / 2 := div_pos (mul_pos p.sigma_pos Real.pi_pos) (by norm_num)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n+1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hbound : ∀ᶠ n : ℕ in atTop, |t| ≤ (p.sigma * Real.pi / 2) * Real.sqrt (n+1) :=
    (hsqrt.const_mul_atTop ha).eventually_ge_atTop |t|
  have hp := (p.charFun_power_limit t).comp (tendsto_add_atTop_nat 1)
  apply hp.congr'
  filter_upwards [hbound] with n hn
  rw [fourierCutoff, ite_eq_left hn]
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]


lemma CriticalEvenOffspring.cutoff_gaussian_bound (p : CriticalEvenOffspring)
    {c : ℝ} (hg : ∀ t : ℝ, |t| ≤ p.sigma * Real.pi / 2 →
      ‖charFun (p.law.toMeasure.map p.standardStep) t‖ ≤ Real.exp (-c*t^2))
    (n : ℕ) (t : ℝ) : ‖p.fourierCutoff n t‖ ≤ Real.exp (-c*t^2) := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hs : 0 < Real.sqrt (n+1) := Real.sqrt_pos.mpr hn
  unfold fourierCutoff
  split_ifs with ht
  · rw [norm_pow]
    have hb : |t / Real.sqrt (n+1)| ≤ p.sigma * Real.pi / 2 := by
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      exact ht
    calc
      ‖charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1))‖^(n+1) ≤
          (Real.exp (-c*(t / Real.sqrt (n+1))^2))^(n+1) :=
        pow_le_pow_left₀ (norm_nonneg _) (hg _ hb) _
      _ = Real.exp (-c*t^2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [div_pow, Real.sq_sqrt hn.le, Nat.cast_add, Nat.cast_one]
        field_simp
  · simp only [norm_zero]
    exact (Real.exp_pos _).le


lemma CriticalEvenOffspring.cutoff_L1_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => ∫ t : ℝ,
      ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖)
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  let bound : ℝ → ℝ := fun t => Real.exp (-c*t^2) + Real.exp (-(1/2:ℝ)*t^2)
  have hnorm (t : ℝ) : ‖Complex.exp (-(t:ℂ)^2/2)‖ = Real.exp (-(1/2:ℝ)*t^2) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.div_ofNat]
    ring
  have hd := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun n t => ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖)
    (f := fun _ => (0:ℝ)) bound
    (fun n => ((p.cutoff_measurable n).sub (by fun_prop)).norm.aestronglyMeasurable)
    ((integrable_exp_neg_mul_sq hc).add (integrable_exp_neg_mul_sq (by norm_num)))
    (fun n => ae_of_all _ fun t => ?_)
    (ae_of_all _ fun t => ?_)
  · simpa using hd
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (add_le_add (p.cutoff_gaussian_bound hg n t) (hnorm t).le)
  · exact tendsto_iff_norm_sub_tendsto_zero.mp (p.cutoff_pointwise t)


lemma integral_exp_even_int (k : ℤ) :
    (∫ t : ℝ in -(Real.pi / 2)..Real.pi / 2,
      Complex.exp ((2 * k : ℂ) * t * Complex.I)) =
        if k = 0 then (Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, ite_true,
      intervalIntegral.integral_const, sub_neg_eq_add, Complex.real_smul]
    push_cast
    ring
  · rw [ite_eq_right hk]
    have hc : (2 * k : ℂ) * Complex.I ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hk)) Complex.I_ne_zero
    simp_rw [mul_right_comm (2 * (k : ℂ)) _ Complex.I]
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp (((2 * k : ℂ) * Complex.I) * (Real.pi / 2 : ℝ)) =
        Complex.exp (((2 * k : ℂ) * Complex.I) * (-(Real.pi / 2) : ℝ)) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨k, ?_⟩
      push_cast
      ring
    rw [he, sub_self, zero_div]


lemma integral_exp_even_int' {k : ℤ} (hk : Even k) :
    (∫ t : ℝ in -(Real.pi / 2)..Real.pi / 2,
      Complex.exp ((k : ℂ) * t * Complex.I)) =
        if k = 0 then (Real.pi : ℂ) else 0 := by
  obtain ⟨r, rfl⟩ := hk
  convert integral_exp_even_int r using 1 <;> simp [two_mul]


lemma spanTwo_inversion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℤ) (hX : Measurable X)
    (j : ℤ) (hj : ∀ᵐ ω ∂P, Even (X ω - j)) :
    (∫ t : ℝ in -(Real.pi / 2)..Real.pi / 2,
      Complex.exp (-(j : ℂ) * t * Complex.I) *
        charFun (P.map (fun ω => (X ω : ℝ))) t) =
      (Real.pi : ℂ) * (P.real {ω | X ω = j} : ℂ) := by
  let f : ℝ → Ω → ℂ := fun t ω => Complex.exp (((X ω - j : ℤ) : ℂ) * t * Complex.I)
  have hmeas : Measurable (Function.uncurry f) := by
    dsimp [f, Function.uncurry]
    fun_prop
  let : IsFiniteMeasure (volume.restrict (uIoc (-(Real.pi/2)) (Real.pi/2))) :=
    ⟨by simp⟩
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc (-(Real.pi/2)) (Real.pi/2))).prod P) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      dsimp [f, Function.uncurry]
      have : ((X z.2 - j : ℤ) : ℂ) * z.1 = (((X z.2 - j : ℤ) : ℝ) * z.1 : ℝ) := by
        push_cast
        rfl
      rw [this, Complex.norm_exp_ofReal_mul_I]
  have hinner (t : ℝ) : Complex.exp (-(j : ℂ) * t * Complex.I) *
      charFun (P.map (fun ω => (X ω : ℝ))) t = ∫ ω, f t ω ∂P := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by
      dsimp [f]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
  simp_rw [hinner]
  rw [intervalIntegral_integral_swap hint]
  have hcalc : (fun ω => ∫ t in -(Real.pi/2)..Real.pi/2, f t ω) =ᵐ[P]
      fun ω => if X ω = j then (Real.pi : ℂ) else 0 := by
    filter_upwards [hj] with ω hω
    dsimp [f]
    rw [integral_exp_even_int' hω]
    simp only [sub_eq_zero]
  rw [integral_congr_ae hcalc]
  have hm : MeasurableSet {ω | X ω = j} := hX (measurableSet_singleton j)
  have heq : (fun ω => if X ω = j then (Real.pi : ℂ) else 0) =
      {ω | X ω = j}.indicator (fun _ => (Real.pi : ℂ)) := by
    ext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator hm, integral_const]
  simp [Measure.real, Complex.real_smul, mul_comm]


def CriticalEvenOffspring.siteFourier (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) (t : ℝ) : ℂ :=
  p.fourierCutoff n t * Complex.exp ((-(j : ℝ) * t /
    (p.sigma * Real.sqrt (n+1)) : ℝ) * Complex.I)


lemma CriticalEvenOffspring.siteFourier_integral (p : CriticalEvenOffspring) (n : ℕ) (j : ℤ) :
    (∫ t : ℝ, p.siteFourier n j t) =
      (p.sigma * Real.sqrt (n+1)) •
        ∫ t : ℝ in -(Real.pi/2)..Real.pi/2,
          Complex.exp (-(j : ℂ) * t * Complex.I) *
            (charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t))^(n+1) := by
  let A := (p.sigma * Real.pi / 2) * Real.sqrt (n+1)
  let scale := p.sigma * Real.sqrt (n+1)
  let f : ℝ → ℂ := fun t =>
    (charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1)))^(n+1) *
      Complex.exp ((-(j : ℝ) * t / scale : ℝ) * Complex.I)
  have hsqrt : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : 0 < scale := mul_pos p.sigma_pos hsqrt
  have hA : 0 ≤ A := mul_nonneg
    (div_nonneg (mul_nonneg p.sigma_pos.le Real.pi_pos.le) (by norm_num)) hsqrt.le
  have heq : p.siteFourier n j = (Icc (-A) A).indicator f := by
    ext t
    simp only [siteFourier, fourierCutoff, Set.indicator_apply, mem_Icc, ← abs_le]
    split_ifs <;> simp [f, scale]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hA)]
  have hlo : -(Real.pi/2) * scale = -A := by dsimp [scale, A]; ring
  have hhi : (Real.pi/2) * scale = A := by dsimp [scale, A]; ring
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (a := -(Real.pi/2)) (b := Real.pi/2) f scale
  rw [hlo, hhi] at hsub
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f]
  have he : -(j : ℝ) * (t * scale) / scale = -(j : ℝ) * t := by
    field_simp
  have ht : t * scale / Real.sqrt (n+1) = p.sigma * t := by
    dsimp [scale]
    field_simp
  rw [he, ht]
  push_cast
  ring


lemma CriticalEvenOffspring.siteFourier_probability (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) (hj : Even (((n+1 : ℕ) : ℤ) + j)) :
    (∫ t : ℝ, p.siteFourier n j t) =
      (p.sigma * Real.sqrt (n+1) * Real.pi *
        (p.iidLaw (n+1)).real {d | totalStep d = j} : ℝ) := by
  have hi := spanTwo_inversion (p.iidLaw (n+1)) totalStep
    (totalStep_measurable _) j (p.iid_totalStep_parity _ hj)
  simp only [p.iid_charFun] at hi
  rw [p.siteFourier_integral, hi]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring


lemma CriticalEvenOffspring.siteFourier_integrable (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) : Integrable (p.siteFourier n j) := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  apply (integrable_exp_neg_mul_sq hc).mono' ?_ ?_
  · exact ((p.cutoff_measurable n).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [] with t
    simpa only [siteFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
      p.cutoff_gaussian_bound hg n t


def CriticalEvenOffspring.localCLTError (p : CriticalEvenOffspring) (n : ℕ) : ℝ :=
  ∫ t : ℝ, ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖


lemma CriticalEvenOffspring.siteFourier_gaussian_error (p : CriticalEvenOffspring)
    (n : ℕ) (j : ℤ) :
    ‖(∫ t : ℝ, p.siteFourier n j t) -
      (Real.sqrt (2*Real.pi) * Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2) : ℝ)‖ ≤
      p.localCLTError n := by
  let x : ℝ := (j:ℝ)/(p.sigma*Real.sqrt (n+1))
  have heq (t : ℝ) : -(j:ℝ)*t/(p.sigma*Real.sqrt (n+1)) = -x*t := by
    dsimp [x]
    ring
  change ‖(∫ t : ℝ, p.siteFourier n j t) -
    (Real.sqrt (2*Real.pi) * Real.exp (-x^2/2) : ℝ)‖ ≤ _
  rw [← gaussian_fourier_shift x, ← integral_sub (p.siteFourier_integrable n j)
    (gaussian_phase_integrable x)]
  have hn (t : ℝ) : ‖p.siteFourier n j t -
      Complex.exp (-(t:ℂ)^2/2) * Complex.exp ((-x*t:ℝ)*Complex.I)‖ =
      ‖p.fourierCutoff n t - Complex.exp (-(t:ℂ)^2/2)‖ := by
    rw [siteFourier, heq, ← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  calc
    _ ≤ ∫ t : ℝ, ‖p.siteFourier n j t -
      Complex.exp (-(t:ℂ)^2/2) * Complex.exp ((-x*t:ℝ)*Complex.I)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp only [hn, localCLTError]


theorem CriticalEvenOffspring.uniform_local_limit (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (n : ℕ) (j : ℤ), Even (((n+1:ℕ):ℤ)+j) →
        |Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} -
          (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2)| ≤ E n := by
  refine ⟨fun n => p.localCLTError n / (p.sigma*Real.pi), fun n => ?_, ?_, ?_⟩
  · exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _))
      (mul_pos p.sigma_pos Real.pi_pos).le
  · simpa only [zero_div, localCLTError] using p.cutoff_L1_limit.div_const (p.sigma*Real.pi)
  · intro n j hj
    have h := p.siteFourier_gaussian_error n j
    rw [p.siteFourier_probability n j hj, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    have hs : 0 < p.sigma*Real.pi := mul_pos p.sigma_pos Real.pi_pos
    have heq :
        (Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} -
          (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2)) * (p.sigma*Real.pi) =
        p.sigma * Real.sqrt (n+1) * Real.pi * (p.iidLaw (n+1)).real {d | totalStep d = j} -
          Real.sqrt (2*Real.pi) * Real.exp (-((j:ℝ)/(p.sigma*Real.sqrt (n+1)))^2/2) := by
      field_simp [p.sigma_pos.ne']
    rw [← heq, abs_mul, abs_of_pos hs] at h
    exact (le_div_iff₀ hs).2 h


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TreeCode
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


instance instFintypeCode (N : ℕ) : Fintype (Code N) := Fintype.ofFinite _


abbrev Bridge (N : ℕ) := {d : Fin N → Fin N // walk d N = -1}


lemma stopped_firstZero_nonneg {Ω : Type*} (S : ℕ → Ω → ℤ) (ω : Ω)
    (h₀ : 0 ≤ S 0 ω) (hstep : ∀ n, S n ω-1 ≤ S (n+1) ω) (n : ℕ) :
    0 ≤ stoppedProcess (fun k ω => (S k ω:ℝ)) (firstZero S) n ω := by
  classical
  by_cases h : ∃ k, S k ω=0
  · by_cases hn : Nat.find h  ≤  n
    · rw [stoppedProcess,firstZero,dite_eq_left h,min_eq_right (WithTop.coe_le_coe.mpr hn)]
      simp only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,Nat.find_spec h,Int.cast_zero,le_refl]
    · rw [stoppedProcess,firstZero,dite_eq_left h,min_eq_left (WithTop.coe_le_coe.mpr (by omega : n ≤ Nat.find h))]
      simp only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      exact_mod_cast integer_path_nonneg_before_zero (fun k => S k ω) h₀ hstep n
        (fun k hk => Nat.find_min h (by omega))
  · rw [stoppedProcess,firstZero,dite_eq_right h,min_top_right,WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    exact_mod_cast integer_path_nonneg_before_zero (fun k => S k ω) h₀ hstep n
      (fun k _ hk => h ⟨k,hk⟩)


theorem integer_martingale_hits_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {S : ℕ → Ω → ℤ} (hS : StronglyAdapted ℱ S)
    (hM : Martingale (fun n ω => (S n ω:ℝ)) ℱ μ)
    (h₀ : ∀ ω, 0 ≤ S 0 ω) (hstep : ∀ n ω, S n ω-1 ≤ S (n+1) ω)
    (hjump : ∀ᵐ ω ∂μ, ∃ᶠ n in atTop, S (n+1) ω ≠ S n ω) :
    ∀ᵐ ω ∂μ, ∃ n, S n ω=0 := by
  let f := stoppedProcess (fun n ω => (S n ω:ℝ)) (firstZero S)
  have hm : Martingale f ℱ μ := martingale_stoppedProcess_real hM (firstZero_isStoppingTime hS)
  have hpos (n : ℕ) (ω : Ω) : 0 ≤ f n ω := stopped_firstZero_nonneg S ω (h₀ ω) (fun k => hstep k ω) n
  have he (n : ℕ) : ∫ ω,f n ω ∂μ=∫ ω,f 0 ω ∂μ := by
    simpa using (hm.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ).symm
  have hb (n : ℕ) : eLpNorm (f n) 1 μ ≤ ENNReal.ofReal (∫ ω,f 0 ω ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hm.integrable n)]
    have hn : (fun ω => ‖f n ω‖)=f n := funext fun ω => Real.norm_of_nonneg (hpos n ω)
    rw [hn,he]
  have hc := hm.submartingale.exists_ae_tendsto_of_bdd hb
  filter_upwards [hc,hjump] with ω hω hj
  obtain ⟨c,hc⟩ := hω
  by_contra hn
  have hz : firstZero S ω=⊤ := by simp [firstZero,hn]
  have hf : (fun n => f n ω)=fun n => (S n ω:ℝ) := by
    funext n
    dsimp [f,stoppedProcess]
    rw [hz,min_top_right,← WithTop.coe_natCast, Nat.cast_id,
      WithTop.untopA_eq_untop WithTop.coe_ne_top]
    rfl
  rw [hf] at hc
  have hd : Tendsto (fun n => (S (n+1) ω:ℝ)-(S n ω:ℝ)) atTop (𝓝 0) := by
    simpa using (hc.comp (tendsto_add_atTop_nat 1)).sub hc
  have hs := hd.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ)<1))
  obtain ⟨n,hn,hneq⟩ := ((hj.and_eventually hs)).exists
  apply hn
  apply Int.cast_injective (α := ℝ)
  have habs : |(S (n+1) ω:ℝ)-(S n ω:ℝ)|<1 := by simpa [Metric.mem_ball,Real.dist_eq] using hneq
  have hi : |S (n+1) ω-S n ω|<1 := by exact_mod_cast habs
  have hi' := abs_lt.mp hi
  omega


lemma reverseIndex_involutive (n : ℕ) : Function.Involutive (reverseIndex n) := by
  intro k
  by_cases hk : k < n
  · have hnk : n-1-k < n := by omega
    simp only [reverseIndex,ite_eq_left hk,ite_eq_left hnk]
    omega
  · simp only [reverseIndex,ite_eq_right hk]


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SimpleWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Discrete reflection principle; this is an identity of the actual killed
transition recursion, not an assumed excursion law. -/
theorem killed_reflection (n a b : ℕ) :
    killed n a b = kernel n ((b:ℤ)-a)-kernel n ((b:ℤ)+a+2) := by
  induction n generalizing a with
  | zero =>
    simp only [killed,kernel_zero]
    have hp : (b:ℤ)+a+2≠0 := by omega
    have he : (b:ℤ)-a=0 ↔ a=b := by omega
    simp only [hp,he,ite_false,sub_zero]
  | succ n ih =>
    cases a with
    | zero =>
      simp only [killed,ih,Nat.cast_zero,sub_zero,add_zero,Nat.cast_one]
      rw [kernel_succ,kernel_succ]
      simp only [show (b:ℤ)+2-1=b+1 by ring,show (b:ℤ)+2+1=b+1+2 by ring]
      ring
    | succ a =>
      simp only [killed,ih,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      rw [kernel_succ,kernel_succ]
      have h1 : (b:ℤ)-(a+1)-1=b-(a+2) := by ring
      have h2 : (b:ℤ)-(a+1)+1=b-a := by ring
      have h3 : (b:ℤ)+(a+1)+2-1=b+a+2 := by ring
      have h4 : (b:ℤ)+(a+1)+2+1=b+(a+2)+2 := by ring
      rw [h1,h2,h3,h4]
      ring

lemma chooseInt_zero (k : ℤ) : chooseInt 0 k = if k=0 then 1 else 0 := by
  by_cases hk : 0≤k
  · have he : k.toNat=0 ↔ k=0 := by omega
    rw [chooseInt,ite_eq_left hk]
    by_cases hz : k=0
    · simp [hz]
    · rw [ite_eq_right hz,Nat.choose_eq_zero_of_lt (by omega : 0<k.toNat)]; simp
  · have hn : k≠0 := by omega
    simp [chooseInt,hk,hn]

lemma kernel_binomial (n : ℕ) (z : ℤ) :
    kernel n z = if (z+n)%2=0 then chooseInt n ((z+n)/2)/(2:ℝ)^n else 0 := by
  induction n generalizing z with
  | zero =>
    rw [kernel_zero,chooseInt_zero]
    by_cases h : z=0
    · simp [h]
    · have hz : (z+0)%2=0 → (z+0)/2≠0 := by omega
      split_ifs <;> simp_all
  | succ n ih =>
    rw [kernel_succ,ih,ih]
    have hcast : (↑(n+1):ℤ)=(n:ℤ)+1 := by norm_cast
    rw [hcast]
    by_cases he : (z+(n:ℤ)+1)%2=0
    · have he1 : (z-1+(n:ℤ))%2=0 := by omega
      have he2 : (z+1+(n:ℤ))%2=0 := by omega
      have hd1 : (z-1+(n:ℤ))/2=(z+((n:ℤ)+1))/2-1 := by omega
      have hd2 : (z+1+(n:ℤ))/2=(z+((n:ℤ)+1))/2 := by omega
      have he' : (z+((n:ℤ)+1))%2=0 := by omega
      simp only [he1,he2,he',ite_true,hd1,hd2,chooseInt_pascal,pow_succ]
      ring
    · have he1 : (z-1+(n:ℤ))%2≠0 := by omega
      have he2 : (z+1+(n:ℤ))%2≠0 := by omega
      have he' : (z+((n:ℤ)+1))%2≠0 := by omega
      simp [he1,he2,he']

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

lemma pathMass_endpoint (n : ℕ) (z : ℤ) :
    pathMass n (fun d => pathSum d n=z)=kernel n z := by
  induction n generalizing z with
  | zero => simp [pathMass,pathSum,kernel,eq_comm]
  | succ n ih =>
    rw [pathMass_succ]
    have h1 : pathMass n (fun d => pathSum (Fin.cons true d) (n+1)=z)=
        pathMass n (fun d => pathSum d n=z-1) := by
      apply pathMass_congr; intro d; rw [pathSum_cons]; simp only [sign,ite_true]; omega
    have h2 : pathMass n (fun d => pathSum (Fin.cons false d) (n+1)=z)=
        pathMass n (fun d => pathSum d n=z+1) := by
      apply pathMass_congr; intro d; rw [pathSum_cons]; simp [sign]; omega
    rw [h1,h2,ih,ih,kernel_succ]

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def binaryOffspring : CriticalEvenOffspring where
  mass := binaryMass
  nonneg := binaryMass_nonneg
  total := binaryMass_total
  even_support k hk := by
    have h0 : k≠0 := by rintro rfl; norm_num at hk
    have h2 : k≠2 := by rintro rfl; norm_num at hk
    simp [binaryMass,h0,h2]
  zero_pos := by norm_num [binaryMass]
  two_pos := by norm_num [binaryMass]
  mean := by simpa using binaryMass_moment 1 (by omega)
  second := (binaryMass_moment 2 (by omega)).summable

@[simp] lemma binaryOffspring_variance : binaryOffspring.variance=1 := by
  unfold CriticalEvenOffspring.variance
  have he : (fun k : ℕ => ((k:ℝ)-1)^2*binaryOffspring.mass k)=binaryMass := by
    funext k
    by_cases h0 : k=0
    · subst k; norm_num [binaryOffspring,binaryMass]
    · by_cases h2 : k=2
      · subst k; norm_num [binaryOffspring,binaryMass]
      · simp [binaryOffspring,binaryMass,h0,h2]
  rw [he,binaryMass_total.tsum_eq]

@[simp] lemma binaryOffspring_sigma : binaryOffspring.sigma=1 := by
  simp [CriticalEvenOffspring.sigma]

lemma binaryDegree_preserving : MeasurePreserving binaryDegree coinLaw binaryOffspring.law.toMeasure := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton k),
    binaryOffspring.law_singleton]
  by_cases h0 : k=0
  · subst k
    have he : binaryDegree ⁻¹' {0}={false} := by ext s; cases s <;> simp [binaryDegree]
    rw [he,coinLaw_singleton]
    norm_num [binaryOffspring,binaryMass,ENNReal.ofReal_div_of_pos]
  · by_cases h2 : k=2
    · subst k
      have he : binaryDegree ⁻¹' {2}={true} := by ext s; cases s <;> simp [binaryDegree]
      rw [he,coinLaw_singleton]
      norm_num [binaryOffspring,binaryMass,ENNReal.ofReal_div_of_pos]
    · have he : binaryDegree ⁻¹' {k}=∅ := by ext s; cases s <;> simp [binaryDegree,Ne.symm h0,Ne.symm h2]
      rw [he,measure_empty]
      simp [binaryOffspring,binaryMass,h0,h2]

lemma binaryStep (s : Bool) : ((binaryDegree s:ℕ):ℤ)-1=SimpleWalk.sign s := by
  cases s <;> norm_num [binaryDegree,SimpleWalk.sign]

def binaryArray {N : ℕ} (d : SimpleWalk.Path N) : Fin N → ℕ := fun i => binaryDegree (d i)

lemma binaryArray_preserving (N : ℕ) :
    MeasurePreserving (@binaryArray N) (Measure.pi (fun _ : Fin N => coinLaw))
      (binaryOffspring.iidLaw N) := by
  refine ⟨measurable_of_countable _,?_⟩
  change (Measure.pi _).map (fun d i => binaryDegree (d i))=Measure.pi _
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable binaryDegree).aemeasurable)]
  simp only [binaryDegree_preserving.map_eq]

lemma binaryArray_totalStep {N : ℕ} (d : SimpleWalk.Path N) :
    totalStep (binaryArray d)=SimpleWalk.pathSum d N := by
  simp [totalStep,binaryArray,binaryStep,SimpleWalk.pathSum]

/-- The recursive symmetric kernel is the exact endpoint law used by the
already-proved finite-variance conditioned bridge invariance principle. -/
lemma binary_kernel (N : ℕ) (z : ℤ) :
    (binaryOffspring.iidLaw N).real {d | totalStep d=z}=SimpleWalk.kernel N z := by
  have hmap := (binaryArray_preserving N).map_eq
  rw [← hmap,measureReal_def,Measure.map_apply (measurable_of_countable _) (by measurability)]
  change (Measure.pi (fun _ : Fin N => coinLaw)).real {d | totalStep (binaryArray d)=z}=_
  simp_rw [binaryArray_totalStep]
  rw [coinPath_event,SimpleWalk.pathMass_endpoint]

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

/-- Full span-two uniform local limit, now for the explicitly reflected simple kernel. -/
theorem kernel_uniform_local_limit :
    ∃ E : ℕ → ℝ, (∀ n,0≤E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (N : ℕ), 0<N → ∀ z : ℤ, Even ((N:ℤ)+z) →
        |Real.sqrt N*kernel N z-(Real.sqrt (2*Real.pi)/Real.pi)*
          Real.exp (-((z:ℝ)/Real.sqrt N)^2/2)|≤E N := by
  obtain ⟨E,hE,hEt,h⟩ := binaryOffspring.uniform_local_limit
  have hsub : Tendsto (fun n : ℕ => n-1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b+1,fun n hn => by omega⟩
  refine ⟨fun N => E (N-1),fun N => hE _,hEt.comp hsub,?_⟩
  intro N hN z hz
  have hn : N-1+1=N := by omega
  have hnR : ((N-1:ℕ):ℝ)+1=(N:ℝ) := by exact_mod_cast hn
  simpa only [hn,hnR,binary_kernel,binaryOffspring_sigma,one_mul] using h (N-1) z (by simpa only [hn] using hz)

end FKCRT.SimpleWalk
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Inventory
attribute [-instance] _root_.OAI.FKCRT.Inventory.instIsProbabilityMeasureForallLetterStreamLaw _root_.OAI.FKCRT.Inventory.instMeasurableSingletonClassListLetter _root_.OAI.FKCRT.Inventory.instMeasurableSpaceLetter _root_.OAI.FKCRT.Inventory.instMeasurableSpaceListLetter _root_.OAI.FKCRT.Inventory.instTopologicalSpaceLetter _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma pop_eq_none_iff (a : Order) (s : List Bool) :
    pop a s=none ↔ ∀ b∈s,¬eligible a b := by
  induction s with
  | nil => simp [pop]
  | cons b bs ih =>
    by_cases h : eligible a b <;> simp [pop,h,ih]

def evalOrders (as : List Order) (s : List Bool) : Evaluation :=
  run (as.map Letter.order) ⟨[],s⟩

lemma run_orders_prefix (w : List Letter) (os : List Order) (e : Evaluation) :
    run w ⟨os++e.orders,e.burgers⟩ =
      ⟨os++(run w e).orders,(run w e).burgers⟩ := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | burger b => simpa only [run,step] using ih ⟨e.orders,b::e.burgers⟩
    | order a =>
      simp only [run,step]
      cases pop a e.burgers with
      | none => simpa only [List.append_assoc] using ih ⟨e.orders++[a],e.burgers⟩
      | some bs => exact ih ⟨e.orders,bs⟩

lemma evalOrders_nil (s : List Bool) : evalOrders [] s=⟨[],s⟩ := rfl

lemma evalOrders_append (as as' : List Order) (s : List Bool) :
    evalOrders (as++as') s =
      ⟨(evalOrders as s).orders++(evalOrders as' (evalOrders as s).burgers).orders,
       (evalOrders as' (evalOrders as s).burgers).burgers⟩ := by
  unfold evalOrders
  rw [List.map_append,run_append]
  simpa only [List.append_nil] using
    run_orders_prefix (as'.map Letter.order) (run (as.map Letter.order) ⟨[],s⟩).orders
      (⟨[],(run (as.map Letter.order) ⟨[],s⟩).burgers⟩ : Evaluation)

/-- Exact older-supply reduction. Unfilled orders retain chronological order;
all surviving new burgers are fresher than all surviving old burgers. -/
theorem run_older_supply (w : List Letter) (s : List Bool) :
    run w ⟨[],s⟩ =
      ⟨(evalOrders (reduce w).orders s).orders,
        (reduce w).burgers++(evalOrders (reduce w).orders s).burgers⟩ := by
  induction w using List.reverseRecOn with
  | nil => simp [run,reduce,evalOrders]
  | append_singleton w a ih =>
    rw [run_append,ih]
    have hr : reduce (w++[a])=step (reduce w) a := by
      simp [reduce,run_append,run]
    rw [hr]
    cases a with
    | burger b => simp only [run,step,List.cons_append]
    | order a =>
      simp only [run,step]
      rw [pop_append]
      cases hp : pop a (reduce w).burgers with
      | some bs => rfl
      | none =>
        dsimp only
        rw [evalOrders_append]
        simp only [evalOrders,List.map_singleton,run,step]
        cases pop a (run (List.map Letter.order (reduce w).orders) ⟨[],s⟩).burgers <;>
          simp only [Option.map_none,Option.map_some,List.append_nil,List.nil_append]

lemma run_burgers (s : List Bool) (e : Evaluation) :
    run (s.map Letter.burger) e=⟨e.orders,s.reverse++e.burgers⟩ := by
  induction s generalizing e with
  | nil => simp [run]
  | cons b bs ih => simp [run,step,ih,List.reverse_cons,List.append_assoc]

def normalWord (e : Evaluation) : List Letter :=
  e.orders.map Letter.order++e.burgers.reverse.map Letter.burger

/-- A finite word may be replaced by its source reduction in any supply. -/
theorem run_normalWord (w : List Letter) (e : Evaluation) :
    run (normalWord (reduce w)) e=run w e := by
  obtain ⟨os,s⟩ := e
  have hz : run (normalWord (reduce w)) ⟨[],s⟩=run w ⟨[],s⟩ := by
    rw [run_older_supply w s]
    simp only [normalWord,run_append,run_burgers,List.reverse_reverse,evalOrders]
  have h₁ := run_orders_prefix (normalWord (reduce w)) os (⟨[],s⟩ : Evaluation)
  have h₂ := run_orders_prefix w os (⟨[],s⟩ : Evaluation)
  simp only [List.append_nil] at h₁ h₂
  rw [h₁,h₂,hz]

/-- Once a suffix has a surviving burger, its freshest survivor is unchanged
by prepending arbitrary further letters. -/
theorem freshest_survivor_prepend (w w' : List Letter) {b : Bool} {bs : List Bool}
    (h : (reduce w).burgers=b::bs) : (reduce (w'++w)).burgers.head?=some b := by
  unfold reduce
  rw [run_append]
  have hh := run_orders_prefix w (reduce w').orders (⟨[],(reduce w').burgers⟩ : Evaluation)
  simp only [List.append_nil] at hh
  rw [show run w' ⟨[],[]⟩=⟨(reduce w').orders,(reduce w').burgers⟩ from rfl,hh,run_older_supply,h]
  rfl

lemma survivor_of_sum_pos (w : List Letter) (h : 0<(w.map Letter.increment).sum) :
    (reduce w).burgers≠[] := by
  intro hn
  rw [← reduce_imbalance,imbalance,hn] at h
  simp only [List.length_nil,Nat.cast_zero,zero_sub] at h
  omega

lemma evalOrders_cons (a : Order) (as : List Order) (s : List Bool) :
    evalOrders (a::as) s = match pop a s with
      | some s' => evalOrders as s'
      | none => ⟨a::(evalOrders as s).orders,(evalOrders as s).burgers⟩ := by
  unfold evalOrders
  simp only [List.map_cons,run,step]
  cases pop a s with
  | some s' => rfl
  | none =>
    simpa only [List.nil_append,List.append_nil,List.singleton_append] using
      run_orders_prefix (as.map Letter.order) [a] (⟨[],s⟩ : Evaluation)

lemma evalOrders_empty (as : List Order) : evalOrders as []=⟨as,[]⟩ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [evalOrders_cons,pop,ih]

lemma evalOrders_singleton (as : List Order) (b : Bool) :
    (evalOrders as [b]).burgers= if ∀ a∈as,¬eligible a b then [b] else [] := by
  induction as with
  | nil => simp [evalOrders,run]
  | cons a as ih =>
    rw [evalOrders_cons]
    by_cases h : eligible a b
    · simp [pop,h,evalOrders_empty]
    · simp [pop,h,ih]

lemma evalOrders_no_match (as : List Order) (s : List Bool)
    (h : ∀ a∈as,pop a s=none) : evalOrders as s=⟨as,s⟩ := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [evalOrders_cons,h a (by simp),ih (by intro a ha; exact h a (by simp [ha]))]

lemma prepend_order_burgers (a : Order) (w : List Letter) :
    (reduce (.order a::w)).burgers=(reduce w).burgers := by
  change (run w (step ⟨[],[]⟩ (.order a))).burgers=_
  simp only [step,pop,List.nil_append]
  have h := run_orders_prefix w [a] (⟨[],[]⟩ : Evaluation)
  simpa only [List.append_nil,reduce] using congrArg Evaluation.burgers h

/-- The first backwards survivor has exactly one burger and only fixed
orders of the opposite type, precisely as in source word:stopped-sum. -/
theorem first_survivor_shape (a : Letter) (w : List Letter)
    (h₀ : (reduce w).burgers=[]) (h₁ : (reduce (a::w)).burgers≠[]) :
    ∃ b, a=.burger b ∧ reduce (a::w)=⟨(reduce w).orders,[b]⟩ ∧
      ∀ o∈(reduce w).orders,o=some (!b) := by
  cases a with
  | order a => exact (h₁ (by rw [prepend_order_burgers,h₀])).elim
  | burger b =>
    have he : reduce (.burger b::w)=evalOrders (reduce w).orders [b] := by
      change run w ⟨[],[b]⟩=_
      rw [run_older_supply,h₀,List.nil_append]
    rw [he,evalOrders_singleton] at h₁
    have hn : ∀ o∈(reduce w).orders,¬eligible o b := by
      by_contra hn
      exact h₁ (ite_eq_right hn)
    refine ⟨b,rfl,?_,?_⟩
    · rw [he,evalOrders_no_match]
      intro o ho
      exact (pop_eq_none_iff o [b]).2 (by simpa using hn o ho)
    · intro o ho
      have hh := hn o ho
      cases o with
      | none => exact (hh (Or.inl rfl)).elim
      | some c => cases b <;> cases c <;> simp_all [eligible]

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WordLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.instMeasurableSingletonClassListLetter _root_.OAI.FKCRT.Inventory.instMeasurableSpaceListLetter _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

instance instDiscreteTopologyLetter : DiscreteTopology Letter := ⟨rfl⟩
instance instBorelSpaceLetter : BorelSpace Letter := ⟨(borel_eq_top_of_discrete).symm⟩

lemma law_real_singleton (P : Parameters) (a : Letter) :
    (law P).toMeasure.real {a}=mass P a := by
  rw [measureReal_def,law_singleton,ENNReal.toReal_ofReal (mass_pos P a).le]

lemma integral_law (P : Parameters) (f : Letter → ℝ) :
    ∫ a,f a ∂(law P).toMeasure=∑ a,mass P a*f a := by
  rw [integral_fintype]
  · simp [law_real_singleton]
  · exact integrableOn_univ.mp (IntegrableOn.of_finite (Set.finite_univ) : IntegrableOn f Set.univ (law P).toMeasure)

lemma integral_increment (P : Parameters) :
    ∫ a,(a.increment:ℝ) ∂(law P).toMeasure=0 := by
  rw [integral_law,sum_letters]
  simp only [mass,Letter.increment,Int.cast_one,Int.cast_neg,mul_one,mul_neg]
  ring

lemma signSum_succ (x : ℕ → Letter) (n : ℕ) :
    signSum x (n+1)=signSum x n+(x n).increment := Finset.sum_range_succ _ _

lemma increment_bounds (a : Letter) : -1≤a.increment ∧ a.increment≤1 ∧ a.increment≠0 := by
  cases a <;> norm_num [Letter.increment]

/-- Recurrence of the actual raw-word signs. This uses the proved integer
martingale recurrence theorem, not a recurrence hypothesis. -/
theorem signs_hit_one (P : Parameters) :
    ∀ᵐ x ∂streamLaw P ℕ,∃ n,signSum x n=1 := by
  let X : ℕ → (ℕ → Letter) → ℝ := fun n x => -((x n).increment:ℝ)
  have hm (n : ℕ) : StronglyMeasurable (X n) := by
    exact (measurable_of_countable (fun a : Letter => -(a.increment:ℝ))).comp (measurable_pi_apply n) |>.stronglyMeasurable
  let ℱ := Filtration.natural X hm
  let S : ℕ → (ℕ → Letter) → ℤ := fun n x => 1-signSum x (n+1)
  have hInt : Integrable (fun a : Letter => -(a.increment:ℝ)) (law P).toMeasure :=
    integrableOn_univ.mp (IntegrableOn.of_finite (Set.finite_univ) :
      IntegrableOn (fun a : Letter => -(a.increment:ℝ)) Set.univ (law P).toMeasure)
  have hz : ∫ a,-(a.increment:ℝ) ∂(law P).toMeasure=0 := by
    rw [integral_neg,integral_increment,neg_zero]
  have hM : Martingale (fun n x => (S n x:ℝ)) ℱ (streamLaw P ℕ) := by
    have h := TreeCoding.independent_sum_martingale X hm
      (fun n => (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) n).integrable_comp_of_integrable hInt)
      (iIndepFun_infinitePi (X := fun _ (a : Letter) => -(a.increment:ℝ)) (fun _ => measurable_of_countable _))
      (fun n => by
        change (∫ x,((fun a : Letter => -(a.increment:ℝ)) (x n)) ∂streamLaw P ℕ)=0
        exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) n).hasLaw.integral_comp
          (f := fun a : Letter => -(a.increment:ℝ)) (measurable_of_countable _).aestronglyMeasurable).trans hz)
    convert (martingale_const ℱ (streamLaw P ℕ) (1:ℝ)).add h using 1
    all_goals try with_reducible_and_instances rfl
    ext n x
    simp [S,signSum,X,Finset.sum_neg_distrib,sub_eq_add_neg]
  have hS : StronglyAdapted ℱ S := by
    intro n
    have hh : Measurable[ℱ n] (fun x => Int.floor (S n x:ℝ)) :=
      Int.measurable_floor.comp (hM.stronglyMeasurable n).measurable
    simpa only [Int.floor_intCast] using hh.stronglyMeasurable
  have h₀ (x : ℕ → Letter) : 0≤S 0 x := by
    simpa [S,signSum,sub_nonneg] using (increment_bounds (x 0)).2.1
  have hstep (n : ℕ) (x : ℕ → Letter) : S n x-1≤S (n+1) x := by
    dsimp [S]
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.1
    omega
  have hjump : ∀ᵐ x ∂streamLaw P ℕ,∃ᶠ n in atTop,S (n+1) x≠S n x := by
    filter_upwards [] with x
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    dsimp [S]
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.2
    omega
  filter_upwards [TreeCoding.integer_martingale_hits_zero (S := S) hS hM h₀ hstep hjump] with x hx
  obtain ⟨n,hn⟩ := hx
  exact ⟨n+1,by dsimp [S] at hn; omega⟩

end FKCRT.Inventory
end



noncomputable section
open scoped BigOperators
namespace FKCRT.Inventory

lemma origins_mass (P : Parameters) (s : List Bool) (a : TypedLetter) :
    (∑ x∈origins s a,mass P x) =
      mass P a.fixed * (1+2*P.p/(1-P.p))^(if flexibleClosing s a then 1 else 0) := by
  have hp : 1-P.p≠0 := ne_of_gt (by linarith [P.upper])
  by_cases h : flexibleClosing s a
  · cases a with
    | burger b => simp [flexibleClosing] at h
    | order b =>
      simp [origins,h,TypedLetter.fixed,mass]
      field_simp
      ring
  · simp [origins,h]

lemma markings_mass (P : Parameters) {v : List TypedLetter} {s t : List Bool}
    (h : stackTypedRun v s=some t) :
    (∑ w∈markings v s,wordMass P w) =
      wordMass P (v.map TypedLetter.fixed)*(1+2*P.p/(1-P.p))^(flexibleCount v s) := by
  induction v generalizing s with
  | nil => simp [markings,wordMass,flexibleCount]
  | cons a v ih =>
    cases hs : stackTypedStep s a with
    | none => simp [stackTypedRun,hs] at h
    | some r =>
      have hr : stackTypedRun v r=some t := by simpa only [stackTypedRun,hs,Option.bind_some] using h
      have hd : (origins s a : Set Letter).PairwiseDisjoint
          (fun x => (markings v r).image (x::·)) := by
        intro x _ y _ hxy
        apply Finset.disjoint_left.mpr
        intro w hx hy
        obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨z,_,he⟩ := Finset.mem_image.mp hy
        exact hxy (List.cons.inj he).1.symm
      rw [markings,hs,Finset.sum_biUnion hd]
      simp_rw [Finset.sum_image (fun x _ y _ hxy => List.cons.inj hxy |>.2)]
      simp only [wordMass,List.map_cons,List.prod_cons]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,origins_mass]
      rw [show (∑ w∈markings v r,(w.map (mass P)).prod)=
          wordMass P (v.map TypedLetter.fixed)*(1+2*P.p/(1-P.p))^flexibleCount v r from ih hr]
      simp only [wordMass,flexibleCount,hs,pow_add]
      ring

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_InventoryStopping
attribute [-instance] _root_.OAI.FKCRT.Inventory.instMeasurableSingletonClassListLetter _root_.OAI.FKCRT.Inventory.instMeasurableSpaceListLetter _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def revealed (x : ℕ → Letter) (n : ℕ) : List Letter :=
  (List.ofFn (fun i : Fin n => x i)).reverse

lemma revealed_zero (x : ℕ → Letter) : revealed x 0=[] := by simp [revealed]
lemma revealed_succ (x : ℕ → Letter) (n : ℕ) :
    revealed x (n+1)=x n::revealed x n := by
  unfold revealed
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append,List.reverse_concat,Fin.val_last,Fin.val_castSucc]

lemma revealed_sum (x : ℕ → Letter) (n : ℕ) :
    ((revealed x n).map Letter.increment).sum=signSum x n := by
  simp only [revealed,List.map_reverse,List.sum_reverse,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun i => (x i).increment) n

lemma survivor_mono (x : ℕ → Letter) {n m : ℕ} (hnm : n ≤ m)
    (hn : (reduce (revealed x n)).burgers ≠ []) :
    (reduce (revealed x m)).burgers ≠ [] := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    rw [show n+(k+1)=n+k+1 by omega,revealed_succ]
    cases h : (reduce (revealed x (n+k))).burgers with
    | nil => exact (ih h).elim
    | cons b bs =>
      have hh := freshest_survivor_prepend (revealed x (n+k)) [x (n+k)] h
      intro hz
      simp only [List.singleton_append,hz,List.head?_nil] at hh
      contradiction

def rawFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Letter)) :=
  Filtration.natural (fun n x => x n) (fun n => (measurable_pi_apply n).stronglyMeasurable)

lemma raw_adapted (n k : ℕ) (hk : k ≤ n) :
    Measurable[rawFiltration n] (fun x : ℕ → Letter => x k) := by
  exact ((Filtration.stronglyAdapted_natural
    (fun j : ℕ => (measurable_pi_apply j).stronglyMeasurable)) k).measurable.mono
      (rawFiltration.mono hk) le_rfl

lemma prefix_measurable {β : Type*} [MeasurableSpace β] (n : ℕ)
    (f : (Fin (n+1) → Letter) → β) :
    Measurable[rawFiltration n] (fun x => f (fun i => x i)) := by
  let : MeasurableSpace (ℕ → Letter) := rawFiltration n
  exact (measurable_of_countable f).comp
    (Measurable.of_eval fun index => raw_adapted n index (by omega))

lemma signSum_adapted : StronglyAdapted rawFiltration
    (fun n x => (signSum x (n+1):ℝ)) := by
  intro n
  have hh := prefix_measurable n (fun y => ((∑ i:Fin (n+1),(y i).increment:ℤ):ℝ))
  convert hh.stronglyMeasurable using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact congrArg (fun z : ℤ => (z:ℝ))
    (Fin.sum_univ_eq_sum_range (fun i => (x i).increment) (n+1)).symm

lemma raw_sign_martingale (P : Parameters) :
    Martingale (fun n x => (signSum x (n+1):ℝ)) rawFiltration (streamLaw P ℕ) := by
  have hi (n : ℕ) : Integrable (fun x : ℕ → Letter => ((x n).increment:ℝ)) (streamLaw P ℕ) := by
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) n).integrable_comp_of_integrable
      (integrableOn_univ.mp (IntegrableOn.of_finite (Set.finite_univ) :
        IntegrableOn (fun a : Letter => (a.increment:ℝ)) Set.univ (law P).toMeasure))
  have hint (n : ℕ) : Integrable (fun x => (signSum x (n+1):ℝ)) (streamLaw P ℕ) := by
    simp only [signSum,Int.cast_sum]
    exact integrable_finsetSum _ (fun k _ => hi k)
  apply martingale_nat signSum_adapted hint
  intro n
  have hind : Indep (MeasurableSpace.comap (fun x : ℕ → Letter => x (n+1)) inferInstance)
      (rawFiltration n) (streamLaw P ℕ) := by
    have h := indep_iSup_of_disjoint
      (fun k : ℕ => (measurable_pi_apply k : Measurable (fun x : ℕ → Letter => x k)).comap_le)
      (iIndepFun_infinitePi (P := fun _ : ℕ => (law P).toMeasure) (X := fun _ (a : Letter) => a) (fun _ => measurable_id))
      (show Disjoint ({n+1} : Set ℕ) {k | k ≤ n} by simp)
    simpa only [iSup_singleton,rawFiltration,Filtration.natural,Set.mem_ofPred_eq,streamLaw] using h
  have hc := condExp_indep_eq
    (measurable_pi_apply (n+1) : Measurable (fun x : ℕ → Letter => x (n+1))).comap_le
    (rawFiltration.le n)
    (((measurable_of_countable (fun a : Letter => (a.increment:ℝ))).comp
      (comap_measurable (fun x : ℕ → Letter => x (n+1)))).stronglyMeasurable) hind
  change (streamLaw P ℕ)[(fun x => ((x (n+1)).increment:ℝ)) | rawFiltration n] =ᵐ[streamLaw P ℕ]
    (fun _ => ∫ x,((x (n+1)).increment:ℝ) ∂streamLaw P ℕ) at hc
  have hz : ∫ x,((x (n+1)).increment:ℝ) ∂streamLaw P ℕ=0 := by
    exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) (n+1)).hasLaw.integral_comp
      (f := fun a : Letter => (a.increment:ℝ)) (measurable_of_countable _).aestronglyMeasurable).trans
      (integral_increment P)
  have he : (fun x => (signSum x (n+1+1):ℝ))=
      (fun x => (signSum x (n+1):ℝ))+(fun x => ((x (n+1)).increment:ℝ)) := by
    ext x; simp only [signSum_succ,Int.cast_add,Pi.add_apply]
  rw [he]
  filter_upwards [condExp_add (hint n) (hi (n+1)) (rawFiltration n),hc] with x hsum hx
  rw [condExp_of_stronglyMeasurable (rawFiltration.le n) (signSum_adapted n) (hint n),
    Pi.add_apply,hx,hz,add_zero] at hsum
  exact hsum.symm

def survivorFlag (n : ℕ) (x : ℕ → Letter) : ℤ :=
  if (reduce (revealed x (n+1))).burgers=[] then 1 else 0

def firstSurvivor (x : ℕ → Letter) : WithTop ℕ := TreeCoding.firstZero survivorFlag x

lemma survivorFlag_adapted : StronglyAdapted rawFiltration survivorFlag := by
  intro n
  exact (prefix_measurable n (fun y => if (reduce (List.ofFn y).reverse).burgers=[] then (1:ℤ) else 0)).stronglyMeasurable

lemma firstSurvivor_stopping : IsStoppingTime rawFiltration firstSurvivor :=
  TreeCoding.firstZero_isStoppingTime survivorFlag_adapted

lemma firstSurvivor_le_iff (x : ℕ → Letter) (n : ℕ) :
    firstSurvivor x ≤ (WithTop.some n) ↔ (reduce (revealed x (n+1))).burgers ≠ [] := by
  change TreeCoding.firstZero survivorFlag x ≤ WithTop.some n ↔ _
  rw [TreeCoding.firstZero_le_iff]
  constructor
  · rintro ⟨k,hk,h⟩
    have hh : (reduce (revealed x (k+1))).burgers ≠ [] := by
      simpa [survivorFlag] using h
    exact survivor_mono x (by omega) hh
  · intro h
    exact ⟨n,le_rfl,by simp [survivorFlag,h]⟩

lemma firstSurvivor_finite (P : Parameters) :
    ∀ᵐ x ∂streamLaw P ℕ, firstSurvivor x ≠ ⊤ := by
  filter_upwards [signs_hit_one P] with x hx
  obtain ⟨n,hn⟩ := hx
  have hb : (reduce (revealed x n)).burgers ≠ [] :=
    survivor_of_sum_pos _ (by rw [revealed_sum,hn]; norm_num)
  have hle := (firstSurvivor_le_iff x n).mpr (survivor_mono x (by omega) hb)
  exact ne_top_of_le_ne_top WithTop.coe_ne_top hle

lemma firstSurvivor_shape {x : ℕ → Letter} {n : ℕ}
    (h : firstSurvivor x=(WithTop.some n)) :
    ∃ b, reduce (revealed x (n+1))=⟨(reduce (revealed x n)).orders,[b]⟩ ∧
      ∀ o∈(reduce (revealed x n)).orders,o=some (!b) := by
  have h₁ := (firstSurvivor_le_iff x n).mp (by rw [h])
  have h₀ : (reduce (revealed x n)).burgers=[] := by
    cases n with
    | zero => simp [revealed_zero,reduce,run]
    | succ n =>
      by_contra hn
      have hle := (firstSurvivor_le_iff x n).mpr hn
      rw [h] at hle
      have hh : n+1 ≤ n := WithTop.coe_le_coe.mp hle
      omega
  rw [revealed_succ] at h₁ ⊢
  obtain ⟨b,_,hb,ho⟩ := first_survivor_shape (x n) (revealed x n) h₀ h₁
  exact ⟨b,hb,ho⟩

def stoppedDefect (n : ℕ) (x : ℕ → Letter) : ℝ :=
  stoppedProcess (fun k x => 1-(signSum x (k+1):ℝ)) firstSurvivor n x

lemma stoppedDefect_martingale (P : Parameters) :
    Martingale stoppedDefect rawFiltration (streamLaw P ℕ) := by
  exact TreeCoding.martingale_stoppedProcess_real
    ((martingale_const rawFiltration (streamLaw P ℕ) (1:ℝ)).sub (raw_sign_martingale P))
    firstSurvivor_stopping

lemma stoppedDefect_nonneg (n : ℕ) (x : ℕ → Letter) : 0 ≤ stoppedDefect n x := by
  by_cases h : firstSurvivor x ≤ (WithTop.some n)
  · obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top h)
    have hk' : firstSurvivor x=(WithTop.some k) := hk.symm
    obtain ⟨b,hb,_⟩ := firstSurvivor_shape hk'
    have hs := reduce_imbalance (revealed x (k+1))
    rw [hb,imbalance,revealed_sum] at hs
    simp only [List.length_singleton,Nat.cast_one] at hs
    change 0 ≤ 1-(signSum x ((min (WithTop.some n) (firstSurvivor x)).untopA+1):ℝ)
    rw [min_eq_right h,hk',WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe]
    have hr : (signSum x (k+1):ℝ)=1-(((reduce (revealed x (k+1))).orders.length):ℝ) := by
      rw [hb]
      exact_mod_cast hs.symm
    rw [hr]
    linarith [Nat.cast_nonneg (α := ℝ) ((reduce (revealed x (k+1))).orders.length)]
  · have hb : (reduce (revealed x (n+1))).burgers=[] := by
      by_contra hn
      exact h ((firstSurvivor_le_iff x n).mpr hn)
    have hs := reduce_imbalance (revealed x (n+1))
    rw [imbalance,hb,revealed_sum] at hs
    simp only [List.length_nil,Nat.cast_zero,zero_sub] at hs
    change 0 ≤ 1-(signSum x ((min (WithTop.some n) (firstSurvivor x)).untopA+1):ℝ)
    rw [min_eq_left (le_of_not_ge h),WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe]
    have hr : (signSum x (n+1):ℝ) ≤ 0 := by exact_mod_cast (by omega : signSum x (n+1) ≤ 0)
    linarith

lemma stoppedDefect_integral (P : Parameters) (n : ℕ) :
    ∫ x,stoppedDefect n x ∂streamLaw P ℕ=1 := by
  have he := (stoppedDefect_martingale P).setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  rw [← he]
  have he0 : stoppedDefect 0=fun x => 1-((x 0).increment:ℝ) := by
    ext x
    simp [stoppedDefect,stoppedProcess,signSum]
  have hi : Integrable (fun x : ℕ → Letter => ((x 0).increment:ℝ)) (streamLaw P ℕ) := by
    simpa [signSum] using (raw_sign_martingale P).integrable 0
  rw [he0,integral_sub (integrable_const _) hi]
  have hz := ((measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).hasLaw.integral_comp
    (f := fun a : Letter => (a.increment:ℝ)) (measurable_of_countable _).aestronglyMeasurable).trans
    (integral_increment P)
  change ∫ x,((x 0).increment:ℝ) ∂streamLaw P ℕ=0 at hz
  simp only [integral_const,probReal_univ,one_smul,hz,sub_zero]

lemma measurableSet_firstSurvivor_eq (n : ℕ) :
    MeasurableSet {x | firstSurvivor x=WithTop.some n} :=
  rawFiltration.le n _ (firstSurvivor_stopping.measurableSet_eq n)

lemma measurableSet_firstSurvivor_finite : MeasurableSet {x | firstSurvivor x ≠ ⊤} := by
  have he : {x | firstSurvivor x ≠ ⊤}=⋃ n : ℕ,{x | firstSurvivor x=WithTop.some n} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    exact WithTop.ne_top_iff_exists.trans (by simp only [eq_comm])
  rw [he]
  exact MeasurableSet.iUnion measurableSet_firstSurvivor_eq

lemma measurable_firstSurvivor : Measurable firstSurvivor := by
  apply measurable_to_countable'
  intro n
  obtain rfl | ⟨n,rfl⟩ := eq_or_ne n ⊤ |>.imp_right (fun h => WithTop.ne_top_iff_exists.mp h)
  · convert measurableSet_firstSurvivor_finite.compl using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp
  · exact measurableSet_firstSurvivor_eq n

def K (x : ℕ → Letter) : ℕ :=
  if firstSurvivor x=⊤ then 0 else
    (reduce (revealed x ((firstSurvivor x).untopD 0+1))).orders.length

lemma K_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    K x=(reduce (revealed x (n+1))).orders.length := by
  simp only [K,h,WithTop.coe_ne_top,ite_false]
  rfl

lemma measurable_K : Measurable K := by
  have hm (n : ℕ) : Measurable (fun x : ℕ → Letter => (reduce (revealed x (n+1))).orders.length) :=
    (prefix_measurable n (fun y => (reduce (List.ofFn y).reverse).orders.length)).mono
      (rawFiltration.le n) le_rfl
  have hp : Measurable (fun x : ℕ → Letter =>
      (reduce (revealed x ((firstSurvivor x).untopD 0+1))).orders.length) :=
    (measurable_from_prod_countable_right (f := fun z : ℕ × (ℕ → Letter) =>
      (reduce (revealed z.2 (z.1+1))).orders.length) hm).comp
      (((measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp measurable_firstSurvivor).prodMk measurable_id)
  exact measurable_const.ite (measurableSet_eq_fun measurable_firstSurvivor measurable_const) hp

lemma stoppedDefect_eq_K {n : ℕ} {x : ℕ → Letter}
    (h : firstSurvivor x ≤ WithTop.some n) : stoppedDefect n x=K x := by
  obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  have hk' : firstSurvivor x=WithTop.some k := hk.symm
  obtain ⟨b,hb,_⟩ := firstSurvivor_shape hk'
  have hs := reduce_imbalance (revealed x (k+1))
  rw [hb,imbalance,revealed_sum] at hs
  simp only [List.length_singleton,Nat.cast_one] at hs
  change 1-(signSum x ((min (WithTop.some n) (firstSurvivor x)).untopA+1):ℝ)=(K x:ℝ)
  rw [min_eq_right h,hk',WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe,K_of_hit hk',hb]
  dsimp only
  have hr : (signSum x (k+1):ℝ)=1-(((reduce (revealed x k)).orders.length):ℝ) := by
    exact_mod_cast hs.symm
  rw [hr]
  ring

lemma stoppedDefect_tendsto (P : Parameters) :
    ∀ᵐ x ∂streamLaw P ℕ,Tendsto (fun n => stoppedDefect n x) atTop (𝓝 (K x:ℝ)) := by
  filter_upwards [firstSurvivor_finite P] with x hx
  obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hx
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (stoppedDefect_eq_K (by rw [← hk]; exact WithTop.coe_le_coe.mpr hn)).symm

/-- The source first optional-stopping bound, without any finite-mean
hypothesis on the stopping time. -/
theorem K_lintegral_le_one (P : Parameters) :
    ∫⁻ x,ENNReal.ofReal (K x:ℝ) ∂streamLaw P ℕ ≤ 1 := by
  have hm (n : ℕ) : Measurable (fun x => ENNReal.ofReal (stoppedDefect n x)) :=
    (((stoppedDefect_martingale P).stronglyMeasurable n).measurable.mono (rawFiltration.le n) le_rfl).ennreal_ofReal
  have hb (n : ℕ) : ∫⁻ x,ENNReal.ofReal (stoppedDefect n x) ∂streamLaw P ℕ=1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((stoppedDefect_martingale P).integrable n)
      (Filter.Eventually.of_forall (stoppedDefect_nonneg n)),stoppedDefect_integral]
    simp
  have he : (fun x => ENNReal.ofReal (K x:ℝ)) =ᵐ[streamLaw P ℕ]
      (fun x => liminf (fun n => ENNReal.ofReal (stoppedDefect n x)) atTop) := by
    filter_upwards [stoppedDefect_tendsto P] with x hx
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx).liminf_eq.symm
  rw [lintegral_congr_ae he]
  exact (lintegral_liminf_le hm).trans_eq (by simp only [hb,liminf_const])

theorem integrable_K (P : Parameters) : Integrable (fun x => (K x:ℝ)) (streamLaw P ℕ) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp measurable_K).aestronglyMeasurable (Filter.Eventually.of_forall (fun x => Nat.cast_nonneg (K x)))).mp
  exact ne_top_of_le_ne_top (by norm_num) (K_lintegral_le_one P)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def orderType (o : Order) (t : Bool) : Bool := o.getD t

def assignedSign (a : Letter × Bool) : ℤ := match a.1 with
  | .burger b => typeSign b
  | .order o => -typeSign (orderType o a.2)

lemma abs_assignedSign (a : Letter × Bool) : |assignedSign a|=1 := by
  rcases a with ⟨a,t⟩
  cases a <;> simp [assignedSign,abs_typeSign]

structure TypedEvaluation where
  orders : List (Order × Bool)
  burgers : List Bool

def TypedEvaluation.erase (e : TypedEvaluation) : Evaluation :=
  ⟨e.orders.map Prod.fst,e.burgers⟩

def typedStep (e : TypedEvaluation) (a : Letter × Bool) : TypedEvaluation := match a.1 with
  | .burger b => ⟨e.orders,b::e.burgers⟩
  | .order o => match pop o e.burgers with
    | some bs => ⟨e.orders,bs⟩
    | none => ⟨e.orders++[(o,a.2)],e.burgers⟩

def typedRun : List (Letter × Bool) → TypedEvaluation → TypedEvaluation
  | [],e => e
  | a::w,e => typedRun w (typedStep e a)

def validStep (s : List Bool) (a : Letter × Bool) : Prop :=
  a.1=.order none → (s=[] ∨ s.head?=some a.2)

def ValidTyping : List (Letter × Bool) → List Bool → Prop
  | [],_ => True
  | a::w,s => validStep s a ∧ ValidTyping w (step ⟨[],s⟩ a.1).burgers

lemma erase_typedStep (e : TypedEvaluation) (a : Letter × Bool) :
    (typedStep e a).erase=step e.erase a.1 := by
  rcases a with ⟨a,t⟩
  cases a with
  | burger b => rfl
  | order o =>
    simp only [typedStep,step,TypedEvaluation.erase]
    cases pop o e.burgers <;> simp

lemma erase_typedRun (w : List (Letter × Bool)) (e : TypedEvaluation) :
    (typedRun w e).erase=run (w.map Prod.fst) e.erase := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => simp only [typedRun,ih,erase_typedStep,List.map_cons,run]

lemma typedStep_burgers (e : TypedEvaluation) (a : Letter × Bool) :
    (typedStep e a).burgers=(step ⟨[],e.burgers⟩ a.1).burgers := by
  rcases a with ⟨a,t⟩
  cases a with
  | burger b => rfl
  | order o => simp only [typedStep,step]; cases pop o e.burgers <;> rfl

lemma pop_sign_sum {o : Order} {s s' : List Bool} {t : Bool}
    (h : pop o s=some s') (ht : o=none → s=[] ∨ s.head?=some t) :
    (s.map typeSign).sum=(s'.map typeSign).sum+typeSign (orderType o t) := by
  induction s generalizing s' with
  | nil => simp [pop] at h
  | cons b bs ih =>
    simp only [pop] at h
    split_ifs at h with he
    · simp only [Option.some.injEq] at h
      subst s'
      have hb : orderType o t=b := by
        obtain rfl | ho := he
        · obtain hf | hb := ht rfl
          · simp at hf
          · simpa [orderType] using (Option.some.inj (by simpa using hb)).symm
        · simp [orderType,ho]
      simp only [List.map_cons,List.sum_cons,hb]
      omega
    · cases hp : pop o bs with
      | none => simp [hp] at h
      | some cs =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst s'
        have hnone : o ≠ none := fun ho => he (Or.inl ho)
        have hh := ih hp (fun ho => (hnone ho).elim)
        simp only [List.map_cons,List.sum_cons]
        omega

def typedImbalance (e : TypedEvaluation) : ℤ :=
  (e.burgers.map typeSign).sum-(e.orders.map (fun o => typeSign (orderType o.1 o.2))).sum

lemma typedStep_imbalance (e : TypedEvaluation) (a : Letter × Bool)
    (h : validStep e.burgers a) :
    typedImbalance (typedStep e a)=typedImbalance e+assignedSign a := by
  rcases a with ⟨a,t⟩
  cases a with
  | burger b => simp [typedStep,typedImbalance,assignedSign]; ring
  | order o =>
    simp only [typedStep,assignedSign]
    cases hp : pop o e.burgers with
    | none => simp [typedImbalance]; ring
    | some bs =>
      have hh := pop_sign_sum hp (fun ho => h (by rw [ho]))
      simp only [typedImbalance]
      dsimp only at *
      omega

lemma typedRun_imbalance (w : List (Letter × Bool)) (e : TypedEvaluation)
    (h : ValidTyping w e.burgers) :
    typedImbalance (typedRun w e)=(w.map assignedSign).sum+typedImbalance e := by
  induction w generalizing e with
  | nil => simp [typedRun]
  | cons a w ih =>
    rw [typedRun,ih (typedStep e a) (by simpa only [typedStep_burgers] using h.2),typedStep_imbalance e a h.1]
    simp only [List.map_cons,List.sum_cons]
    omega

lemma typed_orders_sum_abs_le (l : List (Order × Bool)) :
    |(l.map (fun o => typeSign (orderType o.1 o.2))).sum| ≤ l.length := by
  simpa only [List.map_map,List.length_map,Function.comp_def] using
    sum_typeSign_abs_le (l.map (fun o => orderType o.1 o.2))

lemma typedRun_no_survivor_bound (w : List (Letter × Bool)) (h : ValidTyping w [])
    (h₀ : (reduce (w.map Prod.fst)).burgers=[]) :
    |(w.map assignedSign).sum| ≤ ((reduce (w.map Prod.fst)).orders.length:ℤ) := by
  let e := typedRun w ⟨[],[]⟩
  have he : e.erase=reduce (w.map Prod.fst) := erase_typedRun w ⟨[],[]⟩
  have hs : (w.map assignedSign).sum=typedImbalance e := by
    simpa [typedImbalance] using (typedRun_imbalance w ⟨[],[]⟩ h).symm
  have hb : e.burgers=[] := by
    rw [← h₀,← he]; rfl
  have hl : (reduce (w.map Prod.fst)).orders.length=e.orders.length := by
    rw [← he]; simp [TypedEvaluation.erase]
  rw [hl,hs,typedImbalance,hb]
  simpa using typed_orders_sum_abs_le e.orders

lemma typed_orders_opposite_sum (l : List (Order × Bool)) (b : Bool)
    (h : ∀ o∈l,o.1=some (!b)) :
    (l.map (fun o => typeSign (orderType o.1 o.2))).sum= -(l.length:ℤ)*typeSign b := by
  induction l with
  | nil => simp
  | cons o os ih =>
    rw [List.map_cons,List.sum_cons,ih (fun o ho => h o (by simp [ho]))]
    rw [show orderType o.1 o.2= !b by simp [orderType,h o (by simp)],typeSign_not]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

lemma typedRun_first_survivor_sum (w : List (Letter × Bool)) (b : Bool)
    (h : ValidTyping w []) (hb : (reduce (w.map Prod.fst)).burgers=[b])
    (ho : ∀ o∈(reduce (w.map Prod.fst)).orders,o=some (!b)) :
    (w.map assignedSign).sum=typeSign b*(1+((reduce (w.map Prod.fst)).orders.length:ℤ)) := by
  let e := typedRun w ⟨[],[]⟩
  have he : e.erase=reduce (w.map Prod.fst) := erase_typedRun w ⟨[],[]⟩
  have hs : (w.map assignedSign).sum=typedImbalance e := by
    simpa [typedImbalance] using (typedRun_imbalance w ⟨[],[]⟩ h).symm
  have hb' : e.burgers=[b] := by rw [← hb,← he]; rfl
  have ho' : ∀ o∈e.orders,o.1=some (!b) := by
    intro o hm
    apply ho o.1
    rw [← he]
    exact List.mem_map.mpr ⟨o,hm,rfl⟩
  have hl : (reduce (w.map Prod.fst)).orders.length=e.orders.length := by
    rw [← he]; simp [TypedEvaluation.erase]
  rw [hs,typedImbalance,hb',typed_orders_opposite_sum e.orders b ho',hl]
  simp only [List.map_singleton,List.sum_singleton]
  ring

lemma ValidTyping_append (w v : List (Letter × Bool)) (e : TypedEvaluation) :
    ValidTyping (w++v) e.burgers ↔ ValidTyping w e.burgers ∧ ValidTyping v (typedRun w e).burgers := by
  induction w generalizing e with
  | nil => simp [ValidTyping,typedRun]
  | cons a w ih =>
    simp only [List.cons_append,ValidTyping,typedRun]
    rw [← typedStep_burgers e a,ih]
    tauto

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def Letter.flip : Letter → Letter
  | .burger b => .burger (!b)
  | .order o => .order (o.map Bool.not)

lemma Letter.flip_flip (a : Letter) : a.flip.flip=a := by
  cases a with
  | burger b => simp [Letter.flip]
  | order o => cases o <;> simp [Letter.flip]

lemma eligible_flip (o : Order) (b : Bool) : eligible (o.map Bool.not) (!b) ↔ eligible o b := by
  cases o with
  | none => simp [eligible]
  | some c => cases c <;> cases b <;> simp [eligible]

lemma pop_flip (o : Order) (s : List Bool) :
    pop (o.map Bool.not) (s.map Bool.not)=(pop o s).map (List.map Bool.not) := by
  induction s with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,pop,eligible_flip]
    split_ifs <;> simp only [Option.map_some,ih,Option.map_map,Function.comp_def,List.map_cons]

def Evaluation.flip (e : Evaluation) : Evaluation :=
  ⟨e.orders.map (Option.map Bool.not),e.burgers.map Bool.not⟩

lemma step_flip (e : Evaluation) (a : Letter) : step e.flip a.flip=(step e a).flip := by
  cases a with
  | burger b => rfl
  | order o =>
    simp only [Letter.flip,Evaluation.flip,step,pop_flip]
    cases pop o e.burgers <;> simp

lemma run_flip (w : List Letter) (e : Evaluation) :
    run (w.map Letter.flip) e.flip=(run w e).flip := by
  induction w generalizing e with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons,run,step_flip,ih]

lemma reduce_flip (w : List Letter) : reduce (w.map Letter.flip)=(reduce w).flip := by
  exact run_flip w ⟨[],[]⟩

lemma burgers_flip_empty_iff (w : List Letter) :
    (reduce (w.map Letter.flip)).burgers=[] ↔ (reduce w).burgers=[] := by
  simp [reduce_flip,Evaluation.flip]

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_InventoryDrift
attribute [-instance] _root_.OAI.FKCRT.Inventory.instMeasurableSingletonClassListLetter _root_.OAI.FKCRT.Inventory.instMeasurableSpaceListLetter _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def tail (n : ℕ) (x : ℕ → Letter) : ℕ → Letter := fun k => x (n+k)
lemma tail_zero (x : ℕ → Letter) : tail 0 x=x := by ext k; simp [tail]
lemma tail_tail (m n : ℕ) (x : ℕ → Letter) : tail m (tail n x)=tail (n+m) x := by
  ext k; simp [tail,Nat.add_assoc]

lemma measurable_tail (n : ℕ) : Measurable (tail n) := by
  exact Measurable.of_eval fun index => measurable_pi_apply (n+index)

lemma tail_preserving (P : Parameters) (n : ℕ) : MeasurePreserving (tail n) (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_tail n,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Nat.add_left_cancel h)

lemma revealed_add (x : ℕ → Letter) (n k : ℕ) :
    revealed x (n+k)=revealed (tail n x) k++revealed x n := by
  induction k with
  | zero => simp [revealed_zero]
  | succ k ih =>
    rw [show n+(k+1)=n+k+1 by omega,revealed_succ,revealed_succ,ih]
    rfl

lemma revealed_extension (x : ℕ → Letter) {n m : ℕ} (h : n ≤ m) :
    ∃ w,revealed x m=w++revealed x n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨revealed (tail n x) k,revealed_add x n k⟩

def firstType (x : ℕ → Letter) : Bool :=
  (reduce (revealed x ((firstSurvivor x).untopD 0+1))).burgers.headD false

lemma firstType_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    firstType x=(reduce (revealed x (n+1))).burgers.headD false := by
  unfold firstType
  rw [h]
  rfl

lemma firstType_of_survivor {x : ℕ → Letter} {n : ℕ} {b : Bool} {bs : List Bool}
    (h : (reduce (revealed x n)).burgers=b::bs) : firstType x=b := by
  cases n with
  | zero => simp [revealed_zero,reduce,run] at h
  | succ n =>
    have hle : firstSurvivor x ≤ WithTop.some n :=
      (firstSurvivor_le_iff x n).mpr (by rw [h]; simp)
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
    have hk' : firstSurvivor x=WithTop.some k := hk.symm
    obtain ⟨c,hc,_⟩ := firstSurvivor_shape hk'
    obtain ⟨w,hw⟩ := revealed_extension x (show k+1 ≤ n+1 from by
      rw [← hk] at hle; exact Nat.add_le_add_right (WithTop.coe_le_coe.mp hle) 1)
    have hp := freshest_survivor_prepend (revealed x (k+1)) w (congrArg Evaluation.burgers hc)
    rw [← hw,h] at hp
    simp only [List.head?_cons,Option.some.injEq] at hp
    rw [firstType_of_hit hk',hc]
    exact hp.symm

lemma measurable_firstType : Measurable firstType := by
  have hm (n : ℕ) : Measurable (fun x : ℕ → Letter =>
      (reduce (revealed x (n+1))).burgers.headD false) :=
    (prefix_measurable n (fun y => (reduce (List.ofFn y).reverse).burgers.headD false)).mono
      (rawFiltration.le n) le_rfl
  exact (measurable_from_prod_countable_right (f := fun z : ℕ × (ℕ → Letter) =>
      (reduce (revealed z.2 (z.1+1))).burgers.headD false) hm).comp
      (((measurable_of_countable (fun n : WithTop ℕ => n.untopD 0)).comp measurable_firstSurvivor).prodMk measurable_id)

def typedRevealed (x : ℕ → Letter) (n : ℕ) : List (Letter × Bool) :=
  (List.ofFn (fun i : Fin n => (x i,firstType (tail (i+1) x)))).reverse

lemma typedRevealed_erase (x : ℕ → Letter) (n : ℕ) :
    (typedRevealed x n).map Prod.fst=revealed x n := by
  simp [typedRevealed,revealed,List.map_reverse,List.map_ofFn,Function.comp_def]

lemma typedRevealed_append_newest (x : ℕ → Letter) (n : ℕ) :
    typedRevealed x (n+1)=typedRevealed (tail 1 x) n++[(x 0,firstType (tail 1 x))] := by
  unfold typedRevealed
  rw [List.ofFn_succ,List.reverse_cons]
  apply congrArg (· ++ [(x 0,firstType (tail 1 x))])
  apply congrArg List.reverse
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · simp [FKCRT.Inventory.tail,Nat.add_comm]
  · change firstType (tail (i.val+1+1) x)=firstType (tail (i.val+1) (tail 1 x))
    rw [tail_tail]
    congr 2
    omega

lemma typedRevealed_valid (x : ℕ → Letter) (n : ℕ) : ValidTyping (typedRevealed x n) [] := by
  induction n generalizing x with
  | zero => simp [typedRevealed,ValidTyping]
  | succ n ih =>
    rw [typedRevealed_append_newest]
    apply (ValidTyping_append _ _ ⟨[],[]⟩).mpr
    refine ⟨ih _,?_,trivial⟩
    intro ha
    have he := congrArg Evaluation.burgers (erase_typedRun (typedRevealed (tail 1 x) n) ⟨[],[]⟩)
    rw [typedRevealed_erase] at he
    change (typedRun (typedRevealed (tail 1 x) n) ⟨[],[]⟩).burgers=
      (reduce (revealed (tail 1 x) n)).burgers at he
    rw [he]
    cases hb : (reduce (revealed (tail 1 x) n)).burgers with
    | nil => exact Or.inl rfl
    | cons b bs =>
      right
      simp only [List.head?_cons,Option.some.injEq]
      exact (firstType_of_survivor hb).symm

def D (x : ℕ → Letter) (n : ℕ) : ℤ := assignedSign (x n,firstType (tail (n+1) x))
def Dsum (x : ℕ → Letter) (n : ℕ) : ℤ := ∑ i∈Finset.range n,D x i

lemma abs_D (x : ℕ → Letter) (n : ℕ) : |D x n|=1 := abs_assignedSign _
lemma measurable_D (n : ℕ) : Measurable (fun x => D x n) :=
  (measurable_of_countable assignedSign).comp
    ((measurable_pi_apply n).prodMk (measurable_firstType.comp (measurable_tail (n+1))))
lemma measurable_Dsum (n : ℕ) : Measurable (fun x => Dsum x n) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_D i)

lemma typedRevealed_sum (x : ℕ → Letter) (n : ℕ) :
    ((typedRevealed x n).map assignedSign).sum=Dsum x n := by
  simp only [typedRevealed,List.map_reverse,List.sum_reverse,List.map_ofFn,List.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (D x) n

lemma D_shift (x : ℕ → Letter) (n k : ℕ) : D (tail n x) k=D x (n+k) := by
  simp [D,tail_tail,tail,Nat.add_assoc]
lemma Dsum_add (x : ℕ → Letter) (n k : ℕ) : Dsum x (n+k)=Dsum x n+Dsum (tail n x) k := by
  simp only [Dsum,Finset.sum_range_add,D_shift]

lemma Dsum_no_survivor {x : ℕ → Letter} {n : ℕ} (h : (reduce (revealed x n)).burgers=[]) :
    |Dsum x n| ≤ -signSum x n := by
  have hh := typedRun_no_survivor_bound (typedRevealed x n) (typedRevealed_valid x n)
    (by rw [typedRevealed_erase]; exact h)
  rw [typedRevealed_sum,typedRevealed_erase] at hh
  have hs := reduce_imbalance (revealed x n)
  rw [imbalance,h,revealed_sum] at hs
  simp only [List.length_nil,Nat.cast_zero,zero_sub] at hs
  omega

lemma Dsum_at_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    Dsum x (n+1)=typeSign (firstType x)*(1+(K x:ℤ)) := by
  obtain ⟨b,hb,ho⟩ := firstSurvivor_shape h
  have ht : firstType x=b := firstType_of_survivor (congrArg Evaluation.burgers hb)
  have hh := typedRun_first_survivor_sum (typedRevealed x (n+1)) b (typedRevealed_valid x (n+1))
    (by rw [typedRevealed_erase,hb])
    (by rw [typedRevealed_erase,hb]; exact ho)
  rw [typedRevealed_sum,typedRevealed_erase] at hh
  rw [ht,K_of_hit h]
  exact hh

lemma abs_Dsum_le (x : ℕ → Letter) (n : ℕ) : |Dsum x n| ≤ n := by
  unfold Dsum
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_D])

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma law_flip_preserving (P : Parameters) :
    MeasurePreserving Letter.flip (law P).toMeasure (law P).toMeasure := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton a)]
  have he : Letter.flip ⁻¹' {a}={a.flip} := by
    ext b
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      simpa only [Letter.flip_flip] using congrArg Letter.flip h
    · rintro rfl
      exact Letter.flip_flip _
  rw [he,law_singleton,law_singleton]
  congr 1
  cases a with
  | burger b => rfl
  | order o => cases o <;> rfl

def flipStream (x : ℕ → Letter) : ℕ → Letter := fun i => (x i).flip
lemma measurable_flipStream : Measurable flipStream := by
  exact Measurable.of_eval (fun index => (measurable_of_countable Letter.flip).comp (measurable_pi_apply index))
lemma flipStream_preserving (P : Parameters) :
    MeasurePreserving flipStream (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_flipStream,?_⟩
  unfold streamLaw flipStream
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => (law P).toMeasure) (fun _ => measurable_of_countable Letter.flip)]
  simp only [(law_flip_preserving P).map_eq]

lemma revealed_flip (x : ℕ → Letter) (n : ℕ) :
    revealed (flipStream x) n=(revealed x n).map Letter.flip := by
  simp [revealed,flipStream,List.map_reverse,List.map_ofFn,Function.comp_def]
lemma firstSurvivor_flip (x : ℕ → Letter) : firstSurvivor (flipStream x)=firstSurvivor x := by
  apply eq_of_forall_ge_iff
  intro n
  cases n with
  | top => simp
  | coe n =>
    rw [firstSurvivor_le_iff,firstSurvivor_le_iff,revealed_flip]
    exact not_congr (burgers_flip_empty_iff (revealed x (n+1)))

lemma firstType_flip_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    firstType (flipStream x)= !(firstType x) := by
  obtain ⟨b,hb,_⟩ := firstSurvivor_shape h
  have hh : firstSurvivor (flipStream x)=WithTop.some n := by rw [firstSurvivor_flip,h]
  rw [firstType_of_hit hh,firstType_of_hit h,revealed_flip,reduce_flip,hb]
  rfl

lemma raw_indep_tail (P : Parameters) (n : ℕ) :
    Indep (rawFiltration n) (MeasurableSpace.comap (tail (n+1)) inferInstance) (streamLaw P ℕ) := by
  let m : ℕ → MeasurableSpace (ℕ → Letter) := fun k =>
    MeasurableSpace.comap (fun x : ℕ → Letter => x k) inferInstance
  have h := indep_iSup_of_disjoint
    (fun k : ℕ => (measurable_pi_apply k : Measurable (fun x : ℕ → Letter => x k)).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ => (law P).toMeasure) (X := fun _ (a : Letter) => a) (fun _ => measurable_id))
    (show Disjoint {k : ℕ | k ≤ n} {k : ℕ | n<k} by exact Set.disjoint_left.mpr (fun k hk hk' => by
      change k ≤ n at hk; change n<k at hk'; omega))
  have hm : Measurable[⨆ k∈{k : ℕ | n<k},m k] (tail (n+1)) := by
    let : MeasurableSpace (ℕ → Letter) := ⨆ k∈{k : ℕ | n<k},m k
    apply Measurable.of_eval
    intro k
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (n+1+k) (le_iSup_of_le (show n<n+1+k by omega) le_rfl)
  apply indep_of_indep_of_le_right _ hm.comap_le
  simpa only [rawFiltration,Filtration.natural,Set.mem_ofPred_eq,streamLaw] using h

lemma raw_fun_indep_tail (P : Parameters) (n : ℕ) {β : Type*} [MeasurableSpace β]
    {f : (ℕ → Letter) → β} (hf : Measurable[rawFiltration n] f) :
    IndepFun f (tail (n+1)) (streamLaw P ℕ) := by
  exact indep_of_indep_of_le_left (raw_indep_tail P n) hf.comap_le

lemma integrable_Dsum (P : Parameters) (n : ℕ) : Integrable (fun x => (Dsum x n:ℝ)) (streamLaw P ℕ) := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_Dsum n)).aestronglyMeasurable) n
  exact ae_of_all _ (fun x => by
    change |(Dsum x n:ℝ)| ≤ (n:ℝ)
    exact_mod_cast abs_Dsum_le x n)


/-- Signed first-survivor event. Unlike the totalized first type, this is raw-prefix measurable. -/
def hitType (n : ℕ) (x : ℕ → Letter) : ℝ :=
  if firstSurvivor x=WithTop.some n then (typeSign (firstType x):ℝ) else 0

lemma measurable_hitType_raw (n : ℕ) : Measurable[rawFiltration n] (hitType n) := by
  have he : hitType n=fun x => if firstSurvivor x=WithTop.some n then
      (typeSign ((reduce (revealed x (n+1))).burgers.headD false):ℝ) else 0 := by
    ext x
    unfold hitType
    split_ifs with h
    · rw [firstType_of_hit h]
    · rfl
  rw [he]
  apply Measurable.ite (firstSurvivor_stopping.measurableSet_eq n)
  · exact prefix_measurable n (fun y => (typeSign ((reduce (List.ofFn y).reverse).burgers.headD false):ℝ))
  · exact measurable_const
lemma measurable_hitType (n : ℕ) : Measurable (hitType n) :=
  (measurable_hitType_raw n).mono (rawFiltration.le n) le_rfl
lemma abs_hitType_le (n : ℕ) (x : ℕ → Letter) : |hitType n x| ≤ 1 := by
  unfold hitType
  split_ifs
  · simpa only [← Int.cast_abs,abs_typeSign,Int.cast_one] using (le_rfl : (1:ℝ) ≤ 1)
  · simp
lemma integrable_hitType (P : Parameters) (n : ℕ) : Integrable (hitType n) (streamLaw P ℕ) :=
  Integrable.of_bound (measurable_hitType n).aestronglyMeasurable 1 (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using abs_hitType_le n x)
lemma hitType_flip (n : ℕ) (x : ℕ → Letter) : hitType n (flipStream x)= -hitType n x := by
  unfold hitType
  rw [firstSurvivor_flip]
  split_ifs with h
  · rw [firstType_flip_of_hit h,typeSign_not,Int.cast_neg]
  · simp
lemma integral_hitType (P : Parameters) (n : ℕ) : ∫ x,hitType n x ∂streamLaw P ℕ=0 := by
  have h := (flipStream_preserving P).hasLaw.integral_comp
    (f := hitType n) (measurable_hitType n).aestronglyMeasurable
  change (∫ x,hitType n (flipStream x) ∂streamLaw P ℕ)=∫ x,hitType n x ∂streamLaw P ℕ at h
  simp only [hitType_flip,integral_neg] at h
  linarith
lemma integral_hitType_mul_older (P : Parameters) (n k : ℕ) :
    ∫ x,hitType n x*(Dsum (tail (n+1) x) k:ℝ) ∂streamLaw P ℕ=0 := by
  have h := (raw_fun_indep_tail P n (measurable_hitType_raw n)).comp measurable_id
    ((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_Dsum k))
  have hh := h.integral_mul_eq_mul_integral (integrable_hitType P n).aestronglyMeasurable
    ((tail_preserving P (n+1)).integrable_comp_of_integrable (integrable_Dsum P k)).aestronglyMeasurable
  change (∫ x,hitType n x*(Dsum (tail (n+1) x) k:ℝ) ∂streamLaw P ℕ)=
    (∫ x,hitType n x ∂streamLaw P ℕ)*(∫ x,(Dsum (tail (n+1) x) k:ℝ) ∂streamLaw P ℕ) at hh
  rw [integral_hitType,zero_mul] at hh
  exact hh


end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def T (x : ℕ → Letter) : ℝ := typeSign (firstType x)
lemma measurable_T : Measurable T :=
  (measurable_of_countable (fun b : Bool => (typeSign b:ℝ))).comp measurable_firstType
lemma abs_T (x : ℕ → Letter) : |T x|=1 := by
  unfold T
  exact_mod_cast abs_typeSign (firstType x)
lemma T_sq (x : ℕ → Letter) : T x^2=1 := by
  unfold T
  exact_mod_cast typeSign_sq (firstType x)
lemma bounded_integrable (P : Parameters) {f : (ℕ → Letter) → ℝ} (hf : Measurable f)
    (C : ℝ) (hC : ∀ x,|f x| ≤ C) : Integrable f (streamLaw P ℕ) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hC x)
lemma measurable_Dsum_real (n : ℕ) : Measurable (fun x => (Dsum x n:ℝ)) :=
  (measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_Dsum n)
lemma abs_Dsum_real_le (x : ℕ → Letter) (n : ℕ) : |(Dsum x n:ℝ)| ≤ n := by
  exact_mod_cast abs_Dsum_le x n
lemma integrable_T_Dsum (P : Parameters) (n : ℕ) :
    Integrable (fun x => T x*(Dsum x n:ℝ)) (streamLaw P ℕ) := by
  apply bounded_integrable P (measurable_T.mul (measurable_Dsum_real n)) n
  intro x
  change |T x*(Dsum x n:ℝ)| ≤ (n:ℝ)
  rw [abs_mul,abs_T,one_mul]
  exact abs_Dsum_real_le x n

def truncK (m : ℕ) (x : ℕ → Letter) : ℝ :=
  if firstSurvivor x<WithTop.some m then K x else 0
lemma measurable_truncK (m : ℕ) : Measurable (truncK m) :=
  (((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp measurable_K).ite
    (measurableSet_lt measurable_firstSurvivor measurable_const) measurable_const)
lemma integrable_truncK (P : Parameters) (m : ℕ) : Integrable (truncK m) (streamLaw P ℕ) := by
  have he : truncK m=({x | firstSurvivor x<WithTop.some m} : Set (ℕ → Letter)).indicator (fun x => (K x:ℝ)) := by
    ext x
    simp [truncK,Set.indicator]
  rw [he]
  exact (integrable_K P).indicator (measurableSet_lt measurable_firstSurvivor measurable_const)

lemma truncK_nonneg (m : ℕ) (x : ℕ → Letter) : 0 ≤ truncK m x := by
  unfold truncK
  split_ifs <;> positivity
lemma truncK_le (m : ℕ) (x : ℕ → Letter) : truncK m x ≤ K x := by
  unfold truncK
  split_ifs
  · exact le_rfl
  · positivity
lemma truncK_tendsto (P : Parameters) :
    Tendsto (fun m => ∫ x,truncK m x ∂streamLaw P ℕ) atTop (𝓝 (∫ x,(K x:ℝ) ∂streamLaw P ℕ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (K x:ℝ))
    (fun m => (measurable_truncK m).aestronglyMeasurable) (integrable_K P)
  · intro m
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (truncK_nonneg m x)] using truncK_le m x)
  · filter_upwards [firstSurvivor_finite P] with x hx
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (k+1)] with m hm
    unfold truncK
    rw [← hk,ite_eq_left (WithTop.coe_lt_coe.mpr (by omega))]

/-- The signed contribution of letters strictly older than the first survivor. -/
def olderCorrection (m : ℕ) (x : ℕ → Letter) : ℝ :=
  ∑ j∈Finset.range m,hitType j x*(Dsum (tail (j+1) x) (m-j-1):ℝ)
lemma integrable_older_term (P : Parameters) (m j : ℕ) :
    Integrable (fun x => hitType j x*(Dsum (tail (j+1) x) (m-j-1):ℝ)) (streamLaw P ℕ) := by
  apply bounded_integrable P
    ((measurable_hitType j).mul ((measurable_Dsum_real (m-j-1)).comp (measurable_tail (j+1)))) (m-j-1:ℕ)
  intro x
  change |hitType j x*(Dsum (tail (j+1) x) (m-j-1):ℝ)| ≤ (m-j-1:ℕ)
  rw [abs_mul]
  exact (mul_le_mul (abs_hitType_le j x) (abs_Dsum_real_le _ _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
lemma integrable_olderCorrection (P : Parameters) (m : ℕ) : Integrable (olderCorrection m) (streamLaw P ℕ) :=
  integrable_finsetSum _ (fun j _ => integrable_older_term P m j)
lemma integral_olderCorrection (P : Parameters) (m : ℕ) : ∫ x,olderCorrection m x ∂streamLaw P ℕ=0 := by
  unfold olderCorrection
  rw [integral_finsetSum _ (fun j _ => integrable_older_term P m j)]
  simp only [integral_hitType_mul_older,Finset.sum_const_zero]
lemma olderCorrection_hit {x : ℕ → Letter} {m j : ℕ} (h : firstSurvivor x=WithTop.some j)
    (hj : j < m) : olderCorrection m x=T x*(Dsum (tail (j+1) x) (m-j-1):ℝ) := by
  unfold olderCorrection
  rw [Finset.sum_eq_single j]
  · simp only [hitType,h,ite_eq_left,T]
  · intro k _ hkj
    have hk : firstSurvivor x ≠ WithTop.some k := by
      rw [h]
      exact fun he => hkj (WithTop.coe_injective he).symm
    rw [hitType,ite_eq_right hk,zero_mul]
  · intro hj'
    exact (hj' (Finset.mem_range.mpr hj)).elim
lemma olderCorrection_nohit {x : ℕ → Letter} {m : ℕ}
    (h : ¬firstSurvivor x<WithTop.some m) : olderCorrection m x=0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hn : firstSurvivor x ≠ WithTop.some j := by
    intro he
    exact h (by rw [he]; exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hj))
  rw [hitType,ite_eq_right hn,zero_mul]

lemma covariance_pointwise (m : ℕ) (x : ℕ → Letter) :
    1-stoppedDefect m x+2*truncK (m+1) x+olderCorrection (m+1) x ≤ T x*(Dsum x (m+1):ℝ) := by
  by_cases h : firstSurvivor x<WithTop.some (m+1)
  · obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h)
    have hh : firstSurvivor x=WithTop.some j := hj.symm
    have hjm : j < m+1 := by rw [← hj] at h; exact WithTop.coe_lt_coe.mp h
    rw [truncK,ite_eq_left h,stoppedDefect_eq_K (by rw [hh]; exact WithTop.coe_le_coe.mpr (by omega)),olderCorrection_hit hh hjm]
    have he : Dsum x (m+1)=typeSign (firstType x)*(1+(K x:ℤ))+Dsum (tail (j+1) x) (m+1-j-1) := by
      calc
        Dsum x (m+1)=Dsum x (j+1+(m+1-j-1)) := by congr 1; omega
        _ = _ := by rw [Dsum_add,Dsum_at_hit hh]
    have her : (Dsum x (m+1):ℝ)=T x*(1+(K x:ℝ))+(Dsum (tail (j+1) x) (m+1-j-1):ℝ) := by
      dsimp only [T]
      exact_mod_cast he
    rw [her]
    nlinarith [T_sq x]
  · rw [truncK,ite_eq_right h,olderCorrection_nohit h]
    have hle : ¬firstSurvivor x ≤ WithTop.some m := by
      intro hl
      exact h (lt_of_le_of_lt hl (WithTop.coe_lt_coe.mpr (by omega)))
    have hb : (reduce (revealed x (m+1))).burgers=[] := by
      simpa only [firstSurvivor_le_iff,not_not] using hle
    have hs : stoppedDefect m x=1-(signSum x (m+1):ℝ) := by
      change 1-(signSum x ((min (WithTop.some m) (firstSurvivor x)).untopA+1):ℝ)=_
      rw [min_eq_left (le_of_not_ge hle),WithTop.untopA_eq_untop WithTop.coe_ne_top,WithTop.untop_coe]
    rw [hs]
    have hd : |(Dsum x (m+1):ℝ)| ≤ -(signSum x (m+1):ℝ) := by exact_mod_cast Dsum_no_survivor hb
    have ha : |T x*(Dsum x (m+1):ℝ)|=|(Dsum x (m+1):ℝ)| := by rw [abs_mul,abs_T,one_mul]
    have hl := neg_abs_le (T x*(Dsum x (m+1):ℝ))
    rw [ha] at hl
    linarith

def covariance (P : Parameters) (m : ℕ) : ℝ := ∫ x,T x*(Dsum x m:ℝ) ∂streamLaw P ℕ
lemma covariance_lower (P : Parameters) (m : ℕ) :
    2*(∫ x,truncK m x ∂streamLaw P ℕ) ≤ covariance P m := by
  cases m with
  | zero => simp [truncK,covariance,Dsum]
  | succ m =>
    have hi := integral_mono
      ((((integrable_const (1:ℝ)).sub ((stoppedDefect_martingale P).integrable m)).add
        ((integrable_truncK P (m+1)).const_mul 2)).add (integrable_olderCorrection P (m+1)))
      (integrable_T_Dsum P (m+1)) (covariance_pointwise m)
    simp only [Pi.add_apply,Pi.sub_apply] at hi
    rw [integral_add,integral_add,integral_sub,integral_const_mul,stoppedDefect_integral,
      integral_olderCorrection] at hi
    · simpa only [covariance,integral_const,probReal_univ,one_smul,sub_self,zero_add,add_zero] using hi
    all_goals first | exact integrable_const _ | exact (stoppedDefect_martingale P).integrable m |
      exact (integrable_truncK P (m+1)).const_mul 2 | exact integrable_olderCorrection P (m+1) |
      exact (integrable_const _).sub ((stoppedDefect_martingale P).integrable m) |
      exact ((integrable_const _).sub ((stoppedDefect_martingale P).integrable m)).add
        ((integrable_truncK P (m+1)).const_mul 2)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma integral_assignedSign (P : Parameters) (b : Bool) :
    ∫ a,(assignedSign (a,b):ℝ) ∂(law P).toMeasure= -(P.p/2)*(typeSign b:ℝ) := by
  rw [integral_law,sum_letters]
  cases b <;> norm_num [mass,assignedSign,orderType,typeSign]
lemma abs_assignedSign_real (a : Letter) (b : Bool) : |(assignedSign (a,b):ℝ)|=1 := by
  exact_mod_cast abs_assignedSign (a,b)
lemma measurable_D_real (n : ℕ) : Measurable (fun x => (D x n:ℝ)) :=
  (measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_D n)
lemma Dsum_newest (x : ℕ → Letter) (m : ℕ) : Dsum x (m+1)=D x 0+Dsum (tail 1 x) m := by
  calc
    Dsum x (m+1)=Dsum x (1+m) := by congr 1; omega
    _ = _ := by rw [Dsum_add]; simp [Dsum]
lemma integral_newest_older (P : Parameters) (m : ℕ) :
    ∫ x,(D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ) ∂streamLaw P ℕ= -(P.p/2)*covariance P m := by
  let F : Letter × (ℕ → Letter) → ℝ := fun z =>
    (assignedSign (z.1,firstType z.2):ℝ)*(Dsum z.2 m:ℝ)
  have hF : Measurable F := by
    exact ((measurable_of_countable (fun a : Letter × Bool => (assignedSign a:ℝ))).comp
      (measurable_fst.prodMk (measurable_firstType.comp measurable_snd))).mul
      ((measurable_Dsum_real m).comp measurable_snd)
  have hi : Integrable F ((law P).toMeasure.prod (streamLaw P ℕ)) := by
    apply Integrable.of_bound hF.aestronglyMeasurable m
    exact ae_of_all _ fun z => by
      change |(assignedSign (z.1,firstType z.2):ℝ)*(Dsum z.2 m:ℝ)| ≤ m
      rw [abs_mul,abs_assignedSign_real,one_mul]
      exact abs_Dsum_real_le z.2 m
  have hh := (raw_fun_indep_tail P 0 (raw_adapted 0 0 le_rfl)).hasLaw_prod
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).hasLaw
    (tail_preserving P 1).hasLaw
  have he := hh.integral_comp hi.aestronglyMeasurable
  change (∫ x,(D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ) ∂streamLaw P ℕ)=∫ z,F z ∂((law P).toMeasure.prod (streamLaw P ℕ)) at he
  rw [he,integral_prod_symm _ hi]
  have hx (x : ℕ → Letter) : ∫ a,F (a,x) ∂(law P).toMeasure= -(P.p/2)*(T x*(Dsum x m:ℝ)) := by
    dsimp only [F,T]
    rw [integral_mul_const,integral_assignedSign]
    ring
  simp only [hx,integral_const_mul,covariance]

def varianceSum (P : Parameters) (m : ℕ) : ℝ := ∫ x,(Dsum x m:ℝ)^2 ∂streamLaw P ℕ
lemma varianceSum_nonneg (P : Parameters) (m : ℕ) : 0 ≤ varianceSum P m :=
  integral_nonneg (fun _ => sq_nonneg _)
lemma integrable_Dsum_sq (P : Parameters) (m : ℕ) : Integrable (fun x => (Dsum x m:ℝ)^2) (streamLaw P ℕ) := by
  apply bounded_integrable P ((measurable_Dsum_real m).pow_const 2) ((m:ℝ)^2)
  intro x
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Dsum x m:ℝ)) (Nat.cast_nonneg m)).mpr
    (abs_Dsum_real_le x m)
lemma integrable_newest_older (P : Parameters) (m : ℕ) :
    Integrable (fun x => (D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ)) (streamLaw P ℕ) := by
  apply bounded_integrable P ((measurable_D_real 0).mul ((measurable_Dsum_real m).comp (measurable_tail 1))) m
  intro x
  change |(D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ)| ≤ m
  rw [abs_mul]
  have hd : |(D x 0:ℝ)|=1 := by exact_mod_cast abs_D x 0
  rw [hd,one_mul]
  exact abs_Dsum_real_le _ _
lemma varianceSum_increment (P : Parameters) (m : ℕ) :
    varianceSum P (m+1)-varianceSum P m=1-P.p*covariance P m := by
  have he (x : ℕ → Letter) : (Dsum x (m+1):ℝ)^2=
      1+(Dsum (tail 1 x) m:ℝ)^2+2*((D x 0:ℝ)*(Dsum (tail 1 x) m:ℝ)) := by
    rw [Dsum_newest,Int.cast_add]
    have hd : (D x 0:ℝ)^2=1 := by
      have h : |(D x 0:ℝ)|=1 := by exact_mod_cast abs_D x 0
      nlinarith [sq_abs (D x 0:ℝ)]
    nlinarith
  have hi := (tail_preserving P 1).integrable_comp_of_integrable (integrable_Dsum_sq P m)
  have hshift := (tail_preserving P 1).hasLaw.integral_comp (integrable_Dsum_sq P m).aestronglyMeasurable
  change (∫ x,(Dsum (tail 1 x) m:ℝ)^2 ∂streamLaw P ℕ)=varianceSum P m at hshift
  have hh : varianceSum P (m+1)=1+varianceSum P m+2*(-(P.p/2)*covariance P m) := by
    unfold varianceSum
    simp only [he]
    rw [integral_add,integral_add,integral_const_mul,integral_newest_older,hshift]
    · simp only [integral_const,probReal_univ,one_smul,varianceSum]
    all_goals first | exact (integrable_const _).add hi | exact hi | exact integrable_const _ |
      exact (integrable_newest_older P m).const_mul 2

  linarith
lemma varianceSum_increment_le (P : Parameters) (m : ℕ) :
    varianceSum P (m+1)-varianceSum P m ≤ 1-2*P.p*(∫ x,truncK m x ∂streamLaw P ℕ) := by
  rw [varianceSum_increment]
  have h := mul_le_mul_of_nonneg_left (covariance_lower P m) P.pos.le
  linarith

/-- Strict drift of the actual iid inventory word, without assuming a finite mean stopping time. -/
theorem integral_K_strict_drift (P : Parameters) :
    (∫ x,(K x:ℝ) ∂streamLaw P ℕ) ≤ 1/(2*P.p) := by
  by_contra h
  have hp : 0<2*P.p := mul_pos (by norm_num) P.pos
  have hm : 1<2*P.p*(∫ x,(K x:ℝ) ∂streamLaw P ℕ) := by
    have hh := (div_lt_iff₀ hp).mp (lt_of_not_ge h)
    nlinarith
  let c : ℝ := (1-2*P.p*(∫ x,(K x:ℝ) ∂streamLaw P ℕ))/2
  have hc : c<0 := by dsimp [c]; linarith
  have ht : Tendsto (fun m => 1-2*P.p*(∫ x,truncK m x ∂streamLaw P ℕ)) atTop (𝓝 (2*c)) := by
    have he : 2*c=1-2*P.p*(∫ x,(K x:ℝ) ∂streamLaw P ℕ) := by dsimp [c]; ring
    rw [he]
    exact tendsto_const_nhds.sub ((truncK_tendsto P).const_mul (2*P.p))
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 c (by linarith))
  have hb (k : ℕ) : varianceSum P (N+k) ≤ varianceSum P N+(k:ℝ)*c := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := (varianceSum_increment_le P (N+k)).trans (hN (N+k) (by omega)).le
      push_cast
      rw [show N+(k+1)=N+k+1 by omega]
      linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (varianceSum P N/(-c))
  have hn : 0 < -c := by linarith
  have hh := (div_lt_iff₀ hn).mp hk
  have hz := varianceSum_nonneg P (N+k)
  have hb' := hb k
  nlinarith

theorem integral_K_lt_one (P : Parameters) : (∫ x,(K x:ℝ) ∂streamLaw P ℕ)<1 := by
  apply lt_of_le_of_lt (integral_K_strict_drift P)
  apply (div_lt_one (mul_pos (by norm_num) P.pos)).mpr
  linarith [P.lower]

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_InventoryRenewal
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def survivorTail (x : ℕ → Letter) : ℕ → Letter := tail ((firstSurvivor x).untopD 0+1) x
def survivorData (x : ℕ → Letter) : ℕ × Bool := (K x,firstType x)
def prefixData (n : ℕ) (x : ℕ → Letter) : ℕ × Bool :=
  ((reduce (revealed x (n+1))).orders.length,(reduce (revealed x (n+1))).burgers.headD false)
lemma measurable_prefixData (n : ℕ) : Measurable[rawFiltration n] (prefixData n) :=
  prefix_measurable n (fun y => ((reduce (List.ofFn y).reverse).orders.length,
    (reduce (List.ofFn y).reverse).burgers.headD false))
lemma measurable_survivorData : Measurable survivorData := measurable_K.prodMk measurable_firstType
lemma measurable_survivorTail : Measurable survivorTail := by
  have hm : Measurable (fun x : ℕ → Letter => (firstSurvivor x).untopD 0+1) :=
    (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0+1)).comp measurable_firstSurvivor
  have ht : Measurable (fun z : ℕ × (ℕ → Letter) => tail z.1 z.2) :=
    measurable_from_prod_countable_right (fun n => measurable_tail n)
  exact ht.comp (hm.prodMk measurable_id)
lemma survivorData_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    survivorData x=prefixData n x := by
  simp only [survivorData,prefixData,K_of_hit h,firstType_of_hit h]
lemma survivorTail_of_hit {x : ℕ → Letter} {n : ℕ} (h : firstSurvivor x=WithTop.some n) :
    survivorTail x=tail (n+1) x := by
  simp only [survivorTail,h]
  rfl

lemma survivor_rectangle_sum (P : Parameters) (A : Set (ℕ × Bool)) (B : Set (ℕ → Letter))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (survivorData ⁻¹' A ∩ survivorTail ⁻¹' B)=
      (∑' n : ℕ,streamLaw P ℕ ({x | firstSurvivor x=WithTop.some n} ∩ prefixData n ⁻¹' A))*streamLaw P ℕ B := by
  let C : ℕ → Set (ℕ → Letter) := fun n => {x | firstSurvivor x=WithTop.some n} ∩ prefixData n ⁻¹' A
  have hC (n : ℕ) : MeasurableSet[rawFiltration n] (C n) :=
    (firstSurvivor_stopping.measurableSet_eq n).inter (measurable_prefixData n hA)
  have hCm (n : ℕ) : MeasurableSet (C n) := rawFiltration.le n _ (hC n)
  have he : (survivorData ⁻¹' A ∩ survivorTail ⁻¹' B : Set (ℕ → Letter)) =ᵐ[streamLaw P ℕ]
      (⋃ n,C n ∩ tail (n+1) ⁻¹' B : Set (ℕ → Letter)) := by
    filter_upwards [firstSurvivor_finite P] with x hx
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    have hn' : firstSurvivor x=WithTop.some n := hn.symm
    apply propext
    constructor
    · rintro ⟨ha,hb⟩
      exact Set.mem_iUnion.mpr ⟨n,⟨hn',by simpa only [Set.mem_preimage,← survivorData_of_hit hn'] using ha⟩,
        by simpa only [Set.mem_preimage,← survivorTail_of_hit hn'] using hb⟩
    · intro h
      obtain ⟨m,⟨hm,ha⟩,hb⟩ := Set.mem_iUnion.mp h
      exact ⟨by simpa only [Set.mem_preimage,survivorData_of_hit hm] using ha,
        by simpa only [Set.mem_preimage,survivorTail_of_hit hm] using hb⟩
  rw [measure_congr he,measure_iUnion]
  · have hs (n : ℕ) : streamLaw P ℕ (C n ∩ tail (n+1) ⁻¹' B)=streamLaw P ℕ (C n)*streamLaw P ℕ B := by
      have h := ((indep_iff_forall_indepSet _).mp (raw_indep_tail P n) _ _ (hC n)
        (measurable_iff_comap_le.mpr le_rfl hB)).measure_inter_eq_mul
      rw [(tail_preserving P (n+1)).measure_preimage hB.nullMeasurableSet] at h
      exact h
    simp_rw [hs]
    rw [ENNReal.tsum_mul_right]
  · intro n m hnm
    exact Set.disjoint_left.mpr (fun x hn hm => hnm (WithTop.coe_injective (hn.1.1.symm.trans hm.1.1)))
  · intro n
    exact (hCm n).inter ((measurable_tail (n+1)) hB)

lemma survivor_rectangle (P : Parameters) (A : Set (ℕ × Bool)) (B : Set (ℕ → Letter))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (survivorData ⁻¹' A ∩ survivorTail ⁻¹' B)=
      streamLaw P ℕ (survivorData ⁻¹' A)*streamLaw P ℕ B := by
  rw [survivor_rectangle_sum P A B hA hB]
  have h := survivor_rectangle_sum P A Set.univ hA MeasurableSet.univ
  simp only [Set.preimage_univ,Set.inter_univ,measure_univ,mul_one] at h
  rw [h]
lemma survivorTail_preserving (P : Parameters) :
    MeasurePreserving survivorTail (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_survivorTail,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply measurable_survivorTail hB]
  simpa using survivor_rectangle P Set.univ B MeasurableSet.univ hB
lemma survivorData_indep_tail (P : Parameters) : IndepFun survivorData survivorTail (streamLaw P ℕ) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hA hB
  rw [(survivorTail_preserving P).measure_preimage hB.nullMeasurableSet]
  exact survivor_rectangle P A B hA hB

def parsingData (j : ℕ) (x : ℕ → Letter) : ℕ × Bool := survivorData (survivorTail^[j] x)
lemma parsingData_iid (P : Parameters) : iIndepFun parsingData (streamLaw P ℕ) :=
  TreeCoding.regenerative_iIndepFun (streamLaw P ℕ) survivorData survivorTail measurable_survivorData
    (survivorTail_preserving P) (survivorData_indep_tail P)
lemma parsingData_identDistrib (P : Parameters) (j : ℕ) :
    IdentDistrib (parsingData j) survivorData (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨(measurable_survivorData.comp ((survivorTail_preserving P).iterate j).measurable).aemeasurable,
    measurable_survivorData.aemeasurable,?_⟩
  change Measure.map (survivorData ∘ survivorTail^[j]) (streamLaw P ℕ)=_
  rw [← Measure.map_map measurable_survivorData ((survivorTail_preserving P).iterate j).measurable,
    ((survivorTail_preserving P).iterate j).map_eq]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def parsingK (j : ℕ) (x : ℕ → Letter) : ℕ := (parsingData j x).1
lemma measurable_parsingK (j : ℕ) : Measurable (parsingK j) :=
  measurable_K.comp (measurable_survivorTail.iterate j)
lemma parsingK_iid (P : Parameters) : iIndepFun parsingK (streamLaw P ℕ) :=
  (parsingData_iid P).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
lemma parsingK_identDistrib (P : Parameters) (j : ℕ) :
    IdentDistrib (parsingK j) K (streamLaw P ℕ) (streamLaw P ℕ) :=
  (parsingData_identDistrib P j).comp measurable_fst
lemma integrable_parsingK (P : Parameters) (j : ℕ) :
    Integrable (fun x => (parsingK j x:ℝ)) (streamLaw P ℕ) :=
  ((parsingK_identDistrib P j).comp (measurable_of_countable (fun k : ℕ => (k:ℝ)))).integrable_iff.mpr (integrable_K P)
lemma integral_parsingK (P : Parameters) (j : ℕ) :
    (∫ x,(parsingK j x:ℝ) ∂streamLaw P ℕ)=(∫ x,(K x:ℝ) ∂streamLaw P ℕ) :=
  ((parsingK_identDistrib P j).comp (measurable_of_countable (fun k : ℕ => (k:ℝ)))).integral_eq

def allParsingFinite (x : ℕ → Letter) : Prop := ∀ j,firstSurvivor (survivorTail^[j] x)≠⊤
lemma ae_allParsingFinite (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,allParsingFinite x := by
  apply ae_all_iff.mpr
  intro j
  exact ((survivorTail_preserving P).iterate j).quasiMeasurePreserving.ae (firstSurvivor_finite P)

def parsingLength (x : ℕ → Letter) : ℕ := (firstSurvivor x).untopD 0+1
def parsingOffset : ℕ → (ℕ → Letter) → ℕ
  | 0,_ => 0
  | n+1,x => parsingOffset n x+parsingLength (survivorTail^[n] x)
def rawChunk (j : ℕ) (x : ℕ → Letter) : List Letter :=
  revealed (survivorTail^[j] x) (parsingLength (survivorTail^[j] x))
def shortPrefix : ℕ → (ℕ → Letter) → List Letter
  | 0,_ => []
  | n+1,x => normalWord (reduce (rawChunk n x))++shortPrefix n x

def leftSteps (x : ℕ → Letter) : ℕ := DefectHitting.stopIndex parsingK x
def leftWord (x : ℕ → Letter) : List Letter := revealed x (parsingOffset (leftSteps x) x)
def shortLeftWord (x : ℕ → Letter) : List Letter := shortPrefix (leftSteps x) x

lemma parsingTail_eq (j : ℕ) (x : ℕ → Letter) : survivorTail^[j] x=tail (parsingOffset j x) x := by
  induction j with
  | zero => exact (tail_zero x).symm
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change tail (parsingLength (survivorTail^[j] x)) (survivorTail^[j] x)=_
    conv_lhs => rw [ih]
    rw [tail_tail]
    simp only [parsingOffset,ih]
lemma revealed_offset_succ (j : ℕ) (x : ℕ → Letter) :
    revealed x (parsingOffset (j+1) x)=rawChunk j x++revealed x (parsingOffset j x) := by
  rw [parsingOffset,revealed_add,← parsingTail_eq]
  rfl
lemma run_shortPrefix (j : ℕ) (x : ℕ → Letter) (e : Evaluation) :
    run (shortPrefix j x) e=run (revealed x (parsingOffset j x)) e := by
  induction j generalizing e with
  | zero => rfl
  | succ j ih => rw [shortPrefix,run_append,run_normalWord,ih,revealed_offset_succ,run_append]
lemma run_shortLeftWord (x : ℕ → Letter) (e : Evaluation) : run (shortLeftWord x) e=run (leftWord x) e :=
  run_shortPrefix (leftSteps x) x e

lemma parsing_shape {x : ℕ → Letter} (h : firstSurvivor x≠⊤) :
    ∃ b,reduce (revealed x (parsingLength x))=⟨List.replicate (K x) (some (!b)),[b]⟩ := by
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp h
  have hh : firstSurvivor x=WithTop.some n := hn.symm
  obtain ⟨b,hb,ho⟩ := firstSurvivor_shape hh
  have hlen : parsingLength x=n+1 := by simp only [parsingLength,hh]; rfl
  refine ⟨b,?_⟩
  rw [hlen,hb,K_of_hit hh,hb]
  congr 1
  exact List.eq_replicate_of_mem ho

lemma normal_parsing_length {x : ℕ → Letter} (h : firstSurvivor x≠⊤) :
    (normalWord (reduce (revealed x (parsingLength x)))).length=1+K x := by
  obtain ⟨b,hb⟩ := parsing_shape h
  simp only [hb,normalWord,List.length_append,List.length_map,List.length_replicate,
    List.length_reverse,List.length_singleton,Nat.add_comm]

lemma signSum_add (x : ℕ → Letter) (n k : ℕ) :
    signSum x (n+k)=signSum x n+signSum (tail n x) k := by
  rw [← revealed_sum,revealed_add,List.map_append,List.sum_append,revealed_sum,revealed_sum,add_comm]
lemma signSum_parsing {x : ℕ → Letter} (h : firstSurvivor x≠⊤) :
    signSum x (parsingLength x)=1-(K x:ℤ) := by
  obtain ⟨b,hb⟩ := parsing_shape h
  have he := reduce_imbalance (revealed x (parsingLength x))
  rw [hb,imbalance,List.length_singleton,List.length_replicate,revealed_sum] at he
  exact he.symm
lemma signSum_before_parsing {x : ℕ → Letter} (h : firstSurvivor x≠⊤) {k : ℕ}
    (hk : k<parsingLength x) : signSum x k≤0 := by
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp h
  have hh : firstSurvivor x=WithTop.some n := hn.symm
  have hlen : parsingLength x=n+1 := by simp only [parsingLength,hh]; rfl
  by_contra hp
  have hb : (reduce (revealed x k)).burgers≠[] := survivor_of_sum_pos _ (by rw [revealed_sum]; omega)
  cases k with
  | zero => simp [revealed_zero,reduce,run] at hb
  | succ k =>
    have he := (firstSurvivor_le_iff x k).mpr hb
    rw [hh] at he
    have hnk := WithTop.coe_le_coe.mp he
    omega

lemma signSum_offset {x : ℕ → Letter} (hx : allParsingFinite x) (j : ℕ) :
    signSum x (parsingOffset j x)=DefectHitting.walk parsingK j x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [parsingOffset,signSum_add,← parsingTail_eq,signSum_parsing (hx j),ih,DefectHitting.walk_succ]
    change _+(1-(parsingK j x:ℤ))=_+1-parsingK j x
    ring
lemma shortPrefix_length {x : ℕ → Letter} (hx : allParsingFinite x) (j : ℕ) :
    (shortPrefix j x).length=∑ i∈Finset.range j,(1+parsingK i x) := by
  induction j with
  | zero => simp [shortPrefix]
  | succ j ih =>
    rw [shortPrefix,List.length_append,ih,Finset.sum_range_succ]
    have hh := normal_parsing_length (hx j)
    change (normalWord (reduce (rawChunk j x))).length=1+parsingK j x at hh
    omega
lemma shortLeftWord_length {x : ℕ → Letter} (hx : allParsingFinite x) :
    (shortLeftWord x).length=DefectHitting.stoppedLength parsingK x := shortPrefix_length hx _

lemma signSum_nonpos_prefix {x : ℕ → Letter} (hx : allParsingFinite x) (n : ℕ)
    (hwalk : ∀ j<n,DefectHitting.walk parsingK j x≤0) :
    ∀ k<parsingOffset n x,signSum x k≤0 := by
  induction n with
  | zero => simp [parsingOffset]
  | succ n ih =>
    intro k hk
    by_cases hkn : k<parsingOffset n x
    · exact ih (fun j hj => hwalk j (by omega)) k hkn
    · have hle : parsingOffset n x≤k := by omega
      obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [signSum_add,← parsingTail_eq,signSum_offset hx]
      have hr : r<parsingLength (survivorTail^[n] x) := by rw [parsingOffset] at hk; omega
      exact add_nonpos (hwalk n (by omega)) (signSum_before_parsing (hx n) hr)

lemma ae_left_first_hit (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    signSum x (parsingOffset (leftSteps x) x)=1 ∧
      ∀ k<parsingOffset (leftSteps x) x,signSum x k≤0 := by
  filter_upwards [ae_allParsingFinite P,
    DefectHitting.totalLength_finite measurable_parsingK (parsingK_iid P)
      (integrable_parsingK P) (integral_parsingK P) (integral_K_lt_one P)] with x hx hf
  have hh := DefectHitting.hit_of_totalLength_finite hf
  refine ⟨(signSum_offset hx _).trans (DefectHitting.walk_at_stop hh),?_⟩
  apply signSum_nonpos_prefix hx
  intro j hj
  exact (DefectHitting.stop_spec hh).2 j hj j le_rfl

lemma measurable_shortLeftWord : Measurable shortLeftWord := by
  have hmL : Measurable parsingLength :=
    (measurable_of_countable (fun n : WithTop ℕ => n.untopD 0+1)).comp measurable_firstSurvivor
  have hmc (j : ℕ) : Measurable (rawChunk j) := by
    have hr : Measurable (fun z : ℕ × (ℕ → Letter) => revealed z.2 z.1) :=
      measurable_from_prod_countable_right (fun n => (measurable_of_countable (fun y : Fin n → Letter => (List.ofFn y).reverse)).comp
        (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ))))
    exact hr.comp ((hmL.comp (measurable_survivorTail.iterate j)).prodMk (measurable_survivorTail.iterate j))
  have hms (j : ℕ) : Measurable (shortPrefix j) := by
    induction j with
    | zero => exact measurable_const
    | succ j ih =>
      exact (measurable_of_countable (fun z : List Letter × List Letter => normalWord (reduce z.1)++z.2)).comp ((hmc j).prodMk ih)
  have hf : Measurable (fun z : ℕ × (ℕ → Letter) => shortPrefix z.1 z.2) :=
    measurable_from_prod_countable_right hms
  exact hf.comp ((DefectHitting.measurable_stopIndex measurable_parsingK).prodMk measurable_id)

/-- Source ladder:short-length for the actual first-hit left ladder word,
shortened by the proved reduction-preserving parsing. No E J is used. -/
theorem integrable_shortLeftWord_length (P : Parameters) :
    Integrable (fun x => ((shortLeftWord x).length:ℝ)) (streamLaw P ℕ) := by
  have hh := DefectHitting.integrable_stoppedLength measurable_parsingK (parsingK_iid P)
    (integrable_parsingK P) (integral_parsingK P) (integral_K_lt_one P)
  exact hh.congr ((ae_allParsingFinite P).mono (fun x hx => by change (DefectHitting.stoppedLength parsingK x:ℝ)=((shortLeftWord x).length:ℝ); rw [shortLeftWord_length hx]))

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma K_flip (x : ℕ → Letter) : K (flipStream x)=K x := by
  simp only [K,firstSurvivor_flip,revealed_flip,reduce_flip,Evaluation.flip,List.length_map]
lemma tail_flip (n : ℕ) (x : ℕ → Letter) : tail n (flipStream x)=flipStream (tail n x) := rfl
lemma survivorTail_flip (x : ℕ → Letter) : survivorTail (flipStream x)=flipStream (survivorTail x) := by
  simp only [survivorTail,firstSurvivor_flip,tail_flip]
lemma iterate_survivorTail_flip (j : ℕ) (x : ℕ → Letter) :
    survivorTail^[j] (flipStream x)=flipStream (survivorTail^[j] x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,survivorTail_flip]
lemma parsingK_flip (j : ℕ) (x : ℕ → Letter) : parsingK j (flipStream x)=parsingK j x := by
  change K (survivorTail^[j] (flipStream x))=K (survivorTail^[j] x)
  rw [iterate_survivorTail_flip,K_flip]
lemma leftSteps_flip (x : ℕ → Letter) : leftSteps (flipStream x)=leftSteps x := by
  classical
  unfold leftSteps DefectHitting.stopIndex
  apply Nat.find_congr'
  intro n
  simp only [DefectHitting.stopPredicate,DefectHitting.alive,Set.mem_ofPred_eq,DefectHitting.walk,parsingK_flip]
lemma normalWord_flip (e : Evaluation) : normalWord e.flip=(normalWord e).map Letter.flip := by
  simp only [normalWord,Evaluation.flip,List.map_append,List.map_map,← List.map_reverse,Function.comp_def]
  rfl
lemma rawChunk_flip (j : ℕ) (x : ℕ → Letter) : rawChunk j (flipStream x)=(rawChunk j x).map Letter.flip := by
  simp only [rawChunk,iterate_survivorTail_flip,parsingLength,firstSurvivor_flip,revealed_flip]
lemma shortPrefix_flip (j : ℕ) (x : ℕ → Letter) : shortPrefix j (flipStream x)=(shortPrefix j x).map Letter.flip := by
  induction j with
  | zero => rfl
  | succ j ih => rw [shortPrefix,rawChunk_flip,reduce_flip,normalWord_flip,ih,shortPrefix,List.map_append]
lemma shortLeftWord_flip (x : ℕ → Letter) : shortLeftWord (flipStream x)=(shortLeftWord x).map Letter.flip := by
  rw [shortLeftWord,leftSteps_flip,shortPrefix_flip]; rfl

def Letter.typeNet (b : Bool) : Letter → ℤ
  | .burger c => if c=b then 1 else 0
  | .order (some c) => if c=b then -1 else 0
  | .order none => 0

def typeNet (b : Bool) (w : List Letter) : ℤ := (w.map (Letter.typeNet b)).sum

def FixedWord (w : List Letter) : Prop := Letter.order none∉w

lemma Letter.typeNet_flip (b : Bool) (a : Letter) : Letter.typeNet b a.flip=Letter.typeNet (!b) a := by
  cases a with
  | burger c => cases b <;> cases c <;> rfl
  | order c => cases c with
    | none => rfl
    | some c => cases b <;> cases c <;> rfl
lemma typeNet_flip (b : Bool) (w : List Letter) : typeNet b (w.map Letter.flip)=typeNet (!b) w := by
  simp only [typeNet,List.map_map,Function.comp_def,Letter.typeNet_flip]
lemma Letter.abs_typeNet_le (b : Bool) (a : Letter) : |Letter.typeNet b a| ≤ 1 := by
  cases a with
  | burger c => simp only [Letter.typeNet]; split_ifs <;> norm_num
  | order c => cases c with
    | none => norm_num [Letter.typeNet]
    | some c => simp only [Letter.typeNet]; split_ifs <;> norm_num
lemma abs_typeNet_le (b : Bool) (w : List Letter) : |typeNet b w| ≤ w.length := by
  induction w with
  | nil => simp [typeNet]
  | cons a w ih =>
    change |Letter.typeNet b a+typeNet b w| ≤ (w.length+1:ℕ)
    have ha := Letter.abs_typeNet_le b a
    have ht := abs_add_le (Letter.typeNet b a) (typeNet b w)
    push_cast
    omega
lemma typeNet_total (w : List Letter) (hw : FixedWord w) :
    typeNet false w+typeNet true w=(w.map Letter.increment).sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : a≠Letter.order none := by intro h; exact hw (by simp [h])
    have hh := ih (fun h => hw (List.mem_cons_of_mem a h))
    have he : Letter.typeNet false a+Letter.typeNet true a=a.increment := by
      cases a with
      | burger b => cases b <;> rfl
      | order o => cases o with
        | none => exact (ha rfl).elim
        | some b => cases b <;> rfl
    change (Letter.typeNet false a+typeNet false w)+(Letter.typeNet true a+typeNet true w)=a.increment+(w.map Letter.increment).sum
    omega

lemma fixed_normal_parsing {x : ℕ → Letter} (hx : firstSurvivor x≠⊤) :
    FixedWord (normalWord (reduce (revealed x (parsingLength x)))) := by
  obtain ⟨b,hb⟩ := parsing_shape hx
  simp only [FixedWord,hb,normalWord,List.map_replicate,List.map_reverse,List.map_cons,List.map_nil]
  simp
lemma fixed_shortPrefix {x : ℕ → Letter} (hx : allParsingFinite x) (j : ℕ) : FixedWord (shortPrefix j x) := by
  induction j with
  | zero => simp [FixedWord,shortPrefix]
  | succ j ih =>
    change Letter.order none∉normalWord (reduce (rawChunk j x))++shortPrefix j x
    simpa only [FixedWord,rawChunk,List.mem_append,not_or] using And.intro (fixed_normal_parsing (hx j)) ih
lemma fixed_shortLeftWord {x : ℕ → Letter} (hx : allParsingFinite x) : FixedWord (shortLeftWord x) :=
  fixed_shortPrefix hx _
lemma shortLeftWord_sign (x : ℕ → Letter) :
    ((shortLeftWord x).map Letter.increment).sum=signSum x (parsingOffset (leftSteps x) x) := by
  rw [← reduce_imbalance,reduce,run_shortLeftWord,← reduce]
  rw [reduce_imbalance]
  exact revealed_sum _ _
lemma ae_short_typeNet_total (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    typeNet false (shortLeftWord x)+typeNet true (shortLeftWord x)=1 := by
  filter_upwards [ae_allParsingFinite P,ae_left_first_hit P] with x hx hh
  rw [typeNet_total _ (fixed_shortLeftWord hx),shortLeftWord_sign,hh.1]
lemma integrable_short_typeNet (P : Parameters) (b : Bool) :
    Integrable (fun x => (typeNet b (shortLeftWord x):ℝ)) (streamLaw P ℕ) := by
  apply (integrable_shortLeftWord_length P).mono'
    (((measurable_of_countable (fun w : List Letter => (typeNet b w:ℝ))).comp measurable_shortLeftWord).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs]
    change |(typeNet b (shortLeftWord x):ℝ)| ≤ ((shortLeftWord x).length:ℝ)
    exact_mod_cast abs_typeNet_le b (shortLeftWord x))

/-- Each genuine shortened L-piece has expected net count 1/2 of either type. -/
theorem integral_short_typeNet (P : Parameters) (b : Bool) :
    (∫ x,(typeNet b (shortLeftWord x):ℝ) ∂streamLaw P ℕ)=1/2 := by
  have he := (flipStream_preserving P).hasLaw.integral_comp (integrable_short_typeNet P false).aestronglyMeasurable
  change (∫ x,(typeNet false (shortLeftWord (flipStream x)):ℝ) ∂streamLaw P ℕ)=_ at he
  simp only [shortLeftWord_flip,typeNet_flip,Bool.not_false] at he
  have ht : (∫ x,(typeNet false (shortLeftWord x):ℝ) ∂streamLaw P ℕ)+
      (∫ x,(typeNet true (shortLeftWord x):ℝ) ∂streamLaw P ℕ)=1 := by
    rw [← integral_add (integrable_short_typeNet P false) (integrable_short_typeNet P true)]
    have hh : (fun x => (typeNet false (shortLeftWord x):ℝ)+(typeNet true (shortLeftWord x):ℝ))=ᵐ[streamLaw P ℕ] fun _ => (1:ℝ) :=
      (ae_short_typeNet_total P).mono (fun x hx => by change (typeNet false (shortLeftWord x):ℝ)+(typeNet true (shortLeftWord x):ℝ)=1; exact_mod_cast hx)
    rw [integral_congr_ae hh]
    simp
  cases b <;> linarith

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def shortLeftLaw (P : Parameters) : Measure (List Letter) :=
  (streamLaw P ℕ).map shortLeftWord
lemma shortLeft_hasLaw (P : Parameters) : HasLaw shortLeftWord (shortLeftLaw P) (streamLaw P ℕ) :=
  ⟨measurable_shortLeftWord.aemeasurable,rfl⟩
instance shortLeftLaw_probability (P : Parameters) : IsProbabilityMeasure (shortLeftLaw P) := by
  unfold shortLeftLaw
  exact Measure.isProbabilityMeasure_map measurable_shortLeftWord.aemeasurable

lemma shortLeftLaw_length_integrable (P : Parameters) :
    Integrable (fun w : List Letter => (w.length:ℝ)) (shortLeftLaw P) := by
  rw [shortLeftLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_shortLeftWord.aemeasurable]
  exact integrable_shortLeftWord_length P
lemma shortLeftLaw_typeNet_integrable (P : Parameters) (b : Bool) :
    Integrable (fun w : List Letter => (typeNet b w:ℝ)) (shortLeftLaw P) := by
  rw [shortLeftLaw,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_shortLeftWord.aemeasurable]
  exact integrable_short_typeNet P b
lemma shortLeftLaw_typeNet_mean (P : Parameters) (b : Bool) :
    (∫ w,(typeNet b w:ℝ) ∂shortLeftLaw P)=1/2 := by
  rw [← (shortLeft_hasLaw P).integral_comp (measurable_of_countable _).aestronglyMeasurable]
  exact integral_short_typeNet P b
lemma shortLeftLaw_fixed (P : Parameters) : ∀ᵐ w ∂shortLeftLaw P,FixedWord w := by
  rw [shortLeftLaw,ae_map_iff measurable_shortLeftWord.aemeasurable ((Set.to_countable _).measurableSet)]
  exact (ae_allParsingFinite P).mono (fun x hx => fixed_shortLeftWord hx)

lemma firstSurvivor_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) :
    firstSurvivor x=WithTop.some 0 := by
  apply le_antisymm
  · apply (firstSurvivor_le_iff x 0).mpr
    simp [revealed,reduce,run,step,hx]
  · exact bot_le
lemma parsingLength_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) :
    parsingLength x=1 := by rw [parsingLength,firstSurvivor_of_burger hx]; rfl
lemma K_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) : K x=0 := by
  rw [K_of_hit (firstSurvivor_of_burger hx)]
  simp [revealed,reduce,run,step,hx]
lemma leftSteps_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) : leftSteps x=1 := by
  classical
  have hk : parsingK 0 x=0 := K_of_burger hx
  have hwalk : DefectHitting.walk parsingK 1 x=1 := by
    rw [DefectHitting.walk_succ]
    simp only [DefectHitting.walk,Finset.range_zero,Finset.sum_empty,hk,Nat.cast_zero,zero_add,sub_zero]
  have hnot : x∉DefectHitting.alive parsingK 1 := by
    intro h
    have hh := h 1 le_rfl
    rw [hwalk] at hh
    norm_num at hh
  have hle : leftSteps x ≤ 1 := Nat.find_min' (DefectHitting.stop_exists parsingK x) (Or.inl hnot)
  have hpos : 0<leftSteps x := by
    have hh := (DefectHitting.stop_spec ⟨1,hnot⟩).1
    change x∉DefectHitting.alive parsingK (leftSteps x) at hh
    by_contra hn
    have hz : leftSteps x=0 := by omega
    rw [hz] at hh
    exact hh (by simp [DefectHitting.alive,DefectHitting.walk,Finset.range_zero,Finset.sum_empty])
  omega
lemma shortLeftWord_of_burger {x : ℕ → Letter} {b : Bool} (hx : x 0=Letter.burger b) :
    shortLeftWord x=[Letter.burger b] := by
  rw [shortLeftWord,leftSteps_of_burger hx,shortPrefix]
  simp [rawChunk,parsingLength_of_burger hx,shortPrefix,revealed,reduce,run,step,hx,normalWord]

lemma shortLeftLaw_burger_positive (P : Parameters) (b : Bool) :
    0 < shortLeftLaw P {w | w=[Letter.burger b]} := by
  rw [shortLeftLaw,Measure.map_apply measurable_shortLeftWord ((Set.to_countable _).measurableSet)]
  have hle : streamLaw P ℕ {x | x 0=Letter.burger b} ≤
      streamLaw P ℕ (shortLeftWord ⁻¹' {w | w=[Letter.burger b]}) :=
    measure_mono (fun x hx => shortLeftWord_of_burger hx)
  have he : streamLaw P ℕ {x | x 0=Letter.burger b}=(law P).toMeasure {Letter.burger b} :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).measure_preimage
      (measurableSet_singleton (Letter.burger b)).nullMeasurableSet
  rw [he,law_singleton] at hle
  exact (ENNReal.ofReal_pos.mpr (mass_pos P _)).trans_le hle

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreCompression
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α]

/-- A notation for the actual original all-edge distance of a typed matching. -/
def StackMatching.distance {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (x y : α) : ℕ∞ :=
  let s := l.formPerm*turns M.first
  (dartGraph M.mate s).edist (vertex s x) (vertex s y)

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PlaneTrees
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSingletonClass _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory

/-- The genuine finite ordered connected-core tree. Leaves carry exactly
the trivial word; every nonleaf has one child for each ordered core dart. -/
inductive CoreTree where
  | leaf : CoreTree
  | branch (core : Core) (children : Fin core.val.length→ CoreTree) : CoreTree

namespace CoreTree

def word : CoreTree→List TypedLetter
  | leaf => []
  | branch c ts => cornerInsert (cornerList c (fun i => (ts i).word))

lemma word_empty (t : CoreTree) : stackTypedRun t.word []=some [] := by
  induction t with
  | leaf => rfl
  | branch c ts ih =>
    apply ValidCorners.empty
    refine ⟨?_,?_⟩
    · rw [cornerList_fst];exact c.property
    · intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ih i

lemma branch_nonempty (c : Core) (ts : Fin c.val.length→ CoreTree) : (branch c ts).word≠[] := by
  apply ValidCorners.nonempty
  refine ⟨?_,?_⟩
  · rw [cornerList_fst];exact c.property
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (ts i).word_empty

end CoreTree

end FKCRT.Inventory
end


noncomputable section
open List
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree

def labels : CoreTree → List CoreLabel
  | leaf => [none]
  | branch c ts => some c::(List.ofFn (fun i => labels (ts i))).flatten

lemma labels_branch (c : Core) (ts : Fin c.val.length → CoreTree) :
    (branch c ts).labels=some c::(List.ofFn ts).flatMap labels := by
  simp [labels,List.flatMap_def,Function.comp_def]

def assemble (c : CoreLabel) (fs : List CoreTree) : CoreTree :=
  match c with
  | none => leaf
  | some c => branch c (fun i => fs[i.val]?.getD leaf)

def build : List CoreLabel → List CoreTree → List CoreTree
  | [],fs => fs
  | c::l,fs => let ts := build l fs; assemble c ts::ts.drop c.arity

lemma build_append (l l' : List CoreLabel) (fs : List CoreTree) :
    build (l++l') fs=build l (build l' fs) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.cons_append,build,ih]

lemma build_labels (T : CoreTree) (fs : List CoreTree) : build T.labels fs=T::fs := by
  induction T generalizing fs with
  | leaf => simp [labels,build,assemble,CoreLabel.arity]
  | branch c ts ih =>
    have hf : ∀ (xs : List CoreTree), (∀ t∈xs,∀ fs,build t.labels fs=t::fs)  → 
        ∀ fs,build (xs.flatMap labels) fs=xs++fs := by
      intro xs hx fs
      induction xs with
      | nil => rfl
      | cons t xs ih' =>
        rw [List.flatMap_cons,build_append,ih' (by aesop),hx t (by simp)]
        rfl
    have he := hf (List.ofFn ts) (by
      intro t ht
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
      exact ih i) fs
    rw [labels_branch,build,he]
    simp only [CoreLabel.arity,assemble]
    have ha : (fun i : Fin c.val.length => ((List.ofFn ts)++fs)[i.val]?.getD leaf)=ts := by
      funext i
      rw [List.getElem?_append_left (by simp),List.getElem?_eq_getElem (by simp)]
      simp
    rw [ha]
    simp

lemma ofFn_getD_eq_take (fs : List CoreTree) {k : ℕ} (hk : k≤fs.length) :
    List.ofFn (fun i : Fin k => fs[i.val]?.getD leaf)=fs.take k := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro i h1 h2
    have hi : i<k := by simpa using h1
    rw [List.getElem_ofFn,List.getElem_take]
    rw [List.getElem?_eq_getElem (hi.trans_le hk)]
    rfl

lemma assemble_labels (c : CoreLabel) (fs : List CoreTree) (hc : c.arity≤fs.length) :
    (assemble c fs).labels=c::(fs.take c.arity).flatMap labels := by
  cases c with
  | none => simp [assemble,labels,CoreLabel.arity]
  | some c =>
    simp only [assemble,labels_branch,CoreLabel.arity]
    exact congrArg (fun xs : List CoreTree => some c::xs.flatMap labels)
      (ofFn_getD_eq_take fs (k := c.val.length) hc)

lemma build_correct {l : List CoreLabel}
    (h : FKCRT.TreeCoding.PlaneTree.SuffixNegative (l.map CoreLabel.arity)) :
    (build l []).flatMap labels=l ∧
      ((build l []).length:ℤ)= -(FKCRT.TreeCoding.PlaneTree.incrementWord (l.map CoreLabel.arity)).sum := by
  induction l with
  | nil => simp [build,FKCRT.TreeCoding.PlaneTree.incrementWord]
  | cons c l ih =>
    obtain ⟨he,hlen⟩ := ih (FKCRT.TreeCoding.PlaneTree.suffixNegative_tail h)
    have hneg := h 0 (by simp)
    simp only [List.map_cons,List.drop_zero,FKCRT.TreeCoding.PlaneTree.incrementWord,List.sum_cons] at hneg
    have hk : c.arity≤(build l []).length := by
      unfold FKCRT.TreeCoding.PlaneTree.incrementWord at hlen
      omega
    constructor
    · simp only [build,List.flatMap_cons,assemble_labels c _ hk,List.cons_append]
      rw [← List.flatMap_append,List.take_append_drop,he]
    · simp only [build,List.length_cons,List.length_drop,List.map_cons,
        FKCRT.TreeCoding.PlaneTree.incrementWord,List.sum_cons]
      rw [Nat.cast_add,Nat.cast_sub hk]
      simp only [Nat.cast_one]
      unfold FKCRT.TreeCoding.PlaneTree.incrementWord at hlen
      omega

end CoreTree
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WordCoefficients
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def stoppedWord (T : (ℕ → Letter) → WithTop ℕ) (x : ℕ → Letter) : List Letter :=
  revealed x ((T x).untopD 0+1)
def stoppedTail (T : (ℕ → Letter) → WithTop ℕ) (x : ℕ → Letter) : ℕ → Letter :=
  tail ((T x).untopD 0+1) x
lemma measurable_revealed (n : ℕ) : Measurable (fun x : ℕ → Letter => revealed x n) :=
  (measurable_of_countable (fun y : Fin n → Letter => (List.ofFn y).reverse)).comp
    (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))
lemma measurable_stoppedWord {T : (ℕ → Letter) → WithTop ℕ} (hT : Measurable T) : Measurable (stoppedWord T) := by
  have hm : Measurable (fun x => (T x).untopD 0+1) := (measurable_of_countable (fun t : WithTop ℕ => t.untopD 0+1)).comp hT
  have hh : Measurable (fun z : ℕ × (ℕ → Letter) => revealed z.2 z.1) :=
    measurable_from_prod_countable_right measurable_revealed
  exact hh.comp (hm.prodMk measurable_id)
lemma measurable_stoppedTail {T : (ℕ → Letter) → WithTop ℕ} (hT : Measurable T) : Measurable (stoppedTail T) := by
  have hm : Measurable (fun x => (T x).untopD 0+1) := (measurable_of_countable (fun t : WithTop ℕ => t.untopD 0+1)).comp hT
  have hh : Measurable (fun z : ℕ × (ℕ → Letter) => tail z.1 z.2) :=
    measurable_from_prod_countable_right measurable_tail
  exact hh.comp (hm.prodMk measurable_id)
lemma stoppedWord_of_hit {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter} {n : ℕ}
    (h : T x=WithTop.some n) : stoppedWord T x=revealed x (n+1) := by simp only [stoppedWord,h]; rfl
lemma stoppedTail_of_hit {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter} {n : ℕ}
    (h : T x=WithTop.some n) : stoppedTail T x=tail (n+1) x := by simp only [stoppedTail,h]; rfl

lemma stoppedWord_rectangle_sum (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤)
    (A : Set (List Letter)) (B : Set (ℕ → Letter)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (stoppedWord T ⁻¹' A ∩ stoppedTail T ⁻¹' B)=
      (∑' n : ℕ,streamLaw P ℕ ({x | T x=WithTop.some n} ∩ (fun x => revealed x (n+1)) ⁻¹' A))*streamLaw P ℕ B := by
  let C : ℕ → Set (ℕ → Letter) := fun n => {x | T x=WithTop.some n} ∩ (fun x => revealed x (n+1)) ⁻¹' A
  have hC (n : ℕ) : MeasurableSet[rawFiltration n] (C n) :=
    (hT.measurableSet_eq n).inter (prefix_measurable n (fun y => (List.ofFn y).reverse) hA)
  have hCm (n : ℕ) : MeasurableSet (C n) := rawFiltration.le n _ (hC n)
  have he : (stoppedWord T ⁻¹' A ∩ stoppedTail T ⁻¹' B : Set (ℕ → Letter)) =ᵐ[streamLaw P ℕ]
      (⋃ n,C n ∩ tail (n+1) ⁻¹' B : Set (ℕ → Letter)) := by
    filter_upwards [hfin] with x hx
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    have hn' : T x=WithTop.some n := hn.symm
    apply propext
    constructor
    · rintro ⟨ha,hb⟩
      exact Set.mem_iUnion.mpr ⟨n,⟨hn',by simpa only [Set.mem_preimage,← stoppedWord_of_hit hn'] using ha⟩,
        by simpa only [Set.mem_preimage,← stoppedTail_of_hit hn'] using hb⟩
    · intro h
      obtain ⟨m,⟨hm,ha⟩,hb⟩ := Set.mem_iUnion.mp h
      exact ⟨by simpa only [Set.mem_preimage,stoppedWord_of_hit hm] using ha,
        by simpa only [Set.mem_preimage,stoppedTail_of_hit hm] using hb⟩
  rw [measure_congr he,measure_iUnion]
  · have hs (n : ℕ) : streamLaw P ℕ (C n ∩ tail (n+1) ⁻¹' B)=streamLaw P ℕ (C n)*streamLaw P ℕ B := by
      have h := ((indep_iff_forall_indepSet _).mp (raw_indep_tail P n) _ _ (hC n)
        (measurable_iff_comap_le.mpr le_rfl hB)).measure_inter_eq_mul
      rw [(tail_preserving P (n+1)).measure_preimage hB.nullMeasurableSet] at h
      exact h
    simp_rw [hs]
    rw [ENNReal.tsum_mul_right]
  · intro n m hnm
    exact Set.disjoint_left.mpr (fun x hn hm => hnm (WithTop.coe_injective (hn.1.1.symm.trans hm.1.1)))
  · intro n
    exact (hCm n).inter ((measurable_tail (n+1)) hB)

lemma stoppedWord_rectangle (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤)
    (A : Set (List Letter)) (B : Set (ℕ → Letter)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    streamLaw P ℕ (stoppedWord T ⁻¹' A ∩ stoppedTail T ⁻¹' B)=
      streamLaw P ℕ (stoppedWord T ⁻¹' A)*streamLaw P ℕ B := by
  rw [stoppedWord_rectangle_sum P hT hfin A B hA hB]
  have h := stoppedWord_rectangle_sum P hT hfin A Set.univ hA MeasurableSet.univ
  simp only [Set.preimage_univ,Set.inter_univ,measure_univ,mul_one] at h
  rw [h]
lemma stoppedTail_preserving (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hTm : Measurable T) (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤) :
    MeasurePreserving (stoppedTail T) (streamLaw P ℕ) (streamLaw P ℕ) := by
  refine ⟨measurable_stoppedTail hTm,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_stoppedTail hTm) hB]
  simpa using stoppedWord_rectangle P hT hfin Set.univ B MeasurableSet.univ hB
lemma stoppedWord_indep_tail (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hTm : Measurable T) (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤) :
    IndepFun (stoppedWord T) (stoppedTail T) (streamLaw P ℕ) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A B hA hB
  rw [(stoppedTail_preserving P hTm hT hfin).measure_preimage hB.nullMeasurableSet]
  exact stoppedWord_rectangle P hT hfin A B hA hB

def wordPieces (T : (ℕ → Letter) → WithTop ℕ) (j : ℕ) (x : ℕ → Letter) : List Letter :=
  stoppedWord T ((stoppedTail T)^[j] x)
lemma stoppedWordPieces_iid (P : Parameters) {T : (ℕ → Letter) → WithTop ℕ}
    (hTm : Measurable T) (hT : IsStoppingTime rawFiltration T) (hfin : ∀ᵐ x ∂streamLaw P ℕ,T x≠⊤) :
    iIndepFun (wordPieces T) (streamLaw P ℕ) :=
  TreeCoding.regenerative_iIndepFun (streamLaw P ℕ) (stoppedWord T) (stoppedTail T) (measurable_stoppedWord hTm)
    (stoppedTail_preserving P hTm hT hfin) (stoppedWord_indep_tail P hTm hT hfin)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT
namespace Inventory

lemma stopping_measurable {T : (ℕ → Letter) → WithTop ℕ} (hT : IsStoppingTime rawFiltration T) : Measurable T := by
  have hme (n : ℕ) : MeasurableSet {x | T x=WithTop.some n} := rawFiltration.le n _ (hT.measurableSet_eq n)
  have hmf : MeasurableSet {x | T x≠⊤} := by
    have he : {x | T x≠⊤}=⋃ n : ℕ,{x | T x=WithTop.some n} := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
      simpa only [eq_comm] using (WithTop.ne_top_iff_exists (x := T x))
    rw [he]
    exact MeasurableSet.iUnion hme
  apply measurable_to_countable'
  intro n
  obtain rfl | ⟨n,rfl⟩ := eq_or_ne n ⊤ |>.imp_right (fun h => WithTop.ne_top_iff_exists.mp h)
  · convert hmf.compl using 1
    all_goals try with_reducible_and_instances rfl
    ext x; simp
  · exact hme n

def downPath (h : ℕ) (n : ℕ) (x : ℕ → Letter) : ℤ := (h:ℤ)+signSum x (n+1)
def firstDown (h : ℕ) : (ℕ → Letter) → WithTop ℕ := TreeCoding.firstZero (downPath h)
lemma downPath_adapted (h : ℕ) : StronglyAdapted rawFiltration (downPath h) := by
  intro n
  convert (prefix_measurable n (fun y => (h:ℤ)+(((List.ofFn y).reverse).map Letter.increment).sum)).stronglyMeasurable using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact congrArg (fun z : ℤ => (h:ℤ)+z) (revealed_sum x (n+1)).symm
lemma firstDown_stopping (h : ℕ) : IsStoppingTime rawFiltration (firstDown h) :=
  TreeCoding.firstZero_isStoppingTime (downPath_adapted h)
lemma firstDown_measurable (h : ℕ) : Measurable (firstDown h) := stopping_measurable (firstDown_stopping h)
lemma downPath_step (h n : ℕ) (x : ℕ → Letter) : downPath h n x-1 ≤ downPath h (n+1) x := by
  unfold downPath
  rw [signSum_succ x (n+1)]
  have := (increment_bounds (x (n+1))).1
  omega
lemma downPath_initial (h : ℕ) (hh : 0<h) (x : ℕ → Letter) : 0 ≤ downPath h 0 x := by
  have := (increment_bounds (x 0)).1
  simp only [downPath,signSum,Nat.zero_add,Finset.sum_range_one]
  omega
lemma downPath_martingale (P : Parameters) (h : ℕ) :
    Martingale (fun n x => (downPath h n x:ℝ)) rawFiltration (streamLaw P ℕ) := by
  convert (martingale_const rawFiltration (streamLaw P ℕ) (h:ℝ)).add (raw_sign_martingale P) using 1
  all_goals try with_reducible_and_instances rfl
  ext n x
  simp [downPath]
lemma firstDown_finite (P : Parameters) (h : ℕ) (hh : 0<h) : ∀ᵐ x ∂streamLaw P ℕ,firstDown h x≠⊤ := by
  have hj : ∀ᵐ x ∂streamLaw P ℕ,∃ᶠ n in atTop,downPath h (n+1) x≠downPath h n x := by
    filter_upwards [] with x
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    unfold downPath
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.2
    omega
  filter_upwards [TreeCoding.integer_martingale_hits_zero (downPath_adapted h) (downPath_martingale P h)
    (downPath_initial h hh) (downPath_step h) hj] with x hx
  classical
  simp [firstDown,TreeCoding.firstZero,hx]

lemma firstDown_of_hit_iff (h : ℕ) (x : ℕ → Letter) (n : ℕ) :
    firstDown h x=WithTop.some n ↔ signSum x (n+1)= -(h:ℤ) ∧ ∀ j<n,signSum x (j+1)≠ -(h:ℤ) := by
  rw [firstDown,TreeCoding.firstZero_eq_iff]
  simp only [downPath]
  constructor
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
lemma firstDown_prefix_pos {h : ℕ} (hh : 0<h) {x : ℕ → Letter} {n : ℕ}
    (hn : firstDown h x=WithTop.some n) {j : ℕ} (hj : j ≤ n) : -(h:ℤ) < signSum x j := by
  have hd := (TreeCoding.firstZero_eq_iff (downPath h) x n).mp hn
  cases j with
  | zero => simp only [signSum,Finset.range_zero,Finset.sum_empty]; omega
  | succ j =>
    have hj' : j<n := by omega
    have he := TreeCoding.integer_path_nonneg_before_zero (fun k => downPath h k x)
      (downPath_initial h hh x) (fun k => downPath_step h k x) j (fun k hk => hd.2 k (hk.trans hj'))
    have hnz := hd.2 j hj'
    dsimp [downPath] at he hnz
    omega

def reverseRightWord (x : ℕ → Letter) : List Letter := stoppedWord (firstDown 1) x
def reverseRightLaw (P : Parameters) : Measure (List Letter) := (streamLaw P ℕ).map reverseRightWord
lemma reverseRightWord_measurable : Measurable reverseRightWord := measurable_stoppedWord (firstDown_measurable 1)
instance reverseRightLaw_probability (P : Parameters) : IsProbabilityMeasure (reverseRightLaw P) :=
  Measure.isProbabilityMeasure_map (reverseRightWord_measurable.aemeasurable)
lemma reverseRightWord_net (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    ((reverseRightWord x).map Letter.increment).sum= -1 := by
  filter_upwards [firstDown_finite P 1 (by omega)] with x hx
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
  have hn' : firstDown 1 x=WithTop.some n := hn.symm
  rw [reverseRightWord,stoppedWord_of_hit hn',revealed_sum]
  exact (firstDown_of_hit_iff 1 x n).mp hn' |>.1

end Inventory
end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Expected visits below a first down-crossing are at most twice the
height above the killing boundary. This includes every initial level. -/
theorem killed_green_bound (a b : ℕ) : (∑' n,killed n a b) ≤ 2*(b+1:ℕ) := by
  have hh : (∑' n,killed n a b) ≤ greenMajorant a b :=
    le_of_tendsto (killed_summable a b).hasSum.tendsto_sum_nat (Filter.Eventually.of_forall (fun N => killed_green_partial N a b))
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right (a+1) (b+1)) (by norm_num)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def wordWeight (P : Parameters) (w : List Letter) : ℝ≥0∞ := (w.map (fun a => (law P).toMeasure {a})).prod
lemma rawWord_cylinder (P : Parameters) (w : List Letter) :
    streamLaw P ℕ {x | rawWord x w.length=w}=wordWeight P w := by
  have he : {x | rawWord x w.length=w}=rawPrefix w.length ⁻¹' {w.get} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff,rawWord]
    constructor
    · intro h
      funext i
      have := congrArg (fun l : List Letter => l[i.val]?) h
      simpa using this
    · intro h; rw [h,List.ofFn_get]
  rw [he,(rawPrefix_preserving P w.length).measure_preimage (measurableSet_singleton _).nullMeasurableSet,
    Measure.pi_singleton]
  unfold wordWeight
  conv_rhs => rw [← List.ofFn_get w,List.map_ofFn,List.prod_ofFn]
  rfl

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable
namespace FKCRT.Inventory

lemma fixed_wordMass (P : Parameters) (v : List TypedLetter) :
    wordMass P (v.map TypedLetter.fixed)=(1/4:ℝ)^burgerCount v*((1-P.p)/4)^orderCount v := by
  induction v with
  | nil => simp [wordMass,burgerCount,orderCount]
  | cons a v ih =>
    cases a <;> simp_all [wordMass,burgerCount,orderCount,TypedLetter.fixed,mass,pow_succ] <;> ring

lemma fixed_wordMass_empty (P : Parameters) {m : ℕ} {v : List TypedLetter}
    (hv : v.length=2*m) (h : stackTypedRun v []=some []) :
    wordMass P (v.map TypedLetter.fixed)=((1-P.p)/16)^m := by
  have hb := typed_fixed_balance h
  obtain ⟨ha,hb'⟩ := typed_counts v
  have hB : burgerCount v=m := by omega
  have hO : orderCount v=m := by omega
  rw [fixed_wordMass,hB,hO,← mul_pow]
  congr 1
  ring

lemma markings_mass_empty (P : Parameters) {m : ℕ} {v : List TypedLetter}
    (hv : v.length=2*m) (h : stackTypedRun v []=some []) :
    (∑ w∈markings v [],wordMass P w)=
      ((1-P.p)/16)^m*(1+2*P.p/(1-P.p))^flexibleCount v [] := by
  rw [markings_mass P h,fixed_wordMass_empty P hv h]

lemma markings_disjoint (N : ℕ) : (typedEmptyWords N : Set (List TypedLetter)).PairwiseDisjoint
    (fun v => markings v []) := by
  intro v _ u _ hne
  apply Finset.disjoint_left.mpr
  intro w hv hu
  obtain ⟨t,ht⟩ := mem_markings.mp hv
  obtain ⟨s,hs⟩ := mem_markings.mp hu
  exact hne (Prod.mk.inj (Option.some.inj (ht.symm.trans hs))).1

/-- Exact total genuine iid weight, before identifying it with its cylinder
probability. All flexible markings are summed, not picked deterministically. -/
theorem empty_wordMass_sum (P : Parameters) (m : ℕ) :
    (∑ w∈emptyWords (2*m),wordMass P w)=
      ((1-P.p)/16)^m * ∑ v∈typedEmptyWords (2*m),
        (1+2*P.p/(1-P.p))^flexibleCount v [] := by
  rw [emptyWords_markings,Finset.sum_biUnion (markings_disjoint _),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  obtain ⟨hl,hr⟩ := Finset.mem_filter.mp hv
  exact markings_mass_empty P (mem_wordsOfLength.mp hl) hr

lemma wordMass_nonneg (P : Parameters) (w : List Letter) : 0≤wordMass P w :=
  List.prod_nonneg (fun a ha => by obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha; exact (mass_pos P b).le)

lemma wordWeight_eq (P : Parameters) (w : List Letter) :
    wordWeight P w=ENNReal.ofReal (wordMass P w) := by
  induction w with
  | nil => simp [wordWeight,wordMass]
  | cons a w ih =>
    simp only [wordWeight,wordMass,List.map_cons,List.prod_cons] at *
    rw [law_singleton,ih,ENNReal.ofReal_mul (mass_pos P a).le]

lemma rawEmpty_measure (P : Parameters) (N : ℕ) :
    streamLaw P ℕ {x | EmptyReducing (rawWord x N)}=
      ENNReal.ofReal (∑ w∈emptyWords N,wordMass P w) := by
  have he : {x | EmptyReducing (rawWord x N)}=
      ⋃ w∈emptyWords N,{x | rawWord x N=w} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨rawWord x N,Finset.mem_filter.mpr ⟨mem_wordsOfLength.mpr (by simp [rawWord]),h⟩,rfl⟩
    · rintro ⟨w,hw,hx⟩
      rw [hx]
      exact (Finset.mem_filter.mp hw).2
  have hd : (emptyWords N : Set (List Letter)).PairwiseDisjoint
      (fun w => {x | rawWord x N=w}) := by
    intro v _ w _ hvw
    exact Set.disjoint_left.mpr (fun x hv hw => hvw (hv.symm.trans hw))
  have hm (w : List Letter) : MeasurableSet {x : ℕ→Letter | rawWord x N=w} :=
    ((measurable_of_countable List.ofFn).comp (rawPrefix_measurable N)) (measurableSet_singleton w)
  rw [he,measure_biUnion_finset hd (fun w _ => hm w)]
  have hh (w) (hw : w∈emptyWords N) :
      streamLaw P ℕ {x | rawWord x N=w}=ENNReal.ofReal (wordMass P w) := by
    have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp hw).1
    rw [← hl,rawWord_cylinder,wordWeight_eq]
  simp_rw [Finset.sum_congr rfl hh]
  exact (ENNReal.ofReal_sum_of_nonneg (fun w _ => wordMass_nonneg P w)).symm

lemma rawEmpty_real (P : Parameters) (N : ℕ) :
    (streamLaw P ℕ).real {x | EmptyReducing (rawWord x N)}=
      ∑ w∈emptyWords N,wordMass P w := by
  rw [measureReal_def,rawEmpty_measure,ENNReal.toReal_ofReal (Finset.sum_nonneg (fun w _ => wordMass_nonneg P w))]

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PieceWalks
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma wordSeries_coefficients (t r : ℝ≥0∞) :
    wordSeries t r=∑' m : ℕ,typedCoefficient t m*(r^2)^m := by
  rw [wordSeries,empty_tsum_by_size]
  apply tsum_congr
  intro m
  rw [typedCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w hw
  have hl := mem_wordsOfLength.mp (Finset.mem_filter.mp hw).1
  rw [wordMonomial,hl,pow_mul]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma kernel_uniform_bound : ∃ C : ℝ,0<C ∧ ∀ n : ℕ,0<n → ∀ z : ℤ,
    kernel n z ≤ C/Real.sqrt n := by
  obtain ⟨E,hE,hEt,h⟩ := kernel_uniform_local_limit
  obtain ⟨A,hA⟩ := hEt.bddAbove_range
  let c := Real.sqrt (2*Real.pi)/Real.pi
  have hc : 0 < c := div_pos (Real.sqrt_pos.mpr (by positivity)) Real.pi_pos
  have hA0 : 0≤A := (hE 0).trans (hA (Set.mem_range_self 0))
  refine ⟨c+A,by linarith,?_⟩
  intro n hn z
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  by_cases hz : Even ((n:ℤ)+z)
  · have he := (abs_le.mp (h n hn z hz)).2
    have hx : Real.exp (-((z:ℝ)/Real.sqrt n)^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ((z:ℝ)/Real.sqrt n)])
    have hh := mul_le_mul_of_nonneg_left hx hc.le
    apply (le_div_iff₀ hs).mpr
    have ha := hA (Set.mem_range_self n)
    dsimp [c] at hh ⊢
    nlinarith
  · have hz' : (z+(n:ℤ))%2≠0 := by
      simpa only [Int.even_iff,add_comm] using hz
    rw [kernel_binomial,ite_eq_right hz']
    positivity

lemma killed_sum_bound {C : ℝ} (hC : ∀ n : ℕ,0<n → ∀ z : ℤ,kernel n z ≤ C/Real.sqrt n)
    (n : ℕ) (hn : 0<n) (a N : ℕ) :
    (∑ b∈Finset.range N,killed n a b) ≤ (2*(a+1:ℕ):ℝ)*(C/Real.sqrt n) := by
  have he (b : ℕ) : (b:ℤ)+a+2=(b+(2*(a+1)):ℕ)-a := by push_cast; ring
  simp_rw [killed_reflection,he]
  apply (sum_difference_shift_le (fun b => kernel n ((b:ℤ)-a)) (fun b => kernel_nonneg _ _) (2*(a+1)) N).trans
  calc
    _ ≤ ∑ _b∈Finset.range (2*(a+1)),C/Real.sqrt n := Finset.sum_le_sum (fun b _ => hC n hn _)
    _ = _ := by simp

end FKCRT.SimpleWalk
namespace FKCRT.Inventory

lemma signSum_bounds (x : ℕ → Letter) (n : ℕ) : -(n:ℤ)≤ signSum x n ∧ signSum x n≤ n := by
  induction n with
  | zero => simp [signSum]
  | succ n ih =>
    rw [signSum_succ]
    have hi := increment_bounds (x n)
    push_cast
    omega

def rawSurvival (a n : ℕ) : Set (ℕ → Letter) := {x | ∀ j≤ n,0≤(a:ℤ)+signSum x j}
lemma rawSurvival_union (a n : ℕ) :
    rawSurvival a n=⋃ b∈Finset.range (a+n+1),rawKilled a b n := by
  ext x
  simp only [rawSurvival,Set.mem_ofPred_eq,Set.mem_iUnion,Finset.mem_range,rawKilled]
  constructor
  · intro hx
    have hn := hx n le_rfl
    refine ⟨((a:ℤ)+signSum x n).toNat,?_,hx,?_⟩
    · have hb := signSum_bounds x n
      omega
    · omega
  · rintro ⟨b,_,hb,_⟩
    exact hb
lemma signSum_measurable (n : ℕ) : Measurable (fun x : ℕ → Letter => signSum x n) := by
  unfold signSum
  exact Finset.measurable_sum _ (fun j _ => (measurable_of_countable Letter.increment).comp (measurable_pi_apply j))
lemma rawKilled_measurable (a b n : ℕ) : MeasurableSet (rawKilled a b n) := by
  have h1 : MeasurableSet {x : ℕ → Letter | ∀ j≤n,0≤(a:ℤ)+signSum x j} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j : ℕ => MeasurableSet.iInter (fun _ : j≤n =>
      measurableSet_le measurable_const ((signSum_measurable j).const_add (a:ℤ))))
  exact h1.inter (measurableSet_eq_fun ((signSum_measurable n).const_add (a:ℤ))
    (measurable_const (a := (b:ℤ))))
lemma rawSurvival_measure (P : Parameters) (a n : ℕ) :
    (streamLaw P ℕ).real (rawSurvival a n)=∑ b∈Finset.range (a+n+1),SimpleWalk.killed n a b := by
  rw [rawSurvival_union,measureReal_biUnion_finset]
  · exact Finset.sum_congr rfl (fun b _ => rawKilled_measure P a b n)
  · intro b _ c _ hbc
    apply Set.disjoint_left.mpr
    intro x hb hc
    exact hbc (by have h1 := hb.2; have h2 := hc.2; omega)
  · intro b _; exact rawKilled_measurable a b n

/-- Reflection gives a uniform first-passage survival bound for the actual inventory stream. -/
theorem rawSurvival_bound : ∃ C : ℝ,0<C ∧ ∀ (P : Parameters) (a n : ℕ),0<n →
    (streamLaw P ℕ).real (rawSurvival a n) ≤ C*(a+1)/Real.sqrt n := by
  obtain ⟨C,hC,h⟩ := SimpleWalk.kernel_uniform_bound
  refine ⟨2*C,by positivity,?_⟩
  intro P a n hn
  rw [rawSurvival_measure]
  convert SimpleWalk.killed_sum_bound h n hn a (a+n+1) using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma pop_fixed_count {b a : Bool} {s t : List Bool} (h : pop (some b) s=some t) :
    s.count a=t.count a+if a=b then 1 else 0 := by
  induction s generalizing t with
  | nil => simp [pop] at h
  | cons c s ih =>
    by_cases he : b=c
    · subst c
      simp only [pop,eligible,Option.some.injEq,or_true,ite_true] at h
      cases h
      by_cases ha : a=b
      · subst a; simp only [List.count_cons_self,ite_true]
      · simp only [List.count_cons_of_ne (Ne.symm ha),ite_eq_right ha,Nat.add_zero]
    · have hel : ¬eligible (some b) c := by simp [eligible,he]
      simp only [pop,ite_eq_right hel] at h
      cases hp : pop (some b) s with
      | none => simp [hp] at h
      | some t' =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst t
        have hi := ih hp
        simp only [List.count_cons]
        omega

/-- Removing the freshest burger of type b never reduces the bottom-k
supply of another type. If it reduces the type-b supply, all of the
remaining type-b supply is in the bottom k. -/
lemma pop_fixed_bottom {b a : Bool} {s t : List Bool} (h : pop (some b) s=some t)
    {k : ℕ} (hk : k ≤ t.length) :
    (bottom s k).count a ≤ (bottom t k).count a ∨
      (a=b ∧ t.count a=(bottom t k).count a) := by
  induction s generalizing t k with
  | nil => simp [pop] at h
  | cons c s ih =>
    by_cases he : b=c
    · subst c
      have hel : eligible (some b) b := by simp [eligible]
      simp only [pop,ite_eq_left hel,Option.some.injEq] at h
      subst t
      exact Or.inl (by rw [bottom_cons _ _ hk])
    · have hel : ¬eligible (some b) c := by simp [eligible,he]
      simp only [pop,ite_eq_right hel] at h
      cases hp : pop (some b) s with
      | none => simp [hp] at h
      | some t' =>
        simp only [hp,Option.map_some,Option.some.injEq] at h
        subst t
        have hl := pop_length hp
        by_cases hk' : k ≤ t'.length
        · rw [bottom_cons c s (by omega),bottom_cons c t' hk']
          rcases ih hp hk' with h | ⟨rfl,h⟩
          · exact Or.inl h
          · exact Or.inr ⟨rfl,by simpa [List.count_cons,he,eq_comm] using h⟩
        · have hk'' : k=(c::t').length := by simp only [List.length_cons] at *; omega
          rw [hk'',bottom_all]
          by_cases ha : a=b
          · exact Or.inr ⟨ha,rfl⟩
          · exact Or.inl ((count_bottom_le _ _ a).trans (by
              have hc := pop_fixed_count (a := a) (show pop (some b) (c::s)=some (c::t') by
                simp only [pop,ite_eq_right hel,hp,Option.map_some])
              simpa [ha] using hc.le))

/-- Exact source criterion, expressed in freshest-first stack order. -/
def SupplyCondition (s : List Bool) (os : List Order) : Prop :=
  s.length=os.length ∧ ∀ k ≤ os.length,∀ a : Bool,
    (bottom os k).count (some a) ≤ (bottom s k).count a

lemma fixed_pop_exists {b : Bool} {s : List Bool} (h : 0 < s.count b) :
    ∃ t,pop (some b) s=some t := by
  cases hp : pop (some b) s with
  | some t => exact ⟨t,rfl⟩
  | none =>
    have hb : b∈s := List.count_pos_iff.mp h
    have hn := (pop_eq_none_iff (some b) s).mp hp b hb
    exact False.elim (hn (by simp [eligible]))

lemma supplyCondition_step {s : List Bool} {a : Order} {os : List Order}
    (h : SupplyCondition s (a::os)) :
    ∃ t,pop a s=some t ∧ SupplyCondition t os := by
  obtain ⟨hl,hc⟩ := h
  cases a with
  | none =>
    cases s with
    | nil => simp at hl
    | cons b s =>
      refine ⟨s,by simp [pop,eligible],?_⟩
      have hs : s.length=os.length := by simp only [List.length_cons] at hl; omega
      refine ⟨hs,fun k hk c => ?_⟩
      have hh := hc k (by simp only [List.length_cons]; omega) c
      rw [bottom_cons none os hk,bottom_cons b s (by omega)] at hh
      exact hh
  | some b =>
    have hh := hc (some b::os).length le_rfl b
    rw [bottom_all,← hl,bottom_all] at hh
    have hp : 0 < s.count b := by
      simp only [List.count_cons_self] at hh
      omega
    obtain ⟨t,ht⟩ := fixed_pop_exists hp
    have htl := pop_length ht
    refine ⟨t,ht,⟨by simp only [List.length_cons] at hl; omega,fun k hk c => ?_⟩⟩
    have horig := hc k (by simp only [List.length_cons]; omega) c
    rw [bottom_cons (some b) os hk] at horig
    rcases pop_fixed_bottom (a := c) (k := k) ht (by simp only [List.length_cons] at hl; omega) with hge | ⟨hcb,he⟩
    · exact horig.trans hge
    · subst c
      have hall := hc (some b::os).length le_rfl b
      rw [bottom_all,← hl,bottom_all] at hall
      have hc' := pop_fixed_count (a := b) ht
      simp only [List.count_cons_self,ite_true] at hall hc'
      have htail : os.count (some b) ≤ t.count b := by omega
      exact ((List.Sublist.count_le (some b) (List.drop_sublist _ _)).trans htail).trans_eq he

theorem matching_of_supplyCondition {s : List Bool} {os : List Order} (h : SupplyCondition s os) :
    evalOrders os s=⟨[],[]⟩ := by
  induction os generalizing s with
  | nil =>
    have hs : s=[] := List.length_eq_zero_iff.mp (by simpa using h.1)
    subst s
    rfl
  | cons a os ih =>
    obtain ⟨t,ht,hcond⟩ := supplyCondition_step h
    rw [evalOrders_cons,ht]
    exact ih hcond

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma pop_fixed_exists {c : Bool} {s : List Bool} (h : 0 < s.count c) : ∃ t,pop (some c) s=some t := by
  cases hp : pop (some c) s with
  | some t => exact ⟨t,rfl⟩
  | none =>
    have hh := (pop_eq_none_iff _ _).mp hp c (List.count_pos_iff.mp h)
    exact (hh (by simp [eligible])).elim

lemma fixed_run_buffer {w : List Letter} (hw : FixedWord w) {s : List Bool}
    (hs : ∀ b,w.length ≤ s.count b) :
    (run w ⟨[],s⟩).orders=[] ∧ ∀ b,((run w ⟨[],s⟩).burgers.count b:ℤ)=(s.count b:ℤ)+typeNet b w := by
  induction w generalizing s with
  | nil => simp [run,typeNet]
  | cons a w ih =>
    have hf : FixedWord w := fun h => hw (List.mem_cons_of_mem a h)
    have ha : a≠Letter.order none := by intro h; exact hw (by simp [h])
    cases a with
    | burger c =>
      have hh : ∀ b,w.length ≤ (c::s).count b := by
        intro b
        have hb := hs b
        simp only [List.length_cons] at hb
        have hle : s.count b ≤ (c::s).count b := List.Sublist.count_le b (List.sublist_cons_self ..)
        omega
      obtain ⟨ho,hcount⟩ := ih hf hh
      refine ⟨ho,fun b => ?_⟩
      change ((run w ⟨[],c::s⟩).burgers.count b:ℤ)=(s.count b:ℤ)+(Letter.typeNet b (.burger c)+typeNet b w)
      rw [hcount]
      by_cases hcb : c=b
      · subst c; simp only [List.count_cons_self,Nat.cast_add,Nat.cast_one,Letter.typeNet,ite_true]; ring
      · simp only [List.count_cons_of_ne hcb,Letter.typeNet,ite_eq_right hcb,zero_add]
    | order o =>
      cases o with
      | none => exact (ha rfl).elim
      | some c =>
        obtain ⟨t,ht⟩ := pop_fixed_exists (c := c) (s := s) (by have := hs c; simp only [List.length_cons] at this; omega)
        have hh : ∀ b,w.length ≤ t.count b := by
          intro b
          have hb := hs b
          have hc := pop_fixed_count (a := b) ht
          simp only [List.length_cons] at hb
          split_ifs at hc <;> omega
        obtain ⟨ho,hcount⟩ := ih hf hh
        simp only [run,step,ht]
        refine ⟨ho,fun b => ?_⟩
        rw [hcount]
        change (t.count b:ℤ)+typeNet b w=(s.count b:ℤ)+(Letter.typeNet b (.order (some c))+typeNet b w)
        have hc := pop_fixed_count (a := b) ht
        by_cases hbc : b=c
        · subst b
          simp only [ite_true] at hc
          simp only [Letter.typeNet,ite_true]
          omega
        · have hcb : c≠b := Ne.symm hbc
          simp only [ite_eq_right hbc,Nat.add_zero] at hc
          simp only [Letter.typeNet,ite_eq_right hcb,zero_add,hc]

def piecesPrefix (x : ℕ → List Letter) : ℕ → List Letter
  | 0 => []
  | n+1 => piecesPrefix x n++x n

def pieceSum (b : Bool) (x : ℕ → List Letter) (n : ℕ) : ℤ :=
  ∑ j∈Finset.range n,typeNet b (x j)

def PieceBuffer (K : ℕ) (x : ℕ → List Letter) : Prop :=
  ∀ n b,((x n).length:ℤ) ≤ (K:ℤ)+pieceSum b x n

lemma run_pieces_buffer {x : ℕ → List Letter} (hx : ∀ n,FixedWord (x n)) {K : ℕ}
    (hb : PieceBuffer K x) {s : List Bool} (hs : ∀ b,K ≤ s.count b) (n : ℕ) :
    (run (piecesPrefix x n) ⟨[],s⟩).orders=[] ∧
      ∀ b,((run (piecesPrefix x n) ⟨[],s⟩).burgers.count b:ℤ)=(s.count b:ℤ)+pieceSum b x n := by
  induction n with
  | zero => simp [piecesPrefix,run,pieceSum]
  | succ n ih =>
    let t : List Bool := (run (piecesPrefix x n) ⟨[],s⟩).burgers
    have hcount : ∀ b,(x n).length ≤ t.count b := by
      intro b
      have hh := hb n b
      have hi := ih.2 b
      have hsb := hs b
      change ((run (piecesPrefix x n) ⟨[],s⟩).burgers.count b:ℤ)=_ at hi
      dsimp [t]
      omega
    obtain ⟨ho,hc⟩ := fixed_run_buffer (hx n) hcount
    have he : run (piecesPrefix x n) ⟨[],s⟩=⟨[],t⟩ := by
      have hh := ih.1
      dsimp [t]
      generalize he : run (piecesPrefix x n) ⟨[],s⟩=e at *
      cases e with
      | mk os bs => simp only at hh; subst os; rfl
    rw [piecesPrefix,run_append,he]
    refine ⟨ho,fun b => ?_⟩
    rw [hc]
    change ((run (piecesPrefix x n) ⟨[],s⟩).burgers.count b:ℤ)+typeNet b (x n)=_
    rw [ih.2]
    simp only [pieceSum,Finset.sum_range_succ]
    ring

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma positive_piece_buffer {x : ℕ → List Letter}
    (hnet : ∀ b,Tendsto (fun n => (pieceSum b x n:ℝ)/(n:ℝ)) atTop (𝓝 (1/2)))
    {l : ℝ} (hlen : Tendsto (fun n => (∑ j∈Finset.range n,((x j).length:ℝ))/(n:ℝ)) atTop (𝓝 l)) :
    ∃ K,PieceBuffer K x := by
  have ht := term_div_zero_of_averages hlen
  have hp (b : Bool) : ∀ᶠ n : ℕ in atTop,0 ≤ (pieceSum b x n:ℤ)-((x n).length:ℤ) := by
    have hh := (hnet b).sub ht
    have he : (1/2:ℝ)-0=1/2 := sub_zero _
    rw [he] at hh
    have hev := (tendsto_order.mp hh).1 0 (by norm_num)
    filter_upwards [hev,eventually_gt_atTop (0:ℕ)] with n hn hn0
    have hnR : (0:ℝ)<n := by exact_mod_cast hn0
    have hnum : 0<(pieceSum b x n:ℝ)-((x n).length:ℝ) := by
      rw [← sub_div] at hn
      exact (div_pos_iff.mp hn).resolve_right (fun h => (not_lt_of_ge hnR.le) h.2) |>.1
    exact_mod_cast hnum.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((hp false).and (hp true))
  let K : ℕ := ∑ j∈Finset.range (N+1),(x j).length
  refine ⟨K,fun n b => ?_⟩
  by_cases hn : N ≤ n
  · have hh : 0 ≤ pieceSum b x n-((x n).length:ℤ) := by
      cases b
      · exact (hN n hn).1
      · exact (hN n hn).2
    omega
  · have hnN : n<N := by omega
    have hsum : -(((∑ j∈Finset.range n,(x j).length):ℕ):ℤ) ≤ pieceSum b x n := by
      simp only [pieceSum,Nat.cast_sum]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum (fun j _ => (abs_le.mp (abs_typeNet_le b (x j))).1)
    have hK : (∑ j∈Finset.range n,(x j).length)+(x n).length ≤ K := by
      rw [← Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
    omega

def naturalPiecesLaw (ν : Measure (List Letter)) [IsProbabilityMeasure ν] : Measure (ℕ → List Letter) :=
  Measure.infinitePi (fun _ : ℕ => ν)
instance naturalPieces_probability (ν : Measure (List Letter)) [IsProbabilityMeasure ν] : IsProbabilityMeasure (naturalPiecesLaw ν) := by
  unfold naturalPiecesLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma iid_piece_averages (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    {f : List Letter → ℝ} (hf : Integrable f ν) :
    ∀ᵐ x ∂naturalPiecesLaw ν,Tendsto (fun n => (∑ j∈Finset.range n,f (x j))/(n:ℝ)) atTop (𝓝 (∫ w,f w ∂ν)) := by
  have hfm : Measurable f := measurable_of_countable _
  have hl (j : ℕ) : HasLaw (fun x : ℕ → List Letter => f (x j)) (ν.map f) (naturalPiecesLaw ν) :=
    HasLaw.comp (show HasLaw f (ν.map f) ν from ⟨hfm.aemeasurable,rfl⟩) (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) j).hasLaw
  have hi : iIndepFun (fun j (x : ℕ → List Letter) => f (x j)) (naturalPiecesLaw ν) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => f) (fun _ => hfm)
  have hint := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).integrable_comp_of_integrable hf
  have he := (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0).hasLaw.integral_comp hf.aestronglyMeasurable
  change (∫ x,f (x 0) ∂naturalPiecesLaw ν)=(∫ w,f w ∂ν) at he
  dsimp only [naturalPiecesLaw] at he ⊢
  simpa only [he] using strong_law_ae_real (fun j (x : ℕ → List Letter) => f (x j)) hint
    (fun _ _ h => hi.indepFun h) (fun j => (hl j).identDistrib (hl 0))

lemma iid_piece_buffer_ae (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hlen : Integrable (fun w : List Letter => (w.length:ℝ)) ν)
    (hnet : ∀ b,Integrable (fun w => (typeNet b w:ℝ)) ν)
    (hmean : ∀ b,(∫ w,(typeNet b w:ℝ) ∂ν)=1/2) :
    ∀ᵐ x ∂naturalPiecesLaw ν,∃ K,PieceBuffer K x := by
  have hn (b : Bool) := iid_piece_averages ν (hnet b)
  filter_upwards [iid_piece_averages ν hlen,hn false,hn true] with x hl hf ht
  apply positive_piece_buffer (l := ∫ w,(w.length:ℝ) ∂ν) (hlen := hl)
  intro b
  have he (n : ℕ) : (pieceSum b x n:ℝ)=∑ j∈Finset.range n,(typeNet b (x j):ℝ) := by simp [pieceSum]
  simp only [he]
  cases b
  · simpa only [hmean] using hf
  · simpa only [hmean] using ht

lemma measurableSet_pieceBuffer (K : ℕ) : MeasurableSet {x : ℕ → List Letter | PieceBuffer K x} := by
  simp only [PieceBuffer,Set.ofPred_forall]
  apply MeasurableSet.iInter; intro n
  apply MeasurableSet.iInter; intro b
  exact measurableSet_le ((measurable_of_countable (fun w : List Letter => (w.length:ℤ))).comp (measurable_pi_apply n))
    (measurable_const.add (Finset.measurable_sum _ (fun j _ =>
      (measurable_of_countable (fun w : List Letter => typeNet b w)).comp (measurable_pi_apply j))))

lemma positive_piece_buffer_probability (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hlen : Integrable (fun w : List Letter => (w.length:ℝ)) ν)
    (hnet : ∀ b,Integrable (fun w => (typeNet b w:ℝ)) ν)
    (hmean : ∀ b,(∫ w,(typeNet b w:ℝ) ∂ν)=1/2) :
    ∃ K,0<naturalPiecesLaw ν {x | PieceBuffer K x} := by
  by_contra h
  push Not at h
  have hz (K : ℕ) : naturalPiecesLaw ν {x | PieceBuffer K x}=0 := le_antisymm (h K) (by positivity)
  have hall := iid_piece_buffer_ae ν hlen hnet hmean
  have hu : naturalPiecesLaw ν (⋃ K,{x | PieceBuffer K x})=1 := by
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iUnion measurableSet_pieceBuffer)]
    simpa only [ae_iff,Set.compl_iUnion,Set.compl_ofPred,Set.iInter_ofPred,not_exists] using hall
  have hh := measure_iUnion_le (μ := naturalPiecesLaw ν) (fun K => {x | PieceBuffer K x})
  simp only [hz,tsum_zero,hu] at hh
  exact not_le_of_gt (zero_lt_one' ℝ≥0∞) hh

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def piecesTail (n : ℕ) (x : ℕ → List Letter) : ℕ → List Letter := fun k => x (n+k)
lemma piecesTail_measurable (n : ℕ) : Measurable (piecesTail n) :=
  Measurable.of_eval (fun index => measurable_pi_apply (n+index))
lemma piecesTail_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (piecesTail n) (naturalPiecesLaw ν) (naturalPiecesLaw ν) :=
  ⟨piecesTail_measurable n,Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Nat.add_left_cancel h)⟩

lemma pieceCoords_indep (ν : Measure (List Letter)) [IsProbabilityMeasure ν] {S R : Set ℕ}
    (h : Disjoint S R) : Indep (pieceCoords S) (pieceCoords R) (naturalPiecesLaw ν) :=
  indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (w : List Letter) => w) (fun _ => measurable_id)) h
lemma piecesTail_coords (n : ℕ) : Measurable[pieceCoords {j | n ≤ j}] (piecesTail n) := by
  let : MeasurableSpace (ℕ → List Letter) := pieceCoords {j | n ≤ j}
  apply Measurable.of_eval
  intro k
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le (n+k) (le_iSup_of_le (show n ≤ n+k by omega) le_rfl)

def pieceCylinder (u : List (List Letter)) : Set (ℕ → List Letter) :=
  {x | ∀ i : Fin u.length,x i=u.get i}
lemma pieceCylinder_coords (u : List (List Letter)) :
    MeasurableSet[pieceCoords {j | j<u.length}] (pieceCylinder u) := by
  let : MeasurableSpace (ℕ → List Letter) := pieceCoords {j | j<u.length}
  have hm (i : Fin u.length) : Measurable (fun x : ℕ → List Letter => x i) := by
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le i (le_iSup_of_le i.isLt le_rfl)
  simp only [pieceCylinder,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => (hm i) (measurableSet_singleton (u.get i)))
lemma pieceCylinder_measurable (u : List (List Letter)) : MeasurableSet (pieceCylinder u) := by
  have hle : pieceCoords {j | j<u.length} ≤ (inferInstance : MeasurableSpace (ℕ → List Letter)) :=
    iSup_le (fun j => iSup_le (fun _ => (measurable_pi_apply j).comap_le))
  exact hle _ (pieceCylinder_coords u)
lemma pieceCylinder_eq_pi (u : List (List Letter)) :
    pieceCylinder u=Set.pi (Finset.range u.length) (fun j => {u[j]?.getD []}) := by
  ext x
  simp only [pieceCylinder,Set.mem_ofPred_eq,Set.mem_pi,Finset.mem_coe,Finset.mem_range,Set.mem_singleton_iff]
  constructor
  · intro h j hj
    simpa only [List.getElem?_eq_getElem hj,Option.getD_some,List.get_eq_getElem] using h ⟨j,hj⟩
  · intro h i
    simpa only [List.getElem?_eq_getElem i.isLt,Option.getD_some,List.get_eq_getElem] using h i i.isLt
lemma pieceCylinder_positive (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    {u : List (List Letter)} (hu : ∀ w∈u,0<ν {w}) : 0<naturalPiecesLaw ν (pieceCylinder u) := by
  rw [pieceCylinder_eq_pi]
  unfold naturalPiecesLaw
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  apply bot_lt_iff_ne_bot.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hj' : j<u.length := Finset.mem_range.mp hj
  rw [List.getElem?_eq_getElem hj',Option.getD_some]
  exact ne_of_gt (hu _ (List.getElem_mem hj'))

lemma pieceCylinder_tail_rectangle (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (u : List (List Letter)) {B : Set (ℕ → List Letter)} (hB : MeasurableSet B) :
    naturalPiecesLaw ν (pieceCylinder u ∩ piecesTail u.length ⁻¹' B)=
      naturalPiecesLaw ν (pieceCylinder u)*naturalPiecesLaw ν B := by
  have hi := pieceCoords_indep ν (S := {j | j<u.length}) (R := {j | u.length ≤ j})
    (Set.disjoint_left.mpr (fun j hj hj' => by change j<u.length at hj; change u.length ≤ j at hj'; omega))
  have hh := ((indep_iff_forall_indepSet _).mp hi (pieceCylinder u) (piecesTail u.length ⁻¹' B)
    (pieceCylinder_coords u) (piecesTail_coords u.length hB)).measure_inter_eq_mul
  rw [(piecesTail_preserving ν u.length).measure_preimage hB.nullMeasurableSet] at hh
  exact hh

lemma piecesPrefix_ofFn (x : ℕ → List Letter) (n : ℕ) :
    piecesPrefix x n=(List.ofFn (fun i : Fin n => x i)).flatten := by
  induction n with
  | zero => simp [piecesPrefix]
  | succ n ih =>
    rw [piecesPrefix,ih,List.ofFn_succ']
    simp only [List.concat_eq_append,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
      Fin.val_castSucc,Fin.val_last]
lemma piecesPrefix_of_cylinder {u : List (List Letter)} {x : ℕ → List Letter} (hx : x∈pieceCylinder u) :
    piecesPrefix x u.length=u.flatten := by
  rw [piecesPrefix_ofFn]
  have h : (fun i : Fin u.length => x i)=u.get := funext hx
  rw [h,List.ofFn_get]
lemma piecesPrefix_add (x : ℕ → List Letter) (m n : ℕ) :
    piecesPrefix x (m+n)=piecesPrefix x m++piecesPrefix (piecesTail m x) n := by
  induction n with
  | zero => simp [piecesPrefix]
  | succ n ih =>
    rw [Nat.add_succ,piecesPrefix,ih,piecesPrefix,List.append_assoc]
    rfl

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_LadderCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma firstDown_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstDown h x=WithTop.some n) (hy : firstDown k (tail (n+1) x)=WithTop.some m) :
    firstDown (h+k) x=WithTop.some (n+m+1) := by
  apply (firstDown_of_hit_iff _ _ _).mpr
  constructor
  · rw [show n+m+1+1=(n+1)+(m+1) by omega,signSum_add,
      ((firstDown_of_hit_iff _ _ _).mp hx).1,((firstDown_of_hit_iff _ _ _).mp hy).1]
    push_cast; ring
  · intro j hj
    by_cases hjn : j<n+1
    · by_cases hjn' : j<n
      · have hp := firstDown_prefix_pos hh hx (j := j+1) (by omega)
        push_cast; omega
      · have he : j=n := by omega
        subst j
        rw [((firstDown_of_hit_iff _ _ _).mp hx).1]
        push_cast; omega
    · have hp := firstDown_prefix_pos hk hy (j := j+1-(n+1)) (by omega)
      have he : j+1=(n+1)+(j+1-(n+1)) := by omega
      rw [he,signSum_add,((firstDown_of_hit_iff _ _ _).mp hx).1]
      norm_num only [Nat.cast_add]
      omega
lemma stoppedWord_down_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstDown h x=WithTop.some n) (hy : firstDown k (tail (n+1) x)=WithTop.some m) :
    stoppedWord (firstDown (h+k)) x=stoppedWord (firstDown k) (stoppedTail (firstDown h) x)++stoppedWord (firstDown h) x := by
  rw [stoppedWord_of_hit (firstDown_add hh hk hx hy),stoppedTail_of_hit hx,stoppedWord_of_hit hx,stoppedWord_of_hit hy,
    show n+m+1+1=(n+1)+(m+1) by omega,revealed_add]

def rightPieces (x : ℕ → Letter) : ℕ → List Letter := fun j => wordPieces (firstDown 1) j x
lemma rightPieces_measurable : Measurable rightPieces := by
  apply Measurable.of_eval
  intro j
  exact reverseRightWord_measurable.comp ((measurable_stoppedTail (firstDown_measurable 1)).iterate j)
lemma rightPieces_preserving (P : Parameters) :
    MeasurePreserving rightPieces (streamLaw P ℕ) (naturalPiecesLaw (reverseRightLaw P)) := by
  refine ⟨rightPieces_measurable,?_⟩
  change (streamLaw P ℕ).map (fun x j => (reverseRightWord ∘ (stoppedTail (firstDown 1))^[j]) x)=_
  rw [(stoppedWordPieces_iid P (firstDown_measurable 1) (firstDown_stopping 1) (firstDown_finite P 1 (by omega))).map_fun_eq_infinitePi_map
    (fun j => reverseRightWord_measurable.comp ((measurable_stoppedTail (firstDown_measurable 1)).iterate j))]
  unfold naturalPiecesLaw
  congr 1
  funext j
  have hm := (stoppedTail_preserving P (firstDown_measurable 1) (firstDown_stopping 1) (firstDown_finite P 1 (by omega))).iterate j
  change (streamLaw P ℕ).map (reverseRightWord ∘ (stoppedTail (firstDown 1))^[j])=reverseRightLaw P
  rw [← Measure.map_map reverseRightWord_measurable hm.measurable,hm.map_eq]
  rfl

def reversePiecesPrefix (x : ℕ → List Letter) (n : ℕ) : List Letter :=
  ((List.ofFn (fun i : Fin n => x i)).reverse).flatten
lemma reversePiecesPrefix_succ (x : ℕ → List Letter) (n : ℕ) :
    reversePiecesPrefix x (n+1)=reversePiecesPrefix (piecesTail 1 x) n++x 0 := by
  unfold reversePiecesPrefix
  rw [List.ofFn_succ,List.reverse_cons,List.flatten_append]
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  simp [piecesTail,Nat.add_comm]
lemma rightPieces_tail (x : ℕ → Letter) :
    piecesTail 1 (rightPieces x)=rightPieces (stoppedTail (firstDown 1) x) := by
  funext j
  simp only [piecesTail,rightPieces,wordPieces]
  rw [Nat.add_comm 1 j,Function.iterate_succ_apply]

lemma stoppedWord_down_pieces (P : Parameters) (h : ℕ) : ∀ᵐ x ∂streamLaw P ℕ,
    stoppedWord (firstDown (h+1)) x=reversePiecesPrefix (rightPieces x) (h+1) := by
  induction h with
  | zero =>
    filter_upwards [] with x
    simp [reversePiecesPrefix,rightPieces,wordPieces]
  | succ h ih =>
    have hm := stoppedTail_preserving P (firstDown_measurable 1) (firstDown_stopping 1) (firstDown_finite P 1 (by omega))
    filter_upwards [firstDown_finite P 1 (by omega),hm.quasiMeasurePreserving.tendsto_ae ih,
      hm.quasiMeasurePreserving.tendsto_ae (firstDown_finite P (h+1) (by omega))] with x hx hi hy
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨m,hmm⟩ := WithTop.ne_top_iff_exists.mp hy
    have hn' := hn.symm
    have hm' : firstDown (h+1) (tail (n+1) x)=WithTop.some m := by simpa only [stoppedTail_of_hit hn'] using hmm.symm
    conv_rhs => rw [reversePiecesPrefix_succ,rightPieces_tail]
    rw [show h+1+1=1+(h+1) by omega,stoppedWord_down_add (by omega) (by omega) hn' hm',hi]
    rfl

def reverseFirstPieces (n : ℕ) (x : ℕ → List Letter) : ℕ → List Letter :=
  fun j => x (TreeCoding.reverseIndex n j)
lemma reverseFirstPieces_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (reverseFirstPieces n) (naturalPiecesLaw ν) (naturalPiecesLaw ν) :=
  ⟨Measurable.of_eval (fun _ => measurable_pi_apply _),
    Measure.map_infinitePi_infinitePi_of_inj (TreeCoding.reverseIndex_involutive n).injective⟩
lemma reversePiecesPrefix_eq (x : ℕ → List Letter) (n : ℕ) :
    reversePiecesPrefix x n=piecesPrefix (reverseFirstPieces n x) n := by
  rw [piecesPrefix_ofFn]
  unfold reversePiecesPrefix
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp only [List.length_reverse,List.length_ofFn] at hj hk
    simp [List.getElem_reverse,reverseFirstPieces,TreeCoding.reverseIndex]

lemma rightPrefix_identDistrib (P : Parameters) (h : ℕ) :
    IdentDistrib (stoppedWord (firstDown (h+1))) (fun x => piecesPrefix x (h+1))
      (streamLaw P ℕ) (naturalPiecesLaw (reverseRightLaw P)) := by
  have hp := (reverseFirstPieces_preserving (reverseRightLaw P) (h+1)).comp (rightPieces_preserving P)
  have hm : Measurable (fun x : ℕ → List Letter => piecesPrefix x (h+1)) := by
    rw [show (fun x : ℕ → List Letter => piecesPrefix x (h+1))=
      (fun f : Fin (h+1) → List Letter => (List.ofFn f).flatten) ∘ (fun x i => x i) by
        funext x; exact piecesPrefix_ofFn x (h+1)]
    exact (measurable_of_countable _).comp (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))
  have hi := (hp.hasLaw.identDistrib ((MeasurePreserving.id _).hasLaw)).comp hm
  apply (IdentDistrib.of_ae_eq (measurable_stoppedWord (firstDown_measurable (h+1))).aemeasurable ?_).trans hi
  filter_upwards [stoppedWord_down_pieces P h] with x hx
  simpa only [Function.comp_apply,reversePiecesPrefix_eq] using hx

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma piecesPrefix_measurable (n : ℕ) : Measurable (fun x : ℕ → List Letter => piecesPrefix x n) := by
  have he : (fun x : ℕ → List Letter => piecesPrefix x n)=
      (fun f : Fin n → List Letter => (List.ofFn f).flatten) ∘ (fun x i => x i) := by
    funext x; exact piecesPrefix_ofFn x n
  rw [he]
  exact (measurable_of_countable _).comp (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))

def NonemptyPieces (x : ℕ → List Letter) : Prop := ∀ j,(x j)≠[]
lemma reverseRightLaw_nonempty (P : Parameters) : ∀ᵐ w ∂reverseRightLaw P,w≠[] := by
  apply (ae_map_iff reverseRightWord_measurable.aemeasurable (measurableSet_singleton ([]:List Letter)).compl).mpr
  filter_upwards [reverseRightWord_net P] with x hx hnil
  change reverseRightWord x=[] at hnil
  simp [hnil] at hx
lemma rightPieces_nonempty (P : Parameters) : ∀ᵐ x ∂naturalPiecesLaw (reverseRightLaw P),NonemptyPieces x := by
  rw [show (fun x => NonemptyPieces x)=(fun x => ∀ j,x j≠[]) by rfl,ae_all_iff]
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => reverseRightLaw P) j).quasiMeasurePreserving.tendsto_ae
    (reverseRightLaw_nonempty P)
lemma piecesPrefix_length {x : ℕ → List Letter} (hx : NonemptyPieces x) (n : ℕ) :
    n ≤ (piecesPrefix x n).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hp : 0<(x n).length := List.length_pos_iff.mpr (hx n)
    simp only [piecesPrefix,List.length_append]
    omega
lemma piecesPrefix_extension (x : ℕ → List Letter) {m n : ℕ} (hmn : m ≤ n) :
    ∃ w,piecesPrefix x n=piecesPrefix x m++w := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact ⟨_,piecesPrefix_add x m k⟩

def pieceScan (x : ℕ → List Letter) : ℕ → Letter := fun j =>
  ((piecesPrefix x (j+1))[j]?).getD (.order none)
lemma pieceScan_measurable : Measurable pieceScan := by
  apply Measurable.of_eval
  intro j
  exact (measurable_of_countable (fun w : List Letter => (w[j]?).getD (.order none))).comp (piecesPrefix_measurable (j+1))
lemma pieceScan_get {x : ℕ → List Letter} (hx : NonemptyPieces x) {m j : ℕ} (hj : j < m) :
    pieceScan x j=(piecesPrefix x m)[j]'(lt_of_lt_of_le hj (piecesPrefix_length hx m)) := by
  have hp : j<(piecesPrefix x (j+1)).length := lt_of_lt_of_le (by omega) (piecesPrefix_length hx (j+1))
  obtain ⟨w,hw⟩ := piecesPrefix_extension x (show j+1 ≤ m by omega)
  simp only [pieceScan,List.getElem?_eq_getElem hp,Option.getD_some]
  simp only [hw,List.getElem_append_left hp]
lemma rawWord_pieceScan {x : ℕ → List Letter} (hx : NonemptyPieces x) {m h : ℕ} (hmh : m ≤ h) :
    rawWord (pieceScan x) m=(piecesPrefix x h).take m := by
  have hl := (hmh.trans (piecesPrefix_length hx h))
  apply List.ext_getElem
  · simp [rawWord,List.length_ofFn, min_eq_left hl]
  · intro j hj hk
    have hj' : j < m := by simpa [rawWord] using hj
    simp only [rawWord,List.getElem_ofFn,rawPrefix,List.getElem_take]
    exact pieceScan_get hx (hj'.trans_le hmh)

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawWord_measurable (n : ℕ) : Measurable (fun x : ℕ → Letter => rawWord x n) :=
  (measurable_of_countable _).comp (rawPrefix_measurable n)
lemma wordWeight_reverse (P : Parameters) (w : List Letter) : wordWeight P w.reverse=wordWeight P w := by
  simp [wordWeight,List.map_reverse]
lemma rawWord_reverse (x : ℕ → Letter) (n : ℕ) : (rawWord x n).reverse=revealed x n := rfl
lemma increment_sum_bounds (w : List Letter) :
    -(w.length:ℤ) ≤ (w.map Letter.increment).sum ∧ (w.map Letter.increment).sum ≤ (w.length:ℤ) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := increment_bounds a
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    omega
lemma rightDensity_signSum_bounds (x : ℕ → Letter) (n : ℕ) : -(n:ℤ) ≤ signSum x n ∧ signSum x n ≤ n := by
  have hh := increment_sum_bounds (revealed x n)
  rw [revealed_sum] at hh
  simpa only [revealed,List.length_reverse,List.length_ofFn] using hh
lemma firstDown_length {h n : ℕ} {x : ℕ → Letter} (hx : firstDown h x=WithTop.some n) : h ≤ n+1 := by
  have hh := ((firstDown_of_hit_iff _ _ _).mp hx).1
  have hb := (rightDensity_signSum_bounds x (n+1)).1
  omega

lemma rawKilled_preimage (a b n : ℕ) : rawKilled a b n=rawPrefix n ⁻¹'
    {d | SimpleWalk.nonnegativePath a (finiteSigns d) ∧ (a:ℤ)+SimpleWalk.pathSum (finiteSigns d) n=b} := by
  ext x
  simp only [rawKilled,Set.mem_ofPred_eq,Set.mem_preimage,SimpleWalk.nonnegativePath]
  rw [raw_sign_pathSum x n n le_rfl]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [raw_sign_pathSum x n j hj]
lemma rawPrefix_tail_rectangle (P : Parameters) (n : ℕ) (A : Set (Fin n → Letter))
    (B : Set (ℕ → Letter)) (hB : MeasurableSet B) :
    streamLaw P ℕ (rawPrefix n ⁻¹' A ∩ tail n ⁻¹' B)=streamLaw P ℕ (rawPrefix n ⁻¹' A)*streamLaw P ℕ B := by
  cases n with
  | zero =>
    by_cases ha : (fun i : Fin 0 => Fin.elim0 i)∈A
    · have he : rawPrefix 0 ⁻¹' A=Set.univ := by
        ext x
        simp only [Set.mem_preimage,Set.mem_univ,iff_true]
        convert ha using 1
        all_goals try with_reducible_and_instances rfl
      rw [he,Set.univ_inter,measure_univ,one_mul]
      congr 1
      ext x
      simp only [Set.mem_preimage,tail_zero]
    · have he : rawPrefix 0 ⁻¹' A=∅ := by
        ext x
        simp only [Set.mem_preimage,Set.mem_empty_iff_false,iff_false]
        have hf : rawPrefix 0 x=(fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
        rwa [hf]
      rw [he,Set.empty_inter,measure_empty,zero_mul]
  | succ n =>
    have hi := raw_fun_indep_tail P n (f := rawPrefix (n+1)) (prefix_measurable n id)
    have he := hi.measure_inter_preimage_eq_mul A B (Set.to_countable A).measurableSet hB
    rw [(tail_preserving P (n+1)).measure_preimage hB.nullMeasurableSet] at he
    exact he
lemma rawKilled_block_rectangle (P : Parameters) (a b n : ℕ) (w : List Letter) :
    streamLaw P ℕ (rawKilled a b n ∩ {x | rawWord (tail n x) w.length=w})=
      ENNReal.ofReal (SimpleWalk.killed n a b)*wordWeight P w := by
  rw [rawKilled_preimage]
  change streamLaw P ℕ (rawPrefix n ⁻¹' _ ∩ tail n ⁻¹' {x | rawWord x w.length=w})=_
  rw [rawPrefix_tail_rectangle P n _ {x | rawWord x w.length=w} (by exact (rawWord_measurable _) (measurableSet_singleton w)),rawWord_cylinder]
  rw [← rawKilled_preimage]
  congr 1
  rw [← rawKilled_measure P,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A specified reversed terminal string of a first-downcrossing word leaves
a genuine killed-walk prefix and an independent raw suffix. -/
lemma stoppedWord_suffix_witness {h t : ℕ} {x : ℕ → Letter} {w : List Letter}
    (hwpos : 0<w.length) (hh : w.length<h) (hx : firstDown h x=WithTop.some t)
    (hw : (stoppedWord (firstDown h) x).take w.length=w) :
    ∃ r n : ℕ,0 < r ∧ (r:ℤ)= -(w.map Letter.increment).sum ∧
      x∈rawKilled (h-1) (r-1) n ∧ rawWord (tail n x) w.length=w.reverse := by
  have ht := firstDown_length hx
  let n := t+1-w.length
  have hn : n+w.length=t+1 := by dsimp [n]; omega
  have hnlt : n ≤ t := by dsimp [n]; omega
  have hwr : revealed (tail n x) w.length=w := by
    rw [stoppedWord_of_hit hx,← hn,revealed_add,
      List.take_left' (by simp [revealed])] at hw
    exact hw
  have hwS : signSum (tail n x) w.length=(w.map Letter.increment).sum := by
    rw [← revealed_sum,hwr]
  have hsum := ((firstDown_of_hit_iff _ _ _).mp hx).1
  rw [← hn,signSum_add,hwS] at hsum
  have hp := firstDown_prefix_pos (by omega : 0<h) hx hnlt
  have hneg : (w.map Letter.increment).sum<0 := by omega
  let r := (-(w.map Letter.increment).sum).toNat
  have hr : (r:ℤ)= -(w.map Letter.increment).sum := Int.toNat_of_nonneg (by omega)
  have hrpos : 0 < r := by omega
  refine ⟨r,n,hrpos,hr,⟨?_,?_⟩,?_⟩
  · intro j hj
    have hjp := firstDown_prefix_pos (by omega : 0<h) hx (hj.trans hnlt)
    have hhcast : ((h-1:ℕ):ℤ)=(h:ℤ)-1 := by omega
    rw [hhcast]
    omega
  · have hhcast : ((h-1:ℕ):ℤ)=(h:ℤ)-1 := by omega
    have hrcast : ((r-1:ℕ):ℤ)=(r:ℤ)-1 := by omega
    rw [hhcast,hrcast]
    omega
  · have he := congrArg List.reverse hwr
    simpa only [← rawWord_reverse,List.reverse_reverse] using he

def terminalDeficit (w : List Letter) : ℕ := (-(w.map Letter.increment).sum).toNat

/-- The only density estimate used is a sum of finite-prefix cylinders.
No integrability of the raw downcrossing length is asserted. -/
theorem stoppedWord_prefix_density_bound (P : Parameters) (h : ℕ) (w : List Letter)
    (hwpos : 0<w.length) (hh : w.length<h) :
    streamLaw P ℕ {x | (stoppedWord (firstDown h) x).take w.length=w} ≤
      2*(terminalDeficit w:ℝ≥0∞)*wordWeight P w := by
  let E : Set (ℕ → Letter) := {x | (stoppedWord (firstDown h) x).take w.length=w}
  let r := terminalDeficit w
  have hfin := firstDown_finite P h (by omega)
  by_cases hr : r=0
  · have he : E=ᵐ[streamLaw P ℕ] (∅ : Set (ℕ → Letter)) := by
      filter_upwards [hfin] with x hx
      change ((stoppedWord (firstDown h) x).take w.length=w)=False
      apply propext
      simp only [iff_false]
      intro hw
      obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨s,n,hs,hseq,_,_⟩ := stoppedWord_suffix_witness hwpos hh ht.symm hw
      have hsr : s=r := by dsimp [r,terminalDeficit]; omega
      omega
    rw [measure_congr he,measure_empty]
    exact bot_le
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let C : ℕ → Set (ℕ → Letter) := fun n => rawKilled (h-1) (r-1) n ∩ {x | rawWord (tail n x) w.length=w.reverse}
    have he : E ≤ᵐ[streamLaw P ℕ] ⋃ n,C n := by
      filter_upwards [hfin] with x hx hw
      obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hx
      obtain ⟨s,n,hs,hseq,hk,hw'⟩ := stoppedWord_suffix_witness hwpos hh ht.symm hw
      have hsr : s=r := by dsimp [r,terminalDeficit]; omega
      subst s
      exact Set.mem_iUnion.mpr ⟨n,hk,hw'⟩
    have hc (n : ℕ) : streamLaw P ℕ (C n)=ENNReal.ofReal (SimpleWalk.killed n (h-1) (r-1))*wordWeight P w := by
      simpa only [C,List.length_reverse,wordWeight_reverse] using rawKilled_block_rectangle P (h-1) (r-1) n w.reverse
    calc
      streamLaw P ℕ E ≤ streamLaw P ℕ (⋃ n,C n) := measure_mono_ae he
      _ ≤ ∑' n,streamLaw P ℕ (C n) := measure_iUnion_le _
      _ = (∑' n,ENNReal.ofReal (SimpleWalk.killed n (h-1) (r-1)))*wordWeight P w := by
        simp_rw [hc]
        rw [ENNReal.tsum_mul_right]
      _ ≤ (2*(r:ℝ≥0∞))*wordWeight P w := by
        apply mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => SimpleWalk.killed_nonneg n (h-1) (r-1))
          (SimpleWalk.killed_summable (h-1) (r-1))]
        have hb := SimpleWalk.killed_green_bound (h-1) (r-1)
        have he' : r-1+1=r := by omega
        rw [he'] at hb
        simpa only [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2:ℝ)),ENNReal.ofReal_ofNat,ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def rightScanLaw (P : Parameters) : Measure (ℕ → Letter) :=
  (naturalPiecesLaw (reverseRightLaw P)).map pieceScan
instance instIsProbabilityMeasureForallNatLetterRightScanLaw (P : Parameters) : IsProbabilityMeasure (rightScanLaw P) :=
  Measure.isProbabilityMeasure_map (pieceScan_measurable.aemeasurable)

lemma rightScan_cylinder_bound (P : Parameters) (w : List Letter) (hw : 0<w.length) :
    rightScanLaw P {x | rawWord x w.length=w} ≤
      2*(terminalDeficit w:ℝ≥0∞)*wordWeight P w := by
  rw [rightScanLaw,Measure.map_apply pieceScan_measurable (measurableSet_eq_fun (rawWord_measurable _) measurable_const)]
  have he : pieceScan ⁻¹' {x | rawWord x w.length=w}=ᵐ[naturalPiecesLaw (reverseRightLaw P)]
      {x | (piecesPrefix x (w.length+1)).take w.length=w} := by
    filter_upwards [rightPieces_nonempty P] with x hx
    change (rawWord (pieceScan x) w.length=w)=((piecesPrefix x (w.length+1)).take w.length=w)
    rw [rawWord_pieceScan hx (Nat.le_succ _)]
  rw [measure_congr he]
  have hi := (rightPrefix_identDistrib P w.length).comp
    (measurable_of_countable (fun v : List Letter => v.take w.length))
  have hh := hi.measure_mem_eq (measurableSet_singleton w)
  change streamLaw P ℕ {x | (stoppedWord (firstDown (w.length+1)) x).take w.length=w}=
    naturalPiecesLaw (reverseRightLaw P) {x | (piecesPrefix x (w.length+1)).take w.length=w} at hh
  rw [← hh]
  exact stoppedWord_prefix_density_bound P (w.length+1) w hw (Nat.lt_succ_self _)

lemma rightScan_first_order (P : Parameters) : ∀ᵐ x ∂rightScanLaw P,∃ o,x 0=Letter.order o := by
  have hz (b : Bool) : rightScanLaw P {x | x 0=Letter.burger b}=0 := by
    have hh := rightScan_cylinder_bound P [Letter.burger b] (by simp)
    have he : {x : ℕ → Letter | rawWord x [Letter.burger b].length=[Letter.burger b]}={x | x 0=Letter.burger b} := by
      ext x; simp [rawWord,rawPrefix,List.ofFn_succ]
    rw [he] at hh
    simpa [terminalDeficit,Letter.increment] using hh
  have htrue : ∀ᵐ x ∂rightScanLaw P,x 0≠Letter.burger true := by exact ae_iff.mpr (by simpa only [not_not] using hz true)
  have hfalse : ∀ᵐ x ∂rightScanLaw P,x 0≠Letter.burger false := by exact ae_iff.mpr (by simpa only [not_not] using hz false)
  filter_upwards [htrue,hfalse] with x ht hf
  cases h : x 0 with
  | burger b => cases b <;> contradiction
  | order o => exact ⟨o,rfl⟩

def rightRemainderLaw (P : Parameters) : Measure (ℕ → Letter) := (rightScanLaw P).map (tail 1)
instance instIsProbabilityMeasureForallNatLetterRightRemainderLaw (P : Parameters) : IsProbabilityMeasure (rightRemainderLaw P) :=
  Measure.isProbabilityMeasure_map ((measurable_tail 1).aemeasurable)

lemma rawWord_succ_head (x : ℕ → Letter) (n : ℕ) :
    rawWord x (n+1)=x 0::rawWord (tail 1 x) n := by
  simp only [rawWord,rawPrefix,List.ofFn_succ]
  congr 2
  funext i
  dsimp [rawPrefix,tail]
  congr 1
  omega
lemma wordWeight_cons (P : Parameters) (a : Letter) (w : List Letter) :
    wordWeight P (a::w)=(law P).toMeasure {a}*wordWeight P w := by simp [wordWeight]
lemma terminalDeficit_order (o : Option Bool) (w : List Letter) :
    terminalDeficit (Letter.order o::w)=(1-(w.map Letter.increment).sum).toNat := by
  simp only [terminalDeficit,List.map_cons,List.sum_cons,Letter.increment]
  congr 1; omega
lemma order_mass_sum (P : Parameters) : ∑ o : Option Bool,(law P).toMeasure {Letter.order o}=(2:ℝ≥0∞)⁻¹ := by
  simp only [law_singleton,Fintype.sum_option,Fintype.sum_bool,mass]
  rw [← ENNReal.ofReal_add (by linarith [P.upper]) (by linarith [P.upper]),
    ← ENNReal.ofReal_add (by linarith [P.pos]) (by linarith [P.upper])]
  norm_num [show P.p/2+((1-P.p)/4+(1-P.p)/4)=(1:ℝ)/2 by ring,ENNReal.ofReal_div_of_pos]

theorem rightRemainder_cylinder_bound (P : Parameters) (w : List Letter) :
    rightRemainderLaw P {x | rawWord x w.length=w} ≤
      ((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*wordWeight P w := by
  rw [rightRemainderLaw,Measure.map_apply (measurable_tail 1) (measurableSet_eq_fun (rawWord_measurable _) measurable_const)]
  have he : tail 1 ⁻¹' {x | rawWord x w.length=w}=ᵐ[rightScanLaw P]
      ⋃ o : Option Bool,{x | rawWord x (w.length+1)=Letter.order o::w} := by
    filter_upwards [rightScan_first_order P] with x hx
    obtain ⟨o,ho⟩ := hx
    change (rawWord (tail 1 x) w.length=w)=(x∈⋃ o : Option Bool,{x | rawWord x (w.length+1)=Letter.order o::w})
    apply propext
    rw [Set.mem_iUnion]
    change _ ↔ ∃ o : Option Bool,rawWord x (w.length+1)=Letter.order o::w
    simp only [rawWord_succ_head,ho,List.cons.injEq]
    exact ⟨fun h => ⟨o,rfl,h⟩,fun ⟨_,_,h⟩ => h⟩
  rw [measure_congr he]
  calc
    rightScanLaw P (⋃ o : Option Bool,{x | rawWord x (w.length+1)=Letter.order o::w})
      ≤ ∑ o : Option Bool,rightScanLaw P {x | rawWord x (w.length+1)=Letter.order o::w} := by
        simpa only [tsum_fintype] using measure_iUnion_le (fun o : Option Bool => {x | rawWord x (w.length+1)=Letter.order o::w})
    _ ≤ ∑ o : Option Bool,2*((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*((law P).toMeasure {Letter.order o}*wordWeight P w) := by
      apply Finset.sum_le_sum
      intro o _
      simpa only [List.length_cons,terminalDeficit_order,wordWeight_cons] using
        rightScan_cylinder_bound P (Letter.order o::w) (by simp)
    _ = ((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*wordWeight P w := by
      rw [← Finset.mul_sum,← Finset.sum_mul,order_mass_sum]
      calc
        _ = ((2:ℝ≥0∞)*2⁻¹)*(((1-(w.map Letter.increment).sum).toNat:ℝ≥0∞)*wordWeight P w) := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawFiltration_eq_comap (n : ℕ) : rawFiltration n=(inferInstance : MeasurableSpace (Fin (n+1) → Letter)).comap (rawPrefix (n+1)) := by
  apply le_antisymm
  · change (⨆ k ≤ n,MeasurableSpace.comap (fun x : ℕ → Letter => x k) inferInstance) ≤ _
    apply iSup_le
    intro k
    apply iSup_le
    intro hk
    have hm : Measurable[(inferInstance : MeasurableSpace (Fin (n+1) → Letter)).comap (rawPrefix (n+1))]
        (fun x : ℕ → Letter => x k) := by
      exact (measurable_pi_apply (⟨k,by omega⟩ : Fin (n+1))).comp (comap_measurable (rawPrefix (n+1)))
    exact hm.comap_le
  · exact (prefix_measurable n id).comap_le

lemma rawPrefix_atom (n : ℕ) (d : Fin n → Letter) :
    {x : ℕ → Letter | rawWord x n=List.ofFn d}=rawPrefix n ⁻¹' {d} := by
  ext x
  simp only [rawWord,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_singleton_iff,List.ofFn_inj]
lemma rightRemainder_prefix_bound (P : Parameters) (n : ℕ) (d : Fin n → Letter) :
    rightRemainderLaw P (rawPrefix n ⁻¹' {d}) ≤
      ((1-(∑ i,(d i).increment:ℤ)).toNat:ℝ≥0∞)*streamLaw P ℕ (rawPrefix n ⁻¹' {d}) := by
  have hh := rightRemainder_cylinder_bound P (List.ofFn d)
  rw [List.length_ofFn,rawPrefix_atom] at hh
  rw [← rawWord_cylinder P (List.ofFn d),List.length_ofFn,rawPrefix_atom] at hh
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hh

lemma rightRemainder_prefix_event (P : Parameters) (n : ℕ) (A : Set (Fin n → Letter)) :
    rightRemainderLaw P (rawPrefix n ⁻¹' A) ≤
      ∫⁻ x in rawPrefix n ⁻¹' A,((1-signSum x n).toNat:ℝ≥0∞) ∂streamLaw P ℕ := by
  classical
  let D : (Fin n → Letter) → ℝ≥0∞ := fun d => ((1-(∑ i,(d i).increment:ℤ)).toNat:ℝ≥0∞)
  have hn : MeasurableSet A := (Set.to_countable _).measurableSet
  have he : rawPrefix n ⁻¹' A=⋃ d : Fin n → Letter,if d∈A then rawPrefix n ⁻¹' {d} else ∅ := by
    ext x
    simp only [Set.mem_preimage,Set.mem_iUnion]
    constructor
    · intro hx; exact ⟨rawPrefix n x,by simp [hx]⟩
    · rintro ⟨d,hd⟩
      split_ifs at hd with h
      · have hd' : rawPrefix n x=d := hd; rwa [hd']
      · exact hd.elim
  calc
    rightRemainderLaw P (rawPrefix n ⁻¹' A) ≤
        ∑ d : Fin n → Letter,if d∈A then rightRemainderLaw P (rawPrefix n ⁻¹' {d}) else 0 := by
      rw [he]
      simpa only [tsum_fintype,apply_ite,measure_empty] using
        measure_iUnion_le (fun d : Fin n → Letter => if d∈A then rawPrefix n ⁻¹' {d} else ∅) (μ := rightRemainderLaw P)
    _ ≤ ∑ d : Fin n → Letter,(A.indicator D d)*streamLaw P ℕ (rawPrefix n ⁻¹' {d}) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : d∈A
      · simpa only [hd,ite_eq_left,Set.indicator_of_mem] using rightRemainder_prefix_bound P n d
      · simp only [ite_eq_right hd]; exact bot_le
    _ = ∫⁻ d,A.indicator D d ∂(streamLaw P ℕ).map (rawPrefix n) := by
      rw [lintegral_fintype]
      apply Finset.sum_congr rfl
      intro d _
      rw [Measure.map_apply (rawPrefix_measurable n) (measurableSet_singleton d)]
    _ = ∫⁻ x in rawPrefix n ⁻¹' A,((1-signSum x n).toNat:ℝ≥0∞) ∂streamLaw P ℕ := by
      rw [lintegral_map (measurable_of_countable _) (rawPrefix_measurable n),← lintegral_indicator ((rawPrefix_measurable n) hn)]
      apply lintegral_congr
      intro x
      by_cases hx : rawPrefix n x∈A
      · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (show x∈rawPrefix n ⁻¹' A from hx),D,rawPrefix]
        rw [Fin.sum_univ_eq_sum_range (fun i => (x i).increment) n]
        rfl
      · simp only [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x∉rawPrefix n ⁻¹' A from hx)]

lemma K_signSum_of_hit {x : ℕ → Letter} {n : ℕ} (hx : firstSurvivor x=WithTop.some n) :
    (1-signSum x (n+1)).toNat=K x := by
  obtain ⟨b,hb,_⟩ := firstSurvivor_shape hx
  have hh := reduce_imbalance (revealed x (n+1))
  rw [hb,imbalance,revealed_sum] at hh
  simp only [List.length_singleton,Nat.cast_one] at hh
  rw [K_of_hit hx,hb]
  change (1-signSum x (n+1)).toNat=(reduce (revealed x n)).orders.length
  change 1-((reduce (revealed x n)).orders.length:ℤ)=signSum x (n+1) at hh
  omega

theorem rightRemainder_hit_bound (P : Parameters) (n : ℕ) :
    rightRemainderLaw P {x | firstSurvivor x=WithTop.some n} ≤
      ∫⁻ x in {x | firstSurvivor x=WithTop.some n},(K x:ℝ≥0∞) ∂streamLaw P ℕ := by
  have he := firstSurvivor_stopping.measurableSet_eq n
  rw [rawFiltration_eq_comap,MeasurableSpace.measurableSet_comap] at he
  obtain ⟨A,_,hA⟩ := he
  have hb := rightRemainder_prefix_event P (n+1) A
  rw [hA] at hb
  refine hb.trans_eq ?_
  apply setLIntegral_congr_fun (rawFiltration.le n _ (firstSurvivor_stopping.measurableSet_eq n))
  intro x hx
  exact congrArg (fun k : ℕ => (k:ℝ≥0∞)) (K_signSum_of_hit hx)

theorem rightRemainder_survivor_bound (P : Parameters) :
    rightRemainderLaw P {x | firstSurvivor x≠⊤} ≤ ∫⁻ x,(K x:ℝ≥0∞) ∂streamLaw P ℕ := by
  have he : {x : ℕ → Letter | firstSurvivor x≠⊤}=⋃ n : ℕ,{x | firstSurvivor x=WithTop.some n} := by
    ext x; simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    exact WithTop.ne_top_iff_exists.trans (by simp only [eq_comm])
  have hm (n : ℕ) : MeasurableSet {x : ℕ → Letter | firstSurvivor x=WithTop.some n} :=
    rawFiltration.le n _ (firstSurvivor_stopping.measurableSet_eq n)
  calc
    rightRemainderLaw P {x | firstSurvivor x≠⊤} ≤ ∑' n : ℕ,rightRemainderLaw P {x | firstSurvivor x=WithTop.some n} := by rw [he]; exact measure_iUnion_le _
    _ ≤ ∑' n : ℕ,∫⁻ x in {x | firstSurvivor x=WithTop.some n},(K x:ℝ≥0∞) ∂streamLaw P ℕ := ENNReal.tsum_le_tsum (rightRemainder_hit_bound P)
    _ = ∫⁻ x in {x | firstSurvivor x≠⊤},(K x:ℝ≥0∞) ∂streamLaw P ℕ := by
      rw [he,lintegral_iUnion hm]
      intro i j hij
      exact Set.disjoint_left.mpr (fun x hi hj => hij (WithTop.coe_injective (hi.symm.trans hj)))
    _ ≤ ∫⁻ x,(K x:ℝ≥0∞) ∂streamLaw P ℕ := setLIntegral_le_lintegral _ _

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def RightCut (x : ℕ → List Letter) : Prop := ∀ n,(reduce (piecesPrefix x n).reverse).burgers=[]
lemma measurableSet_rightCut : MeasurableSet {x | RightCut x} := by
  simp only [RightCut,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  exact (piecesPrefix_measurable n) (Set.to_countable {w : List Letter | (reduce w.reverse).burgers=[]}).measurableSet

lemma rawWord_pieceScan_prefix {x : ℕ → List Letter} (hx : NonemptyPieces x) (n : ℕ) :
    rawWord (pieceScan x) (piecesPrefix x n).length=piecesPrefix x n := by
  let m := (piecesPrefix x n).length
  rw [rawWord_pieceScan hx (show m ≤ n+m by omega)]
  obtain ⟨w,hw⟩ := piecesPrefix_extension x (show n ≤ n+m by omega)
  rw [hw]
  exact List.take_left' rfl

lemma noSurvivor_burgers {x : ℕ → Letter} (hx : firstSurvivor x=⊤) (n : ℕ) :
    (reduce (revealed x n)).burgers=[] := by
  cases n with
  | zero => simp [revealed_zero,reduce,run]
  | succ n =>
    by_contra h
    have hh := (firstSurvivor_le_iff x n).mpr h
    rw [hx] at hh
    exact WithTop.not_top_le_coe n hh
lemma append_order_no_burgers {w : List Letter} (hw : (reduce w).burgers=[]) (o : Option Bool) :
    (reduce (w++[Letter.order o])).burgers=[] := by
  change (run (w++[Letter.order o]) ⟨[],[]⟩).burgers=[]
  rw [run_append]
  change (step (reduce w) (Letter.order o)).burgers=[]
  simp only [step,hw,pop]
lemma remainder_noSurvivor_implies_cut {x : ℕ → List Letter} (hx : NonemptyPieces x)
    (ho : ∃ o,pieceScan x 0=Letter.order o) (hs : firstSurvivor (tail 1 (pieceScan x))=⊤) : RightCut x := by
  intro n
  rw [← rawWord_pieceScan_prefix hx n,rawWord_reverse]
  let m := (piecesPrefix x n).length
  change (reduce (revealed (pieceScan x) m)).burgers=[]
  cases m with
  | zero => simp [revealed_zero,reduce,run]
  | succ m =>
    obtain ⟨o,ho⟩ := ho
    rw [show m+1=1+m by omega,revealed_add]
    have he : revealed (pieceScan x) 1=[Letter.order o] := by simp [revealed,List.ofFn_succ,ho]
    rw [he]
    exact append_order_no_burgers (noSurvivor_burgers hs m) o

lemma K_lintegral_lt_one (P : Parameters) : (∫⁻ x,(K x:ℝ≥0∞) ∂streamLaw P ℕ)<1 := by
  have he := ofReal_integral_eq_lintegral_ofReal (integrable_K P)
    (Filter.Eventually.of_forall (fun x => Nat.cast_nonneg (K x)))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he]
  exact_mod_cast (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (integral_K_lt_one P)

lemma rightRemainder_noSurvivor_pos (P : Parameters) :
    0 < rightRemainderLaw P {x | firstSurvivor x=⊤} := by
  have hlt := lt_of_le_of_lt (rightRemainder_survivor_bound P) (K_lintegral_lt_one P)
  have hm : MeasurableSet {x | firstSurvivor x=⊤} := measurableSet_eq_fun measurable_firstSurvivor measurable_const
  have he : {x | firstSurvivor x≠⊤}={x : ℕ → Letter | firstSurvivor x=⊤}ᶜ := rfl
  rw [he,measure_compl hm (measure_ne_top _ _),measure_univ] at hlt
  by_contra! hh
  have hz := le_antisymm hh bot_le
  rw [hz,tsub_zero] at hlt
  exact lt_irrefl _ hlt

theorem positive_rightCut (P : Parameters) :
    0<naturalPiecesLaw (reverseRightLaw P) {x | RightCut x} := by
  have hm : MeasurableSet {x | firstSurvivor x=⊤} := measurableSet_eq_fun measurable_firstSurvivor measurable_const
  have hpos := rightRemainder_noSurvivor_pos P
  rw [rightRemainderLaw,Measure.map_apply (measurable_tail 1) hm,
    rightScanLaw,Measure.map_apply pieceScan_measurable ((measurable_tail 1) hm)] at hpos
  refine hpos.trans_le (measure_mono_ae ?_)
  have ho : ∀ᵐ x ∂naturalPiecesLaw (reverseRightLaw P),∃ o,pieceScan x 0=Letter.order o := by
    exact (ae_map_iff pieceScan_measurable.aemeasurable (by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun o => measurableSet_eq_fun (measurable_pi_apply 0) measurable_const))).mp (rightScan_first_order P)
  filter_upwards [rightPieces_nonempty P,ho] with x hx ho hs
  exact remainder_noSurvivor_implies_cut hx ho hs

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma orders_step_sublist (a : Letter) (e : Evaluation) : e.orders.Sublist (step e a).orders := by
  cases a with
  | burger b => exact List.Sublist.refl _
  | order o => cases h : pop o e.burgers <;> simp [step,h]
lemma orders_run_sublist (w : List Letter) (e : Evaluation) : e.orders.Sublist (run w e).orders := by
  induction w generalizing e with
  | nil => exact List.Sublist.refl _
  | cons a w ih => exact (orders_step_sublist a e).trans (ih _)

def LeftCut (x : ℕ → List Letter) : Prop := ∀ n,(reduce (piecesPrefix x n)).orders=[]
lemma measurable_piecesPrefix (n : ℕ) : Measurable (fun x : ℕ → List Letter => piecesPrefix x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun z : List Letter × List Letter => z.1++z.2)).comp (ih.prodMk (measurable_pi_apply n))
lemma measurableSet_leftCut : MeasurableSet {x | LeftCut x} := by
  simp only [LeftCut,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (measurable_piecesPrefix n)
    ((Set.to_countable {w : List Letter | (reduce w).orders=[]}).measurableSet))

def supplyPieces (K : ℕ) : List (List Letter) :=
  List.replicate K [Letter.burger false]++List.replicate K [Letter.burger true]
lemma supplyPieces_flatten (K : ℕ) : (supplyPieces K).flatten=(startingSupply K).reverse.map Letter.burger := by
  have hh (b : Bool) : (List.replicate K [Letter.burger b]).flatten=List.replicate K (Letter.burger b) := by
    induction K with
    | zero => rfl
    | succ K ih => simp [List.replicate_succ,ih]
  simp [supplyPieces,startingSupply,hh]
lemma run_supplyPieces (K : ℕ) : run (supplyPieces K).flatten ⟨[],[]⟩=⟨[],startingSupply K⟩ := by
  rw [supplyPieces_flatten,run_burgers]
  simp
lemma supplyPieces_mem {K : ℕ} {w : List Letter} (h : w∈supplyPieces K) :
    w=[Letter.burger false] ∨ w=[Letter.burger true] := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (List.mem_replicate.mp h).2
  · exact Or.inr (List.mem_replicate.mp h).2

lemma leftCut_of_buffer_prefix {x : ℕ → List Letter} {K : ℕ}
    (hc : x∈pieceCylinder (supplyPieces K))
    (hf : ∀ n,FixedWord (piecesTail (supplyPieces K).length x n))
    (hb : PieceBuffer K (piecesTail (supplyPieces K).length x)) : LeftCut x := by
  have he : reduce (piecesPrefix x (supplyPieces K).length)=⟨[],startingSupply K⟩ := by
    rw [piecesPrefix_of_cylinder hc]
    exact run_supplyPieces K
  intro n
  by_cases hn : (supplyPieces K).length ≤ n
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [piecesPrefix_add,reduce,run_append]
    change (run (piecesPrefix (piecesTail (supplyPieces K).length x) r)
      (reduce (piecesPrefix x (supplyPieces K).length))).orders=[]
    rw [he]
    exact (run_pieces_buffer hf hb (fun b => (startingSupply_count K b).ge) r).1
  · have hle : n ≤ (supplyPieces K).length := by omega
    obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hle
    have hh := orders_run_sublist (piecesPrefix (piecesTail n x) r) (reduce (piecesPrefix x n))
    have he' := he
    rw [hr,piecesPrefix_add,reduce,run_append] at he'
    change run (piecesPrefix (piecesTail n x) r) (reduce (piecesPrefix x n))=⟨[],startingSupply K⟩ at he'
    rw [he'] at hh
    exact List.sublist_nil.mp hh

lemma iid_all_fixed (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hf : ∀ᵐ w ∂ν,FixedWord w) : ∀ᵐ x ∂naturalPiecesLaw ν,∀ n,FixedWord (x n) := by
  apply ae_all_iff.mpr
  intro n
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ν) n).quasiMeasurePreserving.ae hf

/-- Positive L-cut probability using only shortened-piece integrability,
positive type-drift and the two genuine one-burger atoms. -/
theorem positive_leftCut_general (ν : Measure (List Letter)) [IsProbabilityMeasure ν]
    (hlen : Integrable (fun w : List Letter => (w.length:ℝ)) ν)
    (hnet : ∀ b,Integrable (fun w => (typeNet b w:ℝ)) ν)
    (hmean : ∀ b,(∫ w,(typeNet b w:ℝ) ∂ν)=1/2)
    (hf : ∀ᵐ w ∂ν,FixedWord w)
    (hburger : ∀ b,0<ν {[Letter.burger b]}) :
    0<naturalPiecesLaw ν {x | LeftCut x} := by
  obtain ⟨K,hK⟩ := positive_piece_buffer_probability ν hlen hnet hmean
  let B : Set (ℕ → List Letter) := {x | PieceBuffer K x ∧ ∀ n,FixedWord (x n)}
  have hFm : MeasurableSet {x : ℕ → List Letter | ∀ n,FixedWord (x n)} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun n => (show Measurable (fun x : ℕ → List Letter => x n) from measurable_pi_apply n)
      ((Set.to_countable {w : List Letter | FixedWord w}).measurableSet))
  have hBm : MeasurableSet B := (measurableSet_pieceBuffer K).inter hFm
  have hBp : 0<naturalPiecesLaw ν B := by
    have he : B =ᵐ[naturalPiecesLaw ν] {x | PieceBuffer K x} := by
      filter_upwards [iid_all_fixed ν hf] with x hx
      exact propext (and_iff_left hx)
    rwa [measure_congr he]
  have hC : 0<naturalPiecesLaw ν (pieceCylinder (supplyPieces K)) := by
    apply pieceCylinder_positive ν
    intro w hw
    rcases supplyPieces_mem hw with rfl | rfl
    · exact hburger false
    · exact hburger true
  have hpos : 0<naturalPiecesLaw ν (pieceCylinder (supplyPieces K) ∩ piecesTail (supplyPieces K).length ⁻¹' B) := by
    rw [pieceCylinder_tail_rectangle ν _ hBm]
    exact ENNReal.mul_pos hC.ne' hBp.ne'
  apply hpos.trans_le
  apply measure_mono
  rintro x ⟨hc,hb⟩
  exact leftCut_of_buffer_prefix hc hb.2 hb.1

/-- Source ladder:cuts, L side, for the actual shortened first +1 pieces. -/
theorem shortLeft_positive_cut (P : Parameters) :
    0<naturalPiecesLaw (shortLeftLaw P) {x | LeftCut x} :=
  positive_leftCut_general (shortLeftLaw P) (shortLeftLaw_length_integrable P)
    (shortLeftLaw_typeNet_integrable P) (shortLeftLaw_typeNet_mean P) (shortLeftLaw_fixed P)
    (shortLeftLaw_burger_positive P)

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_StationaryCuts
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {α : Type*} [MeasurableSpace α]

lemma measurable_shift (a : ℤ) : Measurable (shift (α := α) a) :=
  Measurable.of_eval (fun index => measurable_pi_apply (index+a))

lemma shift_preserving (ν : Measure α) [IsProbabilityMeasure ν] (a : ℤ) :
    MeasurePreserving (shift a) (seqLaw ν) (seqLaw ν) := by
  refine ⟨measurable_shift a,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => add_right_cancel h)

lemma finite_window_progression_limit (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f)
    (hint : Integrable f (seqLaw ν)) (a : ℤ) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun q : ℕ =>
      (∑ i∈Finset.range q,f (shift (a+(2*(r:ℤ)+1)*i) x))/(q:ℝ)) atTop (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  have hfm : Measurable f := hf.mono (coords_le _) le_rfl
  let X : ℕ → (ℤ → α) → ℝ := fun i x => f (shift (a+(2*(r:ℤ)+1)*i) x)
  have hident (i : ℕ) : IdentDistrib (X i) f (seqLaw ν) (seqLaw ν) :=
    by
    refine ⟨(hfm.comp (measurable_shift _)).aemeasurable,hfm.aemeasurable,?_⟩
    change Measure.map (f ∘ shift _) (seqLaw ν)=_
    rw [← Measure.map_map hfm (measurable_shift _),(shift_preserving ν _).map_eq]
  have hi : Integrable (X 0) (seqLaw ν) := (hident 0).integrable_iff.mpr hint
  have h := strong_law_ae_real X hi (finite_window_progression_indep ν hf a)
    (fun i => (hident i).trans (hident 0).symm)
  have he := (hident 0).integral_eq
  simpa only [he] using h

lemma finite_window_nonneg_limit (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f)
    (hint : Integrable f (seqLaw ν)) (hn : ∀ x,0 ≤ f x) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift 1) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  have h := ae_all_iff.mpr (fun a : ℕ => finite_window_progression_limit ν hf hint (a:ℤ))
  filter_upwards [h] with x hx
  have hh := interlaced_nonneg_limit (f := fun i => f (shift (i:ℤ) x))
    (fun i => hn _) (2*r+1) (by omega) (∫ x,f x ∂seqLaw ν) (fun a _ => ?_)
  · simpa only [average,shift_iterate] using hh
  · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] using hx a

lemma finite_window_limit (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} {r : ℕ} (hf : Measurable[coords (window r)] f)
    (hint : Integrable f (seqLaw ν)) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift 1) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  let fp : (ℤ → α) → ℝ := fun x => max (f x) 0
  let fm : (ℤ → α) → ℝ := fun x => max (-f x) 0
  have hp : Integrable fp (seqLaw ν) := hint.sup (integrable_const 0)
  have hm : Integrable fm (seqLaw ν) := hint.neg.sup (integrable_const 0)
  have heq : (fun x => fp x-fm x)=f := by
    funext x
    dsimp [fp,fm]
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx,max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)]; ring
  have hmean : (∫ x,fp x ∂seqLaw ν)-(∫ x,fm x ∂seqLaw ν)=∫ x,f x ∂seqLaw ν := by
    rw [← integral_sub hp hm,heq]
  filter_upwards [finite_window_nonneg_limit ν (hf.max measurable_const) hp (fun _ => le_max_right _ _),
    finite_window_nonneg_limit ν (hf.neg.max measurable_const) hm (fun _ => le_max_right _ _)] with x hxp hxm
  change Tendsto (fun n => average (shift 1) fp n x) atTop (𝓝 (∫ x,fp x ∂seqLaw ν)) at hxp
  change Tendsto (fun n => average (shift 1) fm n x) atTop (𝓝 (∫ x,fm x ∂seqLaw ν)) at hxm
  have hh := hxp.sub hxm
  simpa only [← average_sub,heq,hmean] using hh

end FKCRT.Stationary
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Stationary
variable {α : Type*} [MeasurableSpace α]

/-- Stationary averages of any integrable observation of a two-sided iid
sequence, not just cylinder observations. -/
theorem iid_shift_strong_law (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} (hf : Measurable f) (hint : Integrable f (seqLaw ν)) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift 1) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  let μ := seqLaw ν
  let g : ℕ → (ℤ → α) → ℝ := fun r => μ[f | windowFiltration r]
  have hg (r : ℕ) : Integrable (g r) μ := integrable_condExp
  have hmg (r : ℕ) : Measurable[coords (window r)] (g r) := stronglyMeasurable_condExp.measurable
  have ht : Tendsto (fun r => eLpNorm (g r-f) 1 μ) atTop (𝓝 0) := by
    apply hint.tendsto_eLpNorm_condExp (ℱ := windowFiltration)
    rw [windowFiltration_sup]
    exact hf.stronglyMeasurable
  have he (r : ℕ) : (∫ x,|f x-g r x| ∂μ)=(eLpNorm (g r-f) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_sub_comm] using
      integral_norm_eq_lintegral_enorm ((hg r).sub hint).aestronglyMeasurable
  have happ : Tendsto (fun r => ∫ x,|f x-g r x| ∂μ) atTop (𝓝 0) := by
    simpa only [he,ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞)≠⊤)).comp ht
  apply ae_average_limit_of_L1_approx (μ := μ) (g := g)
    (a := fun _ => ∫ x,f x ∂μ) (shift_preserving ν 1) hint hf hg
    (fun r => (hmg r).mono (coords_le _) le_rfl) happ tendsto_const_nhds
  intro r
  have hh := finite_window_limit ν (hmg r) (hg r)
  have hi : (∫ x,g r x ∂μ)=∫ x,f x ∂μ := integral_condExp (windowFiltration.le r)
  change ∀ᵐ x ∂μ,Tendsto (fun n => average (shift 1) (g r) n x) atTop (𝓝 (∫ x,g r x ∂μ)) at hh
  simpa only [hi] using hh

lemma measurable_reflect : Measurable (reflect (α := α)) :=
  Measurable.of_eval (fun index => measurable_pi_apply (-index))
lemma reflect_preserving (ν : Measure α) [IsProbabilityMeasure ν] :
    MeasurePreserving reflect (seqLaw ν) (seqLaw ν) :=
  ⟨measurable_reflect,Measure.map_infinitePi_infinitePi_of_inj neg_injective⟩

theorem iid_reverse_shift_strong_law (ν : Measure α) [IsProbabilityMeasure ν]
    {f : (ℤ → α) → ℝ} (hf : Measurable f) (hint : Integrable f (seqLaw ν)) :
    ∀ᵐ x ∂seqLaw ν,Tendsto (fun n => average (shift (-1)) f n x) atTop
      (𝓝 (∫ x,f x ∂seqLaw ν)) := by
  have hid : IdentDistrib (f ∘ reflect) f (seqLaw ν) (seqLaw ν) := by
    refine ⟨(hf.comp measurable_reflect).aemeasurable,hf.aemeasurable,?_⟩
    rw [← Measure.map_map hf measurable_reflect,(reflect_preserving ν).map_eq]
  have h := iid_shift_strong_law ν (hf.comp measurable_reflect) (hid.integrable_iff.mpr hint)
  have hh := (reflect_preserving ν).quasiMeasurePreserving.ae h
  filter_upwards [hh] with x hx
  have hi : (∫ x,f (reflect x) ∂seqLaw ν)=∫ x,f x ∂seqLaw ν := hid.integral_eq
  simpa only [average,Function.comp_apply,reflected_shift_iterate,hi] using hx

end FKCRT.Stationary
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PieceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

instance instMeasurableSpaceOrder : MeasurableSpace Order := ⊤
instance instMeasurableSpaceListOrder : MeasurableSpace (List Order) := ⊤
instance instMeasurableSingletonClassListOrder : MeasurableSingletonClass (List Order) := ⟨fun _ => trivial⟩

/-- Chronological concatenation between whole-piece boundaries. -/
def intervalWord (x : ℤ → List Letter) (a : ℤ) (n : ℕ) : List Letter :=
  piecesPrefix (fun j => x (a+j)) n
lemma intervalWord_zero (x : ℤ → List Letter) (a : ℤ) : intervalWord x a 0=[] := rfl
lemma intervalWord_succ (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    intervalWord x a (n+1)=intervalWord x a n++x (a+n) := rfl
lemma intervalWord_add (x : ℤ → List Letter) (a : ℤ) (m n : ℕ) :
    intervalWord x a (m+n)=intervalWord x a m++intervalWord x (a+m) n := by
  rw [intervalWord,piecesPrefix_add]
  congr 2
  funext j
  dsimp only [piecesTail]
  congr 1
  push_cast
  ring
lemma intervalWord_measurable (a : ℤ) (n : ℕ) : Measurable (fun x : ℤ → List Letter => intervalWord x a n) :=
  (piecesPrefix_measurable n).comp (Measurable.of_eval (fun j => measurable_pi_apply (a+j)))
lemma intervalWord_shift (x : ℤ → List Letter) (a b : ℤ) (n : ℕ) :
    intervalWord (Stationary.shift b x) a n=intervalWord x (a+b) n := by
  unfold intervalWord
  congr 1
  funext j
  simp only [Stationary.shift]
  congr 1
  omega
lemma intervalWord_net (x : ℤ → List Letter) (a : ℤ) (n : ℕ) (d : ℤ)
    (hd : ∀ j,((x j).map Letter.increment).sum=d) :
    ((intervalWord x a n).map Letter.increment).sum=(n:ℤ)*d := by
  induction n with
  | zero => simp [intervalWord_zero]
  | succ n ih => rw [intervalWord_succ,List.map_append,List.sum_append,ih,hd]; push_cast; ring

lemma reduce_append_no_burgers (u v : List Letter) (hu : (reduce u).burgers=[]) :
    reduce (u++v)=⟨(reduce u).orders++(reduce v).orders,(reduce v).burgers⟩ := by
  unfold reduce
  rw [run_append]
  have he : run u ⟨[],[]⟩=⟨(reduce u).orders,[]⟩ := by cases h : reduce u; simp_all [reduce]
  rw [he]
  simpa only [List.append_nil] using run_orders_prefix v (reduce u).orders (⟨[],[]⟩ : Evaluation)
lemma reduce_append_no_orders (u v : List Letter) (hv : (reduce v).orders=[]) :
    reduce (u++v)=⟨(reduce u).orders,(reduce v).burgers++(reduce u).burgers⟩ := by
  have h := run_orders_prefix v (reduce u).orders (⟨[],(reduce u).burgers⟩ : Evaluation)
  simp only [List.append_nil] at h
  rw [reduce,run_append]
  rw [show run u ⟨[],[]⟩=⟨(reduce u).orders,(reduce u).burgers⟩ by rfl,h,run_older_supply,hv,evalOrders_nil]
  simp only [List.append_nil]

def leftCutAt (x : ℤ → List Letter) (a : ℤ) : Prop := ∀ n,(reduce (intervalWord x a n)).orders=[]
def rightCutAt (x : ℤ → List Letter) (b : ℤ) : Prop := ∀ n : ℕ,(reduce (intervalWord x (b-n) n)).burgers=[]
lemma leftCutAt_measurable (a : ℤ) : MeasurableSet {x | leftCutAt x a} := by
  simp only [leftCutAt,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (intervalWord_measurable a n) ((Set.to_countable {w : List Letter | (reduce w).orders=[]}).measurableSet))
lemma rightCutAt_measurable (b : ℤ) : MeasurableSet {x | rightCutAt x b} := by
  simp only [rightCutAt,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => (intervalWord_measurable (b-n) n) ((Set.to_countable {w : List Letter | (reduce w).burgers=[]}).measurableSet))
lemma leftCutAt_shift (x : ℤ → List Letter) (a b : ℤ) :
    leftCutAt (Stationary.shift b x) a ↔ leftCutAt x (a+b) := by
  simp only [leftCutAt,intervalWord_shift]
lemma rightCutAt_shift (x : ℤ → List Letter) (a b : ℤ) :
    rightCutAt (Stationary.shift b x) a ↔ rightCutAt x (a+b) := by
  simp only [rightCutAt,intervalWord_shift]
  have he (n : ℕ) : a-(n:ℤ)+b=a+b-n := by omega
  simp only [he]
lemma no_burgers_interval {x : ℤ → List Letter} {a : ℤ} {n : ℕ} (h : rightCutAt x (a+n)) :
    (reduce (intervalWord x a n)).burgers=[] := by simpa using h n

def rightOrders (x : ℤ → List Letter) (a : ℤ) (n : ℕ) : List Order := (reduce (intervalWord x a n)).orders
lemma rightOrders_length {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (a : ℤ) (n : ℕ) (hb : rightCutAt x (a+n)) : (rightOrders x a n).length=n := by
  have he := reduce_imbalance (intervalWord x a n)
  rw [imbalance,no_burgers_interval hb,intervalWord_net x a n (-1) hd] at he
  simp only [List.length_nil,Nat.cast_zero,zero_sub,mul_neg_one] at he
  dsimp [rightOrders]
  omega
lemma rightOrders_append {x : ℤ → List Letter} (a : ℤ) (m n : ℕ)
    (hm : rightCutAt x (a+m)) : rightOrders x a (m+n)=rightOrders x a m++rightOrders x (a+m) n := by
  simp only [rightOrders,intervalWord_add,reduce_append_no_burgers _ _ (no_burgers_interval hm)]
def rightOutput (x : ℤ → List Letter) (i : ℤ) : Order := CutOutput.output (rightCutAt x) (rightOrders x) none i
lemma rightOutput_measurable (i : ℤ) : Measurable (fun x => rightOutput x i) := by
  apply CutOutput.output_measurable _ _ none i rightCutAt_measurable
  intro a n
  exact (measurable_of_countable (fun w : List Letter => (reduce w).orders)).comp (intervalWord_measurable a n)
lemma rightOutput_shift (x : ℤ → List Letter) (a i : ℤ) :
    rightOutput (Stationary.shift a x) i=rightOutput x (i+a) := by
  have hc : rightCutAt (Stationary.shift a x)=fun j => rightCutAt x (j+a) := by
    funext j; exact propext (rightCutAt_shift x j a)
  have hw : rightOrders (Stationary.shift a x)=fun j n => rightOrders x (j+a) n := by
    funext j n; simp only [rightOrders,intervalWord_shift]
  exact (show CutOutput.output (rightCutAt (Stationary.shift a x)) (rightOrders (Stationary.shift a x)) none i=_ by
    rw [hc,hw,CutOutput.output_translate]; rfl)
def rightOutputData (x : ℤ → List Letter) (hd : ∀ j,((x j).map Letter.increment).sum= -1) : CutOutput.Data Order where
  cut := rightCutAt x
  word := rightOrders x
  length a n _ hb := rightOrders_length hd a n hb
  append a m n _ hm _ := rightOrders_append a m n hm
lemma rightOutput_segment {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (a : ℤ) (n : ℕ) (ha : rightCutAt x a) (hb : rightCutAt x (a+n)) :
    List.ofFn (fun j : Fin n => rightOutput x (a+j))=rightOrders x a n :=
  (rightOutputData x hd).output_segment none a n ha hb

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def rightWord (x : ℕ → Letter) : List Letter := (reverseRightWord x).reverse
def rightLaw (P : Parameters) : Measure (List Letter) := (reverseRightLaw P).map List.reverse
lemma rightWord_measurable : Measurable rightWord := (measurable_of_countable List.reverse).comp reverseRightWord_measurable
lemma rightLaw_eq (P : Parameters) : rightLaw P=(streamLaw P ℕ).map rightWord := by
  rw [rightLaw,reverseRightLaw,Measure.map_map (measurable_of_countable List.reverse) reverseRightWord_measurable]
  rfl
instance rightLaw_probability (P : Parameters) : IsProbabilityMeasure (rightLaw P) :=
  Measure.isProbabilityMeasure_map ((measurable_of_countable List.reverse).aemeasurable)
lemma rightLaw_reverse (P : Parameters) : (rightLaw P).map List.reverse=reverseRightLaw P := by
  rw [rightLaw,Measure.map_map (measurable_of_countable List.reverse) (measurable_of_countable List.reverse)]
  simp only [Function.comp_def,List.reverse_reverse]
  exact Measure.map_id
lemma rightLaw_net (P : Parameters) : ∀ᵐ w ∂rightLaw P,(w.map Letter.increment).sum= -1 := by
  rw [rightLaw_eq,ae_map_iff rightWord_measurable.aemeasurable ((Set.to_countable _).measurableSet)]
  simpa only [rightWord,List.map_reverse,List.sum_reverse] using reverseRightWord_net P
lemma rightSeq_net (P : Parameters) : ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),∀ j,((x j).map Letter.increment).sum= -1 := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℤ => rightLaw P) j).quasiMeasurePreserving.ae (rightLaw_net P)

def reversedPast (x : ℤ → List Letter) : ℕ → List Letter := fun j => (x (-1-j)).reverse
lemma reversedPast_preserving (P : Parameters) :
    MeasurePreserving reversedPast (Stationary.seqLaw (rightLaw P)) (naturalPiecesLaw (reverseRightLaw P)) := by
  let f : (ℤ → List Letter) → (ℕ → List Letter) := fun x j => x (-1-j)
  have hf : MeasurePreserving f (Stationary.seqLaw (rightLaw P)) (naturalPiecesLaw (rightLaw P)) := by
    refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (-1-(j:ℤ))),?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => by omega)
  have hg : MeasurePreserving (fun x : ℕ → List Letter => fun j => (x j).reverse)
      (naturalPiecesLaw (rightLaw P)) (naturalPiecesLaw (reverseRightLaw P)) := by
    refine ⟨Measurable.of_eval (fun j => (measurable_of_countable List.reverse).comp (measurable_pi_apply j)),?_⟩
    change (Measure.infinitePi _).map _=Measure.infinitePi _
    rw [Measure.infinitePi_map_pi (fun _ : ℕ => rightLaw P) (fun _ => measurable_of_countable List.reverse)]
    simp only [rightLaw_reverse]
  exact hg.comp hf
lemma intervalWord_first (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    intervalWord x a (n+1)=x a++intervalWord x (a+1) n := by
  rw [show n+1=1+n by omega,intervalWord_add]
  simp only [intervalWord_succ,intervalWord_zero,List.nil_append,Nat.cast_zero,add_zero,Nat.cast_one]
lemma reversedPast_prefix (x : ℤ → List Letter) (n : ℕ) :
    (piecesPrefix (reversedPast x) n).reverse=intervalWord x (-(n:ℤ)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [piecesPrefix,List.reverse_append,ih,intervalWord_first]
    simp only [reversedPast,List.reverse_reverse,Nat.cast_add,Nat.cast_one]
    rw [show -((n:ℤ)+1)= -1-n by omega,
      show -1-(n:ℤ)+1= -n by omega]
lemma rightCutAt_zero_iff (x : ℤ → List Letter) : rightCutAt x 0 ↔ RightCut (reversedPast x) := by
  simp only [rightCutAt,RightCut,reversedPast_prefix,zero_sub]
lemma rightCutAt_positive (P : Parameters) : 0<Stationary.seqLaw (rightLaw P) {x | rightCutAt x 0} := by
  have he := (reversedPast_preserving P).measure_preimage measurableSet_rightCut.nullMeasurableSet
  have hs : {x | rightCutAt x 0}=reversedPast ⁻¹' {x | RightCut x} := by ext x; exact rightCutAt_zero_iff x
  rw [hs,he]
  exact positive_rightCut P

lemma rightWord_of_order {x : ℕ → Letter} {o : Order} (hx : x 0=Letter.order o) :
    rightWord x=[Letter.order o] := by
  have hh : firstDown 1 x=WithTop.some 0 := by
    rw [firstDown_of_hit_iff]
    constructor
    · simp [signSum,hx,Letter.increment]
    · intro j hj; omega
  simp [rightWord,reverseRightWord,stoppedWord_of_hit hh,revealed,hx]
lemma rightLaw_order_positive (P : Parameters) (o : Order) : 0 < rightLaw P {[Letter.order o]} := by
  rw [rightLaw_eq,Measure.map_apply rightWord_measurable (measurableSet_singleton _)]
  have hle : streamLaw P ℕ {x | x 0=Letter.order o} ≤ streamLaw P ℕ (rightWord ⁻¹' {[Letter.order o]}) :=
    measure_mono (fun x hx => rightWord_of_order hx)
  have he : streamLaw P ℕ {x | x 0=Letter.order o}=(law P).toMeasure {Letter.order o} :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (law P).toMeasure) 0).measure_preimage
      (measurableSet_singleton (Letter.order o)).nullMeasurableSet
  rw [he,law_singleton] at hle
  exact (ENNReal.ofReal_pos.mpr (mass_pos P _)).trans_le hle

lemma increment_flip (a : Letter) : a.flip.increment=a.increment := by cases a <;> rfl
lemma signSum_flip (x : ℕ → Letter) (n : ℕ) : signSum (flipStream x) n=signSum x n := by
  simp only [signSum,flipStream,increment_flip]
lemma firstDown_flip (h : ℕ) (x : ℕ → Letter) : firstDown h (flipStream x)=firstDown h x := by
  apply eq_of_forall_ge_iff
  intro n
  cases n with
  | top => simp
  | coe n => simp only [firstDown,TreeCoding.firstZero_le_iff,downPath,signSum_flip]
lemma rightWord_flip (x : ℕ → Letter) : rightWord (flipStream x)=(rightWord x).map Letter.flip := by
  simp only [rightWord,reverseRightWord,stoppedWord,firstDown_flip,revealed_flip,List.map_reverse]
lemma rightLaw_flip_preserving (P : Parameters) :
    MeasurePreserving (List.map Letter.flip) (rightLaw P) (rightLaw P) := by
  refine ⟨measurable_of_countable _,?_⟩
  rw [rightLaw_eq,Measure.map_map (measurable_of_countable _) rightWord_measurable]
  have he : List.map Letter.flip ∘ rightWord=rightWord ∘ flipStream := by funext x; exact (rightWord_flip x).symm
  rw [he,← Measure.map_map rightWord_measurable measurable_flipStream,(flipStream_preserving P).map_eq]

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def flipPieceSeq (x : ℤ → List Letter) : ℤ → List Letter := fun j => (x j).map Letter.flip
lemma flipPieceSeq_measurable : Measurable flipPieceSeq :=
  Measurable.of_eval (fun j => (measurable_of_countable _).comp (measurable_pi_apply j))
lemma flipPieceSeq_preserving (P : Parameters) :
    MeasurePreserving flipPieceSeq (Stationary.seqLaw (rightLaw P)) (Stationary.seqLaw (rightLaw P)) := by
  refine ⟨flipPieceSeq_measurable,?_⟩
  change (Measure.infinitePi _).map (fun x : ℤ → List Letter => fun j => (x j).map Letter.flip)=Measure.infinitePi _
  rw [Measure.infinitePi_map_pi (fun _ : ℤ => rightLaw P) (fun _ => measurable_of_countable (List.map Letter.flip))]
  simp only [(rightLaw_flip_preserving P).map_eq]
lemma intervalWord_flip (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    intervalWord (flipPieceSeq x) a n=(intervalWord x a n).map Letter.flip := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intervalWord_succ,ih,flipPieceSeq,List.map_append]
lemma rightCutAt_flip (x : ℤ → List Letter) (a : ℤ) : rightCutAt (flipPieceSeq x) a ↔ rightCutAt x a := by
  simp only [rightCutAt,intervalWord_flip,burgers_flip_empty_iff]
lemma rightOrders_flip (x : ℤ → List Letter) (a : ℤ) (n : ℕ) :
    rightOrders (flipPieceSeq x) a n=(rightOrders x a n).map (Option.map Bool.not) := by
  simp only [rightOrders,intervalWord_flip,reduce_flip,Evaluation.flip]
lemma rightOutput_flip (x : ℤ → List Letter) (i : ℤ) :
    rightOutput (flipPieceSeq x) i=(rightOutput x i).map Bool.not := by
  have hc : rightCutAt (flipPieceSeq x)=rightCutAt x := by funext j; exact propext (rightCutAt_flip x j)
  unfold rightOutput CutOutput.output
  rw [hc,rightOrders_flip,List.getElem?_map]
  exact Option.getD_map (Option.map Bool.not) none _

lemma rightCutAt_zero_past_measurable :
    MeasurableSet[Stationary.coords (α := List Letter) {j | j<0}] {x | rightCutAt x 0} := by
  have hm : Measurable[Stationary.coords (α := List Letter) {j | j<0}] reversedPast := by
    let : MeasurableSpace (ℤ → List Letter) := Stationary.coords {j | j<0}
    apply Measurable.of_eval
    intro j
    apply (measurable_of_countable List.reverse).comp
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (-1-(j:ℤ)) (le_iSup_of_le (show -1-(j:ℤ)<0 by omega) le_rfl)
  have hs : {x | rightCutAt x 0}=reversedPast ⁻¹' {x | RightCut x} := by ext x; exact rightCutAt_zero_iff x
  rw [hs]
  exact hm measurableSet_rightCut
lemma rightCutAt_one_of_order {x : ℤ → List Letter} (hc : rightCutAt x 0) {o : Order}
    (hx : x 0=[Letter.order o]) : rightCutAt x 1 := by
  intro n
  cases n with
  | zero => simp [intervalWord_zero,reduce,run]
  | succ n =>
    rw [intervalWord_succ]
    have ha : (1:ℤ)-(n+1)= -(n:ℤ) := by omega
    have hb : (1:ℤ)-(n+1)+n=0 := by omega
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hb,hx,ha]
    have hh : (reduce (intervalWord x (-(n:ℤ)) n)).burgers=[] := by simpa using hc n
    exact append_order_no_burgers hh o
lemma rightOutput_of_cut_order {x : ℤ → List Letter} (hc : rightCutAt x 0) {o : Order}
    (hx : x 0=[Letter.order o]) : rightOutput x 0=o := by
  have hd := rightCutAt_one_of_order hc hx
  have hl : CutOutput.left (rightCutAt x) 0=0 := by
    apply Nat.eq_zero_of_le_zero
    exact CutOutput.firstIndex_le (p := fun k => rightCutAt x (0-k)) (k := 0) (by simpa using hc)
  have hr : CutOutput.right (rightCutAt x) 0=0 := by
    apply Nat.eq_zero_of_le_zero
    exact CutOutput.firstIndex_le (p := fun k => rightCutAt x (0+1+k)) (k := 0) (by simpa using hd)
  simp [rightOutput,CutOutput.output,hl,hr,rightOrders,intervalWord_succ,intervalWord_zero,hx,reduce,run,step,pop]
lemma rightOutput_flexible_positive (P : Parameters) :
    0<Stationary.seqLaw (rightLaw P) {x | rightOutput x 0=none} := by
  let A : Set (ℤ → List Letter) := {x | rightCutAt x 0}
  let B : Set (ℤ → List Letter) := {x | x 0=[Letter.order none]}
  have hB : MeasurableSet[Stationary.coords (α := List Letter) {j | 0 ≤ j}] B := by
    have hm : Measurable[Stationary.coords (α := List Letter) {j | 0 ≤ j}] (fun x : ℤ → List Letter => x 0) := by
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le 0 (le_iSup_of_le (show (0:ℤ) ≤ 0 by omega) le_rfl)
    exact hm (measurableSet_singleton _)
  have hi := Stationary.indep_coords (rightLaw P) (S := {j | j<0}) (R := {j | 0 ≤ j})
    (Set.disjoint_left.mpr (fun j hj hj' => by change j<0 at hj; change 0 ≤ j at hj'; omega))
  have he := (indep_iff_forall_indepSet _).mp hi A B rightCutAt_zero_past_measurable hB |>.measure_inter_eq_mul
  have hBp : 0<Stationary.seqLaw (rightLaw P) B := by
    have hh := (measurePreserving_eval_infinitePi (fun _ : ℤ => rightLaw P) 0).measure_preimage
      (measurableSet_singleton [Letter.order none]).nullMeasurableSet
    change Stationary.seqLaw (rightLaw P) B=rightLaw P {[Letter.order none]} at hh
    rw [hh]
    exact rightLaw_order_positive P none
  have hpos : 0<Stationary.seqLaw (rightLaw P) (A∩B) := by rw [he]; exact ENNReal.mul_pos_iff.mpr ⟨rightCutAt_positive P,hBp⟩
  exact hpos.trans_le (measure_mono (fun x hx => rightOutput_of_cut_order hx.1 hx.2))

def outputIndicator (o : Order) (x : ℤ → List Letter) : ℝ := if rightOutput x 0=o then 1 else 0
lemma outputIndicator_measurable (o : Order) : Measurable (outputIndicator o) := by
  apply Measurable.ite (measurableSet_eq_fun (rightOutput_measurable 0) measurable_const) measurable_const measurable_const
lemma outputIndicator_integrable (P : Parameters) (o : Order) : Integrable (outputIndicator o) (Stationary.seqLaw (rightLaw P)) := by
  apply (integrable_const (1:ℝ)).mono' (outputIndicator_measurable o).aestronglyMeasurable
  filter_upwards [] with x
  simp only [outputIndicator]
  split_ifs <;> norm_num

def outputMass (P : Parameters) (o : Order) : ℝ := ∫ x,outputIndicator o x ∂Stationary.seqLaw (rightLaw P)
lemma outputMass_eq_measure (P : Parameters) (o : Order) :
    outputMass P o=(Stationary.seqLaw (rightLaw P) {x | rightOutput x 0=o}).toReal := by
  simpa only [outputMass,outputIndicator,Set.indicator,Pi.one_apply,Measure.real,Set.mem_ofPred_eq] using
    integral_indicator_one (μ := Stationary.seqLaw (rightLaw P)) (s := {x | rightOutput x 0=o})
      (measurableSet_eq_fun (rightOutput_measurable 0) measurable_const)
lemma outputMass_flexible_pos (P : Parameters) : 0<outputMass P none := by
  rw [outputMass_eq_measure]
  exact ENNReal.toReal_pos (ne_of_gt (rightOutput_flexible_positive P)) (measure_ne_top _ _)
lemma outputMass_fixed_eq (P : Parameters) : outputMass P (some false)=outputMass P (some true) := by
  have hh := (flipPieceSeq_preserving P).hasLaw.integral_comp (outputIndicator_measurable (some false)).aestronglyMeasurable
  have hf (x : ℤ → List Letter) : outputIndicator (some false) (flipPieceSeq x)=outputIndicator (some true) x := by
    simp only [outputIndicator,rightOutput_flip]
    cases h : rightOutput x 0 with
    | none => simp
    | some b => cases b <;> simp
  simpa only [Function.comp_apply,hf,outputMass] using hh.symm
lemma outputMass_sum (P : Parameters) : outputMass P none+outputMass P (some false)+outputMass P (some true)=1 := by
  have hp (x : ℤ → List Letter) : outputIndicator none x+outputIndicator (some false) x+outputIndicator (some true) x=1 := by
    simp only [outputIndicator]
    cases h : rightOutput x 0 with
    | none =>
      have h₀ : (none : Order) ≠ some false := by intro h; cases h
      have h₁ : (none : Order) ≠ some true := by intro h; cases h
      simp only [h₀,h₁,ite_true,ite_false,add_zero]
    | some b => cases b <;> simp only [Option.some_ne_none,Option.some.injEq,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,zero_add,add_zero]
  have hi := integral_congr_ae (μ := Stationary.seqLaw (rightLaw P)) (Filter.Eventually.of_forall hp)
  have ha := integral_add ((outputIndicator_integrable P none).add (outputIndicator_integrable P (some false)))
    (outputIndicator_integrable P (some true))
  simp only [Pi.add_apply] at ha
  rw [ha,integral_add (outputIndicator_integrable P none) (outputIndicator_integrable P (some false))] at hi
  simpa [outputMass] using hi
lemma outputMass_fixed (P : Parameters) (b : Bool) : outputMass P (some b)=(1-outputMass P none)/2 := by
  have h₁ := outputMass_fixed_eq P
  have h₂ := outputMass_sum P
  cases b <;> linarith

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT
namespace Inventory
open Classical
lemma rightOutput_reverse_frequencies (P : Parameters) (o : Order) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),
      Tendsto (fun n => (∑ j∈Finset.range n,if rightOutput x (-1-j)=o then (1:ℝ) else 0)/(n:ℝ)) atTop (𝓝 (outputMass P o)) := by
  have hh := Stationary.iid_reverse_shift_strong_law (rightLaw P) (outputIndicator_measurable o) (outputIndicator_integrable P o)
  have ht := (Stationary.shift_preserving (rightLaw P) (-1)).quasiMeasurePreserving.ae hh
  filter_upwards [ht] with x hx
  have he (j : ℕ) : rightOutput (Stationary.shift (-(j:ℤ)) (Stationary.shift (-1) x)) 0=rightOutput x (-1-j) := by
    rw [rightOutput_shift,rightOutput_shift]
    congr 1
    omega
  simpa only [Stationary.average,Stationary.shift_neg_iterate,outputIndicator,he,outputMass] using hx

def rightCutDensity (P : Parameters) : ℝ := (Stationary.seqLaw (rightLaw P) {x | rightCutAt x 0}).toReal
lemma rightCutDensity_pos (P : Parameters) : 0 < rightCutDensity P :=
  ENNReal.toReal_pos (ne_of_gt (rightCutAt_positive P)) (measure_ne_top _ _)
lemma rightCut_reverse_density (P : Parameters) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),
      Tendsto (fun n => (CutOutput.count (fun k => rightCutAt x (-(k:ℤ))) n:ℝ)/(n:ℝ)) atTop (𝓝 (rightCutDensity P)) := by
  let f : (ℤ → List Letter) → ℝ := fun x => if rightCutAt x 0 then 1 else 0
  have hf : Measurable f := Measurable.ite (rightCutAt_measurable 0) measurable_const measurable_const
  have hi : Integrable f (Stationary.seqLaw (rightLaw P)) := by
    apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    filter_upwards [] with x
    dsimp [f]
    split_ifs <;> norm_num
  have he : (∫ x,f x ∂Stationary.seqLaw (rightLaw P))=rightCutDensity P := by
    simpa only [f,Set.indicator,Pi.one_apply,Measure.real,Set.mem_ofPred_eq,rightCutDensity] using
      integral_indicator_one (μ := Stationary.seqLaw (rightLaw P)) (s := {x | rightCutAt x 0}) (rightCutAt_measurable 0)
  have hh := Stationary.iid_reverse_shift_strong_law (rightLaw P) hf hi
  filter_upwards [hh] with x hx
  simpa only [CutOutput.countReal,Stationary.average,Stationary.shift_neg_iterate,f,rightCutAt_shift,zero_add,he] using hx
end Inventory
end FKCRT
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def typeBalance (b : Bool) (e : Evaluation) : ℤ := (e.burgers.count b:ℤ)-(e.orders.count (some b):ℤ)
lemma typeBalance_step (b : Bool) (e : Evaluation) {a : Letter} (ha : a≠Letter.order none) :
    typeBalance b (step e a)=typeBalance b e+Letter.typeNet b a := by
  cases a with
  | burger c =>
    by_cases h : c=b
    · subst c; simp only [typeBalance,step,List.count_cons_self,Nat.cast_add,Nat.cast_one,Letter.typeNet,ite_true]; ring
    · simp only [typeBalance,step,List.count_cons_of_ne h,Letter.typeNet,ite_eq_right h,add_zero]
  | order o =>
    cases o with
    | none => exact (ha rfl).elim
    | some c =>
      cases hp : pop (some c) e.burgers with
      | none =>
        by_cases h : c=b
        · subst c
          simp only [typeBalance,step,hp,List.count_append,List.count_singleton,Nat.cast_add,beq_self_eq_true,ite_true,Nat.cast_one,Letter.typeNet,ite_true]
          ring
        · have he : (some c:Order)≠some b := by simpa using h
          simp only [typeBalance,step,hp,List.count_append,List.count_singleton,beq_eq_false_iff_ne.mpr he,Bool.false_eq_true,ite_false,Letter.typeNet,ite_eq_right h,add_zero]
      | some s =>
        have hc := pop_fixed_count (a := b) hp
        by_cases h : b=c
        · subst c
          simp only [ite_true] at hc
          simp only [typeBalance,step,hp,Letter.typeNet,ite_true]
          omega
        · simp only [ite_eq_right h,Nat.add_zero] at hc
          simp only [typeBalance,step,hp,Letter.typeNet,ite_eq_right (Ne.symm h),add_zero,hc]
lemma typeBalance_run (b : Bool) (e : Evaluation) (w : List Letter) (hw : FixedWord w) :
    typeBalance b (run w e)=typeBalance b e+typeNet b w := by
  induction w generalizing e with
  | nil => simp [run,typeNet]
  | cons a w ih =>
    have ha : a≠Letter.order none := by intro h; exact hw (by simp [h])
    have ht : FixedWord w := fun h => hw (List.mem_cons_of_mem a h)
    rw [run,ih _ ht,typeBalance_step b e ha]
    change _=(typeBalance b e)+(Letter.typeNet b a+typeNet b w)
    ring
lemma burger_count_eq_typeNet {w : List Letter} (hw : FixedWord w) (ho : (reduce w).orders=[]) (b : Bool) :
    ((reduce w).burgers.count b:ℤ)=typeNet b w := by
  have hh := typeBalance_run b ⟨[],[]⟩ w hw
  change typeBalance b (reduce w)=typeBalance b ⟨[],[]⟩+typeNet b w at hh
  simpa only [typeBalance,ho,List.count_nil,Nat.cast_zero,sub_zero,sub_self,zero_add] using hh
lemma intervalWord_fixed {x : ℤ → List Letter} (hx : ∀ j,FixedWord (x j)) (a : ℤ) (n : ℕ) : FixedWord (intervalWord x a n) := by
  induction n with
  | zero => simp [intervalWord_zero,FixedWord]
  | succ n ih =>
    rw [intervalWord_succ]
    exact fun h => (List.mem_append.mp h).elim ih (hx _)
lemma typeNet_intervalWord (x : ℤ → List Letter) (b : Bool) (a : ℤ) (n : ℕ) :
    typeNet b (intervalWord x a n)=∑ j∈Finset.range n,typeNet b (x (a+j)) := by
  induction n with
  | zero => simp [intervalWord_zero,typeNet]
  | succ n ih =>
    rw [intervalWord_succ,Finset.sum_range_succ]
    simpa only [typeNet,List.map_append,List.sum_append] using congrArg (·+typeNet b (x (a+n))) ih

lemma shortLeftLaw_net (P : Parameters) : ∀ᵐ w ∂shortLeftLaw P,(w.map Letter.increment).sum=1 := by
  rw [shortLeftLaw,ae_map_iff measurable_shortLeftWord.aemeasurable ((Set.to_countable _).measurableSet)]
  filter_upwards [ae_left_first_hit P] with x hx
  rw [shortLeftWord_sign,hx.1]
lemma leftSeq_net (P : Parameters) : ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),∀ j,((x j).map Letter.increment).sum=1 := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℤ => shortLeftLaw P) j).quasiMeasurePreserving.ae (shortLeftLaw_net P)
lemma leftSeq_fixed (P : Parameters) : ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),∀ j,FixedWord (x j) := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval_infinitePi (fun _ : ℤ => shortLeftLaw P) j).quasiMeasurePreserving.ae (shortLeftLaw_fixed P)

def futurePieces (x : ℤ → List Letter) : ℕ → List Letter := fun j => x j
lemma futurePieces_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] :
    MeasurePreserving futurePieces (Stationary.seqLaw ν) (naturalPiecesLaw ν) := by
  refine ⟨Measurable.of_eval (fun j => measurable_pi_apply (j:ℤ)),?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h => Int.ofNat_inj.mp h)
lemma futurePieces_prefix (x : ℤ → List Letter) (n : ℕ) : piecesPrefix (futurePieces x) n=intervalWord x 0 n := by
  simp only [intervalWord,zero_add]
  rfl
lemma leftCutAt_zero_iff (x : ℤ → List Letter) : leftCutAt x 0 ↔ LeftCut (futurePieces x) := by
  simp only [leftCutAt,LeftCut,futurePieces_prefix]
lemma leftCutAt_positive (P : Parameters) : 0<Stationary.seqLaw (shortLeftLaw P) {x | leftCutAt x 0} := by
  have hh := (futurePieces_preserving (shortLeftLaw P)).measure_preimage measurableSet_leftCut.nullMeasurableSet
  have he : {x | leftCutAt x 0}=futurePieces ⁻¹' {x | LeftCut x} := Set.ext (fun x => leftCutAt_zero_iff x)
  rw [he,hh]
  exact shortLeft_positive_cut P
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_UniformSeams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def leftCutDensity (P : Parameters) : ℝ := (Stationary.seqLaw (shortLeftLaw P) {x | leftCutAt x 0}).toReal
lemma leftCutDensity_pos (P : Parameters) : 0<leftCutDensity P :=
  ENNReal.toReal_pos (ne_of_gt (leftCutAt_positive P)) (measure_ne_top _ _)
lemma leftCut_density (P : Parameters) :
    ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),
      Tendsto (fun n => (CutOutput.count (fun k => leftCutAt x (k:ℤ)) n:ℝ)/(n:ℝ)) atTop (𝓝 (leftCutDensity P)) := by
  let f : (ℤ → List Letter) → ℝ := fun x => if leftCutAt x 0 then 1 else 0
  have hf : Measurable f := Measurable.ite (leftCutAt_measurable 0) measurable_const measurable_const
  have hi : Integrable f (Stationary.seqLaw (shortLeftLaw P)) := by
    apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    filter_upwards [] with x
    dsimp [f]
    split_ifs <;> norm_num
  have he : (∫ x,f x ∂Stationary.seqLaw (shortLeftLaw P))=leftCutDensity P := by
    simpa only [f,Set.indicator,Pi.one_apply,Measure.real,Set.mem_ofPred_eq,leftCutDensity] using
      integral_indicator_one (μ := Stationary.seqLaw (shortLeftLaw P)) (s := {x | leftCutAt x 0}) (leftCutAt_measurable 0)
  have hh := Stationary.iid_shift_strong_law (shortLeftLaw P) hf hi
  filter_upwards [hh] with x hx
  simpa only [CutOutput.countReal,Stationary.average,Stationary.shift_iterate,f,leftCutAt_shift,zero_add,he] using hx

def forwardTypeSum (x : ℤ → List Letter) (b : Bool) (n : ℕ) : ℝ :=
  ∑ j∈Finset.range n,(typeNet b (x j):ℝ)
lemma left_type_averages (P : Parameters) (b : Bool) :
    ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),
      Tendsto (fun n => forwardTypeSum x b n/(n:ℝ)) atTop (𝓝 (1/2)) := by
  have hh := iid_piece_averages (shortLeftLaw P) (shortLeftLaw_typeNet_integrable P b)
  rw [shortLeftLaw_typeNet_mean] at hh
  exact (futurePieces_preserving (shortLeftLaw P)).quasiMeasurePreserving.ae hh

def leftBurgers (x : ℤ → List Letter) (a : ℤ) (n : ℕ) : List Bool := (reduce (intervalWord x a n)).burgers
lemma leftBurgers_length {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum=1)
    (a : ℤ) (n : ℕ) (ha : leftCutAt x a) : (leftBurgers x a n).length=n := by
  have he := reduce_imbalance (intervalWord x a n)
  rw [imbalance,ha n,intervalWord_net x a n 1 hd] at he
  simp only [List.length_nil,Nat.cast_zero,sub_zero,mul_one] at he
  exact_mod_cast he
lemma leftBurgers_append {x : ℤ → List Letter} {g h : ℕ} (hgh : g≤h) (hg : leftCutAt x g) :
    leftBurgers x 0 h=leftBurgers x g (h-g)++leftBurgers x 0 g := by
  have hh : h=g+(h-g) := by omega
  rw [hh,leftBurgers,intervalWord_add]
  have he : (0:ℤ)+(g:ℤ)=g := zero_add _
  rw [he,reduce_append_no_orders _ _ (hg (h-g))]
  simp only [Nat.add_sub_cancel_left]
  rfl
lemma forwardTypeSum_burgers {x : ℤ → List Letter} (hf : ∀ j,FixedWord (x j))
    (h0 : leftCutAt x 0) (g : ℕ) (b : Bool) :
    forwardTypeSum x b g=((leftBurgers x 0 g).count b:ℝ) := by
  have hh := burger_count_eq_typeNet (intervalWord_fixed hf 0 g) (h0 g) b
  rw [typeNet_intervalWord] at hh
  simp only [zero_add] at hh
  dsimp only [forwardTypeSum,leftBurgers]
  exact_mod_cast hh.symm

def bottomBurgerCount (x : ℤ → List Letter) (b : Bool) (h k : ℕ) : ℕ :=
  (bottom (leftBurgers x 0 h) k).count b
lemma bottomBurgerCount_bounds {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum=1)
    (hf : ∀ j,FixedWord (x j)) (h0 : leftCutAt x 0) {g k h : ℕ} (hg : leftCutAt x g)
    (hgk : g≤k) (hkh : k≤h) (b : Bool) :
    forwardTypeSum x b g ≤ (bottomBurgerCount x b h k:ℝ) ∧
      (bottomBurgerCount x b h k:ℝ) ≤ forwardTypeSum x b g+((k-g:ℕ):ℝ) := by
  have hv : (leftBurgers x 0 g).length=g := leftBurgers_length hd _ _ h0
  have hu : (leftBurgers x g (h-g)).length=h-g := leftBurgers_length hd _ _ hg
  have hb := bottom_append_bounds b (u := leftBurgers x g (h-g)) (v := leftBurgers x 0 g)
    (k := k) (by simpa only [hv] using hgk) (by rw [hu,hv]; omega)
  rw [hv] at hb
  rw [forwardTypeSum_burgers hf h0 g b]
  simp only [bottomBurgerCount,leftBurgers_append (hgk.trans hkh) hg]
  exact ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩

/-- Source uniform bottom counts, for genuine shortened +1 pieces. -/
theorem left_uniform_counts (P : Parameters) (b : Bool) :
    ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),leftCutAt x 0 →
      ∀ ε>0,∀ᶠ k : ℕ in atTop,∀ h≥k,
        |(bottomBurgerCount x b h k:ℝ)/(k:ℝ)-1/2|<ε := by
  filter_upwards [leftSeq_net P,leftSeq_fixed P,leftCut_density P,left_type_averages P b] with x hd hf hc ho
  intro h0 ε hε
  let C : ℕ → Prop := fun k => leftCutAt x (k:ℤ)
  let g : ℕ → ℕ := CutOutput.last C
  have hδ := leftCutDensity_pos P
  have hgdiv := CutOutput.last_div C hδ hc
  have hgap := CutOutput.last_gap_div C hδ hc
  have hgt : Tendsto g atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(CutOutput.last_tendsto C hδ hc).eventually (eventually_ge_atTop (b+1))] with n hn
    change b ≤ CutOutput.last C n
    omega
  have hh := (ho.comp hgt).mul hgdiv
  simp only [mul_one] at hh
  have hsum : Tendsto (fun k => forwardTypeSum x b (g k)/(k:ℝ)) atTop (𝓝 (1/2)) := by
    apply hh.congr'
    filter_upwards [hgt.eventually (eventually_ne_atTop (0:ℕ))] with k hk
    dsimp only [Function.comp_apply,Pi.mul_apply]
    change (forwardTypeSum x b (g k)/(g k:ℝ))*((g k:ℝ)/(k:ℝ))=_
    have hp : (g k:ℝ)≠0 := Nat.cast_ne_zero.mpr hk
    field_simp
  have hlow := (tendsto_order.mp hsum).1 (1/2-ε) (by linarith)
  have hup := (tendsto_order.mp (hsum.add hgap)).2 (1/2+ε) (by linarith)
  filter_upwards [hlow,hup,eventually_gt_atTop (0:ℕ)] with k hl hu hk
  intro h hkh
  have hg0 : C 0 := by simpa [C] using h0
  have hbounds := bottomBurgerCount_bounds hd hf h0 (CutOutput.last_spec hg0 k) (CutOutput.last_le C k) hkh b
  have hkpos : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hl' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.1
  have hu' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.2
  rw [add_div] at hu'
  apply abs_lt.mpr
  constructor <;> linarith
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def backwardOutputSum (x : ℤ → List Letter) (o : Order) (n : ℕ) : ℝ :=
  ∑ j∈Finset.range n,if rightOutput x (-1-j)=o then (1:ℝ) else 0
lemma backwardOutputSum_eq {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (h0 : rightCutAt x 0) {g : ℕ} (hg : rightCutAt x (-(g:ℤ))) (o : Order) :
    backwardOutputSum x o g=((rightOrders x (-g) g).count o:ℝ) := by
  classical
  have hs := rightOutput_segment hd (-(g:ℤ)) g hg (by simpa using h0)
  rw [← hs,count_ofFn_real]
  suffices hsum : backwardOutputSum x o g=∑ j∈Finset.range g,if rightOutput x (-(g:ℤ)+(j:ℤ))=o then (1:ℝ) else 0 by
    calc
      _ = _ := hsum
      _ = _ := by
        convert (Fin.sum_univ_eq_sum_range (fun j => if rightOutput x (-(g:ℤ)+(j:ℤ))=o then (1:ℝ) else 0) g).symm using 1
        all_goals try with_reducible_and_instances rfl
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> rfl
  unfold backwardOutputSum
  rw [← Finset.sum_range_reflect (fun j => if rightOutput x (-1-(j:ℤ))=o then (1:ℝ) else 0) g]
  apply Finset.sum_congr rfl
  intro j hj
  have he : -1-((g-1-j:ℕ):ℤ)= -(g:ℤ)+(j:ℤ) := by have := Finset.mem_range.mp hj; omega
  rw [he]

def terminalOrderCount (x : ℤ → List Letter) (o : Order) (h k : ℕ) : ℕ :=
  (bottom (rightOrders x (-(h:ℤ)) h) k).count o
lemma terminalOrderCount_bounds {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (h0 : rightCutAt x 0) {g k h : ℕ} (hg : rightCutAt x (-(g:ℤ))) (hgk : g≤k) (hkh : k≤h) (o : Order) :
    backwardOutputSum x o g ≤ (terminalOrderCount x o h k:ℝ) ∧
      (terminalOrderCount x o h k:ℝ) ≤ backwardOutputSum x o g+((k-g:ℕ):ℝ) := by
  have hm : rightCutAt x (-(h:ℤ)+(h-g:ℕ)) := by
    have he : -(h:ℤ)+((h-g:ℕ):ℤ)= -(g:ℤ) := by omega
    rwa [he]
  have he : -(h:ℤ)+((h-g:ℕ):ℤ)= -(g:ℤ) := by omega
  have hh : h=(h-g)+g := by omega
  have ha := rightOrders_append (x := x) (-(h:ℤ)) (h-g) g hm
  rw [← hh,he] at ha
  have hv : (rightOrders x (-(g:ℤ)) g).length=g := rightOrders_length hd _ _ (by simpa using h0)
  have hu : (rightOrders x (-(h:ℤ)) (h-g)).length=h-g := rightOrders_length hd _ _ hm
  have hb := bottom_append_bounds o (u := rightOrders x (-(h:ℤ)) (h-g)) (v := rightOrders x (-(g:ℤ)) g)
    (k := k) (by simpa only [hv] using hgk) (by rw [hu,hv]; omega)
  rw [hv] at hb
  rw [backwardOutputSum_eq hd h0 hg o]
  simp only [terminalOrderCount,ha]
  exact ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩

/-- Uniform terminal counts on the actual R-cut event; the h variable is
unbounded and is not fixed before the limit. -/
theorem right_uniform_counts (P : Parameters) (o : Order) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),rightCutAt x 0 →
      ∀ ε>0,∀ᶠ k : ℕ in atTop,∀ h≥k,
        |(terminalOrderCount x o h k:ℝ)/(k:ℝ)-outputMass P o|<ε := by
  filter_upwards [rightSeq_net P,rightCut_reverse_density P,rightOutput_reverse_frequencies P o] with x hd hc ho
  intro h0 ε hε
  let C : ℕ → Prop := fun k => rightCutAt x (-(k:ℤ))
  let g : ℕ → ℕ := CutOutput.last C
  have hδ := rightCutDensity_pos P
  have hgdiv := CutOutput.last_div C hδ hc
  have hgap := CutOutput.last_gap_div C hδ hc
  have hgt : Tendsto g atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(CutOutput.last_tendsto C hδ hc).eventually (eventually_ge_atTop (b+1))] with n hn
    change b ≤ CutOutput.last C n
    omega
  have hh := (ho.comp hgt).mul hgdiv
  simp only [mul_one] at hh
  have hsum : Tendsto (fun k => backwardOutputSum x o (g k)/(k:ℝ)) atTop (𝓝 (outputMass P o)) := by
    apply hh.congr'
    filter_upwards [hgt.eventually (eventually_ne_atTop (0:ℕ))] with k hk
    dsimp only [Function.comp_apply,Pi.mul_apply]
    change (backwardOutputSum x o (g k)/(g k:ℝ))*((g k:ℝ)/(k:ℝ))=_
    have hp : (g k:ℝ)≠0 := Nat.cast_ne_zero.mpr hk
    field_simp
  have hlow := (tendsto_order.mp hsum).1 (outputMass P o-ε) (by linarith)
  have hup := (tendsto_order.mp (hsum.add hgap)).2 (outputMass P o+ε) (by linarith)
  filter_upwards [hlow,hup,eventually_gt_atTop (0:ℕ)] with k hl hu hk
  intro h hkh
  have hg0 : C 0 := by simpa [C] using h0
  have hbounds := terminalOrderCount_bounds hd h0 (CutOutput.last_spec hg0 k) (CutOutput.last_le C k) hkh o
  have hkpos : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hl' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.1
  have hu' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.2
  rw [add_div] at hu'
  apply abs_lt.mpr
  constructor
  · linarith
  · linarith
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

lemma outputMass_nonneg (P : Parameters) (o : Order) : 0≤outputMass P o := by
  rw [outputMass_eq_measure]
  exact ENNReal.toReal_nonneg
lemma seam_alpha (P : Parameters) : ∃ α : ℝ,0<α ∧ α<1/2 ∧ ∀ b : Bool,outputMass P (some b)<α := by
  have hpos := outputMass_flexible_pos P
  have hnon := outputMass_nonneg P (some false)
  have hf := outputMass_fixed P false
  obtain ⟨α,hα₁,hα₂⟩ := exists_between (show outputMass P (some false)<1/2 by linarith)
  refine ⟨α,lt_of_le_of_lt hnon hα₁,hα₂,?_⟩
  intro b
  rw [outputMass_fixed P b,← outputMass_fixed P false]
  exact hα₁

def GoodLeft (α : ℝ) (B : ℕ) (x : ℤ → List Letter) : Prop :=
  leftCutAt x 0 ∧ ∀ h k : ℕ,B≤k → k≤h → ∀ b : Bool,α*(k:ℝ)≤bottomBurgerCount x b h k
def GoodRight (α : ℝ) (B : ℕ) (x : ℤ → List Letter) : Prop :=
  rightCutAt x 0 ∧ ∀ h k : ℕ,B≤k → k≤h → ∀ b : Bool,(terminalOrderCount x (some b) h k:ℝ)≤α*(k:ℝ)
lemma GoodLeft.mono {α : ℝ} {B D : ℕ} (hBD : B≤D) {x : ℤ → List Letter} (hx : GoodLeft α B x) : GoodLeft α D x :=
  ⟨hx.1,fun h k hk hh b => hx.2 h k (hBD.trans hk) hh b⟩
lemma GoodRight.mono {α : ℝ} {B D : ℕ} (hBD : B≤D) {x : ℤ → List Letter} (hx : GoodRight α B x) : GoodRight α D x :=
  ⟨hx.1,fun h k hk hh b => hx.2 h k (hBD.trans hk) hh b⟩

lemma goodLeft_positive (P : Parameters) {α : ℝ} (hα : α<1/2) :
    ∃ B,0<Stationary.seqLaw (shortLeftLaw P) {x | GoodLeft α B x} := by
  apply exists_measure_pos_of_ae_cover (Stationary.seqLaw (shortLeftLaw P)) (leftCutAt_positive P)
  filter_upwards [left_uniform_counts P false,left_uniform_counts P true] with x hx₀ hx₁
  intro h0
  have he : 0<1/2-α := by linarith
  have hh := (hx₀ h0 (1/2-α) he).and (hx₁ h0 (1/2-α) he)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N+1,h0,?_⟩
  intro h k hk hkh b
  have hm : |(bottomBurgerCount x b h k:ℝ)/(k:ℝ)-1/2|<1/2-α := by
    cases b
    · exact (hN k (by omega)).1 h hkh
    · exact (hN k (by omega)).2 h hkh
  have hp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hl : α<(bottomBurgerCount x b h k:ℝ)/(k:ℝ) := by have := (abs_lt.mp hm).1; linarith
  exact ((lt_div_iff₀ hp).mp hl).le
lemma goodRight_positive (P : Parameters) {α : ℝ} (hα : ∀ b : Bool,outputMass P (some b)<α) :
    ∃ B,0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x} := by
  apply exists_measure_pos_of_ae_cover (Stationary.seqLaw (rightLaw P)) (rightCutAt_positive P)
  filter_upwards [right_uniform_counts P (some false),right_uniform_counts P (some true)] with x hx₀ hx₁
  intro h0
  have hε (b : Bool) : 0<α-outputMass P (some b) := sub_pos.mpr (hα b)
  have hh := (hx₀ h0 (α-outputMass P (some false)) (hε false)).and
    (hx₁ h0 (α-outputMass P (some true)) (hε true))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N+1,h0,?_⟩
  intro h k hk hkh b
  have hm : |(terminalOrderCount x (some b) h k:ℝ)/(k:ℝ)-outputMass P (some b)|<α-outputMass P (some b) := by
    cases b
    · exact (hN k (by omega)).1 h hkh
    · exact (hN k (by omega)).2 h hkh
  have hp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hu : (terminalOrderCount x (some b) h k:ℝ)/(k:ℝ)<α := by have := (abs_lt.mp hm).2; linarith
  exact ((div_lt_iff₀ hp).mp hu).le

lemma intervalWord_measurable_coords {S : Set ℤ} (a : ℤ) (n : ℕ)
    (hS : ∀ j<n,a+(j:ℤ)∈S) : Measurable[Stationary.coords (α := List Letter) S] (fun x => intervalWord x a n) := by
  let : MeasurableSpace (ℤ → List Letter) := Stationary.coords S
  have hf : Measurable (fun x : ℤ → List Letter => (fun j : Fin n => x (a+j))) := by
    apply Measurable.of_eval
    intro j
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (a+j) (le_iSup_of_le (hS j j.isLt) le_rfl)
  have he : (fun x : ℤ → List Letter => intervalWord x a n)=fun x => (List.ofFn (fun j : Fin n => x (a+j))).flatten := by
    funext x
    exact piecesPrefix_ofFn _ _
  rw [he]
  exact (measurable_of_countable (fun w : Fin n → List Letter => (List.ofFn w).flatten)).comp hf
lemma goodRight_past_measurable (α : ℝ) (B : ℕ) :
    MeasurableSet[Stationary.coords (α := List Letter) {j | j<0}] {x | GoodRight α B x} := by
  simp only [GoodRight,Set.ofPred_and,Set.ofPred_forall]
  apply rightCutAt_zero_past_measurable.inter
  apply MeasurableSet.iInter
  intro h
  have hm := intervalWord_measurable_coords (S := {j | j<0}) (-(h:ℤ)) h (fun j hj => by change -(h:ℤ)+j<0; omega)
  exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _hk => MeasurableSet.iInter (fun _hh =>
    MeasurableSet.iInter (fun b => hm ((Set.to_countable {w : List Letter |
      ((bottom (reduce w).orders k).count (some b):ℝ)≤α*(k:ℝ)}).measurableSet)))))
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def FlexiblePrefix (x : ℤ → List Letter) (D : ℕ) : Prop :=
  ∀ j : ℕ,j<D → x j=[Letter.order none]
lemma intervalWord_flexible {x : ℤ → List Letter} {D n : ℕ} {a : ℤ}
    (hx : FlexiblePrefix x D) (ha : 0≤a) (hn : a+n≤D) :
    intervalWord x a n=List.replicate n (Letter.order none) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [intervalWord_succ,ih (by omega),show x (a+n)=[Letter.order none] by
      have he : a+(n:ℤ)=((a+n).toNat:ℤ) := by rw [Int.toNat_of_nonneg (by omega)]
      rw [he]
      exact hx _ (by omega)]
    simp only [List.replicate_succ']
lemma reduce_flexible (n : ℕ) : reduce (List.replicate n (Letter.order none))=⟨List.replicate n none,[]⟩ := by
  have hh := evalOrders_empty (List.replicate n none)
  simpa only [evalOrders,reduce,List.map_replicate] using hh
lemma forcedRight_shape {x : ℤ → List Letter} {D h : ℕ}
    (hc : rightCutAt x 0) (hx : FlexiblePrefix x D) :
    reduce (intervalWord x ((D:ℤ)-h) h)=
      if h≤D then ⟨List.replicate h none,[]⟩ else
        ⟨rightOrders x (-(h-D:ℕ):ℤ) (h-D)++List.replicate D none,[]⟩ := by
  split_ifs with hh
  · rw [intervalWord_flexible hx (by omega) (by omega),reduce_flexible]
  · have he : h=(h-D)+D := by omega
    have hs : (D:ℤ)-h=-(h-D:ℕ) := by omega
    rw [hs]
    conv_lhs => arg 1; arg 3; rw [he]
    rw [intervalWord_add]
    have hi : -(h-D:ℕ)+(h-D:ℕ)= (0:ℤ) := by omega
    rw [hi,reduce_append_no_burgers _ _ (by simpa using hc (h-D)),
      intervalWord_flexible (a := 0) (n := D) hx (by omega) (by omega),reduce_flexible]
    rfl
lemma count_bottom_flexible (b : Bool) (n k : ℕ) :
    (bottom (List.replicate n (none : Order)) k).count (some b)=0 := by
  simp [bottom,List.drop_replicate,List.count_replicate]
lemma count_bottom_flexible_append (b : Bool) (u : List Order) {D k : ℕ} (hk : D≤k) :
    (bottom (u++List.replicate D none) k).count (some b)=(bottom u (k-D)).count (some b) := by
  rw [bottom_append (by simpa using hk),List.count_append]
  simp [List.count_replicate]
lemma count_bottom_flexible_append_small (b : Bool) (u : List Order) {D k : ℕ} (hk : k≤D) :
    (bottom (u++List.replicate D none) k).count (some b)=0 := by
  unfold bottom
  rw [List.length_append,List.length_replicate,List.drop_append,
    List.drop_eq_nil_of_le (by omega : u.length ≤ u.length+D-k)]
  simp [List.drop_replicate,List.count_replicate]

/-- Deterministic source seam criterion, including every small k. -/
theorem seam_matching {x y : ℤ → List Letter} {α : ℝ} {B D h : ℕ}
    (hα : 0≤α) (hBD : B≤D) (hD : (B:ℝ)≤α*D)
    (hl : GoodLeft α B x) (hr : GoodRight α B y) (hf : FlexiblePrefix y D)
    (hdl : ∀ j,((x j).map Letter.increment).sum=1)
    (hdr : ∀ j,((y j).map Letter.increment).sum= -1) :
    EmptyReducing (intervalWord x 0 h++intervalWord y ((D:ℤ)-h) h) := by
  have hlb : (leftBurgers x 0 h).length=h := leftBurgers_length hdl _ _ hl.1
  have hro : (reduce (intervalWord y ((D:ℤ)-h) h)).orders.length=h := by
    have hi := reduce_imbalance (intervalWord y ((D:ℤ)-h) h)
    rw [imbalance,intervalWord_net y _ h (-1) hdr,forcedRight_shape hr.1 hf] at hi
    split_ifs at hi ⊢ with hh
    · simp only [List.length_replicate,forcedRight_shape hr.1 hf,ite_eq_left hh]
    · rw [forcedRight_shape hr.1 hf,ite_eq_right hh]
      change ((rightOrders y (-(h-D:ℕ):ℤ) (h-D)++List.replicate D none)).length=h
      simp only [List.length_nil,Nat.cast_zero,zero_sub,mul_neg_one] at hi
      omega
  have hno : (reduce (intervalWord y ((D:ℤ)-h) h)).burgers=[] := by
    rw [forcedRight_shape hr.1 hf]
    split_ifs <;> rfl
  have hs : SupplyCondition (leftBurgers x 0 h) (reduce (intervalWord y ((D:ℤ)-h) h)).orders := by
    refine ⟨hlb.trans hro.symm,?_⟩
    intro k hk b
    rw [hro] at hk
    rw [forcedRight_shape hr.1 hf]
    by_cases hh : h≤D
    · rw [ite_eq_left hh,count_bottom_flexible]
      exact Nat.zero_le _
    rw [ite_eq_right hh]
    by_cases hkd : k≤D
    · rw [count_bottom_flexible_append_small b _ hkd]
      exact Nat.zero_le _
    rw [count_bottom_flexible_append b _ (by omega)]
    have hkB : B≤k := by omega
    have hlc := hl.2 h k hkB hk b
    have hrc : ((bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).count (some b):ℝ)≤α*k := by
      by_cases hkb : B≤k-D
      · have hh' := hr.2 (h-D) (k-D) hkb (by omega) b
        change ((bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).count (some b):ℝ)≤α*(k-D:ℕ) at hh'
        exact hh'.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (show k-D≤k by omega)) hα)
      · have hc := List.count_le_length (a := some b) (l := bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D))
        have hlen : (bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).length≤k-D := by
          simp only [bottom,List.length_drop]; omega
        have hb : ((bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).count (some b):ℝ)≤B := by
          exact_mod_cast (hc.trans (hlen.trans (by omega)))
        exact hb.trans (hD.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (show D≤k by omega)) hα))
    exact_mod_cast hrc.trans hlc
  have hm := matching_of_supplyCondition hs
  unfold EmptyReducing reduce
  rw [run_append]
  have he : run (intervalWord x 0 h) ⟨[],[]⟩=⟨[],leftBurgers x 0 h⟩ := by
    change reduce (intervalWord x 0 h)=_
    have hh := hl.1 h
    cases he : reduce (intervalWord x 0 h)
    simp_all only [leftBurgers]
  rw [he,run_older_supply,hm,hno]
  rfl
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

lemma flexiblePrefix_future_measurable (D : ℕ) :
    MeasurableSet[Stationary.coords (α := List Letter) {j | 0≤j}] {x | FlexiblePrefix x D} := by
  simp only [FlexiblePrefix,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hj
  have hm : Measurable[Stationary.coords (α := List Letter) {j | 0≤j}] (fun x : ℤ → List Letter => x j) := by
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (j:ℤ) (le_iSup_of_le (show (0:ℤ)≤j by omega) le_rfl)
  exact hm (measurableSet_singleton _)
lemma flexiblePrefix_positive (P : Parameters) (D : ℕ) :
    0<Stationary.seqLaw (rightLaw P) {x | FlexiblePrefix x D} := by
  have he : {x | FlexiblePrefix x D}=futurePieces ⁻¹' pieceCylinder (List.replicate D [Letter.order none]) := by
    ext x
    simp only [FlexiblePrefix,Set.mem_ofPred_eq,Set.mem_preimage,pieceCylinder]
    constructor
    · intro h j
      simpa [futurePieces] using h j (by simpa using j.isLt)
    · intro h j hj
      simpa [futurePieces] using h ⟨j,by simpa using hj⟩
  rw [he,(futurePieces_preserving (rightLaw P)).measure_preimage (pieceCylinder_measurable _).nullMeasurableSet]
  apply pieceCylinder_positive
  intro w hw
  have he : w=[Letter.order none] := (List.mem_replicate.mp hw).2
  subst w
  exact rightLaw_order_positive P none
lemma goodRight_forced_positive (P : Parameters) {α : ℝ} {B D : ℕ}
    (hR : 0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x}) :
    0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x ∧ FlexiblePrefix x D} := by
  have hi := Stationary.indep_coords (rightLaw P) (S := {j | j<0}) (R := {j | 0≤j})
    (Set.disjoint_left.mpr (fun j hj hj' => by change j<0 at hj; change 0≤j at hj'; omega))
  have he := ((indep_iff_forall_indepSet _).mp hi _ _ (goodRight_past_measurable α B)
    (flexiblePrefix_future_measurable D)).measure_inter_eq_mul
  change Stationary.seqLaw (rightLaw P) ({x | GoodRight α B x}∩{x | FlexiblePrefix x D})>0
  rw [he]
  exact ENNReal.mul_pos_iff.mpr ⟨hR,flexiblePrefix_positive P D⟩

def piecesFrom (a : ℤ) (x : ℤ → List Letter) : ℕ → List Letter := fun j => x (a+j)
lemma piecesFrom_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (a : ℤ) :
    MeasurePreserving (piecesFrom a) (Stationary.seqLaw ν) (naturalPiecesLaw ν) := by
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (a+index)),?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun j k h => Int.ofNat_inj.mp (add_left_cancel h))

def pieceSeamEvent (h : ℕ) : Set ((ℕ → List Letter) × (ℕ → List Letter)) :=
  {z | EmptyReducing (piecesPrefix z.1 h++piecesPrefix z.2 h)}
lemma pieceSeamEvent_measurable (h : ℕ) : MeasurableSet (pieceSeamEvent h) := by
  have hm := ((measurable_of_countable (fun z : List Letter×List Letter => z.1++z.2)).comp
    (((piecesPrefix_measurable h).comp measurable_fst).prodMk ((piecesPrefix_measurable h).comp measurable_snd)))
  exact hm ((Set.to_countable {w | EmptyReducing w}).measurableSet)

/-- Uniform success for the actual independent shortened-L and genuine-R laws.
Raw stopping-word transport is separate: no finite stopping-length mean is used. -/
theorem piece_seam_uniform (P : Parameters) : ∃ δ : ℝ,0<δ ∧ ∀ h : ℕ,
    ENNReal.ofReal δ≤((naturalPiecesLaw (shortLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))) (pieceSeamEvent h) := by
  obtain ⟨α,hα,hα',hαR⟩ := seam_alpha P
  obtain ⟨B₀,hB₀⟩ := goodLeft_positive P hα'
  obtain ⟨B₁,hB₁⟩ := goodRight_positive P hαR
  let B := max B₀ B₁
  have hL : 0<Stationary.seqLaw (shortLeftLaw P) {x | GoodLeft α B x} :=
    hB₀.trans_le (measure_mono (fun _ hx => hx.mono (Nat.le_max_left _ _)))
  have hR : 0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x} :=
    hB₁.trans_le (measure_mono (fun _ hx => hx.mono (Nat.le_max_right _ _)))
  obtain ⟨d,hd⟩ := exists_nat_gt ((B:ℝ)/α)
  let D := max B d
  have hBD : B≤D := Nat.le_max_left _ _
  have hD : (B:ℝ)≤α*D := by
    have he : (B:ℝ)<α*d := by have := (div_lt_iff₀ hα).mp hd; nlinarith
    exact he.le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_max_right B d) hα.le)
  let A : Set (ℤ → List Letter) := {x | GoodLeft α B x}
  let R : Set (ℤ → List Letter) := {x | GoodRight α B x ∧ FlexiblePrefix x D}
  let μ := (Stationary.seqLaw (shortLeftLaw P)).prod (Stationary.seqLaw (rightLaw P))
  have hp : 0<μ (A×ˢR) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos_iff.mpr ⟨hL,goodRight_forced_positive P hR⟩
  refine ⟨(μ (A×ˢR)).toReal,ENNReal.toReal_pos hp.ne' (measure_ne_top _ _),?_⟩
  intro h
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  let F := Prod.map (piecesFrom 0) (piecesFrom ((D:ℤ)-h))
  have hF : MeasurePreserving F μ ((naturalPiecesLaw (shortLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))) :=
    (piecesFrom_preserving (shortLeftLaw P) 0).prod (piecesFrom_preserving (rightLaw P) ((D:ℤ)-h))
  rw [← hF.measure_preimage (pieceSeamEvent_measurable h).nullMeasurableSet]
  apply measure_mono_ae
  have hal : ∀ᵐ z ∂μ,∀ j,((z.1 j).map Letter.increment).sum=1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (leftSeq_net P)
  have har : ∀ᵐ z ∂μ,∀ j,((z.2 j).map Letter.increment).sum= -1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (rightSeq_net P)
  filter_upwards [hal,har] with z hl hr
  intro hz
  exact seam_matching hα.le hBD hD hz.1 hz.2.1 hz.2.2 hl hr
end FKCRT.Inventory

end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SeamLengths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
def upPath (h : ℕ) (n : ℕ) (x : ℕ → Letter) : ℤ := (h:ℤ)-signSum x (n+1)
def firstUp (h : ℕ) : (ℕ → Letter) → WithTop ℕ := TreeCoding.firstZero (upPath h)
lemma upPath_adapted (h : ℕ) : StronglyAdapted rawFiltration (upPath h) := by
  intro n
  convert (prefix_measurable n (fun y => (h:ℤ)-(((List.ofFn y).reverse).map Letter.increment).sum)).stronglyMeasurable using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact congrArg (fun z : ℤ => (h:ℤ)-z) (revealed_sum x (n+1)).symm
lemma firstUp_stopping (h : ℕ) : IsStoppingTime rawFiltration (firstUp h) :=
  TreeCoding.firstZero_isStoppingTime (upPath_adapted h)
lemma firstUp_measurable (h : ℕ) : Measurable (firstUp h) := stopping_measurable (firstUp_stopping h)
lemma upPath_step (h n : ℕ) (x : ℕ → Letter) : upPath h n x-1 ≤ upPath h (n+1) x := by
  unfold upPath
  rw [signSum_succ x (n+1)]
  have := (increment_bounds (x (n+1))).2.1
  omega
lemma upPath_initial (h : ℕ) (hh : 0<h) (x : ℕ → Letter) : 0 ≤ upPath h 0 x := by
  have := (increment_bounds (x 0)).2.1
  simp only [upPath,signSum,Nat.zero_add,Finset.sum_range_one]
  omega
lemma upPath_martingale (P : Parameters) (h : ℕ) :
    Martingale (fun n x => (upPath h n x:ℝ)) rawFiltration (streamLaw P ℕ) := by
  convert (martingale_const rawFiltration (streamLaw P ℕ) (h:ℝ )).sub (raw_sign_martingale P) using 1
  all_goals try with_reducible_and_instances rfl
  ext n x
  simp [upPath]
lemma firstUp_finite (P : Parameters) (h : ℕ) (hh : 0<h) : ∀ᵐ x ∂streamLaw P ℕ,firstUp h x≠⊤ := by
  have hj : ∀ᵐ x ∂streamLaw P ℕ,∃ᶠ n in atTop,upPath h (n+1) x≠upPath h n x := by
    filter_upwards [] with x
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    unfold upPath
    rw [signSum_succ x (n+1)]
    have := (increment_bounds (x (n+1))).2.2
    omega
  filter_upwards [TreeCoding.integer_martingale_hits_zero (upPath_adapted h) (upPath_martingale P h)
    (upPath_initial h hh) (upPath_step h) hj] with x hx
  classical
  simp [firstUp,TreeCoding.firstZero,hx]

lemma firstUp_of_hit_iff (h : ℕ) (x : ℕ → Letter) (n : ℕ) :
    firstUp h x=WithTop.some n ↔ signSum x (n+1)= (h:ℤ) ∧ ∀ j<n,signSum x (j+1)≠ (h:ℤ) := by
  rw [firstUp,TreeCoding.firstZero_eq_iff]
  simp only [upPath]
  constructor
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
  · rintro ⟨hn,hj⟩
    exact ⟨by omega,fun j h => by have := hj j h; omega⟩
lemma firstUp_prefix_lt {h : ℕ} (hh : 0<h) {x : ℕ → Letter} {n : ℕ}
    (hn : firstUp h x=WithTop.some n) {j : ℕ} (hj : j ≤ n) : signSum x j<(h:ℤ) := by
  have hd := (TreeCoding.firstZero_eq_iff (upPath h) x n).mp hn
  cases j with
  | zero => simp only [signSum,Finset.range_zero,Finset.sum_empty]; omega
  | succ j =>
    have hj' : j<n := by omega
    have he := TreeCoding.integer_path_nonneg_before_zero (fun k => upPath h k x)
      (upPath_initial h hh x) (fun k => upPath_step h k x) j (fun k hk => hd.2 k (hk.trans hj'))
    have hnz := hd.2 j hj'
    dsimp [upPath] at he hnz
    omega


lemma stoppedWord_up_eq_leftWord (P : Parameters) : ∀ᵐ x ∂streamLaw P ℕ,
    stoppedWord (firstUp 1) x=leftWord x := by
  filter_upwards [ae_left_first_hit P] with x hx
  let N := parsingOffset (leftSteps x) x
  have hN : 0<N := by
    by_contra hh
    have he : N=0 := by omega
    have hz := hx.1
    change signSum x N=1 at hz
    simp only [he,signSum,Finset.range_zero,Finset.sum_empty] at hz
    omega
  have he : firstUp 1 x=WithTop.some (N-1) := by
    apply (firstUp_of_hit_iff _ _ _).mpr
    refine ⟨by simpa only [Nat.cast_one,Nat.sub_add_cancel hN] using hx.1,?_⟩
    intro j hj
    have hh := hx.2 (j+1) (by omega)
    omega
  rw [stoppedWord_of_hit he,Nat.sub_add_cancel hN]
  rfl

def rawLeftLaw (P : Parameters) : Measure (List Letter) := (streamLaw P ℕ).map (stoppedWord (firstUp 1))
instance rawLeftLaw_probability (P : Parameters) : IsProbabilityMeasure (rawLeftLaw P) :=
  Measure.isProbabilityMeasure_map ((measurable_stoppedWord (firstUp_measurable 1)).aemeasurable)
lemma rawLeftLaw_normal (P : Parameters) :
    (rawLeftLaw P).map (fun w => normalWord (reduce w))=
      (shortLeftLaw P).map (fun w => normalWord (reduce w)) := by
  unfold rawLeftLaw shortLeftLaw
  rw [Measure.map_map (measurable_of_countable _) (measurable_stoppedWord (firstUp_measurable 1)),
    Measure.map_map (measurable_of_countable _) measurable_shortLeftWord]
  apply Measure.map_congr
  filter_upwards [stoppedWord_up_eq_leftWord P] with x hx
  simp only [Function.comp_apply,hx]
  exact congrArg normalWord (run_shortLeftWord x ⟨[],[]⟩).symm

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
lemma firstUp_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstUp h x=WithTop.some n) (hy : firstUp k (tail (n+1) x)=WithTop.some m) :
    firstUp (h+k) x=WithTop.some (n+m+1) := by
  apply (firstUp_of_hit_iff _ _ _).mpr
  constructor
  · rw [show n+m+1+1=(n+1)+(m+1) by omega,signSum_add,
      ((firstUp_of_hit_iff _ _ _).mp hx).1,((firstUp_of_hit_iff _ _ _).mp hy).1]
    push_cast; ring
  · intro j hj
    by_cases hjn : j<n+1
    · by_cases hjn' : j<n
      · have hp := firstUp_prefix_lt hh hx (j := j+1) (by omega)
        push_cast; omega
      · have he : j=n := by omega
        subst j
        rw [((firstUp_of_hit_iff _ _ _).mp hx).1]
        push_cast; omega
    · have hp := firstUp_prefix_lt hk hy (j := j+1-(n+1)) (by omega)
      have he : j+1=(n+1)+(j+1-(n+1)) := by omega
      rw [he,signSum_add,((firstUp_of_hit_iff _ _ _).mp hx).1]
      norm_num only [Nat.cast_add]
      omega
lemma stoppedWord_up_add {h k n m : ℕ} (hh : 0<h) (hk : 0<k) {x : ℕ → Letter}
    (hx : firstUp h x=WithTop.some n) (hy : firstUp k (tail (n+1) x)=WithTop.some m) :
    stoppedWord (firstUp (h+k)) x=stoppedWord (firstUp k) (stoppedTail (firstUp h) x)++stoppedWord (firstUp h) x := by
  rw [stoppedWord_of_hit (firstUp_add hh hk hx hy),stoppedTail_of_hit hx,stoppedWord_of_hit hx,stoppedWord_of_hit hy,
    show n+m+1+1=(n+1)+(m+1) by omega,revealed_add]

def leftPieces (x : ℕ → Letter) : ℕ → List Letter := fun j => wordPieces (firstUp 1) j x
lemma leftPieces_measurable : Measurable leftPieces := by
  apply Measurable.of_eval
  intro j
  exact (measurable_stoppedWord (firstUp_measurable 1)).comp ((measurable_stoppedTail (firstUp_measurable 1)).iterate j)
lemma leftPieces_preserving (P : Parameters) :
    MeasurePreserving leftPieces (streamLaw P ℕ) (naturalPiecesLaw (rawLeftLaw P)) := by
  refine ⟨leftPieces_measurable,?_⟩
  change (streamLaw P ℕ).map (fun x j => (stoppedWord (firstUp 1) ∘ (stoppedTail (firstUp 1))^[j]) x)=_
  rw [(stoppedWordPieces_iid P (firstUp_measurable 1) (firstUp_stopping 1) (firstUp_finite P 1 (by omega))).map_fun_eq_infinitePi_map
    (fun j => (measurable_stoppedWord (firstUp_measurable 1)).comp ((measurable_stoppedTail (firstUp_measurable 1)).iterate j))]
  unfold naturalPiecesLaw
  congr 1
  funext j
  have hm := (stoppedTail_preserving P (firstUp_measurable 1) (firstUp_stopping 1) (firstUp_finite P 1 (by omega))).iterate j
  change (streamLaw P ℕ).map (stoppedWord (firstUp 1) ∘ (stoppedTail (firstUp 1))^[j])=rawLeftLaw P
  rw [← Measure.map_map (measurable_stoppedWord (firstUp_measurable 1)) hm.measurable,hm.map_eq]
  rfl

lemma leftPieces_tail (x : ℕ → Letter) :
    piecesTail 1 (leftPieces x)=leftPieces (stoppedTail (firstUp 1) x) := by
  funext j
  simp only [piecesTail,leftPieces,wordPieces]
  rw [Nat.add_comm 1 j,Function.iterate_succ_apply]

lemma stoppedWord_up_pieces (P : Parameters) (h : ℕ) : ∀ᵐ x ∂streamLaw P ℕ,
    stoppedWord (firstUp (h+1)) x=reversePiecesPrefix (leftPieces x) (h+1) := by
  induction h with
  | zero =>
    filter_upwards [] with x
    simp [reversePiecesPrefix,leftPieces,wordPieces]
  | succ h ih =>
    have hm := stoppedTail_preserving P (firstUp_measurable 1) (firstUp_stopping 1) (firstUp_finite P 1 (by omega))
    filter_upwards [firstUp_finite P 1 (by omega),hm.quasiMeasurePreserving.tendsto_ae ih,
      hm.quasiMeasurePreserving.tendsto_ae (firstUp_finite P (h+1) (by omega))] with x hx hi hy
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hx
    obtain ⟨m,hmm⟩ := WithTop.ne_top_iff_exists.mp hy
    have hn' := hn.symm
    have hm' : firstUp (h+1) (tail (n+1) x)=WithTop.some m := by simpa only [stoppedTail_of_hit hn'] using hmm.symm
    conv_rhs => rw [reversePiecesPrefix_succ,leftPieces_tail]
    rw [show h+1+1=1+(h+1) by omega,stoppedWord_up_add (by omega) (by omega) hn' hm',hi]
    rfl

lemma leftPrefix_identDistrib (P : Parameters) (h : ℕ) :
    IdentDistrib (stoppedWord (firstUp (h+1))) (fun x => piecesPrefix x (h+1))
      (streamLaw P ℕ) (naturalPiecesLaw (rawLeftLaw P)) := by
  have hp := (reverseFirstPieces_preserving (rawLeftLaw P) (h+1)).comp (leftPieces_preserving P)
  have hm : Measurable (fun x : ℕ → List Letter => piecesPrefix x (h+1)) := by
    rw [show (fun x : ℕ → List Letter => piecesPrefix x (h+1))=
      (fun f : Fin (h+1) → List Letter => (List.ofFn f).flatten) ∘ (fun x i => x i) by
        funext x; exact piecesPrefix_ofFn x (h+1)]
    exact (measurable_of_countable _).comp (Measurable.of_eval (fun index => measurable_pi_apply (index:ℕ)))
  have hi := (hp.hasLaw.identDistrib ((MeasurePreserving.id _).hasLaw)).comp hm
  apply (IdentDistrib.of_ae_eq (measurable_stoppedWord (firstUp_measurable (h+1))).aemeasurable ?_).trans hi
  filter_upwards [stoppedWord_up_pieces P h] with x hx
  simpa only [Function.comp_apply,reversePiecesPrefix_eq] using hx


end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def mappedPieceLaw (ν : Measure (List Letter)) (f : List Letter → List Letter) : Measure (List Letter) := ν.map f
instance mappedPieceLaw_probability (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (f : List Letter → List Letter) :
    IsProbabilityMeasure (mappedPieceLaw ν f) := Measure.isProbabilityMeasure_map ((measurable_of_countable f).aemeasurable)
def mapPieces (f : List Letter → List Letter) (x : ℕ → List Letter) : ℕ → List Letter := fun j => f (x j)
lemma mapPieces_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (f : List Letter → List Letter) :
    MeasurePreserving (mapPieces f) (naturalPiecesLaw ν) (naturalPiecesLaw (mappedPieceLaw ν f)) := by
  refine ⟨Measurable.of_eval (fun index => (measurable_of_countable f).comp (measurable_pi_apply index)),?_⟩
  exact Measure.infinitePi_map_pi (fun _ : ℕ => ν) (fun _ => measurable_of_countable f)
lemma run_normalPieces (x : ℕ → List Letter) (h : ℕ) (e : Evaluation) :
    run (piecesPrefix (mapPieces (fun w => normalWord (reduce w)) x) h) e=run (piecesPrefix x h) e := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [piecesPrefix,run_append,ih,mapPieces,run_normalWord]
lemma pieceSeamEvent_normal_preimage (h : ℕ) :
    (Prod.map (mapPieces (fun w => normalWord (reduce w))) id) ⁻¹' pieceSeamEvent h=pieceSeamEvent h := by
  ext z
  change EmptyReducing (piecesPrefix (mapPieces (fun w => normalWord (reduce w)) z.1) h++piecesPrefix z.2 h) ↔
    EmptyReducing (piecesPrefix z.1 h++piecesPrefix z.2 h)
  change run (piecesPrefix (mapPieces (fun w => normalWord (reduce w)) z.1) h++piecesPrefix z.2 h) ⟨[],[]⟩=⟨[],[]⟩ ↔
    run (piecesPrefix z.1 h++piecesPrefix z.2 h) ⟨[],[]⟩=⟨[],[]⟩
  rw [run_append,run_append,run_normalPieces]
lemma pieceSeam_normal_measure (μ ν R : Measure (List Letter)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure R]
    (hμν : μ.map (fun w => normalWord (reduce w))=ν.map (fun w => normalWord (reduce w))) (h : ℕ) :
    ((naturalPiecesLaw μ).prod (naturalPiecesLaw R)) (pieceSeamEvent h)=
      ((naturalPiecesLaw ν).prod (naturalPiecesLaw R)) (pieceSeamEvent h) := by
  have hμ := (mapPieces_preserving μ (fun w => normalWord (reduce w))).prod
    (MeasurePreserving.id (naturalPiecesLaw R))
  have hν := (mapPieces_preserving ν (fun w => normalWord (reduce w))).prod
    (MeasurePreserving.id (naturalPiecesLaw R))
  have heμ := hμ.measure_preimage (pieceSeamEvent_measurable h).nullMeasurableSet
  have heν := hν.measure_preimage (pieceSeamEvent_measurable h).nullMeasurableSet
  have hmapped : mappedPieceLaw μ (fun w => normalWord (reduce w))=mappedPieceLaw ν (fun w => normalWord (reduce w)) := hμν
  simp only [pieceSeamEvent_normal_preimage,hmapped] at heμ
  rw [pieceSeamEvent_normal_preimage] at heν
  exact heμ.trans heν.symm

lemma reverse_reversePiecesPrefix (x : ℕ → List Letter) (n : ℕ) :
    (reversePiecesPrefix x n).reverse=piecesPrefix (mapPieces List.reverse x) n := by
  rw [reversePiecesPrefix,piecesPrefix_ofFn,List.reverse_flatten]
  simp only [List.map_reverse,List.reverse_reverse,List.map_ofFn,mapPieces,Function.comp_def]
lemma chronologicalRight_identDistrib (P : Parameters) (h : ℕ) :
    IdentDistrib (fun x => (stoppedWord (firstDown (h+1)) x).reverse) (fun x => piecesPrefix x (h+1))
      (streamLaw P ℕ) (naturalPiecesLaw (rightLaw P)) := by
  have hp := (mapPieces_preserving (reverseRightLaw P) List.reverse).comp (rightPieces_preserving P)
  have hi := (hp.hasLaw.identDistrib ((MeasurePreserving.id _).hasLaw)).comp (piecesPrefix_measurable (h+1))
  apply (IdentDistrib.of_ae_eq ((measurable_of_countable List.reverse).comp
    (measurable_stoppedWord (firstDown_measurable (h+1)))).aemeasurable ?_).trans hi
  filter_upwards [stoppedWord_down_pieces P h] with x hx
  simp only [hx,reverse_reversePiecesPrefix,Function.comp_apply]

def rawSeamWord (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : List Letter :=
  stoppedWord (firstUp h) z.1++(stoppedWord (firstDown h) z.2).reverse
lemma rawSeamWord_measurable (h : ℕ) : Measurable (rawSeamWord h) :=
  (measurable_of_countable (fun z : List Letter×List Letter => z.1++z.2)).comp
    (((measurable_stoppedWord (firstUp_measurable h)).comp measurable_fst).prodMk
      (((measurable_of_countable List.reverse).comp (measurable_stoppedWord (firstDown_measurable h))).comp measurable_snd))
lemma rawSeam_measure (P : Parameters) (h : ℕ) :
    ((streamLaw P ℕ).prod (streamLaw P ℕ)) {z | EmptyReducing (rawSeamWord (h+1) z)}=
      ((naturalPiecesLaw (rawLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))) (pieceSeamEvent (h+1)) := by
  let f := stoppedWord (firstUp (h+1))
  let g := fun x => (stoppedWord (firstDown (h+1)) x).reverse
  let l := fun x : ℕ → List Letter => piecesPrefix x (h+1)
  have hf : Measurable f := measurable_stoppedWord (firstUp_measurable (h+1))
  have hg : Measurable g := (measurable_of_countable List.reverse).comp (measurable_stoppedWord (firstDown_measurable (h+1)))
  have hl : Measurable l := piecesPrefix_measurable (h+1)
  have he : (((streamLaw P ℕ).prod (streamLaw P ℕ)).map (Prod.map f g))=
      ((naturalPiecesLaw (rawLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))).map (Prod.map l l) := by
    rw [← Measure.map_prod_map _ _ hf hg,← Measure.map_prod_map _ _ hl hl,
      (leftPrefix_identDistrib P h).map_eq,(chronologicalRight_identDistrib P h).map_eq]
  let E : Set (List Letter×List Letter) := {z | EmptyReducing (z.1++z.2)}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  have hh := congrArg (fun ν : Measure (List Letter×List Letter) => ν E) he
  rw [Measure.map_apply (hf.prodMap hg) hE,Measure.map_apply (hl.prodMap hl) hE] at hh
  exact hh

/-- Source ladder:uniform for the actual two independent raw hit intervals.
No conditioning on success or stopping-length moment is assumed. -/
theorem raw_seam_uniform (P : Parameters) : ∃ δ : ℝ,0<δ ∧ ∀ h : ℕ,0<h →
    ENNReal.ofReal δ≤((streamLaw P ℕ).prod (streamLaw P ℕ)) {z | EmptyReducing (rawSeamWord h z)} := by
  obtain ⟨δ,hδ,hbound⟩ := piece_seam_uniform P
  refine ⟨δ,hδ,?_⟩
  intro h hh
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
  rw [rawSeam_measure,pieceSeam_normal_measure (rawLeftLaw P) (shortLeftLaw P) (rightLaw P) (rawLeftLaw_normal P)]
  exact hbound (k+1)
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma sign_not (b : Bool) : sign (!b)= -sign b := by cases b <;> norm_num [sign]
def reflectPath {n : ℕ} (d : Path n) : Path n := fun i => !(d i)
lemma reflectPath_sum {n : ℕ} (d : Path n) (k : ℕ) : pathSum (reflectPath d) k= -pathSum d k := by
  unfold pathSum reflectPath
  simp only [sign_not,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp
lemma not_coin_preserving : MeasurePreserving Bool.not TreeCoding.coinLaw TreeCoding.coinLaw := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : Bool.not ⁻¹' {b}={!b} := by ext a; cases a <;> cases b <;> simp
  rw [he,TreeCoding.coinLaw_singleton,TreeCoding.coinLaw_singleton]
lemma reflectPath_preserving (n : ℕ) : MeasurePreserving (@reflectPath n)
    (Measure.pi (fun _ : Fin n => TreeCoding.coinLaw)) (Measure.pi (fun _ : Fin n => TreeCoding.coinLaw)) := by
  refine ⟨measurable_of_countable _,?_⟩
  change (Measure.pi _).map (fun d i => !(d i))=Measure.pi _
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable Bool.not).aemeasurable)]
  simp only [not_coin_preserving.map_eq]

end FKCRT.SimpleWalk
namespace FKCRT.Inventory

def rawUpperSurvival (a n : ℕ) : Set (ℕ → Letter) := {x | ∀ j≤n,0≤(a:ℤ)-signSum x j}
lemma rawUpperSurvival_measure (P : Parameters) (a n : ℕ) :
    streamLaw P ℕ (rawUpperSurvival a n)=streamLaw P ℕ (rawSurvival a n) := by
  let f := finiteSigns ∘ rawPrefix n
  let A : Set (SimpleWalk.Path n) := {d | SimpleWalk.nonnegativePath a d}
  have hp := (finiteSigns_preserving P n).comp (rawPrefix_preserving P n)
  have hu : rawUpperSurvival a n=(SimpleWalk.reflectPath ∘ f) ⁻¹' A := by
    ext x
    simp only [rawUpperSurvival,Set.mem_ofPred_eq,Set.mem_preimage,A,SimpleWalk.nonnegativePath,Function.comp_apply]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    rw [SimpleWalk.reflectPath_sum]
    change 0≤(a:ℤ)-signSum x j ↔ 0≤(a:ℤ)+ -SimpleWalk.pathSum (finiteSigns (rawPrefix n x)) j
    rw [raw_sign_pathSum x n j hj]
    rfl
  have hl : rawSurvival a n=f ⁻¹' A := by
    ext x
    simp only [rawSurvival,Set.mem_ofPred_eq,Set.mem_preimage,A,SimpleWalk.nonnegativePath]
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    change 0≤(a:ℤ)+signSum x j ↔ 0≤(a:ℤ)+SimpleWalk.pathSum (finiteSigns (rawPrefix n x)) j
    rw [raw_sign_pathSum x n j hj]
  rw [hu,hl,((SimpleWalk.reflectPath_preserving n).comp hp).measure_preimage (Set.to_countable A).measurableSet.nullMeasurableSet,
    hp.measure_preimage (Set.to_countable A).measurableSet.nullMeasurableSet]

lemma stoppedWord_length_of_hit {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter} {n : ℕ}
    (h : T x=WithTop.some n) : (stoppedWord T x).length=n+1 := by
  rw [stoppedWord_of_hit h]
  simp [revealed]
lemma stoppedWord_length_top {T : (ℕ → Letter) → WithTop ℕ} {x : ℕ → Letter}
    (h : T x=⊤) : (stoppedWord T x).length=1 := by simp [stoppedWord,h,revealed]
lemma down_length_tail_subset {h n : ℕ} (hh : 0<h) (hn : 0<n) :
    {x | n<(stoppedWord (firstDown h) x).length} ⊆ rawSurvival (h-1) n := by
  intro x hx
  obtain ht | ⟨k,hk⟩ := eq_or_ne (firstDown h x) ⊤ |>.imp_right (fun he => WithTop.ne_top_iff_exists.mp he)
  · simp only [Set.mem_ofPred_eq,stoppedWord_length_top ht] at hx
    omega
  · have hk' : firstDown h x=WithTop.some k := hk.symm
    rw [Set.mem_ofPred_eq,stoppedWord_length_of_hit hk'] at hx
    intro j hj
    have hp := firstDown_prefix_pos hh hk' (j := j) (by omega)
    have he : (↑(h-1):ℤ)=(h:ℤ)-1 := by omega
    rw [he]
    omega
lemma up_length_tail_subset {h n : ℕ} (hh : 0<h) (hn : 0<n) :
    {x | n<(stoppedWord (firstUp h) x).length} ⊆ rawUpperSurvival (h-1) n := by
  intro x hx
  obtain ht | ⟨k,hk⟩ := eq_or_ne (firstUp h x) ⊤ |>.imp_right (fun he => WithTop.ne_top_iff_exists.mp he)
  · simp only [Set.mem_ofPred_eq,stoppedWord_length_top ht] at hx
    omega
  · have hk' : firstUp h x=WithTop.some k := hk.symm
    rw [Set.mem_ofPred_eq,stoppedWord_length_of_hit hk'] at hx
    intro j hj
    have hp := firstUp_prefix_lt hh hk' (j := j) (by omega)
    have he : (↑(h-1):ℤ)=(h:ℤ)-1 := by omega
    rw [he]
    omega

/-- Both actual first-passage lengths obey the same uniform square-root tail. -/
theorem stopped_lengths_tail : ∃ C : ℝ,0<C ∧ ∀ (P : Parameters) (h n : ℕ),0<h → 0<n →
    (streamLaw P ℕ).real {x | n<(stoppedWord (firstDown h) x).length} ≤ C*h/Real.sqrt n ∧
    (streamLaw P ℕ).real {x | n<(stoppedWord (firstUp h) x).length} ≤ C*h/Real.sqrt n := by
  obtain ⟨C,hC,h⟩ := rawSurvival_bound
  refine ⟨C,hC,?_⟩
  intro P a n ha hn
  have hb := h P (a-1) n hn
  have he : ((a-1:ℕ):ℝ)+1=(a:ℝ) := by exact_mod_cast Nat.sub_add_cancel ha
  rw [he] at hb
  constructor
  · exact (measureReal_mono (down_length_tail_subset ha hn)).trans hb
  · apply le_trans (measureReal_mono (up_length_tail_subset ha hn))
    simpa only [measureReal_def,rawUpperSurvival_measure] using hb

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma rawSeamWord_length (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) :
    (rawSeamWord h z).length=(stoppedWord (firstUp h) z.1).length+(stoppedWord (firstDown h) z.2).length := by
  simp [rawSeamWord]
lemma rawSeam_length_tail {C : ℝ}
    (hC : ∀ (P : Parameters) (h n : ℕ),0<h → 0<n →
      (streamLaw P ℕ).real {x | n<(stoppedWord (firstDown h) x).length} ≤ C*h/Real.sqrt n ∧
      (streamLaw P ℕ).real {x | n<(stoppedWord (firstUp h) x).length} ≤ C*h/Real.sqrt n)
    (P : Parameters) (h n : ℕ) (hh : 0<h) (hn : 0<n) :
    ((streamLaw P ℕ).prod (streamLaw P ℕ)).real {z | 2*n<(rawSeamWord h z).length} ≤ 2*C*h/Real.sqrt n := by
  let U : Set (ℕ → Letter) := {x | n<(stoppedWord (firstUp h) x).length}
  let D : Set (ℕ → Letter) := {x | n<(stoppedWord (firstDown h) x).length}
  have hU : MeasurableSet U := (Set.to_countable {w : List Letter | n<w.length}).measurableSet.preimage
    (measurable_stoppedWord (firstUp_measurable h))
  have hD : MeasurableSet D := (Set.to_countable {w : List Letter | n<w.length}).measurableSet.preimage
    (measurable_stoppedWord (firstDown_measurable h))
  have hs : {z | 2*n<(rawSeamWord h z).length} ⊆ Prod.fst ⁻¹' U ∪ Prod.snd ⁻¹' D := by
    intro z hz
    rw [Set.mem_ofPred_eq,rawSeamWord_length] at hz
    change n<(stoppedWord (firstUp h) z.1).length ∨ n<(stoppedWord (firstDown h) z.2).length
    omega
  apply (measureReal_mono hs).trans
  apply (measureReal_union_le _ _).trans
  have hf := (measurePreserving_fst (μ := streamLaw P ℕ) (ν := streamLaw P ℕ)).measure_preimage hU.nullMeasurableSet
  have hg := (measurePreserving_snd (μ := streamLaw P ℕ) (ν := streamLaw P ℕ)).measure_preimage hD.nullMeasurableSet
  simp only [measureReal_def,hf,hg]
  have hb := hC P h n hh hn
  change _+_≤_
  dsimp only [U,D] at *
  dsimp only [measureReal_def] at hb
  calc
    _ ≤ C*h/Real.sqrt n+C*h/Real.sqrt n := add_le_add hb.2 hb.1
    _ = _ := by ring

/-- Successful genuine seam intervals have a uniform positive probability of
quadratic length; no independence of length and success is used. -/
theorem short_seam_uniform (P : Parameters) : ∃ (δ : ℝ) (A : ℕ),0<δ ∧ 0<A ∧ ∀ h : ℕ,0<h →
    δ ≤ ((streamLaw P ℕ).prod (streamLaw P ℕ)).real
      {z | EmptyReducing (rawSeamWord h z) ∧ (rawSeamWord h z).length≤2*A*h^2} := by
  obtain ⟨δ,hδ,hsuccess⟩ := raw_seam_uniform P
  obtain ⟨C,hC,htail⟩ := stopped_lengths_tail
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 (4*C/δ))
  have hk1 : 1<(k:ℝ) := lt_of_le_of_lt (le_max_left _ _) hk
  have hk0 : 0<k := by exact_mod_cast (lt_trans zero_lt_one hk1)
  have hkC : 4*C/δ<(k:ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
  have hsmall : 2*C/(k:ℝ)≤δ/2 := by
    have hkd : 4*C<(k:ℝ)*δ := (div_lt_iff₀ hδ).mp hkC
    apply (div_le_iff₀ (by positivity : 0<(k:ℝ))).mpr
    nlinarith
  refine ⟨δ/2, k^2,by positivity,by positivity,?_⟩
  intro h hh
  let μ := (streamLaw P ℕ).prod (streamLaw P ℕ)
  let S : Set ((ℕ → Letter) × (ℕ → Letter)) := {z | EmptyReducing (rawSeamWord h z)}
  let T : Set ((ℕ → Letter) × (ℕ → Letter)) := {z | 2*k^2*h^2<(rawSeamWord h z).length}
  have hs : δ≤μ.real S := by
    have he := ENNReal.toReal_mono (measure_ne_top μ S) (hsuccess h hh)
    change δ≤(μ S).toReal
    simpa only [ENNReal.toReal_ofReal hδ.le] using he
  have ht : μ.real T≤δ/2 := by
    have he : 2*(k*h)^2=2*k^2*h^2 := by ring
    have hb := rawSeam_length_tail htail P h ((k*h)^2) hh (by positivity)
    rw [he] at hb
    have hden : Real.sqrt (((k*h)^2:ℕ):ℝ)=(k:ℝ)*h := by
      push_cast
      rw [Real.sqrt_sq (by positivity)]
    rw [hden] at hb
    have heq : 2*C*(h:ℝ)/((k:ℝ)*h)=2*C/(k:ℝ) := by
      have hhR : (h:ℝ)≠0 := by positivity
      field_simp
    rw [heq] at hb
    exact hb.trans hsmall
  have he : S\T={z | EmptyReducing (rawSeamWord h z) ∧ (rawSeamWord h z).length≤2*k^2*h^2} := by
    ext z
    simp only [Set.mem_sdiff,Set.mem_ofPred_eq,S,T,not_lt]
  have hd := le_measureReal_sdiff (μ := μ) (s₁ := S) (s₂ := T)
  rw [he] at hd
  change δ/2≤μ.real _
  linarith

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def letterSplit (l r : ℕ) : (Fin (l+r) → Letter) ≃ᵐ ((Fin l → Letter) × (Fin r → Letter)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (l+r) => Letter) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin l ⊕ Fin r => Letter))
lemma letterSplit_preserving (P : Parameters) (l r : ℕ) :
    MeasurePreserving (letterSplit l r) (Measure.pi (fun _ : Fin (l+r) => (law P).toMeasure))
      ((Measure.pi (fun _ : Fin l => (law P).toMeasure)).prod (Measure.pi (fun _ : Fin r => (law P).toMeasure))) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin l ⊕ Fin r => (law P).toMeasure)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (l+r) => (law P).toMeasure) finSumFinEquiv).symm
lemma letterSplit_word (l r : ℕ) (w : Fin (l+r) → Letter) :
    List.ofFn (letterSplit l r w).1++List.ofFn (letterSplit l r w).2=List.ofFn w := by
  exact List.ofFn_add.symm

def reverseLetters (l : ℕ) : (Fin l → Letter) ≃ᵐ (Fin l → Letter) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin l => Letter) Fin.revPerm
lemma reverseLetters_apply (l : ℕ) (w : Fin l → Letter) (i : Fin l) : reverseLetters l w i=w i.rev := by
  simpa only [Fin.revPerm_apply,Fin.rev_rev,reverseLetters] using
    MeasurableEquiv.piCongrLeft_apply_apply Fin.revPerm (β := fun _ : Fin l => Letter) w i.rev
lemma reverseLetters_word (l : ℕ) (w : Fin l → Letter) : List.ofFn (reverseLetters l w)=(List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_reverse]
    rw [reverseLetters_apply]
    congr 1
    apply Fin.ext
    simp only [Fin.rev,Fin.val_mk,List.length_ofFn]
    omega
lemma reverseLetters_preserving (P : Parameters) (l : ℕ) : MeasurePreserving (reverseLetters l)
    (Measure.pi (fun _ : Fin l => (law P).toMeasure)) (Measure.pi (fun _ : Fin l => (law P).toMeasure)) :=
  measurePreserving_piCongrLeft (fun _ : Fin l => (law P).toMeasure) Fin.revPerm

def seamWord (l r : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : List Letter := revealed z.1 l++rawWord z.2 r
lemma seamWord_measurable (l r : ℕ) : Measurable (seamWord l r) :=
  (measurable_of_countable (fun z : List Letter×List Letter => z.1++z.2)).comp
    (((measurable_revealed l).comp measurable_fst).prodMk
      (((measurable_of_countable List.ofFn).comp (rawPrefix_measurable r)).comp measurable_snd))
lemma seamWord_preserving (P : Parameters) (l r : ℕ) : IdentDistrib (seamWord l r)
    (fun x => rawWord x (l+r)) ((streamLaw P ℕ).prod (streamLaw P ℕ)) (streamLaw P ℕ) := by
  let f := (letterSplit l r).symm ∘ Prod.map (reverseLetters l) id ∘ Prod.map (rawPrefix l) (rawPrefix r)
  have hp : MeasurePreserving f _ (Measure.pi (fun _ : Fin (l+r) => (law P).toMeasure)) :=
    (letterSplit_preserving P l r).symm.comp
      (((reverseLetters_preserving P l).prod (MeasurePreserving.id _)).comp
        ((rawPrefix_preserving P l).prod (rawPrefix_preserving P r)))
  have hi := hp.hasLaw.identDistrib (rawPrefix_preserving P (l+r)).hasLaw
  have hh := hi.comp (measurable_of_countable List.ofFn)
  convert hh using 1
  · funext z
    change revealed z.1 l++rawWord z.2 r=List.ofFn (f z)
    rw [← letterSplit_word l r]
    simp only [f,Function.comp_apply,MeasurableEquiv.apply_symm_apply]
    change revealed z.1 l++rawWord z.2 r=List.ofFn (reverseLetters l (rawPrefix l z.1))++List.ofFn (rawPrefix r z.2)
    rw [reverseLetters_word]
    rfl
  · rfl

lemma seamWord_empty_measure (P : Parameters) (l r : ℕ) :
    ((streamLaw P ℕ).prod (streamLaw P ℕ)).real {z | EmptyReducing (seamWord l r z)}=emptyProb P (l+r) := by
  have h := (seamWord_preserving P l r).map_eq
  have he := congrArg (fun μ : Measure (List Letter) => μ {w | EmptyReducing w}) h
  have hm : Measurable (fun x => rawWord x (l+r)) :=
    (measurable_of_countable List.ofFn).comp (rawPrefix_measurable (l+r))
  rw [Measure.map_apply (seamWord_measurable l r) (Set.to_countable _).measurableSet,
    Measure.map_apply hm (Set.to_countable _).measurableSet] at he
  exact congrArg ENNReal.toReal he

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockCritical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

lemma stoppedWord_length_pos (T : (ℕ → Letter) → WithTop ℕ) (x : ℕ → Letter) :
    0<(stoppedWord T x).length := by simp [stoppedWord,revealed]
lemma rawSeamWord_seamWord (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) :
    rawSeamWord h z=seamWord (stoppedWord (firstUp h) z.1).length (stoppedWord (firstDown h) z.2).length z := by
  simp only [rawSeamWord,seamWord,stoppedWord,revealed,rawWord,rawPrefix,
    List.length_reverse,List.length_ofFn,List.reverse_reverse,Fin.val_cast]
lemma up_length_injective {x : ℕ → Letter} {a b : ℕ}
    (ha : firstUp a x≠⊤) (hb : firstUp b x≠⊤)
    (he : (stoppedWord (firstUp a) x).length=(stoppedWord (firstUp b) x).length) : a=b := by
  obtain ⟨i,hi⟩ := WithTop.ne_top_iff_exists.mp ha
  obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp hb
  have hei := stoppedWord_length_of_hit hi.symm
  have hej := stoppedWord_length_of_hit hj.symm
  have hij : i=j := by omega
  subst j
  have h1 := (firstUp_of_hit_iff a x i).mp hi.symm |>.1
  have h2 := (firstUp_of_hit_iff b x i).mp hj.symm |>.1
  omega

def shortSeamSuccess (A h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : Prop :=
  EmptyReducing (rawSeamWord h z) ∧ (rawSeamWord h z).length≤2*A*h^2
lemma shortSeamSuccess_measurable (A h : ℕ) : MeasurableSet {z | shortSeamSuccess A h z} :=
  (Set.to_countable {w : List Letter | EmptyReducing w ∧ w.length≤2*A*h^2}).measurableSet.preimage (rawSeamWord_measurable h)
lemma seam_count_le (A H : ℕ) (z : (ℕ → Letter) × (ℕ → Letter))
    (hfinite : ∀ h : ℕ,0<h → firstUp h z.1≠⊤) :
    (∑ h∈Finset.Icc 1 H,if shortSeamSuccess A h z then (1:ℝ) else 0) ≤
      ∑ i∈seamIntervals (2*A*H^2),if EmptyReducing (seamWord (i.1+1) (i.2+1) z) then (1:ℝ) else 0 := by
  let f : ℕ → ℕ×ℕ := fun h => ((stoppedWord (firstUp h) z.1).length-1,(stoppedWord (firstDown h) z.2).length-1)
  apply sum_ite_le_of_injection _ _ _ _ f
  · intro h hh hs
    have hh' := Finset.mem_Icc.mp hh
    have hle : h^2≤H^2 := Nat.pow_le_pow_left hh'.2 2
    have hp1 := stoppedWord_length_pos (firstUp h) z.1
    have hp2 := stoppedWord_length_pos (firstDown h) z.2
    have hlen := hs.2
    rw [rawSeamWord_length] at hlen
    constructor
    · rw [mem_seamIntervals]
      dsimp [f]
      have := Nat.mul_le_mul_left (2*A) hle
      omega
    · change EmptyReducing (seamWord ((stoppedWord (firstUp h) z.1).length-1+1)
        ((stoppedWord (firstDown h) z.2).length-1+1) z)
      rw [Nat.sub_add_cancel hp1,Nat.sub_add_cancel hp2,← rawSeamWord_seamWord]
      exact hs.1
  · intro a ha _ b hb _ he
    have hab := congrArg Prod.fst he
    have hp1 := stoppedWord_length_pos (firstUp a) z.1
    have hp2 := stoppedWord_length_pos (firstUp b) z.1
    apply up_length_injective (hfinite a (by have := (Finset.mem_Icc.mp ha).1; omega))
      (hfinite b (by have := (Finset.mem_Icc.mp hb).1; omega))
    dsimp [f] at hab
    omega

lemma interval_expected_count (P : Parameters) (K : ℕ) :
    (∑ i∈seamIntervals K,((streamLaw P ℕ).prod (streamLaw P ℕ)).real
      {z | EmptyReducing (seamWord (i.1+1) (i.2+1) z)})=
      ∑ N∈Finset.range (K+1),(N+1:ℝ)*emptyProb P (N+2) := by
  rw [sum_seamIntervals]
  apply Finset.sum_congr rfl
  intro N _
  simp_rw [seamWord_empty_measure]
  calc
    _ = ∑ _i∈Finset.HasAntidiagonal.antidiagonal N,emptyProb P (N+2) := by
      apply Finset.sum_congr rfl
      intro i hi
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
      congr 1
      omega
    _ = _ := by simp

/-- Counting the actual distinct stopped seam intervals gives quantitative
quadratic-scale partial-sum lower bounds for the exact empty-word probabilities. -/
theorem emptyProb_partial_lower (P : Parameters) : ∃ (δ : ℝ) (A : ℕ),0<δ ∧ 0<A ∧ ∀ H : ℕ,
    δ*H ≤ ∑ N∈Finset.range (2*A*H^2+1),(N+1:ℝ)*emptyProb P (N+2) := by
  obtain ⟨δ,A,hδ,hA,h⟩ := short_seam_uniform P
  refine ⟨δ,A,hδ,hA,?_⟩
  intro H
  let μ := (streamLaw P ℕ).prod (streamLaw P ℕ)
  let S := Finset.Icc 1 H
  let T := seamIntervals (2*A*H^2)
  let F (h : ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : ℝ := if shortSeamSuccess A h z then 1 else 0
  let G (i : ℕ×ℕ) (z : (ℕ → Letter) × (ℕ → Letter)) : ℝ := if EmptyReducing (seamWord (i.1+1) (i.2+1) z) then 1 else 0
  have hF (h : ℕ) : Integrable (F h) μ := (integrable_const (1:ℝ)).indicator (shortSeamSuccess_measurable A h)
  have hG (i : ℕ×ℕ) : Integrable (G i) μ := (integrable_const (1:ℝ)).indicator
    ((Set.to_countable {w | EmptyReducing w}).measurableSet.preimage (seamWord_measurable (i.1+1) (i.2+1)))
  have heF (h : ℕ) : (∫ z,F h z ∂μ)=μ.real {z | shortSeamSuccess A h z} := integral_indicator_one (shortSeamSuccess_measurable A h)
  have heG (i : ℕ×ℕ) : (∫ z,G i z ∂μ)=μ.real {z | EmptyReducing (seamWord (i.1+1) (i.2+1) z)} :=
    integral_indicator_one ((Set.to_countable {w | EmptyReducing w}).measurableSet.preimage (seamWord_measurable (i.1+1) (i.2+1)))
  have hfin : ∀ᵐ z ∂μ,∀ h : ℕ,0<h → firstUp h z.1≠⊤ := by
    apply ae_all_iff.mpr
    intro h
    by_cases hh : 0<h
    · filter_upwards [(measurePreserving_fst (μ := streamLaw P ℕ) (ν := streamLaw P ℕ)).quasiMeasurePreserving.ae (firstUp_finite P h hh)] with z hz _
      exact hz
    · exact Filter.Eventually.of_forall (fun z hz => (hh hz).elim)
  have hm : (∫ z,∑ h∈S,F h z ∂μ)≤∫ z,∑ i∈T,G i z ∂μ := by
    apply integral_mono_ae (integrable_finsetSum _ (fun h _ => hF h)) (integrable_finsetSum _ (fun i _ => hG i))
    filter_upwards [hfin] with z hz
    exact seam_count_le A H z hz
  rw [integral_finsetSum _ (fun h _ => hF h),integral_finsetSum _ (fun i _ => hG i)] at hm
  simp_rw [heF,heG] at hm
  rw [interval_expected_count] at hm
  apply le_trans _ hm
  calc
    δ*(H:ℝ) = ∑ _h∈S,δ := by simp [S]; ring
    _ ≤ _ := Finset.sum_le_sum (fun j hj => h j (by have := (Finset.mem_Icc.mp hj).1; omega))

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

lemma increment_sum_parity (w : List Letter) :
    (w.map Letter.increment).sum%2=(w.length:ℤ)%2 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a <;> simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,Letter.increment] <;> omega
lemma emptyReducing_even {w : List Letter} (h : EmptyReducing w) : Even w.length := by
  have hp := increment_sum_parity w
  rw [(emptyReducing_dyck w h).1] at hp
  exact ⟨w.length/2,by omega⟩
lemma emptyProb_odd (P : Parameters) (N : ℕ) : emptyProb P (2*N+1)=0 := by
  have he : {x | EmptyReducing (rawWord x (2*N+1))}=∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨j,hj⟩ := emptyReducing_even hx
    simp only [rawWord,List.length_ofFn] at hj
    omega
  simp only [emptyProb,he,measureReal_empty]
lemma emptyProb_le_one (P : Parameters) (N : ℕ) : emptyProb P N≤1 := measureReal_le_one

lemma empty_interval_pair_sum (P : Parameters) (M : ℕ) :
    (∑ N∈Finset.range (2*M+1),(N+1:ℝ)*emptyProb P (N+2))=
      ∑ n∈Finset.range (M+1),(2*n+1:ℝ)*emptyProb P (2*(n+1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2*(M+1)+1=(2*M+1)+1+1 by omega,Finset.sum_range_succ (n := 2*M+1+1),Finset.sum_range_succ (n := 2*M+1),ih,Finset.sum_range_succ (n := M+1)]
    rw [show 2*M+1+2=2*(M+1)+1 by omega,emptyProb_odd]
    simp only [mul_zero,add_zero]
    congr 1
    push_cast
    congr 1; ring

lemma empty_even_partial_lower (P : Parameters) : ∃ (δ : ℝ) (A : ℕ),0<δ ∧ 0<A ∧ ∀ H : ℕ,
    δ*H≤∑ n∈Finset.range (2*A*H^2+1),(n:ℝ)*emptyProb P (2*n) := by
  obtain ⟨δ,A,hδ,hA,h⟩ := emptyProb_partial_lower P
  refine ⟨δ/2,A+1,by positivity,by omega,?_⟩
  intro H
  by_cases hH : H=0
  · simp [hH]
  have hH1 : 1≤H := by omega
  have hsquare : 1≤H^2 := by nlinarith
  have hle : A*H^2+2≤2*(A+1)*H^2+1 := by nlinarith
  have hp := h H
  rw [show 2*A*H^2=2*(A*H^2) by ring,empty_interval_pair_sum] at hp
  have hi : (∑ n∈Finset.range (A*H^2+1),(2*n+1:ℝ)*emptyProb P (2*(n+1)))≤
      2*(∑ n∈Finset.range (A*H^2+2),(n:ℝ)*emptyProb P (2*n)) := by
    rw [show A*H^2+2=(A*H^2+1)+1 by omega,Finset.sum_range_succ' (n := A*H^2+1)]
    simp only [Nat.cast_zero,zero_mul,add_zero,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have := emptyProb_nonneg P (2*(n+1))
    push_cast
    nlinarith
  have hj := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hle)
    (fun n _ _ => mul_nonneg (Nat.cast_nonneg n) (emptyProb_nonneg P (2*n)))
  nlinarith [hp.trans hi]

lemma summable_empty_abel (P : Parameters) {x : ℝ} (hx : 0≤x) (hx' : x<1) :
    Summable (fun n : ℕ => (n:ℝ)*emptyProb P (2*n)*x^n) := by
  have hs : Summable (fun n : ℕ => (n:ℝ)*x^n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx')
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (emptyProb_nonneg P (2*n))) (pow_nonneg hx n)) (fun n => ?_) hs
  have h := mul_le_mul_of_nonneg_left (emptyProb_le_one P (2*n)) (Nat.cast_nonneg n : (0:ℝ)≤n)
  exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using h) (pow_nonneg hx _)

/-- The exact genuine iid inventory empty-word coefficients satisfy the source
Abel square-root lower bound; no map-counting identity is assumed here. -/
theorem empty_abel_lower (P : Parameters) : ∃ c : ℝ,0 < c ∧ ∀ x : ℝ,(3:ℝ)/4≤x → x<1 →
    c/Real.sqrt (1-x)≤∑' n : ℕ,(n:ℝ)*emptyProb P (2*n)*x^n := by
  obtain ⟨δ,A,hδ,_,hpartial⟩ := empty_even_partial_lower P
  obtain ⟨c,hc,h⟩ := Analysis.quadratic_partial_abel_lower (fun n => (n:ℝ)*emptyProb P (2*n))
    (fun n => mul_nonneg (Nat.cast_nonneg n) (emptyProb_nonneg P (2*n))) δ hδ A hpartial
  exact ⟨c,hc,fun x hx hx' => h x hx hx' (summable_empty_abel P (by linarith) hx')⟩

end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BlockLaw
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSingletonClass _root_.OAI.FKCRT.Inventory.CoreLabel.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory

def emptyWeights (P : Parameters) : BlockCritical.Weights where
  mass n := emptyProb P (2*n)/emptyTotal P
  nonneg n := div_nonneg (emptyProb_nonneg P (2*n)) (emptyTotal_pos P).le
  total := by
    have hh := (emptyProb_even_summable P).hasSum.div_const (emptyTotal P)
    change HasSum (fun n => emptyProb P (2*n)/emptyTotal P) (emptyTotal P/emptyTotal P) at hh
    simpa only [div_self (emptyTotal_pos P).ne'] using hh

/-- The normalized exact word coefficient law has the required near-endpoint
Abel lower bound. The remaining bridge to map coefficients is combinatorial. -/
theorem emptyWeights_abel_lower (P : Parameters) : ∃ c : ℝ,0 < c ∧ ∀ x : ℝ,(3:ℝ)/4≤x → x<1 →
    c≤Real.sqrt (1-x)*(emptyWeights P).abelMean x := by
  obtain ⟨c,hc,h⟩ := empty_abel_lower P
  refine ⟨c/emptyTotal P,div_pos hc (emptyTotal_pos P),?_⟩
  intro x hx hx'
  have hs : 0<Real.sqrt (1-x) := Real.sqrt_pos.mpr (by linarith)
  have he : (emptyWeights P).abelMean x=(∑' n : ℕ,(n:ℝ)*emptyProb P (2*n)*x^n)/emptyTotal P := by
    rw [BlockCritical.Weights.abelMean,← tsum_div_const]
    apply tsum_congr
    intro n
    change (n:ℝ)*(emptyProb P (2*n)/emptyTotal P)*x^n=((n:ℝ)*emptyProb P (2*n)*x^n)/emptyTotal P
    ring
  rw [he]
  have hl := (div_le_iff₀ hs).mp (h x hx hx')
  have := div_le_div_of_nonneg_right hl (emptyTotal_pos P).le
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using this

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma typedCoefficient_inventory (P : Parameters) (m : ℕ) :
    typedCoefficient (ENNReal.ofReal (flexParameter P)) m*
      (ENNReal.ofReal (radiusParameter P))^m=ENNReal.ofReal (emptyProb P (2*m)) := by
  have h : emptyProb P (2*m)=radiusParameter P^m*
      ∑ v∈typedEmptyWords (2*m),flexParameter P^flexibleCount v [] := by
    rw [emptyProb,rawEmpty_real,empty_wordMass_sum]
    rfl
  rw [h,typedCoefficient,ENNReal.ofReal_mul (pow_nonneg (radiusParameter_pos P).le _),
    ENNReal.ofReal_pow (radiusParameter_pos P).le,ENNReal.ofReal_sum_of_nonneg]
  · rw [mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    exact (ENNReal.ofReal_pow (flexParameter_pos P).le _).symm
  · intro w _
    exact pow_nonneg (flexParameter_pos P).le _

lemma wordSeries_inventory (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    wordSeries (ENNReal.ofReal (flexParameter P))
      (ENNReal.ofReal (Real.sqrt (radiusParameter P*x)))=ENNReal.ofReal (inventorySeries P x) := by
  have hu : 0 ≤ radiusParameter P*x := mul_nonneg (radiusParameter_pos P).le hx
  rw [wordSeries_coefficients,← ENNReal.ofReal_pow (Real.sqrt_nonneg _),Real.sq_sqrt hu,
    ENNReal.ofReal_mul (radiusParameter_pos P).le]
  simp_rw [mul_pow,← mul_assoc,typedCoefficient_inventory]
  unfold inventorySeries
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg (emptyProb_nonneg P _) (pow_nonneg hx _))
    (inventorySeries_summable P hx hx')]
  apply tsum_congr
  intro m
  rw [ENNReal.ofReal_mul (emptyProb_nonneg P _),ENNReal.ofReal_pow hx]

/-- A real HasSum form of the exact root-corner substitution, derived from
finite endpoint summability rather than assumed analytic convergence. -/
theorem actual_core_series (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    HasSum (fun m => coreCoefficientReal (flexParameter P) m*
      (radiusParameter P*x*(inventorySeries P x)^2)^m) (inventorySeries P x-1) := by
  let t := flexParameter P
  let u := radiusParameter P*x*(inventorySeries P x)^2
  have hu : 0 ≤ u := mul_nonneg (mul_nonneg (radiusParameter_pos P).le hx) (sq_nonneg _)
  have he : ENNReal.ofReal (inventorySeries P x)=1+
      ∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal t m*u^m) := by
    have h := wordSeries_core_coefficients (ENNReal.ofReal t)
      (ENNReal.ofReal (Real.sqrt (radiusParameter P*x)))
    rw [wordSeries_inventory P hx hx'] at h
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),Real.sq_sqrt (mul_nonneg (radiusParameter_pos P).le hx)] at h
    rw [← ENNReal.ofReal_pow (inventorySeries_nonneg P hx),
      ← ENNReal.ofReal_mul (mul_nonneg (radiusParameter_pos P).le hx)] at h
    simpa only [coreCoefficient_ofReal (flexParameter_pos P).le,
      ENNReal.ofReal_mul (coreCoefficientReal_nonneg (flexParameter_pos P).le _),
      ENNReal.ofReal_pow hu,t,u] using h
  have hf : (∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal t m*u^m))≠∞ := by
    intro hh
    rw [hh,add_top] at he
    exact ENNReal.ofReal_ne_top he
  have hs := ENNReal.hasSum_toReal hf
  have hv : (∑' m : ℕ,ENNReal.ofReal (coreCoefficientReal t m*u^m)).toReal=
      inventorySeries P x-1 := by
    have h := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_add ENNReal.one_ne_top hf,ENNReal.toReal_one,
      ENNReal.toReal_ofReal (inventorySeries_nonneg P hx)] at h
    linarith
  rw [← ENNReal.tsum_toReal_eq (fun m => ENNReal.ofReal_ne_top),hv] at hs
  simpa only [ENNReal.toReal_ofReal (mul_nonneg
    (coreCoefficientReal_nonneg (flexParameter_pos P).le _) (pow_nonneg hu _)),t,u] using hs

end FKCRT.Inventory
end


noncomputable section
open Filter
open scoped BigOperators Topology
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

lemma inventorySeries_pgf (P : Parameters) (x : ℝ) :
    (emptyWeights P).pgf x=inventorySeries P x/emptyTotal P := by
  rw [BlockCritical.Weights.pgf,inventorySeries,← tsum_div_const]
  apply tsum_congr
  intro m
  change (emptyProb P (2*m)/emptyTotal P)*x^m=(emptyProb P (2*m)*x^m)/emptyTotal P
  ring

lemma actual_block_series (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    HasSum (fun m => blockCoefficientReal (flexParameter P) m*
      (radiusParameter P*x*(inventorySeries P x)^2)^m) (inventorySeries P x) := by
  have hs := (hasSum_ite_eq (0:ℕ) (1:ℝ)).add (actual_core_series P hx hx')
  have he : 1+(inventorySeries P x-1)=inventorySeries P x := by ring
  rw [he] at hs
  apply hs.congr_fun
  intro m
  by_cases hm : m=0
  · simp [hm,blockCoefficientReal]
  · simp [hm,blockCoefficientReal]

/-- The actual connected-core coefficients satisfy precisely the normalized
inverse equation required by the analytic criticality proof. -/
lemma actual_inverse_equation (P : Parameters) {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    HasSum (fun m => actualBlockMass P m*(x*((emptyWeights P).pgf x)^2)^m)
      ((emptyWeights P).pgf x) := by
  have hs := (actual_block_series P hx hx').div_const (emptyTotal P)
  rw [← inventorySeries_pgf] at hs
  apply hs.congr_fun
  intro m
  have hτ := (emptyTotal_pos P).ne'
  have hid : radiusParameter P*(emptyTotal P)^2*(x*((emptyWeights P).pgf x)^2)=
      radiusParameter P*x*(inventorySeries P x)^2 := by
    rw [inventorySeries_pgf]
    field_simp
  dsimp [actualBlockMass]
  rw [← hid,mul_pow]
  ring

/-- Criticality and the finite second moment for the genuine block series.
The only assumptions are the original p∈(1/2,1); no block-law or moment
conclusion is postulated. -/
theorem actual_block_moments (P : Parameters) :
    HasSum (actualBlockMass P) 1 ∧
      HasSum (fun m : ℕ => (m:ℝ)*actualBlockMass P m) (1/2) ∧
      Summable (fun m : ℕ => (m:ℝ)^2*actualBlockMass P m) := by
  obtain ⟨c,hc,hc'⟩ := emptyWeights_abel_lower P
  exact BlockCritical.normalized_inverse_critical (emptyWeights P) (actualBlockMass_nonneg P)
    (fun n => ⟨by linarith [(criticalApproach_bounds n).1],(criticalApproach_bounds n).2⟩)
    criticalApproach_tendsto
    (fun n => actual_inverse_equation P (by linarith [(criticalApproach_bounds n).1])
      (criticalApproach_bounds n).2.le)
    hc (fun n => hc' _ (criticalApproach_bounds n).1 (criticalApproach_bounds n).2)

end FKCRT.Inventory
end


noncomputable section
open List
open scoped BigOperators
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreTree

abbrev LabelExcursion := {l : List CoreLabel // FKCRT.TreeCoding.IsExcursionList
  (FKCRT.TreeCoding.PlaneTree.incrementWord (l.map CoreLabel.arity))}

end CoreTree
end FKCRT.Inventory
end


noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable

namespace CoreLabel

lemma rootMass_total (P : Parameters) :
    (∑' c : CoreLabel,ENNReal.ofReal (rootMass P c))=1 := by
  have h := rootMass_by_size P (fun _ => 1)
  simp only [mul_one] at h
  rw [h,← ENNReal.ofReal_tsum_of_nonneg (actualBlockMass_nonneg P)
    (actual_block_moments P).1.summable,(actual_block_moments P).1.tsum_eq]
  simp

def rootLaw (P : Parameters) : PMF CoreLabel :=
  ⟨fun c => ENNReal.ofReal (rootMass P c),(rootMass_total P) ▸ ENNReal.summable.hasSum⟩

end CoreLabel
end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineMoments
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
attribute [local instance] Classical.propDecidable
namespace CoreLabel

lemma rootMass_pos (P : Parameters) (c : CoreLabel) : 0 < rootMass P c := by
  cases c with
  | none => exact div_pos zero_lt_one (emptyTotal_pos P)
  | some c =>
    exact div_pos (mul_pos (pow_pos (flexParameter_pos P) _)
      (pow_pos (mul_pos (Real.sqrt_pos.mpr (radiusParameter_pos P)) (emptyTotal_pos P)) _))
      (emptyTotal_pos P)

lemma rootLaw_pos (P : Parameters) (c : CoreLabel) : 0 < rootLaw P c :=
  ENNReal.ofReal_pos.mpr (rootMass_pos P c)

/-- Actual conditional root-core marks. The arbitrary probability at an
unattainable arity is never used by the offspring distribution. -/
def markLaw (P : Parameters) (k : ℕ) : PMF CoreLabel :=
  if h : ∃ c : CoreLabel,c.arity=k then
    (rootLaw P).filter {c | c.arity=k} (by
      obtain ⟨c,hc⟩ := h
      exact ⟨c,hc,(rootLaw_pos P c).ne'⟩)
  else PMF.pure none

end CoreLabel
end FKCRT.Inventory
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ConditionedTrees
attribute [-instance] _root_.OAI.FKCRT.Inventory.Core.instFintypeVertexFinLengthTypedLetterValListCoreWordRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

namespace CoreTree

abbrev MarkedCode (N : ℕ) := {x : Code N × (Fin N → CoreLabel) // ∀ i,(x.2 i).arity=(x.1.val i).val}

abbrev Sized (N : ℕ) := {T : CoreTree // T.labels.length=N}

end CoreTree

end FKCRT.Inventory
end


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

namespace CoreTree

abbrev SizedWord (N : ℕ) := {w : EmptyTypedWord // w.val.length=N}

end CoreTree

end FKCRT.Inventory
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CoreMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- Literal darts of the recursively substituted word; no quotient identifies
any darts of distinct blocks. -/
def Dart : CoreTree → Type
  | .leaf => Empty
  | .branch c ts => Fin c.val.length ⊕ (Σ i : Fin c.val.length, Dart (ts i))

instance instDecidableEqDart (t : CoreTree) : DecidableEq t.Dart := Classical.decEq _

def dartLabel : (t : CoreTree) → t.Dart → TypedLetter
  | .leaf,d => d.elim
  | .branch c _ts,.inl i => c.val.get i
  | .branch _c ts,.inr ⟨i,d⟩ => dartLabel (ts i) d

def childDart {c : Core} (ts : Fin c.val.length→ CoreTree) (i : Fin c.val.length)
    (d : (ts i).Dart) : (branch c ts).Dart := .inr ⟨i,d⟩

def coreDart {c : Core} (ts : Fin c.val.length→ CoreTree) (i : Fin c.val.length) :
    (branch c ts).Dart := .inl i

def darts : (t : CoreTree) → List t.Dart
  | .leaf => []
  | .branch _ ts => (List.finRange _).flatMap fun i =>
      coreDart ts i::((ts i).darts.map (childDart ts i))

lemma darts_word (t : CoreTree) : t.darts.map t.dartLabel=t.word := by
  induction t with
  | leaf => rfl
  | branch c ts ih =>
    simp only [darts,List.map_flatMap,List.map_cons,List.map_map]
    change (List.finRange c.val.length).flatMap (fun i =>
      c.val.get i :: List.map ((ts i).dartLabel) (ts i).darts)=_
    simp_rw [ih]
    simp only [word,cornerInsert,cornerList,List.ofFn_eq_map,List.flatMap_map]

def matching (t : CoreTree) : StackMatching t.dartLabel t.darts :=
  StackMatching.ofEmpty (by rw [darts_word];exact t.word_empty)

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

def nextSlot (c : Core) (i : Fin c.val.length) : Fin c.val.length :=
  (List.finRange c.val.length).formPerm i

end FKCRT.Inventory.CoreTree
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

/-- Actual ordered-tree nodes, with a distinct trivial leaf at every empty
corner word. Coincident map poles are not identified as tree nodes. -/
def Node : CoreTree → Type
  | .leaf => PUnit
  | .branch c ts => PUnit ⊕ (Σ i : Fin c.val.length,Node (ts i))

def pole : (t : CoreTree) → t.Node → Option t.Dart
  | .leaf,_ => none
  | .branch c ts,.inl _ => some (coreDart ts c.entry)
  | .branch c ts,.inr ⟨i,v⟩ =>
    some (((pole (ts i) v).map (childDart ts i)).getD (coreDart ts (nextSlot c i)))

end FKCRT.Inventory.CoreTree
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

def childPole (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) (v : (ts i).Node) :
    (branch c ts).Dart :=
  (((ts i).pole v).map (childDart ts i)).getD (coreDart ts (nextSlot c i))

end FKCRT.Inventory.CoreTree
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_NodeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open List Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open TreeCoding
attribute [local instance] Classical.propDecidable

def before (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) : List CoreTree :=
  (List.ofFn ts).take i.val

def after (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) : List CoreTree :=
  (List.ofFn ts).drop (i.val+1)

lemma children_split (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    List.ofFn ts=before c ts i++ts i::after c ts i := by
  have h := List.take_append_drop i.val (List.ofFn ts)
  rw [List.drop_eq_getElem_cons (by simp)] at h
  simpa only [before,after,List.getElem_ofFn] using h.symm

lemma labels_split (c : Core) (ts : Fin c.val.length → CoreTree) (i : Fin c.val.length) :
    (branch c ts).labels=some c::((before c ts i).flatMap labels++(ts i).labels++(after c ts i).flatMap labels) := by
  rw [labels_branch,children_split c ts i,List.flatMap_append,List.flatMap_cons,List.append_assoc]

lemma labels_nonempty (t : CoreTree) : t.labels≠[] := by
  cases t <;> simp [labels]

def nodeIndex : (t : CoreTree) → t.Node → ℕ
  | .leaf,_ => 0
  | .branch _ _,.inl _ => 0
  | .branch c ts,.inr ⟨i,v⟩ => 1+((before c ts i).flatMap labels).length+nodeIndex (ts i) v

end FKCRT.Inventory.CoreTree
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_CornerMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
open scoped BigOperators
namespace FKCRT.Inventory.CoreTree
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable

def VertexConstant {A : Type*} (t : CoreTree) (f : t.Dart → A) : Prop :=
  ∀ a b,t.matching.distance a b=0 → f a=f b

end FKCRT.Inventory.CoreTree
end


end OAI
end


