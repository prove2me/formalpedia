-- Prove2me | Definitions.Def_Q220Uk001
-- name    : Q220Uk001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T14:37:48.551258+00:00
-- url     : https://prove2.me/theorems/a5393332-e361-4620-a93c-13f103c1fa2a
-- title:
--   Definitions bundle Q220Uk001 of the split of OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 497 declarations of OpenAI's Lean: 143 definitions, 10 inductive types or structures and 344 theorems. The definitions and types are `OAI.UniformKServer.AdaptiveAlpha.Config`, `OAI.UniformKServer.AdaptiveAlpha.eta`, `OAI.UniformKServer.AdaptiveAlpha.potential`, `OAI.UniformKServer.AdaptiveAlpha.scale`, `OAI.UniformKServer.AdaptiveAlpha.valid`, `OAI.UniformKServer.AdaptiveAlphaLinear.coefficient`, `OAI.UniformKServer.AdaptiveLedger.expect`, `OAI.UniformKServer.AdaptiveSide.Config`, `OAI.UniformKServer.AdaptiveSide.slope`, `OAI.UniformKServer.AllocationEpoch.State`, `OAI.UniformKServer.AllocationEpoch.charge`, `OAI.UniformKServer.AllocationEpoch.fires`, `OAI.UniformKServer.AllocationEpoch.initial`, `OAI.UniformKServer.AllocationEpoch.schedule`, `OAI.UniformKServer.AllocationEpoch.update`, `OAI.UniformKServer.AllocationEpoch.valid`, `OAI.UniformKServer.AllocationOutputs.excess`, `OAI.UniformKServer.AllocationOutputs.holesTwo`, `OAI.UniformKServer.AllocationOutputs.lower`, `OAI.UniformKServer.AllocationOutputs.ruleOne`, `OAI.UniformKServer.AllocationOutputs.ruleTwo`, `OAI.UniformKServer.AllocationOutputs.sideTotal`, `OAI.UniformKServer.AllocationOutputs.sideVariation`, `OAI.UniformKServer.AllocationOutputs.variation`, `OAI.UniformKServer.AllocationSchedule.charge`, `OAI.UniformKServer.AlphaEmpty.Config`, `OAI.UniformKServer.AlphaEmpty.active`, `OAI.UniformKServer.AlphaEmpty.eta`, `OAI.UniformKServer.AlphaEmpty.potential`, `OAI.UniformKServer.AlphaEmpty.scale`, `OAI.UniformKServer.AlphaEmpty.state`, `OAI.UniformKServer.AlphaEmpty.valid`, `OAI.UniformKServer.AlphaEmptyLinear.coefficient`, `OAI.UniformKServer.AlphaFiniteInput.Data`, `OAI.UniformKServer.AlphaFiniteInput.activeFlag`, `OAI.UniformKServer.AlphaFiniteInput.changes`, `OAI.UniformKServer.AlphaLinear.coefficient`, `OAI.UniformKServer.AlphaLinear.potential`, `OAI.UniformKServer.AlphaParameterChanges.piece`, `OAI.UniformKServer.AlphaRecurrence.InputValid` and 113 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `UniformKServer_AdaptiveAlpha`, `UniformKServer_AdaptiveAlphaLinear`, `UniformKServer_AdaptiveLedger`, `UniformKServer_AdaptiveSide`, `UniformKServer_AllocationAnalysis`, `UniformKServer_AllocationEpoch`, `UniformKServer_AllocationMovement`, `UniformKServer_AllocationOutputs`, `UniformKServer_AllocationSchedule`, `UniformKServer_AlphaEmpty`, `UniformKServer_AlphaEmptyLinear`, `UniformKServer_AlphaFiniteInput`, `UniformKServer_AlphaLinear`, `UniformKServer_AlphaParameterChanges`, `UniformKServer_AlphaPrepared`, `UniformKServer_AlphaRecurrence`, `UniformKServer_AlphaStability`, `UniformKServer_AlphaTracker`, `UniformKServer_AnchorPotential`, `UniformKServer_AnchorRamp`, `UniformKServer_AnchorScalar`, `UniformKServer_BalancedRepair`, `UniformKServer_BalancedStar`, `UniformKServer_CoreFiltering`, `UniformKServer_CrossRule`, `UniformKServer_Denominators`, `UniformKServer_DomainTransport`, `UniformKServer_Epochs`, `UniformKServer_FlowAuxiliary`, `UniformKServer_HeavySchedule`, `UniformKServer_HeavySeparation`, `UniformKServer_HeavyTape`, `UniformKServer_KeySizeTracker`, `UniformKServer_LogPrimitive`, `UniformKServer_PartitionSeparation`, `UniformKServer_PilotCapacity`, `UniformKServer_PilotCompact`, `UniformKServer_PilotConcentration`, `UniformKServer_PilotCredits`, `UniformKServer_PilotDeletion`, `UniformKServer_PilotEdits`, `UniformKServer_PilotExtension`, `UniformKServer_PilotFiltering`, `UniformKServer_PilotPersistence`, `UniformKServer_PilotRelocation`, `UniformKServer_PilotScales`, `UniformKServer_PilotSlope`, `UniformKServer_PilotStability`, `UniformKServer_ProportionParameters`, `UniformKServer_ReverseScales`, `UniformKServer_RosterTails`, `UniformKServer_SideStability`, `UniformKServer_SideTracker`, `UniformKServer_SimplexTracker`, `UniformKServer_SmallScales`, `UniformKServer_SortedRoster`, `UniformKServer_SyntheticCore`, `UniformKServer_TierPilot`.
--
--   **Imports.** It imports the published bundle `Def_UniformKServer`.
--
--   **Imported by** (directly, in this split): the bundles `Q220Uk004`, `Q220Uk005` and `Q220Uk006`.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_UniformKServer

section
-- module Solutions.Q220_UK.UniformKServer_Denominators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Source companion 04, Lemma denominators: the exact logarithmic denominator
family and its dimension-free simplex sum estimate. This is required to
instantiate the compact proportion tracker, not a new main theorem. -/
namespace UniformKServer.Denominators
noncomputable def regular (h a : ℝ) : ℝ := (h+Real.log (1/a))^2/h
noncomputable def height (u : ℝ) : ℝ := 1+Real.log (1/u)
noncomputable def marked (u a : ℝ) : ℝ := u+height u*Real.log (1/a)*(1+Real.log (1/a))
noncomputable def family {ι : Type*} [DecidableEq ι] (o : ι) (u : ℝ) (h a : ι → ℝ) (i : ι) : ℝ :=
  if i = o then marked u (a i) else regular (h i) (a i)

-- CANDIDATE PROOFS


theorem log_nonneg {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) : 0 ≤ Real.log (1/a) := by
  rcases ha.eq_or_lt with hz | hp
  · simp [← hz]
  · exact Real.log_nonneg ((le_div_iff₀ hp).mpr (by linarith))

theorem height_ge_one {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) : 1 ≤ height u := by
  unfold height
  linarith [log_nonneg hu.le hu₁]

theorem regular_pos {h a : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    0 < regular h a := by
  unfold regular
  exact div_pos (sq_pos_of_pos (add_pos_of_pos_of_nonneg hh (log_nonneg ha ha₁))) hh

theorem marked_pos {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    0 < marked u a := by
  unfold marked
  have hH := height_ge_one hu hu₁
  have hlog := log_nonneg ha ha₁
  have hp : 0 ≤ height u*Real.log (1/a)*(1+Real.log (1/a)) := by positivity
  linarith

theorem exp_sq_bound {y : ℝ} (hy : 0 ≤ y) : y^2 ≤ 8*Real.exp (y/2) := by
  have hh := Real.quadratic_le_exp_of_nonneg (show 0 ≤ y/2 by linarith)
  nlinarith

theorem regular_scalar {h a : ℝ} (hh : 1 ≤ h) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    a*regular h a ≤ 25*a*h+32*Real.exp (-h) := by
  have hhp : 0 < h := by linarith
  rcases ha.eq_or_lt with hz | hap
  · simp only [← hz, zero_mul]
    positivity
  let y := Real.log (1/a)
  have hy : 0 ≤ y := log_nonneg ha ha₁
  have hay : Real.exp (-y) = a := by simp [y, one_div, Real.log_inv, Real.exp_log hap]
  change a*((h+y)^2/h) ≤ _
  by_cases hnear : y ≤ 4*h
  · have hb : (h+y)^2/h ≤ 25*h := by
      apply (div_le_iff₀ hhp).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hb ha
    have hp := Real.exp_pos (-h)
    nlinarith
  · have hfar : 4*h < y := lt_of_not_ge hnear
    have hb : (h+y)^2/h ≤ 4*y^2 := by
      apply (div_le_iff₀ hhp).mpr
      have : y^2 ≤ y^2*h := by nlinarith [sq_nonneg y]
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hb ha
    have he := mul_le_mul_of_nonneg_left (exp_sq_bound hy) (Real.exp_nonneg (-y))
    have heq : Real.exp (-y)*Real.exp (y/2) = Real.exp (-y/2) := by
      rw [← Real.exp_add]
      congr 1; ring
    have heq' : Real.exp (-y)*(8*Real.exp (y/2)) = 8*Real.exp (-y/2) := by
      calc
        _ = 8*(Real.exp (-y)*Real.exp (y/2)) := by ring
        _ = _ := by rw [heq]
    rw [heq', hay] at he
    have htail : Real.exp (-y/2) ≤ Real.exp (-h) := Real.exp_le_exp.mpr (by linarith)
    have hab : 0 ≤ a*h := mul_nonneg ha hhp.le
    nlinarith

theorem marked_scalar {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    a*marked u a ≤ a*u+2*height u*(1-a) := by
  have hH := height_ge_one hu hu₁
  rcases ha.eq_or_lt with hz | hap
  · simp only [← hz, zero_mul, zero_add, sub_zero, mul_one]
    linarith
  let y := Real.log (1/a)
  have hy : 0 ≤ y := log_nonneg ha ha₁
  have he : Real.exp y = 1/a := Real.exp_log (div_pos zero_lt_one hap)
  have hb := mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg hy) ha
  rw [he, mul_one_div_cancel hap.ne'] at hb
  have hp : 0 ≤ a*y := mul_nonneg ha hy
  have ht : a*y*(1+y) ≤ 2*(1-a) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ height u by linarith)
  change a*(u+height u*y*(1+y)) ≤ _
  nlinarith

theorem total_ge_one {ι : Type*} [Fintype ι] {h a : ι → ℝ}
    (hh : ∀ i, 1 ≤ h i) (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) :
    1 ≤ ∑ i, a i*h i := by
  rw [← has]
  exact Finset.sum_le_sum fun i _ => by nlinarith [mul_nonneg (ha i) (sub_nonneg.mpr (hh i))]

theorem regular_simplex {ι : Type*} [Fintype ι] (h a : ι → ℝ) (Z : ℝ)
    (hh : ∀ i, 1 ≤ h i) (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1)
    (he : (∑ i, Real.exp (-h i)) ≤ Z) :
    (∑ i, a i*regular (h i) (a i)) ≤ (25+32*Z)*(∑ i, a i*h i) := by
  have hz : 0 ≤ Z := (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => Real.exp_nonneg (-h i))).trans he
  have ha₁ : ∀ i, a i ≤ 1 := fun i => by
    rw [← has]
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => regular_scalar (hh i) (ha i) (ha₁ i))
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hs
  have hT := total_ge_one hh ha has
  have hm := mul_le_mul_of_nonneg_left hT hz
  nlinarith

theorem marked_simplex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι) (u c Z : ℝ) (h a : ι → ℝ)
    (hu : 0 < u) (hu₁ : u ≤ 1) (hc : 0 < c) (hc₁ : c ≤ 1) (hZ : 0 ≤ Z)
    (ho : h o = u) (hh : ∀ i, i ≠ o → 1 ≤ h i)
    (hhc : ∀ i, i ≠ o → c*height u ≤ h i)
    (he : (∑ i ∈ Finset.univ.erase o, Real.exp (-h i)) ≤ Z*u)
    (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1) :
    (∑ i, a i*family o u h a i) ≤ (25+(2+32*Z)/c)*(∑ i, a i*h i) := by
  have ha₁ : ∀ i, a i ≤ 1 := fun i => by
    rw [← has]
    exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hH := height_ge_one hu hu₁
  have hal : (∑ i ∈ Finset.univ.erase o, a i) = 1-a o := by
    have heq := Finset.sum_erase_add Finset.univ a (Finset.mem_univ o)
    rw [has] at heq
    linarith
  have hT : (∑ i, a i*h i) = (∑ i ∈ Finset.univ.erase o, a i*h i)+a o*u := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o), ho]
  have hside : c*height u*(1-a o) ≤ ∑ i ∈ Finset.univ.erase o, a i*h i := by
    rw [← hal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hb := mul_le_mul_of_nonneg_left (hhc i (Finset.ne_of_mem_erase hi)) (ha i)
    nlinarith
  have hR : 0 ≤ ∑ i ∈ Finset.univ.erase o, a i*h i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i) (le_trans (by norm_num) (hh i (Finset.ne_of_mem_erase hi)))
  have hcu : c*u ≤ ∑ i, a i*h i := by
    rw [hT]
    have hhu : c*u*(1-a o) ≤ c*height u*(1-a o) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : u ≤ height u) hc.le)
        (sub_nonneg.mpr (ha₁ o))
    have hao : c*(a o*u) ≤ a o*u := mul_le_of_le_one_left (mul_nonneg (ha o) hu.le) hc₁
    nlinarith
  have hbase : (∑ i, a i*family o u h a i) ≤
      25*(∑ i ∈ Finset.univ.erase o, a i*h i)+32*Z*u+a o*u+2*height u*(1-a o) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o)]
    have hreg : (∑ i ∈ Finset.univ.erase o, a i*family o u h a i) ≤
        25*(∑ i ∈ Finset.univ.erase o, a i*h i)+32*Z*u := by
      have hs := Finset.sum_le_sum (fun i (hi : i ∈ Finset.univ.erase o) =>
        regular_scalar (hh i (Finset.ne_of_mem_erase hi)) (ha i) (ha₁ i))
      have eqn : (∑ i ∈ Finset.univ.erase o, a i*family o u h a i) =
          ∑ i ∈ Finset.univ.erase o, a i*regular (h i) (a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [family, Finset.ne_of_mem_erase hi]
      rw [eqn]
      simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hs
      linarith
    have hm := marked_scalar hu hu₁ (ha o) (ha₁ o)
    simp only [family, ↓reduceIte] at *
    linarith
  have hextra : 32*Z*u+2*height u*(1-a o) ≤ ((2+32*Z)/c)*(∑ i, a i*h i) := by
    apply (mul_le_mul_iff_right₀ hc).mp
    have eqn : c*(((2+32*Z)/c)*(∑ i, a i*h i)) = (2+32*Z)*(∑ i, a i*h i) := by
      field_simp
    rw [eqn]
    have hm := mul_le_mul_of_nonneg_left hcu (show 0 ≤ 32*Z by positivity)
    rw [hT] at hm ⊢
    nlinarith [mul_nonneg hc.le (mul_nonneg (ha o) hu.le)]
  rw [hT]
  rw [hT] at hextra
  nlinarith [mul_nonneg (ha o) hu.le]

end UniformKServer.Denominators

                                                                         
                                                                              

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_LogPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.LogPrimitive
open Set Filter MeasureTheory
open scoped Topology
noncomputable def primitive (D : ℝ → ℝ) (base scale S Q a : ℝ) : ℝ :=
  scale * ∫ s in base..a, (S-Q/s)/D s

def Contract (g D : ℝ → ℝ) (scale S Q : ℝ) : Prop :=
  ContinuousOn g (Icc 0 1) ∧
  (∀ a, 0 < a → a ≤ 1 → HasDerivAt g (scale*((S-Q/a)/D a)) a) ∧
  (0 < Q → 0 < scale → Tendsto (fun a => (g a-g 0)/a) (𝓝[>] 0) atBot)

-- CANDIDATE PROOFS

noncomputable def J (x : ℝ) : ℝ := if x = 0 then 0 else 1/(1+Real.log (1/x))
noncomputable def w (x : ℝ) : ℝ := 1/(x*(1+Real.log (1/x))^2)

theorem log_recip_top : Tendsto (fun x : ℝ => Real.log (1/x)) (𝓝[>] 0) atTop := by
  simpa only [one_div, Function.comp_def] using Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

theorem J_continuous : ContinuousOn J (Icc 0 1) := by
  intro x hx
  by_cases hz : x = 0
  · subst x
    have ht : Tendsto J (𝓝[>] (0 : ℝ)) (𝓝 (J 0)) := by
      simp only [J]
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).add_atTop log_recip_top).inv_tendsto_atTop
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [J, ne_of_gt hx.out, one_div]
    exact (continuousWithinAt_Ioi_iff_Ici.mp ht).mono (fun x hx => hx.1)
  · have hp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hz)
    have hd : 1+Real.log (1/x) ≠ 0 := ne_of_gt (by
      linarith [UniformKServer.Denominators.log_nonneg hx.1 hx.2])
    apply ContinuousAt.continuousWithinAt
    apply ((continuousAt_const (y := (1 : ℝ))).div (continuousAt_const.add
      ((continuousAt_const.div continuousAt_id hz).log (one_div_ne_zero hz))) hd).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with y hy
    simp [J, hy]

theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ w x := by
  unfold w
  positivity

theorem J_derivative {x : ℝ} (hx : 0 < x) (hx₁ : x ≤ 1) : HasDerivAt J (w x) x := by
  have hd : 1+Real.log (1/x) ≠ 0 := ne_of_gt (by
    linarith [UniformKServer.Denominators.log_nonneg hx.le hx₁])
  have he : J =ᶠ[𝓝 x] (fun y : ℝ => (1+Real.log (1/y))⁻¹) := by
    filter_upwards [eventually_ne_nhds hx.ne'] with y hy
    simp [J, hy, one_div]
  apply HasDerivAt.congr_of_eventuallyEq _ he
  have hh := ((hasDerivAt_const x 1).add
    (((hasDerivAt_id x).inv hx.ne').log (inv_ne_zero hx.ne'))).inv (by simpa [one_div] using hd)
  convert! hh using 1
  · funext y; simp [one_div]
  · simp only [Pi.inv_apply, Pi.add_apply, id_eq, zero_add, one_div, w] at *
    field_simp [hx.ne', hd]

theorem w_integrable : IntervalIntegrable w volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
  · simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using J_continuous
  · simp only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun x hx => J_derivative hx.1 hx.2.le
  · simp only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1), max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    exact fun x hx => w_nonneg hx.1.le

theorem integrand_integrable {D : ℝ → ℝ} (hDm : Measurable D) {c : ℝ} (hc : 0 < c)
    (hD : ∀ x, 0 < x → x ≤ 1 → c*(1+Real.log (1/x))^2 ≤ D x) (S Q : ℝ) :
    IntervalIntegrable (fun x => (S-Q/x)/D x) volume 0 1 := by
  apply (w_integrable.const_mul ((|S|+|Q|)/c)).mono_fun'
  · exact ((measurable_const.sub (measurable_const.div measurable_id)).div hDm).aestronglyMeasurable
  · rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x ≤ 1 := hx.2
    have hy : 0 ≤ Real.log (1/x) := UniformKServer.Denominators.log_nonneg hx.1.le hx.2
    have hq : 0 < (1+Real.log (1/x))^2 := sq_pos_of_pos (by linarith)
    have hDp : 0 < D x := lt_of_lt_of_le (mul_pos hc hq) (hD x hx.1 hx.2)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hDp]
    have hn : |S-Q/x| ≤ |S|+|Q|/x := by
      convert! abs_sub S (Q/x) using 1
      all_goals try with_reducible_and_instances rfl
      rw [abs_div, abs_of_pos hx.1]
    have hr : |S| * x+|Q| ≤ |S|+|Q| := by nlinarith [abs_nonneg S]
    calc
      _ ≤ (|S|+|Q|/x)/D x := div_le_div_of_nonneg_right hn hDp.le
      _ ≤ (|S|+|Q|/x)/(c*(1+Real.log (1/x))^2) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hc hq) (hD x hx.1 hx.2)
      _ = (|S| * x+|Q|)/(c*x*(1+Real.log (1/x))^2) := by field_simp [hx0.ne']
      _ ≤ (|S|+|Q|)/(c*x*(1+Real.log (1/x))^2) :=
        div_le_div_of_nonneg_right hr (by positivity)
      _ = ((|S|+|Q|)/c)*w x := by unfold w; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem slope_atBot {f f' : ℝ → ℝ} (hfc : ContinuousOn f (Icc 0 1))
    (hfd : ∀ x, 0 < x → x ≤ 1 → HasDerivAt f (f' x) x)
    (hlim : Tendsto f' (𝓝[>] 0) atBot) :
    Tendsto (fun x => (f x-f 0)/x) (𝓝[>] 0) atBot := by
  apply tendsto_atBot.mpr
  intro K
  obtain ⟨δ, hδ, hb⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hlim.eventually_le_atBot K)
  filter_upwards [Ioc_mem_nhdsGT (show 0 < min δ 1 by exact lt_min hδ (by norm_num))] with x hx
  obtain ⟨r, hr, he⟩ := exists_hasDerivAt_eq_slope f f' hx.1
    (hfc.mono (Icc_subset_Icc le_rfl (hx.2.trans (min_le_right _ _))))
    (fun r hr => hfd r hr.1 (hr.2.le.trans (hx.2.trans (min_le_right _ _))))
  have hk := hb (show r ∈ Ioc 0 δ from ⟨hr.1, hr.2.le.trans (hx.2.trans (min_le_left _ _))⟩)
  change f' r ≤ K at hk
  rw [he, sub_zero] at hk
  exact hk

theorem generic_contract {D : ℝ → ℝ} (hDm : Measurable D) {c : ℝ} (hc : 0 < c)
    (hD : ∀ x, 0 < x → x ≤ 1 → c*(1+Real.log (1/x))^2 ≤ D x)
    (hDc : ∀ x, 0 < x → x ≤ 1 → ContinuousAt D x)
    (hlim : Tendsto (fun x => x*D x) (𝓝[>] 0) (𝓝 0))
    (base scale S Q : ℝ) (hbase : base ∈ Icc 0 1) :
    Contract (primitive D base scale S Q) D scale S Q := by
  have hDp : ∀ x, 0 < x → x ≤ 1 → 0 < D x := by
    intro x hx hx₁
    have hy := UniformKServer.Denominators.log_nonneg hx.le hx₁
    exact lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (by linarith))) (hD x hx hx₁)
  let f := fun x => (S-Q/x)/D x
  have hfm : Measurable f := (measurable_const.sub (measurable_const.div measurable_id)).div hDm
  have hfi : IntervalIntegrable f volume 0 1 := integrand_integrable hDm hc hD S Q
  have hfba : ∀ a, a ∈ Icc (0 : ℝ) 1 → IntervalIntegrable f volume base a := by
    intro a ha
    apply hfi.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact uIcc_subset_Icc hbase ha
  have hfc : ∀ a, 0 < a → a ≤ 1 → ContinuousAt f a := by
    intro a ha ha₁
    exact (continuousAt_const.sub (continuousAt_const.div continuousAt_id ha.ne')).div
      (hDc a ha ha₁) (hDp a ha ha₁).ne'
  have hg : ContinuousOn (primitive D base scale S Q) (Icc 0 1) := by
    have h₀ : IntegrableOn f (uIcc (0 : ℝ) 1) volume := (intervalIntegrable_iff' enorm_ne_top).mp hfi
    have h : ContinuousOn (fun a => ∫ x in 0..a, f x) (Icc (0 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        intervalIntegral.continuousOn_primitive_interval h₀
    have hh := h.sub (continuousOn_const (s := Icc (0 : ℝ) 1) (c := (∫ x in 0..base, f x)))
    apply (continuousOn_const.mul hh).congr
    intro a ha
    have h0a : IntervalIntegrable f volume 0 a := hfi.mono_set (by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact uIcc_subset_Icc (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ha)
    have h0b : IntervalIntegrable f volume 0 base := (hfba 0 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).symm
    change scale*(∫ x in base..a, f x) = scale*((∫ x in 0..a, f x)-(∫ x in 0..base, f x))
    rw [intervalIntegral.integral_interval_sub_left h0a h0b]
  have hgd : ∀ a, 0 < a → a ≤ 1 → HasDerivAt (primitive D base scale S Q)
      (scale*((S-Q/a)/D a)) a := by
    intro a ha ha₁
    exact (intervalIntegral.integral_hasDerivAt_right (hfba a ⟨ha.le, ha₁⟩)
      hfm.stronglyMeasurable.stronglyMeasurableAtFilter (hfc a ha ha₁)).const_mul scale
  refine ⟨hg, hgd, ?_⟩
  intro hQ hs
  apply slope_atBot hg hgd
  have hden : Tendsto (fun x => x*D x) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hlim, ?_⟩
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact mul_pos hx.1 (hDp x hx.1 hx.2)
  have hn : Tendsto (fun x : ℝ => S*x-Q) (𝓝[>] 0) (𝓝 (-Q)) := by
    have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ((tendsto_const_nhds (x := S)).mul hx).sub_const Q
  have hh := (Tendsto.neg_mul_atTop (neg_lt_zero.mpr hQ) hn hden.inv_tendsto_nhdsGT_zero) |> Tendsto.const_mul_atBot hs
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.out
  dsimp only [Pi.inv_apply]
  field_simp [hx0]

theorem powlog_zero (n : ℕ) :
    Tendsto (fun x : ℝ => x*(Real.log (1/x))^n) (𝓝[>] 0) (𝓝 0) := by
  simpa only [Function.comp_def, one_mul, mul_one, add_zero, div_inv_eq_mul, one_div, mul_comm] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).comp tendsto_inv_nhdsGT_zero

theorem log_recip_continuousAt {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (fun x : ℝ => Real.log (1/x)) x :=
  (continuousAt_const.div continuousAt_id hx).log (one_div_ne_zero hx)

open UniformKServer.Denominators

theorem regular_lower {h x : ℝ} (hh : 1 ≤ h) (hx : 0 < x) (hx₁ : x ≤ 1) :
    (1/h)*(1+Real.log (1/x))^2 ≤ regular h x := by
  have hp : 0 < h := by linarith
  have hy := log_nonneg hx.le hx₁
  unfold regular
  rw [one_div, ← div_eq_inv_mul]
  apply (div_le_div_iff_of_pos_right hp).mpr
  nlinarith

theorem marked_lower {u x : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hx : 0 < x) (hx₁ : x ≤ 1) :
    (u/4)*(1+Real.log (1/x))^2 ≤ marked u x := by
  have hH := height_ge_one hu hu₁
  have hy := log_nonneg hx.le hx₁
  have h₁ := mul_le_mul_of_nonneg_right hu₁ hy
  have h₂ := mul_le_mul_of_nonneg_right hu₁ (sq_nonneg (Real.log (1/x)))
  have h₃ := mul_le_mul_of_nonneg_right hH hy
  have h₄ := mul_le_mul_of_nonneg_right hH (sq_nonneg (Real.log (1/x)))
  unfold marked
  nlinarith

theorem regular_contract (h scale S Q : ℝ) (hh : 1 ≤ h) :
    Contract (primitive (regular h) 0 scale S Q) (regular h) scale S Q := by
  have hp : 0 < h := by linarith
  apply generic_contract (c := 1/h)
  · unfold regular
    fun_prop
  · positivity
  · exact fun x hx hx₁ => regular_lower hh hx hx₁
  · intro x hx hx₁
    unfold regular
    exact (continuousAt_const.add (log_recip_continuousAt hx.ne')).pow 2 |>.div_const h
  · have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hy : Tendsto (fun x : ℝ => x*Real.log (1/x)) (𝓝[>] 0) (𝓝 0) := by simpa using powlog_zero 1
    have ht := ((hx.const_mul h).add (hy.const_mul 2)).add ((powlog_zero 2).div_const h)
    simp only [mul_zero, zero_add, zero_div] at ht
    apply ht.congr'
    exact Filter.Eventually.of_forall fun x => by unfold regular; field_simp <;> ring
  · simp

theorem marked_contract (u scale S Q : ℝ) (hu : 0 < u) (hu₁ : u ≤ 1) :
    Contract (primitive (marked u) 1 scale S Q) (marked u) scale S Q := by
  apply generic_contract (c := u/4)
  · unfold marked
    fun_prop
  · positivity
  · exact fun x hx hx₁ => marked_lower hu hu₁ hx hx₁
  · intro x hx hx₁
    unfold marked
    have hl := log_recip_continuousAt hx.ne'
    exact continuousAt_const.add ((continuousAt_const.mul hl).mul (continuousAt_const.add hl))
  · have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hy : Tendsto (fun x : ℝ => x*Real.log (1/x)) (𝓝[>] 0) (𝓝 0) := by simpa using powlog_zero 1
    have ht := ((hx.const_mul u).add (hy.const_mul (height u))).add ((powlog_zero 2).const_mul (height u))
    simp only [mul_zero, zero_add] at ht
    apply ht.congr'
    exact Filter.Eventually.of_forall fun x => by unfold marked; ring
  · simp

end UniformKServer.LogPrimitive


                                                                             
                                                                               
                                                                         
                                                                               


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SimplexTracker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.SimplexTracker
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def simplex (a : ι → ℝ) : Prop := (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1

def movement (a b : ι → ℝ) : ℝ := ∑ i, |a i-b i|

def transfer (a : ι → ℝ) (i j : ι) (s : ℝ) : ι → ℝ :=
  Function.update (Function.update a i (a i-s)) j (a j+s)

def objective (g : ι → ℝ → ℝ) (S : ℝ) (a₀ a : ι → ℝ) : ℝ :=
  (∑ i, g i (a i))+S*movement a a₀

structure AnalyticData (g : ι → ℝ → ℝ) (B h : ι → ℝ)
    (F : ι → ℝ → ℝ) (ell ct C A E : ℝ) : Prop where
  B_nonneg : ∀ i, 0 ≤ B i
  h_pos : ∀ i, 0 < h i
  ell_pos : 0 < ell
  ct_pos : 0 < ct
  A_nonneg : 0 ≤ A
  E_nonneg : 0 ≤ E
  eta_le : ∀ i, ct*h i/ell ≤ E
  multiplier : 2*A*(1+E) < C*ct
  F_pos : ∀ i x, 0 < x → x ≤ 1 → 0 < F i x
  denominator_bound : ∀ a, simplex a →
    (∑ i, a i*F i (a i)) ≤ A*(∑ i, a i*h i)
  continuous : ∀ i, ContinuousOn (g i) (Icc 0 1)
  derivative : ∀ i x, 0 < x → x ≤ 1 →
    HasDerivAt (g i) ((C*ell/F i x)*((∑ r, B r)-(1+ct*h i/ell)*B i/x)) x
  inward : ∀ i, 0 < B i →
    Tendsto (fun s : ℝ => (g i s-g i 0)/s) (𝓝[>] 0) atBot

omit [DecidableEq ι] in
theorem coordinate_le_one {a : ι → ℝ} (ha : simplex a) (i : ι) : a i ≤ 1 := by
  rw [← ha.2]
  exact Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem simplex_compact : IsCompact {a : ι → ℝ | simplex a} := by
  have h₁ : IsClosed {a : ι → ℝ | ∀ i, 0 ≤ a i} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h₂ : IsClosed {a : ι → ℝ | ∑ i, a i = 1} := isClosed_eq (by fun_prop) continuous_const
  apply (isCompact_Icc : IsCompact (Icc (fun _ : ι => (0 : ℝ)) (fun _ => 1))).of_isClosed_subset (h₁.inter h₂)
  intro a ha
  exact ⟨ha.1, coordinate_le_one ha⟩

theorem sum_update (a : ι → ℝ) (i : ι) (t : ℝ) :
    ∑ j, Function.update a i t j = (∑ j, a j)+t-a i := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]; ring

theorem potential_update (g : ι → ℝ → ℝ) (a : ι → ℝ) (i : ι) (t : ℝ) :
    (∑ j, g j (Function.update a i t j)) = (∑ j, g j (a j))+g i t-g i (a i) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ (fun j => g j (a j)) (Finset.mem_univ i)]
  have he : ∑ j ∈ Finset.univ.erase i, g j (Function.update a i t j) =
      ∑ j ∈ Finset.univ.erase i, g j (a j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he, Function.update_self]; ring

theorem transfer_simplex {a : ι → ℝ} (ha : simplex a) {i j : ι} (hij : i ≠ j)
    {s : ℝ} (hs : 0 ≤ s) (hsi : s ≤ a i) : simplex (transfer a i j s) := by
  refine ⟨?_, ?_⟩
  · intro r
    by_cases hrj : r = j
    · subst r; simp only [transfer, Function.update_self]; exact add_nonneg (ha.1 j) hs
    · by_cases hri : r = i
      · subst r; simp [transfer, Function.update_of_ne hij, sub_nonneg.mpr hsi]
      · simp [transfer, Function.update_of_ne hrj, Function.update_of_ne hri, ha.1 r]
  · simp only [transfer, sum_update, Function.update_of_ne hij.symm, ha.2]
    ring

theorem transfer_potential (g : ι → ℝ → ℝ) (a : ι → ℝ) {i j : ι} (hij : i ≠ j) (s : ℝ) :
    (∑ r, g r (transfer a i j s r)) = (∑ r, g r (a r)) +
      (g i (a i-s)-g i (a i))+(g j (a j+s)-g j (a j)) := by
  simp only [transfer, potential_update, Function.update_of_ne hij.symm]
  ring

theorem transfer_movement (a b : ι → ℝ) {i j : ι} (hij : i ≠ j) (s : ℝ) :
    movement (transfer a i j s) b ≤ movement a b+2*|s| := by
  unfold movement
  rw [transfer_potential (fun r t => |t-b r|) a hij]
  have hi := abs_add_le (a i-b i) (-s)
  simp only [abs_neg, ← sub_eq_add_neg] at hi
  have hj := abs_add_le (a j-b j) s
  have ei : a i-s-b i = a i-b i-s := by ring
  have ej : a j+s-b j = a j-b j+s := by ring
  rw [ei, ej]; linarith

theorem scalar_deficit {a eta E : ℝ} (ha : 0 ≤ a) (he : 0 ≤ eta) (hE : eta ≤ E) :
    a/(1+eta) ≤ a-a*eta/(1+E) := by
  have h₁ : 0 < 1+eta := by linarith
  have h₂ : 0 < 1+E := by linarith
  apply (div_le_iff₀ h₁).mpr
  apply (mul_le_mul_iff_right₀ h₂).mp
  have eqn : (a-a*eta/(1+E))*(1+eta)*(1+E) = a*(1+E)+a*eta*(E-eta) := by
    field_simp <;> ring
  nlinarith [mul_nonneg (mul_nonneg ha he) (sub_nonneg.mpr hE)]

omit [DecidableEq ι] in
theorem multiplier_pos {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E) : 0 < C := by
  have hn : 0 ≤ 2*A*(1+E) := mul_nonneg (mul_nonneg (by norm_num) H.A_nonneg) (by linarith [H.E_nonneg])
  have hp : 0 < C*ct := lt_of_le_of_lt hn H.multiplier
  exact pos_of_mul_pos_left hp H.ct_pos.le

omit [DecidableEq ι] in
theorem weighted_deficit {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E)
    {a : ι → ℝ} (ha : simplex a) :
    (∑ i, a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell))) < 1 := by
  have hC := multiplier_pos H
  have hK : 0 < C*ell := mul_pos hC H.ell_pos
  have he : 0 < 1+E := by linarith [H.E_nonneg]
  have hT : 0 < ∑ i, a i*h i := by
    obtain ⟨i, hi, hai⟩ := (Finset.sum_pos_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => ha.1 i)).mp
      (show 0 < ∑ i, a i from by rw [ha.2]; norm_num)
    exact Finset.sum_pos' (fun i _ => mul_nonneg (ha.1 i) (H.h_pos i).le)
      ⟨i, hi, mul_pos hai (H.h_pos i)⟩
  have hs : ∀ i, a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell)) ≤
      a i-(ct/(ell*(1+E)))*(a i*h i)+(2/(C*ell))*(a i*F i (a i)) := by
    intro i
    have hη : 0 ≤ ct*h i/ell := le_of_lt (div_pos (mul_pos H.ct_pos (H.h_pos i)) H.ell_pos)
    have hp : 0 ≤ a i*F i (a i) := by
      rcases (ha.1 i).eq_or_lt with hz | hz
      · rw [← hz, zero_mul]
      · exact mul_nonneg hz.le (H.F_pos i _ hz (coordinate_le_one ha i)).le
    have hdef := scalar_deficit (ha.1 i) hη (H.eta_le i)
    have hself := div_le_self hp (show (1:ℝ) ≤ 1+ct*h i/ell by linarith)
    have hextra := mul_le_mul_of_nonneg_left hself (div_nonneg (by norm_num : (0:ℝ) ≤ 2) hK.le)
    have eq₁ : a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell)) =
        a i/(1+ct*h i/ell)+(2/(C*ell))*(a i*F i (a i)/(1+ct*h i/ell)) := by ring
    have eq₂ : a i*(ct*h i/ell)/(1+E) = (ct/(ell*(1+E)))*(a i*h i) := by field_simp
    rw [eq₁]
    rw [eq₂] at hdef
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ha.2] at hsum
  have hbound := mul_le_mul_of_nonneg_left (H.denominator_bound a ha) (show 0 ≤ 2/(C*ell) by positivity)
  have hco : 2*A/(C*ell) < ct/(ell*(1+E)) := by
    apply (div_lt_div_iff₀ hK (mul_pos H.ell_pos he)).mpr
    have hh := mul_lt_mul_of_pos_right H.multiplier H.ell_pos
    nlinarith
  have hf := mul_lt_mul_of_pos_right hco hT
  have heq : 2/(C*ell)*(A*(∑ i, a i*h i)) = 2*A/(C*ell)*(∑ i, a i*h i) := by ring
  rw [heq] at hbound
  linarith

omit [DecidableEq ι] in
theorem low_coordinate {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E)
    {a : ι → ℝ} (ha : simplex a) (hS : 0 < ∑ i, B i) :
    ∃ i, (a i = 0 ∧ 0 < B i) ∨
      (0 < a i ∧ (C*ell/F i (a i))*((∑ r, B r)-(1+ct*h i/ell)*B i/a i) < -2*(∑ r, B r)) := by
  by_contra hn
  push Not at hn
  have hK : 0 < C*ell := mul_pos (multiplier_pos H) H.ell_pos
  have hpoint : ∀ i, B i ≤ (∑ r, B r)*(a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell))) := by
    intro i
    have heta : 0 < 1+ct*h i/ell := by
      have hh := div_pos (mul_pos H.ct_pos (H.h_pos i)) H.ell_pos
      linarith
    by_cases hai : a i = 0
    · have hb : B i = 0 := le_antisymm ((hn i).1 hai) (H.B_nonneg i)
      simp [hai, hb]
    · have hap : 0 < a i := lt_of_le_of_ne (ha.1 i) (Ne.symm hai)
      have hF := H.F_pos i _ hap (coordinate_le_one ha i)
      have hgrad := (hn i).2 hap
      have hgrad' := (le_div_iff₀ hF).mp (show -2*(∑ r, B r) ≤
        (C*ell*((∑ r, B r)-(1+ct*h i/ell)*B i/a i))/F i (a i) by
          simpa only [div_mul_eq_mul_div] using hgrad)
      have hgrad'' := mul_le_mul_of_nonneg_right hgrad' hap.le
      have eqn : C*ell*((∑ r, B r)-(1+ct*h i/ell)*B i/a i)*a i =
          C*ell*((∑ r, B r)*a i-(1+ct*h i/ell)*B i) := by field_simp
      rw [eqn] at hgrad''
      apply (mul_le_mul_iff_right₀ (mul_pos hK heta)).mp
      have hr : ell+ct*h i ≠ 0 := (add_pos H.ell_pos (mul_pos H.ct_pos (H.h_pos i))).ne'
      have eqrhs : (C*ell*(1+ct*h i/ell))*((∑ r, B r)*(a i/(1+ct*h i/ell)*(1+2*F i (a i)/(C*ell)))) =
          (∑ r, B r)*a i*(C*ell+2*F i (a i)) := by
        field_simp [hr, hK.ne', heta.ne', (multiplier_pos H).ne', H.ell_pos.ne']
      rw [eqrhs]
      nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [← Finset.mul_sum] at hh
  have hstrict := mul_lt_mul_of_pos_left (weighted_deficit H ha) hS
  rw [mul_one] at hstrict
  linarith

theorem minimizing_slope {g : ι → ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g S a₀) {a | simplex a} a)
    {i j : ι} (hij : i ≠ j) {s : ℝ} (hs : 0 < s) (hsi : s ≤ a i) :
    0 ≤ (g i (a i-s)-g i (a i))/s + (g j (a j+s)-g j (a j))/s + 2*S := by
  have hv := transfer_simplex ha hij hs.le hsi
  have hh : objective g S a₀ a ≤ objective g S a₀ (transfer a i j s) := hm hv
  unfold objective at hh
  rw [transfer_potential g a hij] at hh
  have hb := mul_le_mul_of_nonneg_left (transfer_movement a a₀ hij s) hS
  rw [abs_of_pos hs] at hb
  have hnn : 0 ≤ (g i (a i-s)-g i (a i))+(g j (a j+s)-g j (a j))+2*S*s := by linarith
  have hdiv := div_nonneg hnn hs.le
  convert! hdiv using 1 ; field_simp

theorem right_derivative_nonneg {f : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hf : HasDerivAt f d 0) (hmin : ∀ s, 0 < s → s < δ → f 0 ≤ f s) : 0 ≤ d := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with s hs hsδ
  simp only [Set.mem_Ioi, Set.mem_Iio] at hs hsδ
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr (hmin s hs hsδ))

theorem minimum_gradient_difference {g : ι → ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g S a₀) {a | simplex a} a)
    {i j : ι} (hij : i ≠ j) (hi : 0 < a i) {di dj : ℝ}
    (hdi : HasDerivAt (g i) di (a i)) (hdj : HasDerivAt (g j) dj (a j)) :
    di-dj ≤ 2*S := by
  have hdi' : HasDerivAt (fun s : ℝ => g i (a i-s)) (-di) 0 := by
    have hd₀ : HasDerivAt (g i) di (a i-id 0) := by simpa using hdi
    have hh := hd₀.comp 0 ((hasDerivAt_id 0).const_sub (a i))
    convert! hh using 1 ; simp
  have hdj' : HasDerivAt (fun s : ℝ => g j (a j+s)) dj 0 := by
    have hd₀ : HasDerivAt (g j) dj (a j+id 0) := by simpa using hdj
    have hh := hd₀.comp 0 ((hasDerivAt_id 0).const_add (a j))
    convert! hh using 1 ; simp
  have hd : HasDerivAt (fun s : ℝ => g i (a i-s)+g j (a j+s)+2*S*s) (-di+dj+2*S) 0 := by
    convert! (hdi'.add hdj').add ((hasDerivAt_id 0).const_mul (2*S)) using 1 ; simp
  have hge := right_derivative_nonneg hi hd (fun s hs hsi => ?_)
  · linarith
  have hh := minimizing_slope hS ha hm hij hs hsi.le
  have hh' := mul_nonneg hh hs.le
  simp only [sub_zero, add_zero, mul_zero]
  field_simp at hh'
  linarith

theorem minimum_excludes_singular {g : ι → ℝ → ℝ} {S : ℝ} (hS : 0 ≤ S)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g S a₀) {a | simplex a} a)
    {i j : ι} (hij : i ≠ j) (hi : 0 < a i) (hj : a j = 0) {di : ℝ}
    (hdi : HasDerivAt (g i) di (a i))
    (hsing : Tendsto (fun s : ℝ => (g j s-g j 0)/s) (𝓝[>] 0) atBot) : False := by
  have hdi' : HasDerivAt (fun s : ℝ => g i (a i-s)) (-di) 0 := by
    have hd₀ : HasDerivAt (g i) di (a i-id 0) := by simpa using hdi
    have hh := hd₀.comp 0 ((hasDerivAt_id 0).const_sub (a i))
    convert! hh using 1 ; simp
  have hlim : Tendsto (fun s : ℝ => (g i (a i-s)-g i (a i))/s) (𝓝[>] 0) (𝓝 (-di)) := by
    simpa only [zero_add, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hdi'.tendsto_slope_zero_right
  have hbot := (hlim.add_atBot hsing).atBot_add (tendsto_const_nhds (x := 2*S))
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (g i (a i-s)-g i (a i))/s+(g j s-g j 0)/s+2*S < 0 :=
    hbot.eventually (eventually_lt_atBot 0)
  have hcontra : ∀ᶠ s in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hev, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hi)] with s hs hspos hsi
    have hh := minimizing_slope hS ha hm hij hspos hsi.le
    simp only [hj, zero_add] at hh
    linarith
  rcases hcontra.exists with ⟨s, hs⟩
  exact hs

theorem minimum_feasible {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (H : AnalyticData g B h F ell ct C A E)
    {a a₀ : ι → ℝ} (ha : simplex a)
    (hm : IsMinOn (objective g (∑ i, B i) a₀) {a | simplex a} a) :
    ∀ i, (∑ r, B r)*a i ≤ (1+ct*h i/ell)*B i := by
  intro i
  by_contra hbad
  have hb := lt_of_not_ge hbad
  have he : 0 < 1+ct*h i/ell := by
    have hh := div_pos (mul_pos H.ct_pos (H.h_pos i)) H.ell_pos
    linarith
  have hS₀ : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ => H.B_nonneg i)
  have hprod : 0 < (∑ r, B r)*a i := lt_of_le_of_lt (mul_nonneg he.le (H.B_nonneg i)) hb
  have hi : 0 < a i := pos_of_mul_pos_right hprod hS₀
  have hS : 0 < ∑ i, B i := pos_of_mul_pos_left hprod (ha.1 i)
  have hgi : 0 < (C*ell/F i (a i))*((∑ r, B r)-(1+ct*h i/ell)*B i/a i) := by
    apply mul_pos (div_pos (mul_pos (multiplier_pos H) H.ell_pos) (H.F_pos i _ hi (coordinate_le_one ha i)))
    exact sub_pos.mpr ((div_lt_iff₀ hi).mpr hb)
  obtain ⟨j, hj | hj⟩ := low_coordinate H ha hS
  · have hij : i ≠ j := by intro e; subst j; linarith [hj.1]
    exact minimum_excludes_singular hS₀ ha hm hij hi hj.1
      (H.derivative i _ hi (coordinate_le_one ha i)) (H.inward j hj.2)
  · have hij : i ≠ j := by intro e; subst j; linarith [hj.2]
    have hh := minimum_gradient_difference hS₀ ha hm hij hi
      (H.derivative i _ hi (coordinate_le_one ha i)) (H.derivative j _ hj.1 (coordinate_le_one ha j))
    linarith [hj.2]

/-- Compact minimizing update, with no convexity assumption on the primitives. -/
theorem update (g : ι → ℝ → ℝ) (B h : ι → ℝ)
    (F : ι → ℝ → ℝ) (ell ct C A E : ℝ)
    (H : AnalyticData g B h F ell ct C A E) (a₀ : ι → ℝ) (ha₀ : simplex a₀) :
    ∃ a, simplex a ∧ IsMinOn (objective g (∑ i, B i) a₀) {a | simplex a} a ∧
      (∀ i, (∑ r, B r)*a i ≤ (1+ct*h i/ell)*B i) ∧
      (∑ i, B i)*movement a a₀ ≤ (∑ i, g i (a₀ i))-(∑ i, g i (a i)) := by
  have hc : ContinuousOn (objective g (∑ i, B i) a₀) {a | simplex a} := by
    apply ContinuousOn.add
    · apply continuousOn_finsetSum
      intro i _
      exact (H.continuous i).comp (continuous_apply i).continuousOn
        (fun a ha => ⟨ha.1 i, coordinate_le_one ha i⟩)
    · unfold movement
      exact Continuous.continuousOn (by fun_prop)
  obtain ⟨a, ha, hm⟩ := simplex_compact.exists_isMinOn ⟨a₀, ha₀⟩ hc
  refine ⟨a, ha, hm, minimum_feasible H ha hm, ?_⟩
  have hh : objective g (∑ i, B i) a₀ a ≤ objective g (∑ i, B i) a₀ a₀ := hm ha₀
  simp only [objective, movement, sub_self, abs_zero, Finset.sum_const_zero, mul_zero, add_zero] at hh ⊢
  linarith

end UniformKServer.SimplexTracker


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaTracker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace UniformKServer.AlphaTracker
open Set Filter
open scoped Topology
open UniformKServer.Denominators UniformKServer.LogPrimitive UniformKServer.SimplexTracker
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def regularG (h B : ι → ℝ) (ell ct C : ℝ) (i : ι) : ℝ → ℝ :=
  primitive (regular (h i)) 0 (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i)
noncomputable def markedF (o : ι) (u : ℝ) (h : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  if i = o then marked u x else regular (h i) x
noncomputable def markedG (o : ι) (u : ℝ) (h B : ι → ℝ) (ell ct C : ℝ) (i : ι) : ℝ → ℝ :=
  primitive (markedF o u h i) (if i = o then 1 else 0)
    (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i)
def UpdateConclusion (g : ι → ℝ → ℝ) (B h : ι → ℝ) (ell ct : ℝ) (a₀ : ι → ℝ) : Prop :=
  ∃ a, simplex a ∧ IsMinOn (objective g (∑ i, B i) a₀) {a | simplex a} a ∧
    (∀ i, (∑ r, B r)*a i ≤ (1+ct*h i/ell)*B i) ∧
    (∑ i, B i)*movement a a₀ ≤ (∑ i, g i (a₀ i))-(∑ i, g i (a i))
-- CANDIDATE PROOFS
omit [DecidableEq ι] in
theorem analytic_data {g : ι → ℝ → ℝ} {B h : ι → ℝ} {F : ι → ℝ → ℝ}
    {ell ct C A E : ℝ} (hB : ∀ i, 0 ≤ B i) (hh : ∀ i, 0 < h i)
    (hl : 0 < ell) (hc : 0 < ct) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (heta : ∀ i, ct*h i/ell ≤ E) (hm : 2*A*(1+E) < C*ct)
    (hF : ∀ i x, 0 < x → x ≤ 1 → 0 < F i x)
    (hsum : ∀ a, simplex a → (∑ i, a i*F i (a i)) ≤ A*(∑ i, a i*h i))
    (hg : ∀ i, Contract (g i) (F i) (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i)) :
    AnalyticData g B h F ell ct C A E := by
  have hC : 0 < C := pos_of_mul_pos_left
    (lt_of_le_of_lt (by positivity : 0 ≤ 2*A*(1+E)) hm) hc.le
  refine ⟨hB, hh, hl, hc, hA, hE, heta, hm, hF, hsum, fun i => (hg i).1, ?_, ?_⟩
  · intro i x hx hx₁
    convert! (hg i).2.1 x hx hx₁ using 1 ; ring
  · intro i hi
    apply (hg i).2.2
    · apply mul_pos _ hi
      have hp := div_pos (mul_pos hc (hh i)) hl
      linarith
    · exact mul_pos hC hl

theorem regular_update (h B a₀ : ι → ℝ) (ell ct C E Z : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hh : ∀ i, 1 ≤ h i) (hl : 0 < ell) (hc : 0 < ct)
    (hE : 0 ≤ E) (hZ : 0 ≤ Z) (heta : ∀ i, ct*h i/ell ≤ E)
    (hm : 2*(25+32*Z)*(1+E) < C*ct) (he : (∑ i, Real.exp (-h i)) ≤ Z)
    (ha₀ : simplex a₀) : UpdateConclusion (regularG h B ell ct C) B h ell ct a₀ := by
  apply update _ B h (fun i => regular (h i)) ell ct C (25+32*Z) E _ a₀ ha₀
  apply analytic_data hB (fun i => lt_of_lt_of_le (by norm_num) (hh i)) hl hc
    (by positivity) hE heta hm
  · exact fun i x hx hx₁ => regular_pos (by linarith [hh i]) hx.le hx₁
  · exact fun a ha => regular_simplex h a Z hh ha.1 ha.2 he
  · exact fun i => regular_contract (h i) (C*ell) (∑ r, B r) ((1+ct*h i/ell)*B i) (hh i)

end UniformKServer.AlphaTracker

end


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideTracker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

                                                                          
                                                                       
noncomputable section
namespace UniformKServer.SideTracker
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def domain (W : ℝ) (w : ι → ℝ) : Prop := (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ W

def coordinate (b θ z C B D s : ℝ) : ℝ :=
  C*(D/θ*(s-z*Real.log (1+s/z)) + D*z*Real.log (1+s/z)/2 -
    (b+θ/2)*B*Real.log (1+s/z)/θ)

def potential (b C D : ℝ) (θ z B w : ι → ℝ) : ℝ :=
  ∑ i, coordinate b (θ i) (z i) C (B i) D (w i)

def movement (w v : ι → ℝ) : ℝ := ∑ i, |w i-v i|

-- CANDIDATE PROOFS
theorem right_derivative_nonneg {f : ℝ → ℝ} {d δ : ℝ} (hδ : 0 < δ)
    (hf : HasDerivAt f d 0) (hmin : ∀ s, 0 < s → s < δ → f 0 ≤ f s) : 0 ≤ d := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with s hs hsδ
  simp only [Set.mem_Ioi, Set.mem_Iio] at hs hsδ
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (sub_nonneg.mpr (hmin s hs hsδ))

omit [DecidableEq ι] in
theorem domain_compact (W : ℝ) : IsCompact {w : ι → ℝ | domain W w} := by
  have h₁ : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h₂ : IsClosed {w : ι → ℝ | ∑ i, w i ≤ W} := isClosed_le (by fun_prop) continuous_const
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => (0 : ℝ)) (fun _ => W))).of_isClosed_subset (h₁.inter h₂)
  intro w hw
  refine ⟨hw.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)).trans hw.2

theorem coordinate_continuous {b θ z C B D s : ℝ} (hz : 0 < z) (hs : 0 ≤ s) :
    ContinuousAt (coordinate b θ z C B D) s := by
  have hl : ContinuousAt (fun s : ℝ => Real.log (1+s/z)) s := by
    apply ContinuousAt.log (by fun_prop)
    have : 0 ≤ s/z := div_nonneg hs hz.le
    linarith
  unfold coordinate
  fun_prop

theorem coordinate_deriv {b θ z C B D s : ℝ} (hθ : 0 < θ) (hz : 0 < z) (hs : 0 ≤ s) :
    HasDerivAt (coordinate b θ z C B D)
      (C*(D*s-(b+θ/2)*B+D*θ*z/2)/(θ*(s+z))) s := by
  have he : 1+s/z ≠ 0 := by have := div_nonneg hs hz.le; linarith
  have hl : HasDerivAt (fun s : ℝ => Real.log (1+s/z)) (1/(s+z)) s := by
    convert! (((hasDerivAt_id s).div_const z).const_add 1).log he using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq]
    field_simp [hz.ne', (add_pos_of_nonneg_of_pos hs hz).ne']
    ring
  have hh := (((hasDerivAt_id s).sub (hl.const_mul z)).const_mul (D/θ)).add
    ((hl.const_mul (D*z)).div_const 2)
  have hh' := (hh.sub ((hl.const_mul ((b+θ/2)*B)).div_const θ)).const_mul C
  convert! hh' using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hθ.ne', (add_pos_of_nonneg_of_pos hs hz).ne']
  ring

theorem sum_update (w : ι → ℝ) (i : ι) (s : ℝ) :
    ∑ j, Function.update w i (w i+s) j = (∑ j, w j)+s := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

theorem potential_update (g : ι → ℝ → ℝ) (w : ι → ℝ) (i : ι) (s : ℝ) :
    (∑ j, g j (Function.update w i (w i+s) j)) =
    (∑ j, g j (w j))+g i (w i+s)-g i (w i) := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ (fun j => g j (w j)) (Finset.mem_univ i)]
  have he : ∑ j ∈ Finset.univ.erase i, g j (Function.update w i (w i+s) j) =
      ∑ j ∈ Finset.univ.erase i, g j (w j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he, Function.update_self]
  ring

theorem movement_update_le (w v : ι → ℝ) (i : ι) (s : ℝ) :
    movement (Function.update w i (w i+s)) v ≤ movement w v+|s| := by
  unfold movement
  rw [potential_update (fun j t => |t-v j|)]
  have hh := abs_add_le (w i-v i) s
  have he : w i+s-v i = (w i-v i)+s := by ring
  rw [he]
  linarith

theorem gradient_upper (g : ι → ℝ → ℝ) (W D : ℝ) (w₀ w : ι → ℝ)
    (hD : 0 ≤ D) (hw : domain W w)
    (hmin : ∀ v, domain W v → (∑ i, g i (w i))+D*movement w w₀ ≤
      (∑ i, g i (v i))+D*movement v w₀)
    (i : ι) (hwpos : 0 < w i) {d : ℝ} (hg : HasDerivAt (g i) d (w i)) : d ≤ D := by
  have hd : HasDerivAt (fun s => g i (w i-s)+D*s) (-d+D) 0 := by
    have hgi : HasDerivAt (g i) d (w i-id 0) := by simpa using hg
    have hh := hgi.comp 0 ((hasDerivAt_id 0).const_sub (w i))
    convert! hh.add ((hasDerivAt_id 0).const_mul D) using 1 ; simp
  have hge := right_derivative_nonneg hwpos hd (fun s hs hsδ => ?_)
  · linarith
  have hv : domain W (Function.update w i (w i + -s)) := by
    refine ⟨?_, ?_⟩
    · intro j
      by_cases he : j = i
      · subst j; simp only [Function.update_self] <;> linarith
      · rw [Function.update_of_ne he]; exact hw.1 j
    · rw [sum_update]; linarith [hw.2]
  have hh := hmin _ hv
  rw [potential_update] at hh
  have hm := mul_le_mul_of_nonneg_left (movement_update_le w w₀ i (-s)) hD
  rw [abs_neg, abs_of_nonneg hs.le] at hm
  simp only [sub_zero, mul_zero, add_zero]
  simp only [← sub_eq_add_neg] at hh hm
  linarith

theorem gradient_lower (g : ι → ℝ → ℝ) (W D : ℝ) (w₀ w : ι → ℝ)
    (hD : 0 ≤ D) (hw : domain W w) (hroom : ∑ i, w i < W)
    (hmin : ∀ v, domain W v → (∑ i, g i (w i))+D*movement w w₀ ≤
      (∑ i, g i (v i))+D*movement v w₀)
    (i : ι) {d : ℝ} (hg : HasDerivAt (g i) d (w i)) : -D ≤ d := by
  have hd : HasDerivAt (fun s => g i (w i+s)+D*s) (d+D) 0 := by
    have hgi : HasDerivAt (g i) d (w i+id 0) := by simpa using hg
    have hh := hgi.comp 0 ((hasDerivAt_id 0).const_add (w i))
    convert! hh.add ((hasDerivAt_id 0).const_mul D) using 1 ; simp
  have hge := right_derivative_nonneg (sub_pos.mpr hroom) hd (fun s hs hsδ => ?_)
  · linarith
  have hv : domain W (Function.update w i (w i+s)) := by
    refine ⟨?_, ?_⟩
    · intro j
      by_cases he : j = i
      · subst j; simp only [Function.update_self] <;> linarith [hw.1 i]
      · rw [Function.update_of_ne he]; exact hw.1 j
    · rw [sum_update]; linarith
  have hh := hmin _ hv
  rw [potential_update] at hh
  have hm := mul_le_mul_of_nonneg_left (movement_update_le w w₀ i s) hD
  rw [abs_of_nonneg hs.le] at hm
  simp only [add_zero, mul_zero]
  linarith


theorem upper_violation {b θ z C B D s : ℝ}
    (hb : 0 < b) (hθ : 0 < θ) (hz : 0 < z) (hB : 0 ≤ B) (hD : 0 < D)
    (hs : 0 ≤ s) (hC : 4*(b+θ+1) ≤ C) (hv : (b+θ)*B < D*s) :
    D < C*(D*s-(b+θ/2)*B+D*θ*z/2)/(θ*(s+z)) := by
  let N := D*s-(b+θ/2)*B+D*θ*z/2
  let e := D*s-(b+θ)*B
  have he : 0 < e := sub_pos.mpr hv
  have heN : N = e+θ*B/2+D*θ*z/2 := by dsimp [N,e] <;> ring
  have hN : 0 < N := by rw [heN]; positivity
  have hq : 0 < 2*(b+θ+1)-θ := by linarith
  have hid : 2*(b+θ+1)*N-D*θ*(s+z) =
      (2*(b+θ+1)-θ)*e+θ*B+D*θ*(b+θ)*z := by dsimp [N,e] <;> ring
  have hstrict : D*θ*(s+z) < 2*(b+θ+1)*N := by
    apply sub_pos.mp
    rw [hid]
    positivity
  have hlarge : 2*(b+θ+1) ≤ C := by linarith
  apply (lt_div_iff₀ (mul_pos hθ (add_pos_of_nonneg_of_pos hs hz))).mpr
  change D*(θ*(s+z)) < C*N
  calc
    D*(θ*(s+z)) = D*θ*(s+z) := by ring
    _ < 2*(b+θ+1)*N := hstrict
    _ ≤ C*N := mul_le_mul_of_nonneg_right hlarge hN.le

theorem lower_violation {b θ z C B D s : ℝ}
    (hb : 0 < b) (hθ : 0 < θ) (hz : 0 < z) (hB : 0 ≤ B) (hD : 0 < D)
    (hs : 0 ≤ s) (hC : 4*(b+θ+1) ≤ C) (hv : D*s < b*B-θ*z*D) :
    C*(D*s-(b+θ/2)*B+D*θ*z/2)/(θ*(s+z)) < -D := by
  let N := D*s-(b+θ/2)*B+D*θ*z/2
  let e := b*B-D*s-D*θ*z
  have he : 0 < e := by dsimp [e] <;> nlinarith
  have heN : -N = e+θ*B/2+D*θ*z/2 := by dsimp [N,e] <;> ring
  have hN : 0 < -N := by rw [heN]; positivity
  have hq : 0 < 2*(b+1)+θ := by linarith
  have hid : 2*(b+1)*(-N)-D*θ*(s+z) =
      (2*(b+1)+θ)*e+θ*B+D*θ^2*z+D*θ*b*z := by dsimp [N,e] <;> ring
  have hstrict : D*θ*(s+z) < 2*(b+1)*(-N) := by
    apply sub_pos.mp
    rw [hid]
    positivity
  have hlarge : 2*(b+1) ≤ C := by linarith
  have hh := hstrict.trans_le (mul_le_mul_of_nonneg_right hlarge hN.le)
  apply (div_lt_iff₀ (mul_pos hθ (add_pos_of_nonneg_of_pos hs hz))).mpr
  change C*N < -D*(θ*(s+z))
  nlinarith


theorem side_update (b C D W m S : ℝ) (θ z B w₀ : ι → ℝ)
    (hb : 0 < b) (hD : 0 ≤ D) (hm : 0 ≤ m) (hW : 2*m < W)
    (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i) (hB : ∀ i, 0 ≤ B i)
    (hS : ∑ i, B i ≤ S) (hbound : ∀ i, b+θ i ≤ m)
    (hC : ∀ i, 4*(b+θ i+1) ≤ C) (hw₀ : domain W w₀) :
    ∃ w, domain W w ∧
      (∀ i, D*w i ≤ (b+θ i)*B i) ∧
      (S ≤ 2*D → ∀ i, b*B i-θ i*z i*D ≤ D*w i) ∧
      D*movement w w₀ ≤ potential b C D θ z B w₀-potential b C D θ z B w := by
  have hc : ContinuousOn (fun w => potential b C D θ z B w+D*movement w w₀)
      {w | domain W w} := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.add
    · unfold potential
      apply tendsto_finsetSum
      intro i hi
      exact (coordinate_continuous (hz i) (hw.1 i)).comp' (f := fun v : ι → ℝ => v i) (continuous_apply i).continuousAt
    · exact (show Continuous (fun w => D*movement w w₀) by unfold movement; fun_prop).continuousAt
  obtain ⟨w, hw, hwmin⟩ := (domain_compact (ι := ι) W).exists_isMinOn ⟨w₀, hw₀⟩ hc
  have hmin : ∀ v, domain W v →
      (∑ i, coordinate b (θ i) (z i) C (B i) D (w i))+D*movement w w₀ ≤
      (∑ i, coordinate b (θ i) (z i) C (B i) D (v i))+D*movement v w₀ := by
    intro v hv
    exact hwmin hv
  refine ⟨w, hw, ?_, ?_, ?_⟩
  · intro i
    by_cases he : D = 0
    · subst D
      simp only [zero_mul]
      exact mul_nonneg (add_pos hb (hθ i)).le (hB i)
    have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm he)
    by_contra hn
    have hv := lt_of_not_ge hn
    have hwi : 0 < w i := by
      have hbB := mul_nonneg (add_pos hb (hθ i)).le (hB i)
      by_contra hnw
      have := mul_nonpos_of_nonneg_of_nonpos hD (le_of_not_gt hnw)
      linarith
    have hu := gradient_upper _ W D w₀ w hD hw hmin i hwi
      (coordinate_deriv (hθ i) (hz i) (hw.1 i))
    have hv' := upper_violation hb (hθ i) (hz i) (hB i) hDp (hw.1 i) (hC i) hv
    linarith
  · intro hSD i
    by_cases he : D = 0
    · subst D
      have hzero : B i = 0 := by
        have hle := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
        have : S ≤ 0 := by simpa using hSD
        linarith [hB i]
      simp [hzero]
    have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm he)
    have hu : ∀ j, D*w j ≤ (b+θ j)*B j := by
      intro j
      by_contra hn
      have hv := lt_of_not_ge hn
      have hwj : 0 < w j := by
        have hbB := mul_nonneg (add_pos hb (hθ j)).le (hB j)
        by_contra hnw
        have := mul_nonpos_of_nonneg_of_nonpos hD (le_of_not_gt hnw)
        linarith
      have hh := gradient_upper _ W D w₀ w hD hw hmin j hwj
        (coordinate_deriv (hθ j) (hz j) (hw.1 j))
      have hv' := upper_violation hb (hθ j) (hz j) (hB j) hDp (hw.1 j) (hC j) hv
      linarith
    have hsum : D*(∑ j, w j) ≤ m*(2*D) := by
      calc
        D*(∑ j, w j) = ∑ j, D*w j := Finset.mul_sum ..
        _ ≤ ∑ j, (b+θ j)*B j := Finset.sum_le_sum fun j _ => hu j
        _ ≤ ∑ j, m*B j := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hbound j) (hB j)
        _ = m*(∑ j, B j) := (Finset.mul_sum ..).symm
        _ ≤ m*S := mul_le_mul_of_nonneg_left hS hm
        _ ≤ m*(2*D) := mul_le_mul_of_nonneg_left hSD hm
    have hroom : ∑ j, w j < W := by nlinarith
    by_contra hn
    have hv := lt_of_not_ge hn
    have hl := gradient_lower _ W D w₀ w hD hw hroom hmin i
      (coordinate_deriv (hθ i) (hz i) (hw.1 i))
    have hv' := lower_violation hb (hθ i) (hz i) (hB i) hDp (hw.1 i) (hC i) hv
    linarith
  · have hh : potential b C D θ z B w+D*movement w w₀ ≤
        potential b C D θ z B w₀+D*movement w₀ w₀ := hwmin hw₀
    have hm₀ : movement w₀ w₀ = 0 := by simp [movement]
    rw [hm₀, mul_zero, add_zero] at hh
    linarith

end UniformKServer.SideTracker

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_DomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Zero-extension and the exact prepared domain-change operation in companion
 §04. Departing coordinates are NOT erased until the minimizing feasibility
 inequalities have been obtained for the synthetic common-core input. -/
noncomputable section
namespace UniformKServer.DomainTransport
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def Supported (I : Finset ι) (a : ι → ℝ) : Prop := ∀ i, i ∉ I → a i=0

def extend (I : Finset ι) (a : I → ℝ) (i : ι) : ℝ := if h : i ∈ I then a ⟨i,h⟩ else 0

def simplex (I : Finset ι) (a : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ Supported I a ∧ ∑ i, a i=1

def domain (I : Finset ι) (W : ℝ) (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ Supported I w ∧ ∑ i, w i ≤ W

theorem sum_restrict {I : Finset ι} {a : ι → ℝ} (ha : Supported I a) :
    (∑ i : I, a i)=∑ i, a i := by
  rw [sum_coe_sort]
  exact sum_subset (subset_univ I) (fun i _ hi => ha i hi)

omit [Fintype ι] in
theorem extend_supported (I : Finset ι) (a : I → ℝ) : Supported I (extend I a) := by
  intro i hi
  simp [extend,hi]

omit [Fintype ι] in
theorem extend_apply (I : Finset ι) (a : I → ℝ) (i : I) : extend I a i=a i := by
  simp [extend,i.property]

theorem extend_sum (I : Finset ι) (a : I → ℝ) : (∑ i, extend I a i)=∑ i : I, a i := by
  rw [←sum_restrict (extend_supported I a)]
  apply sum_congr rfl
  intro i _
  exact extend_apply I a i

theorem restrict_simplex {I : Finset ι} {a : ι → ℝ} (ha : simplex I a) :
    SimplexTracker.simplex (fun i : I => a i) := by
  refine ⟨fun i => ha.1 i,?_⟩
  rw [sum_restrict ha.2.1,ha.2.2]

theorem extend_simplex {I : Finset ι} {a : I → ℝ} (ha : SimplexTracker.simplex a) :
    simplex I (extend I a) := by
  refine ⟨?_,extend_supported I a,?_⟩
  · intro i
    unfold extend
    split_ifs with h
    · exact ha.1 ⟨i,h⟩
    · rfl
  · rw [extend_sum]
    exact ha.2

theorem exists_simplex {I : Finset ι} (hI : I.Nonempty) : ∃ a, simplex I a := by
  obtain ⟨i,hi⟩ := hI
  refine ⟨fun j => if j=i then 1 else 0,?_,?_,?_⟩
  · intro j; dsimp; split_ifs <;> norm_num
  · intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj hi
    simp [hji]
  · simp

theorem potential_restrict {I : Finset ι} (g : ι → ℝ → ℝ) {a : ι → ℝ}
    (ha : Supported I a) (hg : ∀ i, i ∉ I → g i 0=0) :
    (∑ i : I, g i (a i))=∑ i, g i (a i) :=
  sum_restrict (a:=fun i => g i (a i)) (fun i hi => by dsimp; rw [ha i hi,hg i hi])

theorem movement_extend (I : Finset ι) (a : I → ℝ) {b : ι → ℝ} (hb : Supported I b) :
    SimplexTracker.movement (extend I a) b =
      SimplexTracker.movement a (fun i : I => b i) := by
  unfold SimplexTracker.movement
  have hs : Supported I (fun i => |extend I a i-b i|) := by
    intro i hi
    dsimp
    rw [extend_supported I a i hi,hb i hi,sub_self,abs_zero]
  rw [←sum_restrict hs]
  apply sum_congr rfl
  intro i _
  rw [extend_apply]

def delete (J : Finset ι) (w : ι → ℝ) (i : ι) : ℝ := if i ∈ J then w i else 0

theorem delete_domain {I J : Finset ι} {w : ι → ℝ} {W : ℝ} (hw : domain I W w) :
    domain J W (delete J w) := by
  refine ⟨?_,?_,?_⟩
  · intro i; unfold delete; split_ifs; exact hw.1 i; rfl
  · intro i hi; simp [delete,hi]
  · refine (sum_le_sum fun i _ => ?_).trans hw.2.2
    unfold delete
    split_ifs
    · rfl
    · exact hw.1 i

/-- Exact side primitive is unchanged by prepared deletion, including D=0. -/
theorem prepared_side {I J : Finset ι} {w B θ z : ι → ℝ} {W D b C : ℝ}
    (hw : domain I W w) (hD : 0 ≤ D) (hB : Supported J B)
    (hf : ∀ i, i ∉ J → D*w i ≤ (b+θ i)*B i) :
    domain J W (delete J w) ∧ D*SideTracker.movement (delete J w) w=0 ∧
      SideTracker.potential b C D θ z B (delete J w)=SideTracker.potential b C D θ z B w := by
  refine ⟨delete_domain hw,?_,?_⟩
  · rcases hD.eq_or_lt with he | hp
    · rw [←he,zero_mul]
    · have hd : delete J w=w := by
        funext i
        unfold delete
        split_ifs with hi
        · rfl
        · have h := hf i hi
          rw [hB i hi,mul_zero] at h
          exact (le_antisymm (by nlinarith : w i ≤ 0) (hw.1 i)).symm
      simp [hd,SideTracker.movement]
  · unfold SideTracker.potential
    apply sum_congr rfl
    intro i _
    by_cases hi : i ∈ J
    · simp [delete,hi]
    · rcases hD.eq_or_lt with he | hp
      · simp [delete,hi,hB i hi,←he,SideTracker.coordinate]
      · have h := hf i hi
        rw [hB i hi,mul_zero] at h
        have hz : w i=0 := le_antisymm (by nlinarith : w i ≤ 0) (hw.1 i)
        simp [delete,hi,hz]

end UniformKServer.DomainTransport

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Epochs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer
structure Entry (n k : ℕ) where
  position : Configuration n k
  moves : ℕ

/-- Number of nodes in the full k-ary tree of depth m. -/
def treeBudget (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => 1 + k * treeBudget k m

@[simp] theorem treeBudget_zero (k : ℕ) : treeBudget k 0 = 1 := rfl
@[simp] theorem treeBudget_succ (k m : ℕ) :
    treeBudget k (m+1) = 1 + k * treeBudget k m := rfl

def weight {n k : ℕ} (M : ℕ) (e : Entry n k) : ℕ := treeBudget k (M - e.moves)

def mass {n k : ℕ} (M : ℕ) (es : List (Entry n k)) : ℕ :=
  (es.map (weight M)).sum

@[simp] theorem mass_nil {n k : ℕ} (M : ℕ) : mass M ([] : List (Entry n k)) = 0 := rfl
@[simp] theorem mass_cons {n k : ℕ} (M : ℕ) (e : Entry n k) (es : List (Entry n k)) :
    mass M (e :: es) = weight M e + mass M es := rfl

@[simp] theorem mass_append {n k : ℕ} (M : ℕ) (a b : List (Entry n k)) :
    mass M (a ++ b) = mass M a + mass M b := by simp [mass]

end UniformKServer



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

                                                                          
                                                                                

noncomputable section
namespace UniformKServer.UniformIntegrals
open MeasureTheory Set Filter
open scoped Topology

def height (u : ℝ) : ℝ := 1 + Real.log (1/u)
def regular (h y : ℝ) : ℝ := (h+y)^2/h
def marked (u y : ℝ) : ℝ := u + height u*y*(1+y)

theorem height_ge_one {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) : 1 ≤ height u := by
  unfold height
  have hh := Real.log_nonneg ((le_div_iff₀ hu).mpr (by simpa using hu₁))
  linarith

theorem regular_deriv {h : ℝ} (hh : 0 < h) {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt (fun z => -h/(h+z)) (1/regular h y) y := by
  have hd := (hasDerivAt_const y (-h)).div ((hasDerivAt_id y).const_add h) (by linarith : h+y ≠ 0)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp [regular]

theorem regular_tendsto (h : ℝ) : Tendsto (fun y : ℝ => -h/(h+y)) atTop (𝓝 0) := by
  have hh : Tendsto (fun y : ℝ => h+y) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  simpa [div_eq_mul_inv] using hh.inv_tendsto_atTop.const_mul (-h)

theorem regular_integrable {h : ℝ} (hh : 1 ≤ h) :
    IntegrableOn (fun y => 1 / regular h y) (Ioi 0) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (fun y hy => regular_deriv (by linarith) hy) _ (regular_tendsto h)
  intro y hy
  dsimp [regular]
  positivity

theorem regular_integral {h : ℝ} (hh : 1 ≤ h) :
    (∫ y in Ioi (0:ℝ), 1 / regular h y) = 1 := by
  have hx := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y (hy : y ∈ Ici (0:ℝ)) => regular_deriv (show 0 < h by linarith) hy)
    (regular_integrable hh) (regular_tendsto h)
  simpa [ne_of_gt (show 0 < h by linarith)] using hx

theorem marked_pos {u y : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hy : 0 ≤ y) : 0 < marked u y := by
  dsimp [marked]
  have hh := height_ge_one hu hu₁
  positivity

theorem marked_local {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntegrableOn (fun y => 1/marked u y) (Ioc 0 1) volume := by
  apply (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
  apply continuousOn_const.div
  · unfold marked; fun_prop
  · intro y hy; exact ne_of_gt (marked_pos hu hu₁ hy.1)

theorem tail_deriv {y : ℝ} (hy : 1 ≤ y) : HasDerivAt (fun z : ℝ => -1/z) (1/y^2) y := by
  convert! (hasDerivAt_const y (-1:ℝ)).div (hasDerivAt_id y) (by linarith : y ≠ 0) using 1
  all_goals try with_reducible_and_instances rfl
  simp

theorem tail_tendsto : Tendsto (fun y : ℝ => -1/y) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).const_mul (-1)

theorem tail_integrable : IntegrableOn (fun y : ℝ => 1/y^2) (Ioi 1) volume := by
  exact integrableOn_Ioi_deriv_of_nonneg' (fun y hy => tail_deriv hy) (fun y hy => by positivity) tail_tendsto

theorem tail_integral : (∫ y in Ioi (1:ℝ), 1/y^2) = 1 := by
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun y hy => tail_deriv hy) tail_integrable tail_tendsto

theorem marked_tail_bound {u y : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hy : 1 ≤ y) :
    1/marked u y ≤ 1/height u * (1/y^2) := by
  have hh := height_ge_one hu hu₁
  rw [one_div_mul_one_div]
  apply one_div_le_one_div_of_le
  · positivity
  · dsimp [marked]
    nlinarith [mul_nonneg (show 0 ≤ height u by linarith) (show 0 ≤ y by linarith)]

theorem marked_tail {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntegrableOn (fun y => 1/marked u y) (Ioi 1) volume := by
  refine (tail_integrable.const_mul (1/height u)).mono' ?_ ?_
  · apply (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi)
    apply continuousOn_const.div
    · unfold marked; fun_prop
    · intro y hy; exact ne_of_gt (marked_pos hu hu₁ (by have := (show 1 < y from hy); linarith))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (one_div_pos.mpr (marked_pos hu hu₁ (by have := (show 1 < y from hy); linarith))))]
    exact marked_tail_bound hu hu₁ (le_of_lt hy)

theorem marked_integrable {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntegrableOn (fun y => 1 / marked u y) (Ioi 0) volume := by
  have hs : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext y
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hy : y ≤ 1
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr (lt_of_not_ge hy)
  rw [← hs]
  exact (marked_local hu hu₁).union (marked_tail hu hu₁)

theorem linear_local {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntervalIntegrable (fun y => 1/(u+height u*y)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply continuousOn_const.div (by fun_prop)
  intro y hy
  have hh := height_ge_one hu hu₁
  exact ne_of_gt (by nlinarith [hy.1] : 0 < u+height u*y)

theorem linear_integral {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in (0:ℝ)..1, 1/(u+height u*y)) = (Real.log (u+height u)-Real.log u)/height u := by
  have hh := height_ge_one hu hu₁
  have hd : ∀ y ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun z => Real.log (u+height u*z)/height u) (1/(u+height u*y)) y := by
    intro y hy
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
    have hp : 0 < u+height u*y := by nlinarith [hy.1]
    convert! (((hasDerivAt_id y).const_mul (height u)).const_add u).log hp.ne' |>.div_const (height u) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [id_eq, mul_one]
    field_simp
  convert! intervalIntegral.integral_eq_sub_of_hasDerivAt hd (linear_local hu hu₁) using 1
  all_goals try with_reducible_and_instances rfl
  simp
  ring

theorem log_bound {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (Real.log (u+height u)-Real.log u)/height u ≤ 2 := by
  have hh := height_ge_one hu hu₁
  have hm : Real.log (u+height u) ≤ Real.log (1+height u) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+height u by linarith)
  have he : Real.log u = 1-height u := by simp [height, one_div, Real.log_inv]
  apply (div_le_iff₀ (show 0 < height u by linarith)).mpr
  linarith

theorem marked_local_integral {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in Ioc (0:ℝ) 1, 1/marked u y) ≤ 2 := by
  have hh := height_ge_one hu hu₁
  have hi : IntegrableOn (fun y => 1/(u+height u*y)) (Ioc 0 1) volume := (linear_local hu hu₁).1
  calc
    _ ≤ ∫ y in Ioc (0:ℝ) 1, 1/(u+height u*y) := by
      apply setIntegral_mono_on (marked_local hu hu₁) hi measurableSet_Ioc
      intro y hy
      apply one_div_le_one_div_of_le
      · nlinarith [hy.1]
      · unfold marked
        nlinarith [mul_nonneg (show 0 ≤ height u by linarith) (sq_nonneg y)]
    _ = (Real.log (u+height u)-Real.log u)/height u := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact linear_integral hu hu₁
    _ ≤ 2 := log_bound hu hu₁

theorem marked_tail_integral {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in Ioi (1:ℝ), 1/marked u y) ≤ 1 := by
  calc
    _ ≤ ∫ y in Ioi (1:ℝ), 1/height u * (1/y^2) :=
      setIntegral_mono_on (marked_tail hu hu₁) (tail_integrable.const_mul _) measurableSet_Ioi
        (fun y hy => marked_tail_bound hu hu₁ (le_of_lt hy))
    _ = 1/height u := by rw [integral_const_mul, tail_integral, mul_one]
    _ ≤ 1 := (div_le_one (show 0 < height u by linarith [height_ge_one hu hu₁])).mpr (height_ge_one hu hu₁)

theorem marked_integral_uniform {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    (∫ y in Ioi (0:ℝ), 1 / marked u y) ≤ 3 := by
  have hs : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext y; simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hy : y ≤ 1
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr (lt_of_not_ge hy)
  have hd : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := Set.disjoint_left.mpr (fun y hy hz => not_lt_of_ge hy.2 hz)
  rw [← hs, setIntegral_union hd measurableSet_Ioi
    (marked_local hu hu₁) (marked_tail hu hu₁)]
  linarith [marked_local_integral hu hu₁, marked_tail_integral hu hu₁]

end UniformKServer.UniformIntegrals

namespace UniformKServer.AlphaBounds
open MeasureTheory Set Filter
open scoped Topology
open UniformKServer.LogPrimitive

local notation "reg" => UniformKServer.Denominators.regular
local notation "mark" => UniformKServer.Denominators.marked

theorem logarithmic_substitution (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    (∫ x in a..1, 1/(x * F (Real.log (1/x)))) =
      ∫ y in (0:ℝ)..Real.log (1/a), 1/F y := by
  have hI : uIcc a 1 = Icc a 1 := uIcc_of_le ha₁
  have hf : ContinuousOn (fun x : ℝ => -Real.log x) (uIcc a 1) := by
    rw [hI]
    exact (continuousOn_id.log (fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1))).neg
  have hd : ∀ x ∈ Ioo (min a 1) (max a 1), HasDerivAt (fun x : ℝ => -Real.log x) (-1/x) x := by
    intro x hx
    rw [min_eq_left ha₁, max_eq_right ha₁] at hx
    convert! (Real.hasDerivAt_log (ne_of_gt (lt_trans ha hx.1))).neg using 1
    all_goals try with_reducible_and_instances rfl
    simp [div_eq_mul_inv]
  have hn : ∀ x ∈ Ioo (min a 1) (max a 1), -1/x ≤ (0:ℝ) := by
    intro x hx
    rw [min_eq_left ha₁, max_eq_right ha₁] at hx
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt (lt_trans ha hx.1))
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (g := fun y => 1/F y) hf hd hn
  have hl : (fun x : ℝ => ((fun y => 1/F y) ∘ (fun x => -Real.log x)) x * (-1/x)) =
      fun x => -(1/(x * F (Real.log (1/x)))) := by
    funext x
    simp only [Function.comp_apply, one_div, Real.log_inv, neg_div]
    ring
  rw [hl, intervalIntegral.integral_neg] at he
  simp only [Real.log_one, neg_zero] at he
  rw [intervalIntegral.integral_symm (f := fun y => 1/F y) 0] at he
  simpa only [neg_inj, ← Real.log_inv, ← one_div] using he

theorem weighted_integral_positive {F : ℝ → ℝ} {C a : ℝ}
    (hint : IntegrableOn (fun y => 1/F y) (Ioi 0) volume)
    (hpos : ∀ y, 0 ≤ y → 0 < F y)
    (hbound : (∫ y in Ioi (0:ℝ), 1/F y) ≤ C) (ha : 0 < a) (ha₁ : a ≤ 1) :
    (∫ x in a..1, 1/(x*F (Real.log (1/x)))) ≤ C := by
  rw [logarithmic_substitution F ha ha₁,
    intervalIntegral.integral_of_le (UniformKServer.Denominators.log_nonneg ha.le ha₁)]
  apply le_trans (setIntegral_mono_set hint ?_ ?_) hbound
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (one_div_pos.mpr (hpos y (le_of_lt hy))).le
  · exact Filter.Eventually.of_forall fun y hy => hy.1

theorem weighted_integral_closed {D : ℝ → ℝ} {C : ℝ}
    (hc : ContinuousOn (fun a => ∫ x in a..1, 1/(x*D x)) (Icc 0 1))
    (hb : ∀ a, 0 < a → a ≤ 1 → (∫ x in a..1, 1/(x*D x)) ≤ C)
    {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) : (∫ x in a..1, 1/(x*D x)) ≤ C := by
  apply le_on_closure (s := Ioc (0:ℝ) 1) (f := fun a => ∫ x in a..1, 1/(x*D x))
    (g := fun _ => C) (fun a ha => hb a ha.1 ha.2)
  · simpa only [closure_Ioc (by norm_num : (0:ℝ) ≠ 1)] using hc
  · exact continuousOn_const
  · simpa only [closure_Ioc (by norm_num : (0:ℝ) ≠ 1)] using ha

theorem weight_continuous {D : ℝ → ℝ}
    (hc : ContinuousOn (primitive D 1 1 0 (-1)) (Icc 0 1)) :
    ContinuousOn (fun a => ∫ x in a..1, 1/(x*D x)) (Icc 0 1) := by
  apply hc.neg.congr
  intro a ha
  change (∫ x in a..1, 1/(x*D x)) = -(primitive D 1 1 0 (-1) a)
  simp only [primitive, one_mul, zero_sub, neg_div, neg_neg, div_div]
  exact intervalIntegral.integral_symm _ _

theorem regular_weight {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Icc (0:ℝ) 1) :
    (∫ x in a..1, 1/(x*reg h x)) ≤ 1 := by
  apply weighted_integral_closed _ _ ha
  · apply weight_continuous
    -- Contracts at either base follow from the same integrable density.
    have hc := (regular_contract h 1 0 (-1) hh).1
    have hi : IntervalIntegrable (fun x => (0-(-1)/x)/reg h x) volume 0 1 :=
      integrand_integrable (by unfold UniformKServer.Denominators.regular; fun_prop)
        (by positivity : (0:ℝ) < 1/h) (fun x hx hx₁ => regular_lower hh hx hx₁) 0 (-1)
    have he : ∀ a ∈ Icc (0:ℝ) 1, primitive (reg h) 1 1 0 (-1) a =
        primitive (reg h) 0 1 0 (-1) a - primitive (reg h) 0 1 0 (-1) 1 := by
      intro a ha
      unfold primitive
      simp only [one_mul]
      exact (intervalIntegral.integral_interval_sub_left
        (hi.mono_set (by simpa only [uIcc_of_le ha.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
          (Icc_subset_Icc (a₁ := (0:ℝ)) le_rfl ha.2))) hi).symm
    apply (hc.sub continuousOn_const).congr
    intro a ha
    exact he a ha
  · intro a ha ha₁
    exact weighted_integral_positive (UniformKServer.UniformIntegrals.regular_integrable hh)
      (fun y hy => by unfold UniformKServer.UniformIntegrals.regular; positivity)
      (le_of_eq (UniformKServer.UniformIntegrals.regular_integral hh)) ha ha₁

theorem marked_weight {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : a ∈ Icc (0:ℝ) 1) :
    (∫ x in a..1, 1/(x*mark u x)) ≤ 3 := by
  apply weighted_integral_closed (weight_continuous (marked_contract u 1 0 (-1) hu hu₁).1) _ ha
  intro a ha ha₁
  exact weighted_integral_positive (UniformKServer.UniformIntegrals.marked_integrable hu hu₁)
    (fun y hy => by
      unfold UniformKServer.UniformIntegrals.marked
      have := UniformKServer.UniformIntegrals.height_ge_one hu hu₁
      positivity)
    (UniformKServer.UniformIntegrals.marked_integral_uniform hu hu₁) ha ha₁

theorem regular_weight_integrable {h : ℝ} (hh : 1 ≤ h) :
    IntervalIntegrable (fun x => 1/(x*reg h x)) volume 0 1 := by
  have hp : 0 < h := by linarith
  simpa only [zero_sub, neg_div, neg_neg, div_div] using
    (integrand_integrable (by unfold UniformKServer.Denominators.regular; fun_prop)
      (by positivity : (0:ℝ) < 1/h) (fun x hx hx₁ => regular_lower hh hx hx₁) 0 (-1))

theorem marked_weight_integrable {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) :
    IntervalIntegrable (fun x => 1/(x*mark u x)) volume 0 1 := by
  simpa only [zero_sub, neg_div, neg_neg, div_div] using
    (integrand_integrable (by unfold UniformKServer.Denominators.marked; fun_prop)
      (by positivity : (0:ℝ) < u/4) (fun x hx hx₁ => marked_lower hu hu₁ hx hx₁) 0 (-1))

theorem regular_ge_one {h x : ℝ} (hh : 1 ≤ h) (hx : x ∈ Icc (0:ℝ) 1) :
    1 ≤ reg h x := by
  have hp : 0 < h := by linarith
  have hl := UniformKServer.Denominators.log_nonneg hx.1 hx.2
  unfold UniformKServer.Denominators.regular
  apply (le_div_iff₀ hp).mpr
  nlinarith [mul_nonneg hp.le hl, sq_nonneg (Real.log (1/x))]

theorem regular_component {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q : ℝ) :
    |primitive (reg h) 0 scale S Q a| ≤ |scale| * (|S| *a + |Q|) := by
  have hi := regular_weight_integrable hh
  have hia : IntervalIntegrable (fun x => 1/(x*reg h x)) volume 0 a := hi.mono_set (by
    simpa only [uIcc_of_le ha.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      (Icc_subset_Icc (a₁ := (0:ℝ)) le_rfl ha.2))
  have hweight : (∫ x in (0:ℝ)..a, 1/(x*reg h x)) ≤ 1 := by
    apply le_trans (intervalIntegral.integral_mono_interval le_rfl ha.1 ha.2 ?_ hi)
      (regular_weight hh (show (0:ℝ) ∈ Icc 0 1 by simp))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact div_nonneg (by norm_num) (mul_nonneg hx.1.le (by linarith [regular_ge_one hh ⟨hx.1.le,hx.2⟩]))
  have hb : |∫ x in (0:ℝ)..a, (S-Q/x)/reg h x| ≤
      ∫ x in (0:ℝ)..a, |S| + |Q| *(1/(x*reg h x)) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le ha.1 _
      (intervalIntegrable_const.add (hia.const_mul _))
    apply Filter.Eventually.of_forall
    intro x hx
    have hx₁ : x ≤ 1 := le_trans hx.2 ha.2
    have hD := regular_ge_one hh ⟨hx.1.le,hx₁⟩
    have hDp : 0 < reg h x := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hDp]
    calc
      _ ≤ (|S|+|Q|/x)/reg h x := div_le_div_of_nonneg_right
        (by simpa only [abs_div, abs_of_pos hx.1] using abs_sub S (Q/x)) hDp.le
      _ = |S|/reg h x + |Q| *(1/(x*reg h x)) := by ring
      _ ≤ |S| + |Q| *(1/(x*reg h x)) := by
        gcongr
        exact (div_le_self (abs_nonneg S) hD)
  rw [intervalIntegral.integral_add intervalIntegrable_const (hia.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hb
  simp only [sub_zero, smul_eq_mul] at hb
  rw [primitive, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg scale)
  nlinarith [mul_le_mul_of_nonneg_left hweight (abs_nonneg Q)]

theorem marked_component {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q : ℝ) :
    |primitive (mark u) 1 scale S Q a| ≤ 3*|scale| * (|S| *(1-a) + |S-Q|) := by
  have hi := marked_weight_integrable hu hu₁
  have hia : IntervalIntegrable (fun x => 1/(x*mark u x)) volume a 1 := hi.mono_set (by
    rw [uIcc_of_le ha.2, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    intro x hx
    exact ⟨le_trans ha.1 hx.1, hx.2⟩)
  let K := |S| *(1-a)+|S-Q|
  have hK : 0 ≤ K := add_nonneg (mul_nonneg (abs_nonneg S) (sub_nonneg.mpr ha.2)) (abs_nonneg _)
  have hb : |∫ x in a..1, (S-Q/x)/mark u x| ≤
      ∫ x in a..1, K*(1/(x*mark u x)) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le ha.2 _ (hia.const_mul _)
    apply Filter.Eventually.of_forall
    intro x hx
    have hx₀ : 0 < x := lt_of_le_of_lt ha.1 hx.1
    have hD := UniformKServer.Denominators.marked_pos hu hu₁ hx₀.le hx.2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hD]
    have he : S-Q/x = (S*(x-1)+(S-Q))/x := by field_simp <;> ring
    rw [he, abs_div, abs_of_pos hx₀]
    calc
      _ ≤ ((|S| *|x-1|+|S-Q|)/x)/mark u x := by
        gcongr
        simpa only [abs_mul] using abs_add_le (S*(x-1)) (S-Q)
      _ ≤ (K/x)/mark u x := by
        gcongr
        rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
        dsimp [K]
        nlinarith [abs_nonneg S, hx.1]
      _ = K*(1/(x*mark u x)) := by ring
  rw [intervalIntegral.integral_const_mul] at hb
  have hw := marked_weight hu hu₁ ha
  have hb' : |∫ x in a..1, (S-Q/x)/mark u x| ≤ K*3 :=
    hb.trans (mul_le_mul_of_nonneg_left hw hK)
  rw [primitive, abs_mul, intervalIntegral.integral_symm, abs_neg]
  calc
    _ ≤ |scale| *(K*3) := mul_le_mul_of_nonneg_left hb' (abs_nonneg scale)
    _ = 3*|scale| *(|S| *(1-a)+|S-Q|) := by dsimp [K]; ring

end UniformKServer.AlphaBounds

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Companion §04: exact primitive input slopes on the entire simplex.  The
 constants do not depend on the number of children.  These estimates apply to
 the old flags after filtering, without requiring feasibility of that input. -/
namespace UniformKServer.AlphaStability
noncomputable section
open Set MeasureTheory Finset
open UniformKServer.LogPrimitive UniformKServer.Denominators UniformKServer.AlphaBounds

/-- Linearity in the two raw inputs, with the improper endpoint justified by
 the same integrable density as the original primitive. -/
theorem primitive_sub {D : ℝ → ℝ} {base a scale S Q S' Q' : ℝ}
    (hb : base ∈ Icc (0:ℝ) 1) (ha : a ∈ Icc (0:ℝ) 1)
    (hI : IntervalIntegrable (fun x => (S-Q/x)/D x) volume 0 1)
    (hI' : IntervalIntegrable (fun x => (S'-Q'/x)/D x) volume 0 1) :
    primitive D base scale S Q a-primitive D base scale S' Q' a =
      primitive D base scale (S-S') (Q-Q') a := by
  have hs : uIcc base a ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.uIcc_subset_Icc hb ha
  have he : (fun x => (S-S'-(Q-Q')/x)/D x) =
      fun x => (S-Q/x)/D x-(S'-Q'/x)/D x := by funext x; ring
  rw [primitive,primitive,primitive,he,intervalIntegral.integral_sub (hI.mono_set hs) (hI'.mono_set hs)]
  ring

theorem regular_integrable {h : ℝ} (hh : 1 ≤ h) (S Q : ℝ) :
    IntervalIntegrable (fun x => (S-Q/x)/regular h x) volume 0 1 :=
  integrand_integrable (by unfold regular; fun_prop)
    (by positivity : (0:ℝ) < 1/h) (fun x hx hx₁ => regular_lower hh hx hx₁) S Q

theorem marked_integrable {u : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (S Q : ℝ) :
    IntervalIntegrable (fun x => (S-Q/x)/marked u x) volume 0 1 :=
  integrand_integrable (by unfold marked; fun_prop)
    (by positivity : (0:ℝ) < u/4) (fun x hx hx₁ => marked_lower hu hu₁ hx hx₁) S Q

theorem regular_difference {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q S' Q' : ℝ) :
    |primitive (regular h) 0 scale S Q a-primitive (regular h) 0 scale S' Q' a| ≤
      |scale| *(|S-S'| *a+|Q-Q'|) := by
  rw [primitive_sub (by simp) ha (regular_integrable hh S Q) (regular_integrable hh S' Q')]
  exact regular_component hh ha scale (S-S') (Q-Q')

theorem marked_difference {u a : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (ha : a ∈ Icc (0:ℝ) 1)
    (scale S Q S' Q' : ℝ) :
    |primitive (marked u) 1 scale S Q a-primitive (marked u) 1 scale S' Q' a| ≤
      3*|scale| *(|S-S'| *(1-a)+|(S-S')-(Q-Q')|) := by
  rw [primitive_sub (by simp) ha (marked_integrable hu hu₁ S Q) (marked_integrable hu hu₁ S' Q')]
  exact marked_component hu hu₁ ha scale (S-S') (Q-Q')

variable {ι : Type*} [Fintype ι]

theorem sum_difference (B B' : ι → ℝ) : |(∑ i, B i)-(∑ i, B' i)| ≤ ∑ i, |B i-B' i| := by
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

/-- Dimension-free whole-simplex input Lipschitz bound in an unmarked epoch. -/
theorem regular_input (h η a B B' : ι → ℝ) (scale E : ℝ)
    (hh : ∀ i, 1 ≤ h i) (ha : ∀ i, a i ∈ Icc (0:ℝ) 1)
    (hasum : ∑ i, a i=1) (hη : ∀ i, 0 ≤ η i) (hηE : ∀ i, η i ≤ E) :
    |(∑ i, primitive (regular (h i)) 0 scale (∑ r, B r) ((1+η i)*B i) (a i))-
      (∑ i, primitive (regular (h i)) 0 scale (∑ r, B' r) ((1+η i)*B' i) (a i))| ≤
      |scale| *(2+E)*(∑ i, |B i-B' i|) := by
  rw [←sum_sub_distrib]
  have hQ (i : ι) : |(1+η i)*B i-(1+η i)*B' i| ≤ (1+E)*|B i-B' i| := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (by linarith [hη i] : 0 ≤ 1+η i)]
    exact mul_le_mul_of_nonneg_right (by linarith [hηE i]) (abs_nonneg _)
  calc
    _ ≤ ∑ i, |primitive (regular (h i)) 0 scale (∑ r, B r) ((1+η i)*B i) (a i)-
        primitive (regular (h i)) 0 scale (∑ r, B' r) ((1+η i)*B' i) (a i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |scale| *(|(∑ r, B r)-(∑ r, B' r)| *a i+(1+E)*|B i-B' i|) := by
      apply sum_le_sum
      intro i _
      exact (regular_difference (hh i) (ha i) ..).trans
        (mul_le_mul_of_nonneg_left (add_le_add_right (hQ i) _) (abs_nonneg scale))
    _ = |scale| *(|(∑ r, B r)-(∑ r, B' r)|+(1+E)*(∑ i, |B i-B' i|)) := by
      rw [←mul_sum,sum_add_distrib,←mul_sum,hasum,mul_one,←mul_sum]
    _ ≤ |scale| *((∑ i, |B i-B' i|)+(1+E)*(∑ i, |B i-B' i|)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left (sum_difference B B') _) (abs_nonneg _)
    _ = _ := by ring


noncomputable def mixedPrimitive [DecidableEq ι] (o : ι) (u : ℝ)
    (h η B : ι → ℝ) (scale : ℝ) (a : ι → ℝ) (i : ι) : ℝ :=
  if i = o then primitive (marked u) 1 scale (∑ r, B r) ((1+η i)*B i) (a i)
  else primitive (regular (h i)) 0 scale (∑ r, B r) ((1+η i)*B i) (a i)

/-- Cancellation at the marked base point 1 converts a parameter refresh
 into a side-size charge. This bound stays uniform as u tends to zero. -/
theorem marked_prepared_component {u a S B η κ E : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1)
    (ha : a ∈ Icc (0:ℝ) 1) (hS : 0 ≤ S) (hB : 0 ≤ B) (hBS : B ≤ S)
    (hη : 0 ≤ η) (hκ : η ≤ κ*u) (hprep : S*(1-a) ≤ (1+E)*(S-B)) (scale : ℝ) :
    |primitive (marked u) 1 scale S ((1+η)*B) a| ≤
      3*|scale| * ((2+E)*(S-B)+κ*u*S) := by
  have hp := marked_component hu hu₁ ha scale S ((1+η)*B)
  rw [abs_of_nonneg hS] at hp
  have hm : |S-(1+η)*B| ≤ S-B+η*B := by
    have he : S-(1+η)*B=(S-B)-η*B := by ring
    rw [he]
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sub_nonneg.mpr hBS),abs_of_nonneg (mul_nonneg hη hB)])
  have hηS : η*B ≤ κ*u*S := (mul_le_mul_of_nonneg_left hBS hη).trans
    (mul_le_mul_of_nonneg_right hκ hS)
  exact hp.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end
end UniformKServer.AlphaStability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ProportionParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                           
section

/-! Exact compact alpha update uniformly across unmarked, marked, and automatic
singleton stars. The fixed numerical envelopes are justified by the actual
held epoch geometry in EpochParameters; they are not competitive assumptions. -/
noncomputable section
namespace UniformKServer.ProportionParameters
open Finset
open scoped Classical
open UniformKServer.SimplexTracker UniformKServer.AlphaTracker
variable {ι : Type*} [Fintype ι]

inductive Kind (ι : Type*) where
  | regular
  | marked (o : ι) (u : ℝ)
  | singleton (o : ι)

structure Parameters (ι : Type*) where
  kind : Kind ι
  h : ι → ℝ
  ell : ℝ
  ct : ℝ
  C : ℝ

def eta (p : Parameters ι) (i : ι) : ℝ := p.ct*p.h i/p.ell

def valid (p : Parameters ι) : Prop :=
  0 < p.ell ∧ 0 < p.ct ∧ 1000 < p.C*p.ct ∧ (∀ i, eta p i ≤ 1) ∧
  match p.kind with
  | .regular => (∀ i, 1 ≤ p.h i) ∧ (∑ i, Real.exp (-p.h i)) ≤ 2
  | .marked o u => 0 < u ∧ u ≤ 1 ∧ p.h o=u ∧
      (∀ i, i ≠ o → 1 ≤ p.h i) ∧
      (∀ i, i ≠ o → (1/2)*Denominators.height u ≤ p.h i) ∧
      (∑ i ∈ univ.erase o, Real.exp (-p.h i)) ≤ 2*u
  | .singleton o => (∀ i, i=o) ∧ (∀ i, p.h i=0)

def component (p : Parameters ι) (B : ι → ℝ) (i : ι) : ℝ → ℝ :=
  match p.kind with
  | .regular => regularG p.h B p.ell p.ct p.C i
  | .marked o u => markedG o u p.h B p.ell p.ct p.C i
  | .singleton _ => fun _ => 0

def potential (p : Parameters ι) (B a : ι → ℝ) : ℝ := ∑ i, component p B i (a i)

theorem C_pos {p : Parameters ι} (hp : valid p) : 0 < p.C :=
  pos_of_mul_pos_left (by linarith [hp.2.2.1] : 0 < p.C*p.ct) hp.2.1.le

theorem h_nonneg {p : Parameters ι} (hp : valid p) (i : ι) : 0 ≤ p.h i := by
  rcases hp with ⟨_,_,_,_,hk⟩
  cases he : p.kind with
  | regular => simp only [he] at hk <;> linarith [hk.1 i]
  | marked o u =>
    simp only [he] at hk
    by_cases hi : i=o
    · rw [hi,hk.2.2.1]; exact hk.1.le
    · linarith [hk.2.2.2.1 i hi]
  | singleton o => simp only [he] at hk; rw [hk.2 i]

theorem eta_nonneg {p : Parameters ι} (hp : valid p) (i : ι) : 0 ≤ eta p i :=
  div_nonneg (mul_nonneg hp.2.1.le (h_nonneg hp i)) hp.1.le

theorem singleton_sum (o : ι) (ho : ∀ i, i=o) (f : ι → ℝ) (i : ι) :
    (∑ j, f j)=f i := by
  apply sum_eq_single i
  · intro j _ hji
    exact False.elim (hji ((ho j).trans (ho i).symm))
  · simp

theorem primitive_zero (D : ℝ → ℝ) (base scale a : ℝ) :
    LogPrimitive.primitive D base scale 0 0 a=0 := by
  simp [LogPrimitive.primitive]

theorem component_zero (p : Parameters ι) (i : ι) (a : ℝ) :
    component p (fun _ => 0) i a=0 := by
  unfold component
  cases p.kind <;> simp [regularG,markedG,primitive_zero]

theorem potential_zero (p : Parameters ι) (a : ι → ℝ) : potential p (fun _ => 0) a=0 := by
  simp [potential,component_zero]

theorem component_mixed {p : Parameters ι} {o : ι} {u : ℝ} (he : p.kind=.marked o u)
    (B a : ι → ℝ) (i : ι) : component p B i (a i)=
      AlphaStability.mixedPrimitive o u p.h (eta p) B (p.C*p.ell) a i := by
  unfold component
  rw [he]
  dsimp only
  unfold markedG markedF AlphaStability.mixedPrimitive eta
  by_cases hi : i=o <;> simp only [hi,ite_true, if_true,ite_false, if_false]

end UniformKServer.ProportionParameters

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveAlpha
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The two compact minimizations and intermediate common-core transport of
 companion §04, on a fixed child set. All movement estimates use the actual
 weighted L1 distance, including changing active domains and singleton states. -/
noncomputable section
namespace UniformKServer.AdaptiveAlpha
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

structure Config (ι : Type*) where
  active : Finset ι
  param : ProportionParameters.Parameters active

def valid (p : Config ι) : Prop := p.active.Nonempty ∧ ProportionParameters.valid p.param

def potential (p : Config ι) (B a : ι → ℝ) : ℝ :=
  ProportionParameters.potential p.param (fun i => B i) (fun i => a i)

def eta (p : Config ι) (i : ι) : ℝ := DomainTransport.extend p.active
  (ProportionParameters.eta p.param) i

def scale (p : Config ι) : ℝ := p.param.C*p.param.ell

omit [Fintype ι] in
theorem scale_nonneg {p : Config ι} (hp : valid p) : 0 ≤ scale p :=
  mul_nonneg (ProportionParameters.C_pos hp.2).le hp.2.1.le

omit [Fintype ι] in
theorem potential_zero (p : Config ι) (a : ι → ℝ) : potential p (fun _ => 0) a=0 :=
  ProportionParameters.potential_zero _ _

theorem diameter {I J : Finset ι} {a b : ι → ℝ}
    (ha : DomainTransport.simplex I a) (hb : DomainTransport.simplex J b) :
    SimplexTracker.movement a b ≤ 2 := by
  calc
    _ ≤ ∑ i, (a i+b i) := sum_le_sum fun i _ =>
      (abs_sub _ _).trans (by rw [abs_of_nonneg (ha.1 i),abs_of_nonneg (hb.1 i)])
    _ = 2 := by rw [sum_add_distrib,ha.2.2,hb.2.2]; norm_num

theorem triangle (a b c : ι → ℝ) :
    SimplexTracker.movement a c ≤ SimplexTracker.movement a b+SimplexTracker.movement b c := by
  unfold SimplexTracker.movement
  rw [←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

theorem movement_nonneg (a b : ι → ℝ) : 0 ≤ SimplexTracker.movement a b :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- A slightly sharper (two rather than four) weight-change error is available
 by applying the diameter bound after transport. In particular it proves the
 source's four-delta inequality, with no positive-weight division. -/
theorem weight_comparison {I J K : Finset ι} {old prep moved new : ι → ℝ}
    {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (hold : DomainTransport.simplex I old) (hmoved : DomainTransport.simplex J moved)
    (hnew : DomainTransport.simplex K new)
    (hfree : S*SimplexTracker.movement moved prep=0) :
    T*SimplexTracker.movement new old ≤
      S*SimplexTracker.movement prep old+T*SimplexTracker.movement new moved+4*(T-S) := by
  have ht := mul_le_mul_of_nonneg_left (triangle new moved old) (hS.trans hST)
  have hs := mul_le_mul_of_nonneg_left (triangle moved prep old) hS
  have hd := mul_le_mul_of_nonneg_left (diameter hmoved hold) (sub_nonneg.mpr hST)
  rw [mul_add,hfree,zero_add] at hs
  have hn := movement_nonneg new old
  have hdn := diameter hnew hold
  nlinarith

end UniformKServer.AdaptiveAlpha

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! Finite adaptive all-step accounting. This is the filtering telescope used
 twice in the allocation proof (primitive trackers and output-rule switching).
 No martingale assertion is conditioned on the later event being charged. -/
namespace UniformKServer.AdaptiveLedger
noncomputable section
open Finset
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

def expect (w : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, w ω*X ω

theorem expect_add (w : Ω → ℝ) (X Y : Ω → ℝ) :
    expect w (fun ω => X ω+Y ω)=expect w X+expect w Y := by
  simp only [expect,mul_add,sum_add_distrib]

theorem expect_sub (w : Ω → ℝ) (X Y : Ω → ℝ) :
    expect w (fun ω => X ω-Y ω)=expect w X-expect w Y := by
  simp only [expect,mul_sub,sum_sub_distrib]

theorem expect_mono {w X Y : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hXY : ∀ ω, X ω ≤ Y ω) : expect w X ≤ expect w Y :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hXY ω) (hw ω)

end
end UniformKServer.AdaptiveLedger

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! Exact old-state affine forms for the all-step filtering leg in §04.  In
particular the marked coefficient bound is uniform as its side mass vanishes. -/
namespace UniformKServer.AlphaLinear
noncomputable section
open Set MeasureTheory Finset
open UniformKServer.LogPrimitive UniformKServer.Denominators UniformKServer.AlphaStability

theorem primitive_linear {D : ℝ → ℝ} {base a : ℝ}
    (hb : base ∈ Icc (0:ℝ) 1) (ha : a ∈ Icc (0:ℝ) 1)
    (hS : IntervalIntegrable (fun x => (1-0/x)/D x) volume 0 1)
    (hQ : IntervalIntegrable (fun x => (0-1/x)/D x) volume 0 1)
    (scale S Q : ℝ) :
    primitive D base scale S Q a =
      S*primitive D base scale 1 0 a+Q*primitive D base scale 0 1 a := by
  have hs : uIcc base a ⊆ uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.uIcc_subset_Icc hb ha
  have hid : (fun x => (S-Q/x)/D x) =
      fun x => S*((1-0/x)/D x)+Q*((0-1/x)/D x) := by funext x; ring
  rw [primitive,hid,intervalIntegral.integral_add ((hS.mono_set hs).const_mul S)
    ((hQ.mono_set hs).const_mul Q),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  simp only [primitive]
  ring

variable {ι : Type*} [Fintype ι]

def potential (D : ι → ℝ → ℝ) (base η : ι → ℝ) (scale : ℝ)
    (B a : ι → ℝ) : ℝ :=
  ∑ i, primitive (D i) (base i) scale (∑ j, B j) ((1+η i)*B i) (a i)

def coefficient (D : ι → ℝ → ℝ) (base η : ι → ℝ) (scale : ℝ)
    (a : ι → ℝ) (j : ι) : ℝ :=
  (∑ i, primitive (D i) (base i) scale 1 0 (a i))+
    (1+η j)*primitive (D j) (base j) scale 0 1 (a j)

theorem potential_affine (D : ι → ℝ → ℝ) (base η : ι → ℝ) (scale : ℝ)
    (B a : ι → ℝ) (hb : ∀ i, base i ∈ Icc (0:ℝ) 1)
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1)
    (hS : ∀ i, IntervalIntegrable (fun x => (1-0/x)/D i x) volume 0 1)
    (hQ : ∀ i, IntervalIntegrable (fun x => (0-1/x)/D i x) volume 0 1) :
    potential D base η scale B a = ∑ j, coefficient D base η scale a j*B j := by
  let X (i : ι) := primitive (D i) (base i) scale 1 0 (a i)
  let Y (i : ι) := primitive (D i) (base i) scale 0 1 (a i)
  calc
    _ = ∑ i, ((∑ j, B j)*X i+((1+η i)*B i)*Y i) := by
      apply sum_congr rfl
      intro i _
      exact primitive_linear (hb i) (ha i) (hS i) (hQ i) ..
    _ = (∑ j, B j)*(∑ i, X i)+∑ i, ((1+η i)*B i)*Y i := by
      rw [sum_add_distrib,←mul_sum]
    _ = (∑ i, X i)*(∑ j, B j)+∑ i, ((1+η i)*Y i)*B i := by
      congr 1
      · ring
      · apply sum_congr rfl
        intro i _
        ring
    _ = ∑ i, ((∑ j, X j)+(1+η i)*Y i)*B i := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    _ = _ := rfl

/-- An affine functional's coefficients inherit its exact L1 input bound. -/
theorem coefficient_of_lipschitz [DecidableEq ι] (f : (ι → ℝ) → ℝ) (c : ι → ℝ)
    (L : ℝ) (hf : ∀ B, f B=∑ i, c i*B i)
    (hLip : ∀ B B', |f B-f B'| ≤ L*(∑ i, |B i-B' i|)) (j : ι) : |c j| ≤ L := by
  have h := hLip (fun i => if i=j then 1 else 0) (fun _ => 0)
  simp only [hf,mul_zero,sum_const_zero,sub_zero] at h
  simpa [abs_ite] using h

end
end UniformKServer.AlphaLinear

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CoreFiltering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Source §04, filtering with held core flags.  The old-state coefficients
are tested on every step, before selecting any refresh or active-domain event. -/
namespace UniformKServer.CoreFiltering
noncomputable section
open Finset UniformKServer.AdaptiveLedger
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

def masked (flag : Ω → ι → R → Bool) (p : Ω → ι × R → ℝ)
    (ω : Ω) (i : ι) : ℝ := ∑ r, if flag ω i r then p ω (i,r) else 0

def liftCoefficient (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool)
    (ω : Ω) (ir : ι × R) : ℝ := if flag ω ir.1 ir.2 then a ω ir.1 else 0

omit [Fintype Ω] in
theorem masked_linear (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool)
    (p : Ω → ι × R → ℝ) (ω : Ω) :
    (∑ i, a ω i*masked flag p ω i) =
      ∑ ir, liftCoefficient a flag ω ir*p ω ir := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  rw [masked,mul_sum]
  apply sum_congr rfl
  intro r _
  simp only [liftCoefficient]
  split_ifs <;> ring

omit [Fintype Ω] [Fintype ι] [Fintype R] in
theorem lift_bound (a : Ω → ι → ℝ) (flag : Ω → ι → R → Bool)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ ω i, |a ω i| ≤ C) :
    ∀ ω ir, |liftCoefficient a flag ω ir| ≤ C := by
  intro ω ir
  simp only [liftCoefficient]
  split_ifs
  · exact ha ω ir.1
  · simpa only [abs_zero] using hC

end
end UniformKServer.CoreFiltering

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveAlphaLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! Exact affine old-state alpha coefficients on changing active domains.
 These are computed from the genuine regular/marked improper primitives.
 Their uniform bound is used before, not after, testing refresh events. -/
noncomputable section
namespace UniformKServer.ProportionParameters
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

def coefficient (p : Parameters ι) (a : ι → ℝ) : ι → ℝ :=
  match p.kind with
  | .regular => AlphaLinear.coefficient (fun i => Denominators.regular (p.h i))
      (fun _ => 0) (eta p) (p.C*p.ell) a
  | .marked o u => AlphaLinear.coefficient
      (fun i => if i=o then Denominators.marked u else Denominators.regular (p.h i))
      (fun i => if i=o then 1 else 0) (eta p) (p.C*p.ell) a
  | .singleton _ => fun _ => 0

theorem affine {p : Parameters ι} (hp : valid p) (B a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    potential p B a=∑ i, coefficient p a i*B i := by
  have hk := hp.2.2.2.2
  cases he : p.kind with
  | regular =>
    simp only [he] at hk
    have hf := AlphaLinear.potential_affine (fun i => Denominators.regular (p.h i))
      (fun _ => 0) (eta p) (p.C*p.ell) B a (by intro i; simp) ha
      (fun i => AlphaStability.regular_integrable (hk.1 i) 1 0)
      (fun i => AlphaStability.regular_integrable (hk.1 i) 0 1)
    simpa only [potential,component,coefficient,he,AlphaLinear.potential,
      AlphaTracker.regularG,eta] using hf
  | marked o u =>
    simp only [he] at hk
    let D (i : ι) := if i=o then Denominators.marked u else Denominators.regular (p.h i)
    let base (i : ι) : ℝ := if i=o then 1 else 0
    have hf := AlphaLinear.potential_affine D base (eta p) (p.C*p.ell) B a
      (by intro i; dsimp [base]; split_ifs <;> simp) ha
      (by intro i; dsimp [D]; split_ifs with hi
          · exact AlphaStability.marked_integrable hk.1 hk.2.1 1 0
          · exact AlphaStability.regular_integrable (hk.2.2.2.1 i hi) 1 0)
      (by intro i; dsimp [D]; split_ifs with hi
          · exact AlphaStability.marked_integrable hk.1 hk.2.1 0 1
          · exact AlphaStability.regular_integrable (hk.2.2.2.1 i hi) 0 1)
    have hpot : potential p B a=AlphaLinear.potential D base (eta p) (p.C*p.ell) B a := by
      apply sum_congr rfl
      intro i _
      simp only [component,he,AlphaTracker.markedG,D,base,eta]
      have hF : AlphaTracker.markedF o u p.h i = D i := by
        funext x
        simp only [AlphaTracker.markedF,D]
        split_ifs <;> rfl
      rw [hF]
    rw [hpot,hf]
    simp only [coefficient,he]
    rfl
  | singleton o => simp [potential,component,coefficient,he]

end UniformKServer.ProportionParameters

namespace UniformKServer.AdaptiveAlphaLinear
open Finset AdaptiveAlpha
open scoped Classical
variable {ι : Type*} [Fintype ι]

def coefficient (p : Config ι) (a : ι → ℝ) : ι → ℝ :=
  DomainTransport.extend p.active (ProportionParameters.coefficient p.param (fun i => a i))

theorem affine {p : Config ι} (hp : valid p) (B a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    potential p B a=∑ i, coefficient p a i*B i := by
  rw [potential,ProportionParameters.affine hp.2 _ _ (fun i => ha i)]
  rw [←DomainTransport.extend_sum p.active (fun i =>
    ProportionParameters.coefficient p.param (fun j => a j) i*B i)]
  apply sum_congr rfl
  intro i _
  unfold coefficient DomainTransport.extend
  split_ifs <;> simp

end UniformKServer.AdaptiveAlphaLinear

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SideStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The exact side primitives have dimension-free input slopes, uniformly in
 the number of sides and their sizes. Companion §04 side-potential-bounds. -/
namespace UniformKServer.SideStability
noncomputable section
open Finset UniformKServer.SideTracker

/-- The coefficient of the parent input D, after analytic integration. -/
def dCoefficient (θ z s : ℝ) : ℝ :=
  (s-z*Real.log (1+s/z))/θ+z*Real.log (1+s/z)/2
/-- The negative coefficient of the side input B. -/
def bCoefficient (b θ z s : ℝ) : ℝ :=
  (b+θ/2)*Real.log (1+s/z)/θ

theorem coordinate_affine (b θ z C B D s : ℝ) :
    coordinate b θ z C B D s = C*(D*dCoefficient θ z s-B*bCoefficient b θ z s) := by
  unfold coordinate dCoefficient bCoefficient
  ring

theorem logarithm_bounds {z s : ℝ} (hz : 0 < z) (hs : 0 ≤ s) :
    0 ≤ z*Real.log (1+s/z) ∧ z*Real.log (1+s/z) ≤ s := by
  have hp : 0 < 1+s/z := by positivity
  refine ⟨mul_nonneg hz.le (Real.log_nonneg (by linarith [div_nonneg hs hz.le])), ?_⟩
  have h := Real.log_le_sub_one_of_pos hp
  have hm := mul_le_mul_of_nonneg_left h hz.le
  have he : z*(1+s/z-1)=s := by field_simp <;> ring
  rwa [he] at hm

theorem dCoefficient_bounds {θ z s T : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (hs : 0 ≤ s) (hT : 1/θ ≤ T) :
    0 ≤ dCoefficient θ z s ∧ dCoefficient θ z s ≤ (T+1/2)*s := by
  obtain ⟨hl,hu⟩ := logarithm_bounds hz hs
  have hq : (s-z*Real.log (1+s/z))/θ ≤ s/θ := (div_le_div_iff_of_pos_right hθ).mpr (by linarith)
  unfold dCoefficient
  refine ⟨by positivity, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hT hs
  rw [mul_comm (1/θ) s, ←div_eq_mul_one_div s θ] at hm
  nlinarith

theorem bCoefficient_bounds {b θ z s J Q : ℝ} (hb : 0 ≤ b) (hθ : 0 < θ)
    (hz : 0 < z) (hs : 0 ≤ s) (hJ : Real.log (1+s/z)/θ ≤ J)
    (hQ : b+θ/2 ≤ Q) :
    0 ≤ bCoefficient b θ z s ∧ bCoefficient b θ z s ≤ Q*J := by
  have hl : 0 ≤ Real.log (1+s/z) := nonneg_of_mul_nonneg_right (logarithm_bounds hz hs).1 hz
  unfold bCoefficient
  rw [mul_div_assoc]
  refine ⟨by positivity, ?_⟩
  exact mul_le_mul hQ hJ (by positivity) (by linarith)

/-- A scalar slope bound; B,D may have either sign, as needed for a raw
 filtered-input difference. -/
theorem coordinate_bound {b θ z s T J Q : ℝ} (hb : 0 ≤ b) (hθ : 0 < θ)
    (hz : 0 < z) (hs : 0 ≤ s) (hT : 1/θ ≤ T)
    (hJ : Real.log (1+s/z)/θ ≤ J) (hQ : b+θ/2 ≤ Q) (C B D : ℝ) :
    |coordinate b θ z C B D s| ≤ |C| * (|D| *(T+1/2)*s+|B| *Q*J) := by
  obtain ⟨hd,hd'⟩ := dCoefficient_bounds hθ hz hs hT
  obtain ⟨hb',hb''⟩ := bCoefficient_bounds hb hθ hz hs hJ hQ
  rw [coordinate_affine,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
  calc
    _ ≤ |D*dCoefficient θ z s|+|B*bCoefficient b θ z s| := abs_sub _ _
    _ = |D| *dCoefficient θ z s+|B| *bCoefficient b θ z s := by
      rw [abs_mul,abs_mul,abs_of_nonneg hd,abs_of_nonneg hb']
    _ ≤ |D| *((T+1/2)*s)+|B| *(Q*J) := add_le_add
      (mul_le_mul_of_nonneg_left hd' (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hb'' (abs_nonneg _))
    _ = _ := by ring

theorem coordinate_sub (b θ z C B D B' D' s : ℝ) :
    coordinate b θ z C B D s-coordinate b θ z C B' D' s =
      coordinate b θ z C (B-B') (D-D') s := by
  simp only [coordinate_affine]
  ring

variable {ι : Type*} [Fintype ι]

/-- Summing the exact coefficients costs the side-domain bound, not its
 cardinality. This applies even when the raw filtered inputs are infeasible. -/
theorem input_bound (b C D D' T J Q W : ℝ) (θ z B B' w : ι → ℝ)
    (hb : 0 ≤ b) (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i)
    (hw : domain W w) (hT : ∀ i, 1/θ i ≤ T)
    (hJ : ∀ i, Real.log (1+w i/z i)/θ i ≤ J)
    (hQ : ∀ i, b+θ i/2 ≤ Q) (hT' : 0 ≤ T+1/2) :
    |potential b C D θ z B w-potential b C D' θ z B' w| ≤
      |C| * (|D-D'| *(T+1/2)*W+Q*J*(∑ i, |B i-B' i|)) := by
  unfold potential
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑ i, |coordinate b (θ i) (z i) C (B i) D (w i)-
      coordinate b (θ i) (z i) C (B' i) D' (w i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |C| * (|D-D'| *(T+1/2)*w i+|B i-B' i| *Q*J) := by
      apply sum_le_sum
      intro i _
      rw [coordinate_sub]
      exact coordinate_bound hb (hθ i) (hz i) (hw.1 i) (hT i) (hJ i) (hQ i) ..
    _ = |C| * (|D-D'| *(T+1/2)*(∑ i, w i)+Q*J*(∑ i, |B i-B' i|)) := by
      rw [←mul_sum,sum_add_distrib,←mul_sum]
      congr 2
      rw [←sum_mul,←sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_left
      (mul_le_mul_of_nonneg_left hw.2 (mul_nonneg (abs_nonneg _) hT')) _) (abs_nonneg _)

end
end UniformKServer.SideStability

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AdaptiveSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! Actual side-domain update with the exact held height/offset parameters.
 The source leaves fixed absolute constants flexible; W=11, C'=28 apply in
 the eventual b≤4, θ≤1 parameter interval. Empty side domains are included. -/
noncomputable section
namespace UniformKServer.AdaptiveSide
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

structure Config (ι : Type*) where
  active : Finset ι
  A : ℝ
  a : active → ℝ
  ell : ℝ
  cw : ℝ
  b : ℝ

def slope (p : Config ι) : ℝ := 2000*(p.ell/p.cw+1)

theorem coordinate_zero (b θ z B D : ℝ) : SideTracker.coordinate b θ z 28 B D 0=0 := by
  simp [SideTracker.coordinate]

theorem restrict_domain {I : Finset ι} {w : ι → ℝ}
    (hw : DomainTransport.domain I 11 w) : SideTracker.domain 11 (fun i : I => w i) := by
  refine ⟨fun i => hw.1 i,?_⟩
  rw [DomainTransport.sum_restrict hw.2.1]
  exact hw.2.2

theorem extend_domain {I : Finset ι} {w : I → ℝ} (hw : SideTracker.domain 11 w) :
    DomainTransport.domain I 11 (DomainTransport.extend I w) := by
  refine ⟨?_,DomainTransport.extend_supported I w,?_⟩
  · intro i
    unfold DomainTransport.extend
    split_ifs with hi
    · exact hw.1 ⟨i,hi⟩
    · rfl
  · rw [DomainTransport.extend_sum]
    exact hw.2

theorem coordinate_le_sum {I : Finset ι} {w : ι → ℝ}
    (hw : DomainTransport.domain I 11 w) (i : ι) : w i ≤ 11 :=
  (single_le_sum (s:=univ) (f:=w) (fun j _ => hw.1 j) (mem_univ i)).trans hw.2.2

theorem triangle (a b c : ι → ℝ) :
    SideTracker.movement a c ≤ SideTracker.movement a b+SideTracker.movement b c := by
  unfold SideTracker.movement
  rw [←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le (a i) (b i) (c i)

end UniformKServer.AdaptiveSide

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationEpoch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Source companion §03, cumulative-variation epochs.  Variation credit is
carried in one potential; a forced parent refresh discards unused credit, and
never creates a fresh initialization allowance. -/
namespace UniformKServer.AllocationEpoch
noncomputable section
open Finset

structure State where
  base : ℝ
  credit : ℝ

def initial (x : ℝ) : State := ⟨x,0⟩

def fires (s : State) (d : ℝ) (parent : Bool) : Prop :=
  parent = true ∨ s.base/100 < s.credit+d

def update (s : State) (x d : ℝ) (parent : Bool) : State := by
  classical
  exact if fires s d parent then initial x else ⟨s.base,s.credit+d⟩

def valid (x : ℝ) (s : State) : Prop :=
  0 ≤ s.base ∧ 0 ≤ s.credit ∧ s.credit ≤ s.base/100 ∧ |x-s.base| ≤ s.credit

def charge (s : State) (x y d : ℝ) (parent : Bool) : ℝ := by
  classical
  exact if fires s d parent then x+y else 0

theorem initial_valid {x : ℝ} (hx : 0 ≤ x) : valid x (initial x) := by
  simp only [valid,initial,sub_self,abs_zero]
  exact ⟨hx,le_rfl,by positivity,le_rfl⟩

theorem update_valid {x y d : ℝ} {s : State} (hs : valid x s)
    (hy : 0 ≤ y) (hd : |y-x| ≤ d) (parent : Bool) :
    valid y (update s y d parent) := by
  have hdn : 0 ≤ d := (abs_nonneg _).trans hd
  unfold update
  split
  · exact initial_valid hy
  · rename_i h
    have hh : s.credit+d ≤ s.base/100 := by
      exact le_of_not_gt (fun h' => h (Or.inr h'))
    refine ⟨hs.1,add_nonneg hs.2.1 hdn,hh,?_⟩
    calc
      |y-s.base| = |(x-s.base)+(y-x)| := by congr 1; ring
      _ ≤ |x-s.base|+|y-x| := abs_add_le _ _
      _ ≤ s.credit+d := add_le_add hs.2.2.2 hd

theorem wholesale_bound {x y d : ℝ} {s : State} (hs : valid x s)
    (hd : |y-x| ≤ d) (hfail : s.base/100 < s.credit+d) :
    x+y ≤ 203*(s.credit+d) := by
  have hx : x ≤ (101/100:ℝ)*s.base := by
    have ha := le_abs_self (x-s.base)
    linarith [hs.2.2.2,hs.2.2.1]
  have hy : y ≤ (101/100:ℝ)*s.base+(s.credit+d) := by
    have ha := le_abs_self (y-x)
    linarith [hs.2.1]
  linarith

def schedule (x d : ℕ → ℝ) (parent : ℕ → Bool) : ℕ → State
  | 0 => initial (x 0)
  | t+1 => update (schedule x d parent t) (x (t+1)) (d t) (parent t)

theorem schedule_valid {x d : ℕ → ℝ} (hx : ∀ t, 0 ≤ x t)
    (hd : ∀ t, |x (t+1)-x t| ≤ d t) (parent : ℕ → Bool) :
    ∀ t, valid (x t) (schedule x d parent t) := by
  intro t
  induction t with
  | zero => exact initial_valid (hx 0)
  | succ t ih => exact update_valid ih (hx (t+1)) (hd t) (parent t)

end
end UniformKServer.AllocationEpoch

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                        
section

/-! Exact two child-output rules of companion §05.  The estimates retain one
copy of the parent variation; this coefficient must be independent of k for
the tree absorption.  Input inequalities below are the explicit rank, cap,
and proportion conditions, not an assumed output feasibility statement. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def lower (n B f β : ι → ℝ) (i : ι) : ℝ := n i-β i*B i+f i

def excess (d : ι → ℝ) (parent : ℝ) : ℝ := max ((∑ i, d i)-parent) 0

def ruleOne (d α : ι → ℝ) (parent : ℝ) (i : ι) : ℝ := d i-excess d parent*α i

def ruleTwo (d w : ι → ℝ) (parent D : ℝ) (o i : ι) : ℝ :=
  if i=o then min (d o) (parent-∑ j ∈ univ.erase o, (d j-D*w j)) else d i-D*w i

def variation (a b : ι → ℝ) : ℝ := ∑ i, |b i-a i|

omit [DecidableEq ι] in
theorem excess_nonneg (d : ι → ℝ) (q : ℝ) : 0 ≤ excess d q := le_max_right _ _

omit [DecidableEq ι] in
theorem required_holes (n B f b : ι → ℝ) (β q e : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hparent : (∑ i, (n i-β*B i+f i)) ≤ q)
    (hcap : (∑ i, (b i-f i)) ≤ e) :
    excess (fun i => n i+b i) q ≤ β*(∑ i, B i)+e := by
  unfold excess
  apply max_le
  · have hid : (∑ i, (n i+b i))-(∑ i, (n i-β*B i+f i)) =
        β*(∑ i, B i)+(∑ i, (b i-f i)) := by
      rw [←sum_sub_distrib,mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro i _
      ring
    linarith
  · exact add_nonneg (mul_nonneg hβ (sum_nonneg (fun i _ => hB i))) he

omit [DecidableEq ι] in
theorem rule_one_budget (d α : ι → ℝ) (q : ℝ) (hα : (∑ i, α i)=1) :
    (∑ i, ruleOne d α q i) = min (∑ i, d i) q := by
  simp only [ruleOne,sum_sub_distrib,←mul_sum,hα,mul_one,excess]
  rcases le_total (∑ i, d i) q with h|h
  · rw [max_eq_right (by linarith),min_eq_left h,sub_zero]
  · rw [max_eq_left (by linarith),min_eq_right h]
    ring

omit [DecidableEq ι] in
theorem rule_one_upper (d α : ι → ℝ) (q : ℝ) (hα : ∀ i, 0 ≤ α i) (i : ι) :
    ruleOne d α q i ≤ d i :=
  sub_le_self _ (mul_nonneg (excess_nonneg _ _) (hα i))

omit [DecidableEq ι] in
/-- Source Rule I, at regular coordinates.  The error comparison e≤εS
includes the admissible zero case S=0, so no division by S is used. -/
theorem rule_one_regular (n B f b β η α : ι → ℝ) (βv q e ε : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hα : ∀ i, 0 ≤ α i)
    (hβ : 0 ≤ βv+ε)
    (hR : excess (fun i => n i+b i) q ≤ βv*(∑ i, B i)+e)
    (he : e ≤ ε*(∑ i, B i))
    (hprop : ∀ i, (∑ j, B j)*α i ≤ (1+η i)*B i)
    (i : ι) (hgap : (βv+ε)*(1+η i) ≤ β i) (hcap : f i ≤ b i) :
    lower n B f β i ≤ ruleOne (fun i => n i+b i) α q i := by
  have hR' : excess (fun i => n i+b i) q ≤ (βv+ε)*(∑ i, B i) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hR' (hα i)
  have h2 := mul_le_mul_of_nonneg_left (hprop i) hβ
  have h3 := mul_le_mul_of_nonneg_right hgap (hB i)
  dsimp [lower,ruleOne]
  nlinarith

omit [DecidableEq ι] in
/-- Source Rule I at the marked dominant coordinate: the cap's excess e is
retained without multiplying it by a inverse core mass. -/
theorem rule_one_dominant (n B f b β η α : ι → ℝ) (βv q e : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hα : ∀ i, 0 ≤ α i) (hαsum : (∑ i, α i)=1)
    (hβ : 0 ≤ βv) (he : 0 ≤ e)
    (hR : excess (fun i => n i+b i) q ≤ βv*(∑ i, B i)+e)
    (hprop : ∀ i, (∑ j, B j)*α i ≤ (1+η i)*B i)
    (o : ι) (hgap : βv*(1+η o) ≤ β o) (hcap : f o+e ≤ b o) :
    lower n B f β o ≤ ruleOne (fun i => n i+b i) α q o := by
  have hαo : α o ≤ 1 := by
    rw [←hαsum]
    exact single_le_sum (fun i _ => hα i) (mem_univ o)
  have h1 := mul_le_mul_of_nonneg_right hR (hα o)
  have h2 := mul_le_mul_of_nonneg_left (hprop o) hβ
  have h3 := mul_le_mul_of_nonneg_right hgap (hB o)
  have h4 := mul_le_mul_of_nonneg_left hαo he
  dsimp [lower,ruleOne]
  nlinarith

end
end UniformKServer.AllocationOutputs

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Companion §05, the exact non-wholesale hole identities and movement
bounds. The coefficient of the parent variation is exactly one. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_difference_le (a b : ι → ℝ) : |(∑ i, b i)-(∑ i, a i)| ≤ variation a b := by
  rw [←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

omit [DecidableEq ι] in
theorem excess_difference (a b : ι → ℝ) (p q : ℝ) :
    |excess b q-excess a p| ≤ variation a b+|q-p| := by
  calc
    _ ≤ |((∑ i, b i)-q)-((∑ i, a i)-p)| := abs_max_sub_max_le_abs _ _ _
    _ = |((∑ i, b i)-(∑ i, a i))-(q-p)| := by congr 1; ring
    _ ≤ |(∑ i, b i)-(∑ i, a i)|+|q-p| := abs_sub _ _
    _ ≤ _ := add_le_add (sum_difference_le a b) le_rfl

omit [DecidableEq ι] in
theorem outputs_from_holes (a b x y : ι → ℝ) :
    variation (fun i => a i-x i) (fun i => b i-y i) ≤ variation a b+variation x y := by
  rw [variation,variation,variation,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  convert abs_sub (b i-a i) (y i-x i) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

omit [DecidableEq ι] in
theorem scalar_vector_movement (a b : ι → ℝ) (p q : ℝ)
    (hq : 0 ≤ q) (ha : ∀ i, 0 ≤ a i) :
    variation (fun i => p*a i) (fun i => q*b i) ≤
      q*variation a b+|q-p| *(∑ i, a i) := by
  rw [variation,variation,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  calc
    _ = |q*(b i-a i)+(q-p)*a i| := by congr 1; ring
    _ ≤ |q*(b i-a i)|+|(q-p)*a i| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg hq,abs_of_nonneg (ha i)]

omit [DecidableEq ι] in
theorem rule_one_movement (d₀ d₁ α₀ α₁ : ι → ℝ) (q₀ q₁ : ℝ)
    (hα : ∀ i, 0 ≤ α₀ i) (hsum : (∑ i, α₀ i)=1) :
    variation (ruleOne d₀ α₀ q₀) (ruleOne d₁ α₁ q₁) ≤
      |q₁-q₀|+2*variation d₀ d₁+excess d₁ q₁*variation α₀ α₁ := by
  have hm := outputs_from_holes d₀ d₁ (fun i => excess d₀ q₀*α₀ i)
    (fun i => excess d₁ q₁*α₁ i)
  have hh := scalar_vector_movement α₀ α₁ (excess d₀ q₀) (excess d₁ q₁)
    (excess_nonneg _ _) hα
  rw [hsum,mul_one] at hh
  have he := excess_difference d₀ d₁ q₀ q₁
  change variation (ruleOne d₀ α₀ q₀) (ruleOne d₁ α₁ q₁) ≤ _ at hm
  linarith

def sideTotal (a : ι → ℝ) (o : ι) : ℝ := ∑ i ∈ univ.erase o, a i

def sideVariation (a b : ι → ℝ) (o : ι) : ℝ := ∑ i ∈ univ.erase o, |b i-a i|

def holesTwo (R : ℝ) (ω : ι → ℝ) (o i : ι) : ℝ :=
  if i=o then max (R-sideTotal ω o) 0 else ω i

theorem side_total_difference (a b : ι → ℝ) (o : ι) :
    |sideTotal b o-sideTotal a o| ≤ sideVariation a b o := by
  rw [sideTotal,sideTotal,←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

theorem side_variation_le (a b : ι → ℝ) (o : ι) :
    sideVariation a b o ≤ variation a b :=
  sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _ => abs_nonneg (b i-a i))

end
end UniformKServer.AllocationOutputs

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AllocationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                         
section

/-! Exact coarse held-size schedule in companion §03. The deterministic
potential below pays relative refreshes and both hysteretic on/off transitions
from variation of the underlying persistent rank estimates. In particular it
does not restart any initialization allowance when a child becomes active. -/
namespace UniformKServer.AllocationSchedule
noncomputable section
open Finset

def charge (a b : ℝ) : ℝ := if a=b then 0 else a+b

theorem charge_self (a : ℝ) : charge a a=0 := by simp [charge]

theorem charge_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : charge a b ≤ a+b := by
  unfold charge
  split
  · linarith
  · rfl

end
end UniformKServer.AllocationSchedule

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Empty active domains are genuine zero states, not a hidden nonempty
 hypothesis. They occur only at wholesale changes in the derived schedule;
 the algebra here incurs no restart allowance. -/
noncomputable section
namespace UniformKServer.AlphaEmpty
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

abbrev Config (ι : Type*) := Option (AdaptiveAlpha.Config ι)

def active : Config ι → Finset ι
  | none => ∅
  | some p => p.active

def valid : Config ι → Prop
  | none => True
  | some p => AdaptiveAlpha.valid p

def state : Config ι → (ι → ℝ) → Prop
  | none, a => a=fun _ => 0
  | some p, a => DomainTransport.simplex p.active a

def potential : Config ι → (ι → ℝ) → (ι → ℝ) → ℝ
  | none, _, _ => 0
  | some p, B, a => AdaptiveAlpha.potential p B a

def scale : Config ι → ℝ
  | none => 0
  | some p => AdaptiveAlpha.scale p

def eta : Config ι → ι → ℝ
  | none, _ => 0
  | some p, i => AdaptiveAlpha.eta p i

omit [Fintype ι] in
theorem zero_supported {B : ι → ℝ} (hs : DomainTransport.Supported (∅ : Finset ι) B) :
    B=fun _ => 0 := by
  funext i
  exact hs i (by simp)

theorem exists_state {p : Config ι} (hp : valid p) : ∃ a, state p a := by
  cases p with
  | none => exact ⟨fun _ => 0,rfl⟩
  | some p => exact DomainTransport.exists_simplex hp.1

omit [Fintype ι] in
theorem scale_nonneg {p : Config ι} (hp : valid p) : 0 ≤ scale p := by
  cases p with
  | none => exact le_rfl
  | some p => exact AdaptiveAlpha.scale_nonneg hp

omit [Fintype ι] in
theorem potential_zero (p : Config ι) (a : ι → ℝ) : potential p (fun _ => 0) a=0 := by
  cases p with
  | none => rfl
  | some p => exact AdaptiveAlpha.potential_zero p a

theorem state_interval {p : Config ι} {a : ι → ℝ} (ha : state p a) (i : ι) :
    a i ∈ Set.Icc (0:ℝ) 1 := by
  cases p with
  | none => rw [ha]; simp
  | some p =>
    change DomainTransport.simplex p.active a at ha
    refine ⟨ha.1 i,?_⟩
    have h := single_le_sum (s:=univ) (f:=a) (fun j _ => ha.1 j) (mem_univ i)
    linarith [ha.2.2]

end UniformKServer.AlphaEmpty

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaEmptyLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! The true affine potential extended to empty domains. -/
noncomputable section
namespace UniformKServer.AlphaEmptyLinear
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

def coefficient : Config ι → (ι → ℝ) → ι → ℝ
  | none, _, _ => 0
  | some p, a, i => AdaptiveAlphaLinear.coefficient p a i

theorem affine {p : Config ι} (hp : valid p) (B a : ι → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1) :
    potential p B a=∑ i, coefficient p a i*B i := by
  cases p with
  | none => simp [potential,coefficient]
  | some p => exact AdaptiveAlphaLinear.affine hp B a ha

end UniformKServer.AlphaEmptyLinear

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! A single deterministic selection of the two proven minimizations. This
 supplies causal states, rather than postulating a trajectory satisfying the
 desired movement bound. The fallback branch is never used on valid input. -/
noncomputable section
namespace UniformKServer.AlphaRecurrence
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

def StepSpec (p q : Config ι) (Bstar Bnew old a b : ι → ℝ) : Prop :=
  state q a ∧ state q b ∧
  (∀ i, (∑ j, Bnew j)*a i ≤ (1+eta q i)*Bnew i) ∧
  (∀ i, (∑ j, Bstar j)*b i ≤ (1+eta p i)*Bstar i) ∧
  (∑ j, Bnew j)*SimplexTracker.movement a old ≤
    potential p Bstar old-potential q Bnew a+
    (potential q Bstar b-potential p Bstar b)+
    15*scale q*(∑ i, |Bnew i-Bstar i|)+4*((∑ i, Bnew i)-(∑ i, Bstar i))

def initial (p : Config ι) : ι → ℝ :=
  if h : ∃ a, state p a then h.choose else fun _ => 0

def chooseStep (p q : Config ι) (Bstar Bnew old : ι → ℝ) : (ι → ℝ) × (ι → ℝ) :=
  if h : ∃ ab : (ι → ℝ) × (ι → ℝ), StepSpec p q Bstar Bnew old ab.1 ab.2
    then h.choose else (fun _ => 0,fun _ => 0)

def trajectory (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) : ℕ → ι → ℝ
  | 0 => initial (p 0)
  | t+1 => (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B t)).1

def prepared (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  (chooseStep (p t) (p (t+1)) (Bstar t) (B (t+1)) (trajectory p Bstar B t)).2

def InputValid (p : ℕ → Config ι) (Bstar B : ℕ → ι → ℝ) : Prop :=
  (∀ t, valid (p t)) ∧ (∀ t i, 0 ≤ Bstar t i) ∧ (∀ t i, 0 ≤ B t i) ∧
  (∀ t, (∑ i, Bstar t i) ≤ ∑ i, B (t+1) i) ∧
  (∀ t, DomainTransport.Supported (active (p t)) (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (active (p (t+1))) (Bstar t)) ∧
  (∀ t, DomainTransport.Supported (active (p t)) (B t))

variable {Ω : Type*}
/-- Prefix equality suffices for output equality; choices cannot inspect any
 later input. This directly gives measurability in every finite reveal law. -/
theorem causal_through (p q : ℕ → Config ι) (S T B D : ℕ → ι → ℝ) (n : ℕ)
    (hp : ∀ t, t ≤ n → p t=q t) (hS : ∀ t, t < n → S t=T t)
    (hB : ∀ t, t ≤ n → B t=D t) :
    trajectory p S B n=trajectory q T D n := by
  induction n with
  | zero => simp only [trajectory,hp 0 le_rfl]
  | succ n ih =>
    have he := ih (fun t ht => hp t (ht.trans (Nat.le_succ n)))
      (fun t ht => hS t (ht.trans (Nat.lt_succ_self n)))
      (fun t ht => hB t (ht.trans (Nat.le_succ n)))
    simp only [trajectory,hp n (Nat.le_succ n),hp (n+1) le_rfl,
      hS n (Nat.lt_succ_self n),hB (n+1) le_rfl,he]

end UniformKServer.AlphaRecurrence

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SyntheticCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Common-core preparation in the adaptive allocation update, companion
 eqs. synthetic-core-input and synthetic-core-errors. All input probabilities
 here are the NEW posteriors, including when used with the old flags. -/
namespace UniformKServer.SyntheticCore
noncomputable section
open Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def input (p : κ → ℝ) (f : κ → Bool) : ℝ := ∑ j, if f j then p j else 0

def changes (f g : κ → Bool) : ℝ := ∑ j, if f j=g j then 0 else 1

theorem input_nonneg {p : κ → ℝ} (hp : ∀ j, 0 ≤ p j) (f : κ → Bool) : 0 ≤ input p f := by
  apply sum_nonneg
  intro j _
  split_ifs
  · exact hp j
  · rfl

theorem changes_nonneg (f g : κ → Bool) : 0 ≤ changes f g := by
  apply sum_nonneg
  intro j _
  split_ifs <;> norm_num

theorem no_flags (p : κ → ℝ) {f : κ → Bool} (hf : ∀ j, f j=false) : input p f=0 := by
  simp only [input,hf,Bool.false_eq_true,ite_false, if_false,sum_const_zero]

theorem input_difference (p : κ → ℝ) (f g : κ → Bool) (hp : ∀ j, p j ∈ Set.Icc (0:ℝ) 1) :
    |input p f-input p g| ≤ changes f g := by
  unfold input changes
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rcases hp j with ⟨h₀,h₁⟩
  cases hf : f j <;> cases hg : g j <;> simp [abs_of_nonneg h₀,abs_neg,h₁]

def core (old new : ι → Bool) (p : ι → κ → ℝ) (f : ι → κ → Bool) (i : ι) : ℝ :=
  if old i && new i then input (p i) (f i) else 0

/-- Inactivity entails an empty core, not merely a zero observed value. -/
def Supported (active : ι → Bool) (flag : ι → κ → Bool) : Prop :=
  ∀ i, active i=false → ∀ j, flag i j=false

omit [Fintype ι] in
theorem core_le_new (old new : ι → Bool) (p : ι → κ → ℝ) (g : ι → κ → Bool)
    (hp : ∀ i j, 0 ≤ p i j) (i : ι) :
    0 ≤ core old new p g i ∧ core old new p g i ≤ input (p i) (g i) := by
  unfold core
  split_ifs
  · exact ⟨input_nonneg (hp i) _,le_rfl⟩
  · exact ⟨le_rfl,input_nonneg (hp i) _⟩

omit [Fintype ι] in
theorem old_core_difference (old new : ι → Bool) (p : ι → κ → ℝ)
    (f g : ι → κ → Bool) (hp : ∀ i j, p i j ∈ Set.Icc (0:ℝ) 1)
    (hf : Supported old f) (hg : Supported new g) (i : ι) :
    |input (p i) (f i)-core old new p g i| ≤ changes (f i) (g i) := by
  have hn := changes_nonneg (f i) (g i)
  have hb := input_difference (p i) (f i) (g i) (hp i)
  cases ho : old i <;> cases hn' : new i
  · simp only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false, if_false,sub_zero]
    rw [no_flags _ (hf i ho),abs_zero]
    exact hn
  · simp only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false, if_false,sub_zero]
    rw [no_flags _ (hf i ho),abs_zero]
    exact hn
  · simpa only [core,ho,hn',Bool.true_and,Bool.false_eq_true,ite_false, if_false,
      no_flags _ (hg i hn')] using hb
  · simpa only [core,ho,hn',Bool.true_and,ite_true, if_true] using hb

omit [Fintype ι] in
theorem new_core_difference (old new : ι → Bool) (p : ι → κ → ℝ)
    (f g : ι → κ → Bool) (hp : ∀ i j, p i j ∈ Set.Icc (0:ℝ) 1)
    (hf : Supported old f) (hg : Supported new g) (i : ι) :
    |input (p i) (g i)-core old new p g i| ≤ changes (f i) (g i) := by
  have hn := changes_nonneg (f i) (g i)
  have hb := input_difference (p i) (f i) (g i) (hp i)
  cases ho : old i <;> cases hn' : new i
  · simp only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false, if_false,sub_zero]
    rw [no_flags _ (hg i hn'),abs_zero]
    exact hn
  · rw [no_flags _ (hf i ho),zero_sub,abs_neg] at hb
    simpa only [core,ho,Bool.false_and,Bool.false_eq_true,ite_false, if_false,sub_zero] using hb
  · simp only [core,ho,hn',Bool.true_and,Bool.false_eq_true,ite_false, if_false,sub_zero]
    rw [no_flags _ (hg i hn'),abs_zero]
    exact hn
  · simp only [core,ho,hn',Bool.true_and,ite_true, if_true,sub_self,abs_zero]
    exact hn

/-- All three source errors, on the fixed child set with zero extension. -/
theorem errors (old new : ι → Bool) (p : ι → κ → ℝ)
    (f g : ι → κ → Bool) (hp : ∀ i j, p i j ∈ Set.Icc (0:ℝ) 1)
    (hf : Supported old f) (hg : Supported new g) :
    (∑ i, |input (p i) (f i)-core old new p g i|) ≤ ∑ i, changes (f i) (g i) ∧
    (∑ i, |input (p i) (g i)-core old new p g i|) ≤ ∑ i, changes (f i) (g i) ∧
    0 ≤ (∑ i, input (p i) (g i))-(∑ i, core old new p g i) ∧
    (∑ i, input (p i) (g i))-(∑ i, core old new p g i) ≤ ∑ i, changes (f i) (g i) := by
  have hn (i : ι) : 0 ≤ input (p i) (g i)-core old new p g i :=
    sub_nonneg.mpr (core_le_new old new p g (fun i j => (hp i j).1) i).2
  have h₁ := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => old_core_difference old new p f g hp hf hg i)
  have h₂ := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => new_core_difference old new p f g hp hf hg i)
  refine ⟨h₁,h₂,?_,?_⟩
  · rw [←sum_sub_distrib]
    exact sum_nonneg fun i _ => hn i
  · simpa only [abs_of_nonneg (hn _),sum_sub_distrib] using h₂

end
end UniformKServer.SyntheticCore

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaFiniteInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                       
section

/-! Actual posterior/core inputs in a finite reveal law. Conditions describe the
 held, measurable data, not a movement conclusion. Empty and null-fiber cases
 still use the zero conventions of the conditional kernel. -/
noncomputable section
namespace UniformKServer.AlphaFiniteInput
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {Ω ι R : Type*} [Fintype Ω] [Fintype ι] [Fintype R]

structure Data (Ω ι R : Type*) [Fintype Ω] [Fintype ι] [Fintype R] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  filtration : ℕ → Setoid Ω
  refines : ∀ t ω v, (filtration (t+1)).r ω v → (filtration t).r ω v
  hidden : ℕ → Ω → ι × R → ℝ
  hidden_range : ∀ t ω ir, hidden t ω ir ∈ Set.Icc (0:ℝ) 1
  param : ℕ → Ω → Config ι
  param_valid : ∀ t ω, valid (param t ω)
  param_measurable : ∀ t ω v, (filtration t).r ω v → param t ω=param t v
  flag : ℕ → Ω → ι → R → Bool
  flag_measurable : ∀ t ω v, (filtration t).r ω v → flag t ω=flag t v
  supported : ∀ t ω i, i ∉ active (param t ω) → ∀ r, flag t ω i r=false

def activeFlag (p : Config ι) : ι → Bool := fun i => decide (i ∈ active p)

def changes (d : Data Ω ι R) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i, SyntheticCore.changes (d.flag t ω i) (d.flag (t+1) ω i)

theorem flag_supported (d : Data Ω ι R) (t : ℕ) (ω : Ω) :
    SyntheticCore.Supported (activeFlag (d.param t ω)) (d.flag t ω) := by
  intro i hi r
  exact d.supported t ω i (by simpa [activeFlag] using hi) r

theorem refining (d : Data Ω ι R) {s t : ℕ} (hst : s ≤ t) {ω v : Ω}
    (h : (d.filtration t).r ω v) : (d.filtration s).r ω v := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact ih (d.refines t ω v h)

end UniformKServer.AlphaFiniteInput

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaParameterChanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                            
section

/-! Prepared logarithmic parameter changes. All bounds concern the actual
 improper primitives, with constants uniform at vanishing side mass. -/
noncomputable section
namespace UniformKServer.AlphaParameterChanges
open Finset UniformKServer.AdaptiveAlpha
open scoped Classical
variable {ι : Type*} [Fintype ι]

def piece (p : Config ι) (B a : ι → ℝ) : ι → ℝ :=
  DomainTransport.extend p.active (fun i =>
    ProportionParameters.component p.param (fun j => B j) i (a i))

theorem sum_piece (p : Config ι) (B a : ι → ℝ) : (∑ i, piece p B a i)=potential p B a := by
  exact DomainTransport.extend_sum _ _

omit [Fintype ι] in
theorem piece_outside (p : Config ι) (B a : ι → ℝ) (i : ι) (hi : i ∉ p.active) :
    piece p B a i=0 := DomainTransport.extend_supported _ _ _ hi

omit [Fintype ι] in
theorem piece_inside (p : Config ι) (B a : ι → ℝ) (i : p.active) :
    piece p B a i=ProportionParameters.component p.param (fun j => B j) i (a i) :=
  DomainTransport.extend_apply _ _ _

/-- An ordinary coordinate costs only its prepared input. -/
theorem regular_piece {p : Config ι} (hp : valid p) (B a : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hs : DomainTransport.Supported p.active B)
    (ha : ∀ i, a i ∈ Set.Icc (0:ℝ) 1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i) (i : p.active)
    (he : ProportionParameters.component p.param (fun j => B j) i (a i)=
      AlphaTracker.regularG p.param.h (fun j => B j) p.param.ell p.param.ct p.param.C i (a i))
    (hh : 1 ≤ p.param.h i) : |piece p B a i| ≤ 4*scale p*B i := by
  rw [piece_inside,he]
  have h := AlphaBounds.regular_component hh (ha i) (scale p)
    (∑ j : p.active, B j) ((1+ProportionParameters.eta p.param i)*B i)
  rw [DomainTransport.sum_restrict hs,abs_of_nonneg (scale_nonneg hp),
    abs_of_nonneg (sum_nonneg fun j _ => hB j),
    abs_of_nonneg (mul_nonneg (by linarith [ProportionParameters.eta_nonneg hp.2 i]) (hB i))] at h
  have hm := mul_le_mul_of_nonneg_right (hp.2.2.2.2.1 i) (hB i)
  have heq : AlphaTracker.regularG p.param.h (fun j => B j) p.param.ell p.param.ct p.param.C i (a i)=
      LogPrimitive.primitive (Denominators.regular (p.param.h i)) 0 (scale p)
        (∑ j, B j) ((1+ProportionParameters.eta p.param i)*B i) (a i) := by
    unfold AlphaTracker.regularG scale ProportionParameters.eta
    rw [DomainTransport.sum_restrict hs]
  rw [heq]
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left (hf i) (scale_nonneg hp),
    mul_le_mul_of_nonneg_left hm (scale_nonneg hp)])

/-- Sum of prepared side constraints, without division by total input. -/
theorem prepared_side (B a : ι → ℝ) (ha : ∑ i, a i=1)
    (hf : ∀ i, (∑ j, B j)*a i ≤ 2*B i) (o : ι) :
    (∑ j, B j)*(1-a o) ≤ 2*((∑ j, B j)-B o) := by
  have h := sum_le_sum (s:=univ.erase o) (fun i _ => hf i)
  rw [←mul_sum,←mul_sum,sum_erase_eq_sub (mem_univ o),
    sum_erase_eq_sub (mem_univ o),ha] at h
  exact h

omit [Fintype ι] in
theorem singleton_potential {p : Config ι} (o : p.active)
    (he : p.param.kind=.singleton o) (B a : ι → ℝ) : potential p B a=0 := by
  simp [potential,ProportionParameters.potential,ProportionParameters.component,he]

end UniformKServer.AlphaParameterChanges

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AlphaPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! Common-core prepared states can be evaluated in either parameter domain.
 The zero-weight case is proved separately; there is no hidden division by a
 small core mass. -/
noncomputable section
namespace UniformKServer.AlphaPrepared
open Finset UniformKServer.AlphaEmpty
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem zero_of_sum {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) (hz : ∑ i, B i=0) :
    B=fun _ => 0 := by
  funext i
  have hi := single_le_sum (s:=univ) (f:=B) (fun j _ => hB j) (mem_univ i)
  exact le_antisymm (by linarith) (hB i)

theorem prepared_state {p q : Config ι} {B b : ι → ℝ}
    (hS : 0 < ∑ i, B i) (hs : DomainTransport.Supported (active p) B)
    (hqB : DomainTransport.Supported (active q) B) (hb : state q b)
    (hf : ∀ i, (∑ j, B j)*b i ≤ (1+eta p i)*B i) : state p b := by
  cases p with
  | none =>
    have he := zero_supported hs
    simp only [he,sum_const_zero,lt_self_iff_false] at hS
  | some p =>
    cases q with
    | none =>
      have he := zero_supported hqB
      simp only [he,sum_const_zero,lt_self_iff_false] at hS
    | some q =>
      change DomainTransport.simplex q.active b at hb
      refine ⟨hb.1,?_,hb.2.2⟩
      intro i hi
      have h := hf i
      rw [hs i hi,mul_zero] at h
      exact le_antisymm ((nonpos_of_mul_nonpos_right h hS)) (hb.1 i)

end UniformKServer.AlphaPrepared

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorRamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

/-! Exact clipped ramp and retained-heavy-anchor release. All integrals here
are finite weighted sums on the original finite metric. -/
noncomputable section
namespace UniformKServer.AnchorRamp
open Finset
open scoped Classical

def ramp (u : ℝ) : ℝ := max 0 (min 1 ((u-4)/3))

theorem range (u : ℝ) : ramp u ∈ Set.Icc 0 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem zero (u : ℝ) (hu : u ≤ 4) : ramp u=0 := by
  unfold ramp
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

theorem one (u : ℝ) (hu : 7 ≤ u) : ramp u=1 := by
  unfold ramp
  rw [min_eq_left (by linarith)]
  norm_num

theorem lipschitz (u v : ℝ) : |ramp u-ramp v| ≤ |u-v|/3 := by
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min 1 ((u-4)/3)) 0 (min 1 ((v-4)/3))
  have hmin := abs_min_sub_min_le_max (1:ℝ) ((u-4)/3) 1 ((v-4)/3)
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 ((u-4)/3)-min 1 ((v-4)/3)))] at hmax
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg ((u-4)/3-(v-4)/3))] at hmin
  have he : |(u-4)/3-(v-4)/3|=|u-v|/3 := by rw [←sub_div,show (u-4)-(v-4)=u-v by ring,abs_div]; norm_num
  rw [he] at hmin
  exact hmax.trans hmin

variable {X : Type*} [MetricSpace X]

def value (r : ℝ) (a z : X) : ℝ := ramp (dist a z/r)

theorem value_range (r : ℝ) (a z : X) : value r a z ∈ Set.Icc 0 1 := range _

variable [Fintype X]

def ball (x : X) (R : ℝ) : Finset X := univ.filter (fun z => dist x z ≤ R)
def mass (μ : X → ℝ) (C : Finset X) : ℝ := ∑ z ∈ C, μ z

omit [Fintype X] in
theorem inner_change (r γ : ℝ) (hr : 0 < r) (hγ : γ < 1) (a x z : X)
    (ha : 8*r < dist a x) (hz : dist x z ≤ γ*r) : value r x z-value r a z = -1 := by
  have hn : value r x z=0 := zero _ ((div_le_iff₀ hr).2 (by nlinarith))
  have hp : value r a z=1 := by
    apply one
    apply (le_div_iff₀ hr).2
    have ht := dist_triangle a z x
    rw [dist_comm z x] at ht
    nlinarith
  rw [hn,hp]
  norm_num

theorem payment (r b d H I δ : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b) (hd : 0 < d)
    (hH : 0 ≤ H) (hδ : δ ≤ 1/100) (hden : d ≤ (6/5)*(2+δ)*H)
    (hI : I ≤ -(1-δ)*H) : r*b/d*I ≤ -(1/4)*r*b := by
  have hm := mul_le_mul_of_nonneg_left hI (show 0 ≤ r*b/d by positivity)
  have hc : d/4 ≤ (1-δ)*H := by nlinarith [mul_nonneg (show 0 ≤ 1/100-δ by linarith) hH]
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ r*b/d by positivity)
  have he : r*b/d*(d/4)=r*b/4 := by field_simp
  rw [he] at hh
  nlinarith

end UniformKServer.AnchorRamp

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

/-! The signed scalar accounting inequalities for the reference, park and
hidden-key substeps of the retained-anchor potential. -/
noncomputable section
namespace UniformKServer.AnchorScalar
open Finset
open scoped Classical

 theorem reference (r b I M u s C : ℝ) (hr : 0 ≤ r) (hb : 0≤b) (hI : 0≤I)
    (hIM : I≤M) (hu : 0<u) (hs : s=1+M) (hspos : 0 < s) (hbC : b≤C*u)
    (hC : 0≤C) : r*b/s*I-r*b/u*I ≤ r*C*(u+s) := by
  by_cases hsu : u ≤ s
  · have hinv : 1/s≤1/u := one_div_le_one_div_of_le hu hsu
    have hm := mul_le_mul_of_nonneg_left hinv (show 0 ≤ r*b*I by positivity)
    have he : r*b/s*I-r*b/u*I≤0 := by
      have h1 : r*b*I*(1/s)=r*b/s*I := by ring
      have h2 : r*b*I*(1/u)=r*b/u*I := by ring
      rw [h1,h2] at hm
      linarith
    exact he.trans (by positivity)
  · have hIs : I/s≤1 := (div_le_one hspos).mpr (by linarith)
    have hm := mul_le_mul_of_nonneg_left hIs (show 0 ≤ r*b by positivity)
    have hz : 0 ≤ r*b/u*I := by positivity
    have hbc := mul_le_mul_of_nonneg_left hbC hr
    have hcs : 0 ≤ r*C*s := by positivity
    have he : r*b*(I/s)=r*b/s*I := by ring
    rw [he] at hm
    nlinarith

theorem parks (r b c I u ρ : ℝ) (hr : 0 ≤ r) (hI : 0≤I) (hu : 0<u)
    (hIu : I≤ρ*u) : |r*c/u*I-r*b/u*I|≤ρ*r*|c-b| := by
  have hb : I/u≤ρ := (div_le_iff₀ hu).mpr hIu
  have he : r*c/u*I-r*b/u*I=r*(c-b)*(I/u) := by ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg (by positivity : 0≤I/u)]
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ r*|c-b| by positivity)
  nlinarith

variable {X H T : Type*} [MetricSpace X]
def value (r : ℝ) (c : H→ℝ) (a : H→X) (l : H⊕T) (p : X) : ℝ :=
  match l with
  | Sum.inl h => c h*AnchorRamp.value r (a h) p
  | Sum.inr _ => 0

theorem value_nonneg (r : ℝ) (c : H→ℝ) (a : H→X) (hc : ∀ h,0 ≤ c h) (l : H⊕T) (p : X) :
    0≤value r c a l p := by
  cases l with
  | inl h => exact mul_nonneg (hc h) (AnchorRamp.value_range r (a h) p).1
  | inr _ => exact le_rfl

theorem value_bound (r C : ℝ) (c : H→ℝ) (a : H→X) (hc : ∀ h,0 ≤ c h)
    (hC : 0≤C) (hcC : ∀ h,c h≤C) (l : H⊕T) (p : X) : value r c a l p≤C := by
  cases l with
  | inl h =>
    exact (mul_le_of_le_one_right (hc h) (AnchorRamp.value_range r (a h) p).2).trans (hcC h)
  | inr _ => exact hC

def near (r : ℝ) (c : H→ℝ) (a : H→X) (l : H⊕T) (p : X) : ℝ :=
  match l with
  | Sum.inl h => if dist (a h) p<7*r then c h else 0
  | Sum.inr _ => 0

theorem near_nonneg (r : ℝ) (c : H→ℝ) (a : H→X) (hc : ∀ h,0 ≤ c h) (l : H⊕T) (p : X) :
    0≤near r c a l p := by
  cases l with
  | inl h => dsimp only [near]; split_ifs; exact hc h; exact le_rfl
  | inr _ => exact le_rfl

end UniformKServer.AnchorScalar

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_KeySizeTracker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section

/-! The unreset affine entropy tracker for each fixed heavy-key slot. Filtering
is charged at the old measurable coefficient on every step. -/
noncomputable section
namespace UniformKServer.KeySizeTracker
open Finset
open scoped Classical
variable {Ω : Type*} [Fintype Ω]

variable {K : ℝ}

def keep (s u : ℝ) : Prop := s ≤ (6/5)*u ∧ u ≤ (6/5)*s

end UniformKServer.KeySizeTracker

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_AnchorPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Finite heavy-slot potentials and the non-event-conditioned parameter
substeps. This is scalar accounting, not an assumption of the travel budget. -/
noncomputable section
namespace UniformKServer.AnchorPotential
open Finset
open scoped Classical
variable {X H T Ω : Type*} [Fintype H] [MetricSpace X] [Fintype Ω]

def integral (r : ℝ) (μ : X→ℝ) (C : Finset X) (a : X) : ℝ :=
  ∑ p∈C,μ p*AnchorRamp.value r a p

theorem integral_nonneg (r : ℝ) (μ : X→ℝ) (hμ : ∀ p,0 ≤ μ p) (C : Finset X) (a : X) :
    0 ≤ integral r μ C a := sum_nonneg (fun p _=>mul_nonneg (hμ p) (AnchorRamp.value_range r a p).1)

theorem integral_le (r : ℝ) (μ : X→ℝ) (hμ : ∀ p,0 ≤ μ p) (C : Finset X) (a : X) :
    integral r μ C a ≤ ∑ p∈C,μ p :=
  sum_le_sum (fun p _=>mul_le_of_le_one_right (hμ p) (AnchorRamp.value_range r a p).2)

end UniformKServer.AnchorPotential

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BalancedRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

                                                                      
                                                                        
                                                                  
namespace UniformKServer.BalancedRepair
open scoped symmDiff
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

abbrev Joint (Ω ι : Type*) := (Ω × Finset ι) → ℝ

def admissible (μ : Ω → ℝ) (r : Ω → ℕ) (g : Joint Ω ι) : Prop :=
  (∀ q, 0 ≤ g q) ∧ (∀ ω, ∑ A : Finset ι, g (ω,A) = μ ω) ∧
    ∀ q, q.2.card ≠ r q.1 → g q = 0

def marginal (g : Joint Ω ι) (i : ι) : ℝ :=
  ∑ q, g q * if i ∈ q.2 then 1 else 0

def discrepancy (f : ι → ℝ) (g : Joint Ω ι) : ℝ :=
  ∑ i, |marginal g i - f i|

def hamming (base : Ω → Finset ι) (q : Ω × Finset ι) : ℝ :=
  (q.2 ∆ base q.1).card

def cost (base : Ω → Finset ι) (g : Joint Ω ι) : ℝ :=
  ∑ q, g q * hamming base q

def initial (μ : Ω → ℝ) (base : Ω → Finset ι) : Joint Ω ι :=
  fun q => if q.2 = base q.1 then μ q.1 else 0

def objective (base : Ω → Finset ι) (f : ι → ℝ) (g : Joint Ω ι) : ℝ :=
  cost base g + 10 * discrepancy f g


omit [Fintype Ω] [DecidableEq Ω] in
theorem initial_admissible (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι)
    (hμ : ∀ ω, 0 ≤ μ ω) (hbase : ∀ ω, (base ω).card = r ω) :
    admissible μ r (initial μ base) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp only [initial]
    split
    · exact hμ q.1
    · exact le_rfl
  · intro ω
    simp [initial]
  · intro q hq
    simp only [initial]
    split_ifs with h
    · exact False.elim (hq (h ▸ hbase q.1))
    · rfl

omit [DecidableEq Ω] [DecidableEq ι] in
theorem total_mass {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) : ∑ q, g q = ∑ ω, μ ω := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ω _ => hg.2.1 ω

omit [DecidableEq Ω] in
theorem initial_cost (μ : Ω → ℝ) (base : Ω → Finset ι) :
    cost base (initial μ base) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  simp only [initial]
  split_ifs with h
  · simp [hamming, h]
  · simp

omit [DecidableEq Ω] [DecidableEq ι] in
theorem admissible_compact (μ : Ω → ℝ) (r : Ω → ℕ) :
    IsCompact {g : Joint Ω ι | admissible μ r g} := by
  have h₁ : IsClosed {g : Joint Ω ι | ∀ q, 0 ≤ g q} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun q => isClosed_le continuous_const (continuous_apply q)
  have h₂ : IsClosed {g : Joint Ω ι | ∀ ω, ∑ A : Finset ι, g (ω,A) = μ ω} := by
    simp only [← Set.iInter_ofPred]
    exact isClosed_iInter fun ω => isClosed_eq (by fun_prop) continuous_const
  have h₃ : IsClosed {g : Joint Ω ι | ∀ q, q.2.card ≠ r q.1 → g q = 0} := by
    simp only [← Set.iInter_ofPred]
    apply isClosed_iInter
    intro q
    by_cases hq : q.2.card ≠ r q.1
    · simpa [hq] using isClosed_eq (continuous_apply q) (continuous_const (y := (0 : ℝ)))
    · simp [hq]
  have hc : IsClosed {g : Joint Ω ι | admissible μ r g} := h₁.inter (h₂.inter h₃)
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Ω × Finset ι => (0 : ℝ))
    (fun _ => ∑ ω, μ ω))).of_isClosed_subset hc
  intro g hg
  refine ⟨hg.1, ?_⟩
  intro q
  calc
    g q ≤ ∑ q', g q' := Finset.single_le_sum (fun q' _ => hg.1 q') (Finset.mem_univ q)
    _ = _ := total_mass hg

omit [DecidableEq Ω] in
theorem objective_continuous (base : Ω → Finset ι) (f : ι → ℝ) :
    Continuous (objective base f) := by
  unfold objective cost discrepancy marginal
  fun_prop

omit [DecidableEq Ω] in
theorem minimizer_exists (μ : Ω → ℝ) (r : Ω → ℕ) (base : Ω → Finset ι)
    (f : ι → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (hbase : ∀ ω, (base ω).card = r ω) :
    ∃ g, admissible μ r g ∧ ∀ g', admissible μ r g' →
      objective base f g ≤ objective base f g' := by
  exact (admissible_compact μ r).exists_isMinOn
    ⟨initial μ base, initial_admissible μ r base hμ hbase⟩
    (objective_continuous base f).continuousOn

def transfer (g : Joint Ω ι) (q q' : Ω × Finset ι) (ε : ℝ) : Joint Ω ι :=
  fun z => g z - (if z = q then ε else 0) + (if z = q' then ε else 0)

theorem sum_transfer (g : Joint Ω ι) (q q' : Ω × Finset ι) (ε : ℝ)
    (c : (Ω × Finset ι) → ℝ) :
    (∑ z, transfer g q q' ε z * c z) = (∑ z, g z * c z) + ε*(c q' - c q) := by
  simp only [transfer, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he : ∀ a : Ω × Finset ι, (∑ z, (if z = a then ε else 0) * c z) = ε*c a := by
    intro a
    simp
  rw [he, he]
  ring


def exchange (A : Finset ι) (i j : ι) : Finset ι := insert j (A.erase i)

omit [Fintype ι] in
theorem exchange_card {A : Finset ι} {i j : ι} (hi : i ∈ A) (hj : j ∉ A) :
    (exchange A i j).card = A.card := by
  rw [exchange, Finset.card_insert_of_notMem (by simp [hj]), Finset.card_erase_of_mem hi]
  have : 0 < A.card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

omit [Fintype ι] in
theorem exchange_indicator {A : Finset ι} {i j : ι} (hi : i ∈ A) (hj : j ∉ A) (l : ι) :
    (if l ∈ exchange A i j then (1 : ℝ) else 0) =
      (if l ∈ A then 1 else 0) + (if l = j then 1 else 0) - (if l = i then 1 else 0) := by
  have hij : i ≠ j := by intro h; subst j; exact hj hi
  by_cases hli : l = i
  · subst l; simp [exchange, hij, hi]
  · by_cases hlj : l = j
    · subst l; simp [exchange, hli, hj]
    · by_cases hl : l ∈ A <;> simp [exchange, hli, hlj, hl]

omit [Fintype Ω] [Fintype ι] [DecidableEq Ω] in
theorem exchange_hamming (base : Ω → Finset ι) (ω : Ω) (A : Finset ι) (i j : ι) :
    hamming base (ω, exchange A i j) ≤ hamming base (ω,A) + 2 := by
  have hs : exchange A i j ∆ base ω ⊆ insert j (insert i (A ∆ base ω)) := by
    intro l hl
    by_cases hi : l = i
    · simp [hi]
    by_cases hj : l = j
    · simp [hj]
    simp only [Finset.mem_insert, hi, hj, false_or]
    simpa [exchange, Finset.mem_symmDiff, hi, hj] using hl
  have hcard := Finset.card_le_card hs
  have h₁ := Finset.card_insert_le j (insert i (A ∆ base ω))
  have h₂ := Finset.card_insert_le i (A ∆ base ω)
  dsimp [hamming]
  exact_mod_cast (show (exchange A i j ∆ base ω).card ≤ (A ∆ base ω).card + 2 by omega)

def swap (g : Joint Ω ι) (ω : Ω) (A : Finset ι) (i j : ι) (ε : ℝ) : Joint Ω ι :=
  transfer g (ω,A) (ω,exchange A i j) ε

theorem swap_marginal (g : Joint Ω ι) (ω : Ω) (A : Finset ι) (i j : ι) (ε : ℝ)
    (hi : i ∈ A) (hj : j ∉ A) (l : ι) :
    marginal (swap g ω A i j ε) l = marginal g l +
      ε*((if l = j then 1 else 0) - (if l = i then 1 else 0)) := by
  rw [marginal, swap, sum_transfer]
  change marginal g l + ε * ((if l ∈ exchange A i j then 1 else 0) -
    (if l ∈ A then 1 else 0)) = _
  rw [exchange_indicator hi hj]
  ring

theorem swap_cost (base : Ω → Finset ι) (g : Joint Ω ι) (ω : Ω) (A : Finset ι)
    (i j : ι) (ε : ℝ) (hε : 0 ≤ ε) :
    cost base (swap g ω A i j ε) ≤ cost base g + 2*ε := by
  rw [cost, swap, sum_transfer]
  change cost base g + ε*(hamming base (ω,exchange A i j) - hamming base (ω,A)) ≤ _
  nlinarith [exchange_hamming base ω A i j]

omit [DecidableEq Ω] in
theorem discrepancy_transfer {f : ι → ℝ} {g g' : Joint Ω ι} {i j : ι} {ε : ℝ}
    (hij : i ≠ j) (hε : 0 ≤ ε)
    (hi : ε ≤ marginal g i - f i) (hj : ε ≤ f j - marginal g j)
    (hmarg : ∀ l, marginal g' l = marginal g l +
      ε*((if l = j then 1 else 0) - (if l = i then 1 else 0))) :
    discrepancy f g' = discrepancy f g - 2*ε := by
  have he : ∀ l, |marginal g' l - f l| = |marginal g l - f l| -
      (if l = i then ε else 0) - (if l = j then ε else 0) := by
    intro l
    rw [hmarg]
    by_cases hli : l = i
    · subst l
      simp only [hij, ↓reduceIte, zero_sub, mul_neg, mul_one]
      rw [abs_of_nonneg (by linarith : 0 ≤ marginal g i + -ε - f i),
        abs_of_nonneg (by linarith : 0 ≤ marginal g i - f i)]
      ring
    · by_cases hlj : l = j
      · subst l
        simp only [hli, ↓reduceIte, sub_zero, mul_one]
        rw [abs_of_nonpos (by linarith : marginal g j + ε - f j ≤ 0),
          abs_of_nonpos (by linarith : marginal g j - f j ≤ 0)]
        ring
      · simp [hli, hlj]
  simp only [discrepancy, he, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

omit [DecidableEq Ω] in
theorem sum_marginal {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) : ∑ i, marginal g i = ∑ ω, μ ω * (r ω : ℝ) := by
  unfold marginal
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    (∑ A : Finset ι, g (ω,A) * (A.card : ℝ)) =
        ∑ A : Finset ι, g (ω,A) * (r ω : ℝ) := by
      apply Finset.sum_congr rfl
      intro A _
      by_cases h : A.card = r ω
      · rw [h]
      · rw [hg.2.2 (ω,A) h]; simp
    _ = _ := by rw [← Finset.sum_mul, hg.2.1]


omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
theorem supported_card {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) {q : Ω × Finset ι} (hq : 0 < g q) : q.2.card = r q.1 := by
  by_contra h
  have := hg.2.2 q h
  linarith

omit [DecidableEq Ω] in
theorem supported_mem {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) {i : ι} (hi : 0 < marginal g i) :
    ∃ q, 0 < g q ∧ i ∈ q.2 := by
  obtain ⟨q, _, hq⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun q _ => mul_nonneg (hg.1 q) (by split <;> positivity))).mp hi
  by_cases h : i ∈ q.2
  · exact ⟨q, by simpa [h] using hq, h⟩
  · simp [h] at hq

omit [DecidableEq Ω] in
theorem supported_notMem {μ : Ω → ℝ} {r : Ω → ℕ} {g : Joint Ω ι}
    (hg : admissible μ r g) (hμ : ∑ ω, μ ω = 1) {i : ι} (hi : marginal g i < 1) :
    ∃ q, 0 < g q ∧ i ∉ q.2 := by
  by_contra! h
  have he : marginal g i = ∑ q, g q := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases hzero : g q = 0
    · simp [hzero]
    · have hp : 0 < g q := lt_of_le_of_ne (hg.1 q) (Ne.symm hzero)
      simp [h q hp]
  rw [he, total_mass hg, hμ] at hi
  exact lt_irrefl _ hi

theorem four_positive {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ a ∧ ε ≤ b ∧ ε ≤ c ∧ ε ≤ d := by
  refine ⟨min a (min b (min c d)), lt_min ha (lt_min hb (lt_min hc hd)),
    min_le_left _ _, ?_, ?_, ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

omit [Fintype ι] in
theorem exchange_intermediate {A B : Finset ι} {i j : ι}
    (hij : i ≠ j) (hiA : i ∈ A) (hjA : j ∈ A) (hiB : i ∉ B) (hjB : j ∉ B)
    (hc : A.card ≤ B.card + 1) : ∃ h, h ∈ B ∧ h ∉ A := by
  by_contra! h
  have hsub : insert i (insert j B) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hiA
    · exact hjA
    · exact h x hx
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hij, hiB]),
    Finset.card_insert_of_notMem hjB] at hcard
  omega

omit [DecidableEq ι] in
theorem discrepancy_pair {f p : ι → ℝ} (hsum : ∑ i, p i = ∑ i, f i)
    (hne : ¬ ∀ i, p i = f i) : ∃ i j, f i < p i ∧ p j < f j := by
  have hpos : ∃ i, f i < p i := by
    by_contra! h
    exact hne (fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp hsum i (Finset.mem_univ i))
  have hneg : ∃ j, p j < f j := by
    by_contra! h
    exact hne (fun i => ((Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp hsum.symm i
      (Finset.mem_univ i)).symm)
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj⟩ := hneg
  exact ⟨i,j,hi,hj⟩

end UniformKServer.BalancedRepair


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_BalancedStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.BalancedStar
open UniformKServer.BalancedRepair
open scoped symmDiff
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω] [DecidableEq ι]

def Balanced (a : ℝ) (x : ℤ) : Prop := x = ⌊a⌋ ∨ x = ⌈a⌉

structure Input (Ω ι : Type*) [Fintype Ω] [Fintype ι] where
  μ : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ μ ω
  total : ∑ ω, μ ω = 1
  a : ι → ℝ
  b : ι → ℝ
  a_nonneg : ∀ i, 0 ≤ a i
  b_nonneg : ∀ i, 0 ≤ b i
  X : Ω → ι → ℤ
  N : Ω → ℤ
  X_balanced : ∀ ω i, Balanced (a i) (X ω i)
  N_balanced : ∀ ω, Balanced (∑ i, b i) (N ω)
  X_mean : ∀ i, ∑ ω, μ ω * (X ω i : ℝ) = a i
  N_mean : ∑ ω, μ ω * (N ω : ℝ) = ∑ i, b i

noncomputable def realized (b : ι → ℝ) (A : Finset ι) (i : ι) : ℤ :=
  ⌊b i⌋ + if i ∈ A then 1 else 0

def T (I : Input Ω ι) : ℝ := ∑ i, |I.a i - I.b i|

def Valid (I : Input Ω ι) (ω : Ω) (A : Finset ι) : Prop :=
  (∀ i, Balanced (I.b i) (realized I.b A i)) ∧
    (∑ i, realized I.b A i) = I.N ω


noncomputable def clip (b : ℝ) (x : ℤ) : ℤ := max ⌊b⌋ (min ⌈b⌉ x)

theorem balanced_bounds {a : ℝ} {x : ℤ} (hx : Balanced a x) : ⌊a⌋ ≤ x ∧ x ≤ ⌈a⌉ := by
  rcases hx with rfl | rfl <;> exact ⟨by first | rfl | exact Int.floor_le_ceil a,
    by first | rfl | exact Int.floor_le_ceil a⟩

theorem bounds_balanced {a : ℝ} {x : ℤ} (hx : ⌊a⌋ ≤ x ∧ x ≤ ⌈a⌉) : Balanced a x := by
  have := Int.ceil_le_floor_add_one a
  dsimp [Balanced]
  omega

theorem clip_balanced (b : ℝ) (x : ℤ) : Balanced b (clip b x) := by
  apply bounds_balanced
  dsimp [clip]
  exact ⟨le_max_left _ _, max_le (Int.floor_le_ceil b) (min_le_left _ _)⟩

omit [DecidableEq Ω] in
theorem clip_nonexpansive (μ : Ω → ℝ) (X : Ω → ℤ) (a b : ℝ)
    (_hμ : ∀ ω, 0 ≤ μ ω) (hμsum : ∑ ω, μ ω = 1)
    (hX : ∀ ω, Balanced a (X ω)) (hmean : ∑ ω, μ ω * (X ω : ℝ) = a) :
    (∑ ω, μ ω * |(clip b (X ω) : ℝ) - (X ω : ℝ)|) ≤ |a-b| := by
  rcases le_total a b with hab | hba
  · have hu : ∀ ω, X ω ≤ ⌈b⌉ := fun ω =>
      (balanced_bounds (hX ω)).2.trans (Int.ceil_mono hab)
    by_cases hl : ⌊b⌋ ≤ ⌊a⌋
    · have he : ∀ ω, clip b (X ω) = X ω := by
        intro ω
        rw [clip, min_eq_right (hu ω), max_eq_right (hl.trans (balanced_bounds (hX ω)).1)]
      simp [he]
    · have hl' : ∀ ω, X ω ≤ ⌊b⌋ := by
        intro ω
        have h₁ := (balanced_bounds (hX ω)).2
        have h₂ := Int.ceil_le_floor_add_one a
        omega
      have he : ∀ ω, clip b (X ω) = ⌊b⌋ := by
        intro ω
        rw [clip, min_eq_right (hu ω), max_eq_left (hl' ω)]
      calc
        _ = (⌊b⌋ : ℝ) - a := by
          simp only [he, abs_of_nonneg (sub_nonneg.mpr (Int.cast_le.mpr (hl' _))),
            mul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, hμsum, hmean, one_mul]
        _ ≤ |a-b| := by rw [abs_of_nonpos (sub_nonpos.mpr hab)]; linarith [Int.floor_le b]
  · have hl : ∀ ω, ⌊b⌋ ≤ X ω := fun ω =>
      (Int.floor_mono hba).trans (balanced_bounds (hX ω)).1
    by_cases hu : ⌈a⌉ ≤ ⌈b⌉
    · have he : ∀ ω, clip b (X ω) = X ω := by
        intro ω
        rw [clip, min_eq_right ((balanced_bounds (hX ω)).2.trans hu), max_eq_right (hl ω)]
      simp [he]
    · have hu' : ∀ ω, ⌈b⌉ ≤ X ω := by
        intro ω
        have h₁ := (balanced_bounds (hX ω)).1
        have h₂ := Int.ceil_le_floor_add_one a
        omega
      have he : ∀ ω, clip b (X ω) = ⌈b⌉ := by
        intro ω
        rw [clip, min_eq_left (hu' ω), max_eq_right (Int.floor_le_ceil b)]
      calc
        _ = a - (⌈b⌉ : ℝ) := by
          simp only [he, abs_of_nonpos (sub_nonpos.mpr (Int.cast_le.mpr (hu' _)))]
          simp only [neg_sub, mul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, hμsum, hmean, one_mul]
        _ ≤ |a-b| := by rw [abs_of_nonneg (sub_nonneg.mpr hba)]; linarith [Int.le_ceil b]


noncomputable def lowerSum (b : ι → ℝ) : ℤ := ∑ i, ⌊b i⌋
noncomputable def upperSet (b : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => ⌊b i⌋ < ⌈b i⌉)

theorem sum_realized (b : ι → ℝ) (A : Finset ι) :
    (∑ i, realized b A i) = lowerSum b + (A.card : ℤ) := by
  simp [realized, lowerSum, Finset.sum_add_distrib]

theorem ceil_sum (b : ι → ℝ) :
    (∑ i, ⌈b i⌉) = lowerSum b + ((upperSet b).card : ℤ) := by
  rw [← sum_realized]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [realized]
  have hf := Int.floor_le_ceil (b i)
  have hc := Int.ceil_le_floor_add_one (b i)
  simp only [upperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

omit [DecidableEq ι] in
theorem ceil_le_sum (b : ι → ℝ) : ⌈∑ i, b i⌉ ≤ ∑ i, ⌈b i⌉ := by
  apply Int.ceil_le.mpr
  simp only [Int.cast_sum]
  exact Finset.sum_le_sum fun i _ => Int.le_ceil (b i)

theorem choose_subset_close (H B : Finset ι) (r : ℕ) (hB : B ⊆ H) (hr : r ≤ H.card) :
    ∃ A : Finset ι, A ⊆ H ∧ A.card = r ∧
      ((A ∆ B).card : ℝ) = |(r : ℝ) - (B.card : ℝ)| := by
  rcases le_total r B.card with h | h
  · obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq h
    refine ⟨A,hA.trans hB,hcard,?_⟩
    rw [symmDiff_of_le hA, Finset.card_sdiff_of_subset hA, hcard,
      Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · obtain ⟨A,hBA,hA,hcard⟩ := Finset.exists_subsuperset_card_eq hB h hr
    refine ⟨A,hA,hcard,?_⟩
    rw [symmDiff_of_ge hBA, Finset.card_sdiff_of_subset hBA, hcard,
      Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]


omit [DecidableEq ι] in
theorem abs_sum_sub_le (u v : ι → ℝ) :
    |(∑ i, u i) - ∑ i, v i| ≤ ∑ i, |u i-v i| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

noncomputable def clipCost (I : Input Ω ι) : ℝ :=
  ∑ ω, I.μ ω * ∑ i, |(clip (I.b i) (I.X ω i) : ℝ) - (I.X ω i : ℝ)|

omit [DecidableEq Ω] [DecidableEq ι] in
theorem clipCost_le (I : Input Ω ι) : clipCost I ≤ T I := by
  simp only [clipCost, Finset.mul_sum, T]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun i _ =>
    clip_nonexpansive I.μ (fun ω => I.X ω i) (I.a i) (I.b i) I.nonneg I.total
      (fun ω => I.X_balanced ω i) (I.X_mean i)

end UniformKServer.BalancedStar

/-! One conditional update of the complete finite tree rounding process.
The arbitrary supported old law includes every correlation produced by earlier
ancestor roundings; no conditional independence is imposed. -/

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_CrossRule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! The two actual hysteresis crossings in the star outputs. In contrast to
 comparing with an unused old rule, these bounds use only the states that
 actually existed. The coefficient of parent variation stays exactly one. -/
namespace UniformKServer.AllocationOutputs
noncomputable section
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem holes_two_nonneg (R : ℝ) (ω : ι → ℝ) (o : ι) (hω : ∀ i, 0 ≤ ω i) (i : ι) :
    0 ≤ holesTwo R ω o i := by
  unfold holesTwo
  split_ifs
  · exact le_max_right _ _
  · exact hω i

omit [DecidableEq ι] in
theorem nonnegative_movement (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    variation a b ≤ (∑ i, a i)+(∑ i, b i) := by
  rw [variation,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  exact abs_le.mpr ⟨by linarith [ha i,hb i], by linarith [ha i,hb i]⟩

theorem side_scalar_bound (D W : ℝ) (w : ι → ℝ) (o : ι)
    (hD : 0 ≤ D) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≤ W) :
    0 ≤ sideTotal (fun i => D*w i) o ∧ sideTotal (fun i => D*w i) o ≤ D*W := by
  unfold sideTotal
  refine ⟨sum_nonneg (fun i _ => mul_nonneg hD (hw i)), ?_⟩
  have hsum : (∑ i ∈ univ.erase o, w i) ≤ ∑ i, w i :=
    sum_le_sum_of_subset_of_nonneg (erase_subset o univ) (fun i _ _ => hw i)
  rw [←mul_sum]
  exact mul_le_mul_of_nonneg_left (hsum.trans hW) hD

end
end UniformKServer.AllocationOutputs

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                 
section

                                                                               
                                                                            
namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def bumpB (σ v : ℝ) : ℝ := max 0 (min 1 (2-v/σ))
def bumpA (σ R v : ℝ) : ℝ :=
  if v ≤ R then min (v^2/σ^2) 1 else if v ≤ 2*R then 2-v/R else 0
def gate (R v : ℝ) : ℝ := max 0 (min 1 (v/(10*R)-1))
def feasible (r σ R : ℝ) (z : X → ℝ) : Prop :=
  (∀ s, 0 ≤ z s) ∧
  (∀ p, (∑ s, max (z s-gate R (dist s p/r)) 0) ≤ 1) ∧
  (∀ s s', s ≠ s' → 0 < z s → 0 < z s' → 5*σ*r ≤ dist s s')
def integrand (r σ R : ℝ) (g z : X → ℝ) (p : X) : ℝ :=
  (1+g p)*(1-∑ s, z s*bumpB σ (dist s p/r)) +
    256*∑ s, z s*(1+g s)*bumpA σ R (dist s p/r)
def objective (r σ R : ℝ) (μ g z : X → ℝ) : ℝ :=
  r*∑ p, μ p*integrand r σ R g z p
def value (r σ R : ℝ) (μ g : X → ℝ) : ℝ :=
  sInf (objective r σ R μ g '' {z : X → ℝ | feasible r σ R z})

theorem gate_nonneg (R v : ℝ) : 0 ≤ gate R v := le_max_left _ _

theorem zero_feasible (r σ R : ℝ) : feasible (X := X) r σ R (fun _ => 0) := by
  refine ⟨fun _ => le_rfl, ?_, ?_⟩
  · intro p
    have hg : ∀ s : X, max (0-gate R (dist s p/r)) 0 = 0 := by
      intro s
      exact max_eq_right (by linarith [gate_nonneg R (dist s p/r)])
    simp only [hg, Finset.sum_const_zero]
    norm_num
  · intro s s' hss hs
    linarith

theorem feasible_upper (r σ R : ℝ) (z : X → ℝ) (hz : feasible r σ R z) (s : X) :
    z s ≤ 1 := by
  have hs : max (z s-gate R (dist s s/r)) 0 ≤
      ∑ t, max (z t-gate R (dist t s/r)) 0 :=
    Finset.single_le_sum (f := fun t => max (z t-gate R (dist t s/r)) 0)
      (fun t ht => le_max_right _ _) (Finset.mem_univ s)
  have hg : max (z s-gate R (dist s s/r)) 0 = z s := by
    simp [gate, max_eq_left (hz.1 s)]
  rw [hg] at hs
  exact hs.trans (hz.2.1 s)

theorem feasible_closed_form (r σ R : ℝ) (z : X → ℝ) :
    feasible r σ R z ↔ (∀ s, 0 ≤ z s) ∧
      (∀ p, (∑ s, max (z s-gate R (dist s p/r)) 0) ≤ 1) ∧
      (∀ s s', s ≠ s' → dist s s' < 5*σ*r → z s*z s' = 0) := by
  constructor
  · rintro ⟨hn, hc, hs⟩
    refine ⟨hn, hc, ?_⟩
    intro s s' hne hdist
    rcases (hn s).eq_or_lt with hz | hp
    · rw [← hz]; ring
    rcases (hn s').eq_or_lt with hz | hp'
    · rw [← hz]; ring
    linarith [hs s s' hne hp hp']
  · rintro ⟨hn, hc, hs⟩
    refine ⟨hn, hc, ?_⟩
    intro s s' hne hp hp'
    by_contra h
    have he := hs s s' hne (lt_of_not_ge h)
    have hm := mul_pos hp hp'
    linarith

theorem feasible_isClosed (r σ R : ℝ) : IsClosed {z : X → ℝ | feasible r σ R z} := by
  simp only [feasible_closed_form, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  · apply IsClosed.inter
    · apply isClosed_iInter
      intro p
      apply isClosed_le _ continuous_const
      fun_prop
    · apply isClosed_iInter
      intro s
      apply isClosed_iInter
      intro s'
      apply isClosed_iInter
      intro hne
      apply isClosed_iInter
      intro hdist
      exact isClosed_eq ((continuous_apply s).mul (continuous_apply s')) continuous_const

theorem feasible_isCompact (r σ R : ℝ) : IsCompact {z : X → ℝ | feasible r σ R z} := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : X => Set.Icc (0:ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hc.of_isClosed_subset (feasible_isClosed r σ R)
  intro z hz s hs
  exact ⟨hz.1 s, feasible_upper r σ R z hz s⟩

theorem objective_continuous (r σ R : ℝ) (μ g : X → ℝ) :
    Continuous (objective r σ R μ g) := by
  unfold objective integrand
  fun_prop

theorem minimum_exists (r σ R : ℝ) (μ g : X → ℝ) :
    ∃ z, feasible r σ R z ∧ objective r σ R μ g z = value r σ R μ g ∧
      ∀ w, feasible r σ R w → objective r σ R μ g z ≤ objective r σ R μ g w := by
  obtain ⟨z, hz, hmin⟩ := (feasible_isCompact (X := X) r σ R).exists_isMinOn
    ⟨fun _ => 0, zero_feasible r σ R⟩ (objective_continuous r σ R μ g).continuousOn
  refine ⟨z, hz, ?_, hmin⟩
  have hleast : IsLeast (objective r σ R μ g '' {w | feasible r σ R w})
      (objective r σ R μ g z) := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmin hw
  exact hleast.csInf_eq.symm

theorem value_le (r σ R : ℝ) (μ g z : X → ℝ) (hz : feasible r σ R z) :
    value r σ R μ g ≤ objective r σ R μ g z := by
  obtain ⟨w, hw, he, hmin⟩ := minimum_exists r σ R μ g
  rw [← he]
  exact hmin z hz

theorem bumpB_bounds (σ v : ℝ) : bumpB σ v ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem bumpA_bounds (σ R v : ℝ) (hR : 0 < R) :
    bumpA σ R v ∈ Set.Icc (0:ℝ) 1 := by
  unfold bumpA
  split_ifs with hv hv'
  · exact ⟨le_min (div_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num), min_le_right _ _⟩
  · have hdiv₁ : 1 ≤ v/R := (le_div_iff₀ hR).mpr (by linarith)
    have hdiv₂ : v/R ≤ 2 := (div_le_iff₀ hR).mpr (by linarith)
    constructor <;> linarith
  · exact ⟨le_rfl, by norm_num⟩

theorem gate_eq_zero (R v : ℝ) (hR : 0 < R) (hv : v ≤ 10*R) : gate R v = 0 := by
  have hdiv : v/(10*R) ≤ 1 := (div_le_iff₀ (by positivity : 0 < 10*R)).mpr (by linarith)
  unfold gate
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem bumpB_zero (σ v : ℝ) (hσ : 0 < σ) (hv : 2*σ ≤ v) : bumpB σ v = 0 := by
  have hd : 2 ≤ v/σ := (le_div_iff₀ hσ).mpr hv
  unfold bumpB
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

theorem weighted_bumpB (σ R v z : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (hz : 0 ≤ z) :
    z*bumpB σ v ≤ max (z-gate R v) 0 := by
  by_cases hv : v ≤ 2*σ
  · have hg : gate R v = 0 := gate_eq_zero R v (by linarith) (by linarith)
    rw [hg, sub_zero, max_eq_left hz]
    nlinarith [mul_le_mul_of_nonneg_left (bumpB_bounds σ v).2 hz]
  · rw [bumpB_zero σ v hσ (by linarith), mul_zero]
    exact le_max_right _ _

theorem weighted_bumpB_sum (r σ R : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hR : 256 ≤ R) (z : X → ℝ) (hz : feasible r σ R z) (p : X) :
    (∑ s, z s*bumpB σ (dist s p/r)) ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun s _ => mul_nonneg (hz.1 s) (bumpB_bounds σ _).1
  · exact (Finset.sum_le_sum fun s _ => weighted_bumpB σ R _ _ hσ hσ1 hR (hz.1 s)).trans (hz.2.1 p)

theorem candidate_drift [DecidableEq X] (r σ R : ℝ) (hr : 0 < r)
    (μ ν g : X → ℝ) (hν : ∀ p, 0 ≤ ν p) (hν1 : ∑ p, ν p = 1) (x : X)
    (z : X → ℝ) (hz : feasible r σ R z)
    (hmin : objective r σ R μ g z = value r σ R μ g) :
    value r σ R (fun p => μ p-ν p+if p=x then 1 else 0) g - value r σ R μ g ≤
      r*∑ p, ν p*max (integrand r σ R g z x-integrand r σ R g z p) 0 := by
  have he : objective r σ R (fun p => μ p-ν p+if p=x then 1 else 0) g z -
      objective r σ R μ g z = r*∑ p, ν p*(integrand r σ R g z x-integrand r σ R g z p) := by
    unfold objective
    simp_rw [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_sub, Finset.sum_sub_distrib]
    have hd : (∑ p : X, (if p=x then (1:ℝ) else 0)*integrand r σ R g z p) =
        integrand r σ R g z x := by simp
    rw [hd, ← Finset.sum_mul, hν1]
    ring
  calc
    _ ≤ objective r σ R (fun p => μ p-ν p+if p=x then 1 else 0) g z -
        objective r σ R μ g z := by
      rw [hmin]
      exact sub_le_sub_right (value_le r σ R _ g z hz) _
    _ = _ := he
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hr.le
      exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hν p)


/-! Local optimality construction. -/

theorem feasible_mono (r σ R : ℝ) (z w : X → ℝ) (hz : feasible r σ R z)
    (hw : ∀ s, 0 ≤ w s) (hwz : ∀ s, w s ≤ z s) : feasible r σ R w := by
  refine ⟨hw, ?_, ?_⟩
  · intro p
    exact (Finset.sum_le_sum fun s _ => max_le_max (sub_le_sub_right (hwz s) _) le_rfl).trans (hz.2.1 p)
  · intro s s' hne hp hp'
    exact hz.2.2 s s' hne (hp.trans_le (hwz s)) (hp'.trans_le (hwz s'))

theorem erase_feasible [DecidableEq X] (r σ R : ℝ) (z : X → ℝ)
    (hz : feasible r σ R z) (s : X) : feasible r σ R (Function.update z s 0) := by
  apply feasible_mono r σ R z _ hz
  · intro p
    by_cases h : p=s <;> simp [h, hz.1 p]
  · intro p
    by_cases h : p=s <;> simp [h, hz.1 s]

def coefficient (r σ R : ℝ) (g : X → ℝ) (s p : X) : ℝ :=
  256*(1+g s)*bumpA σ R (dist s p/r) - (1+g p)*bumpB σ (dist s p/r)

omit [MetricSpace X] in
theorem sum_erase_weight [DecidableEq X] (z f : X → ℝ) (s : X) :
    (∑ t, z t*f t) - (∑ t, Function.update z s 0 t*f t) = z s*f s := by
  have he : ∀ t, z t*f t-Function.update z s 0 t*f t = if t=s then z s*f s else 0 := by
    intro t
    by_cases h : t=s <;> simp [h]
  rw [← Finset.sum_sub_distrib]
  simp_rw [he]
  simp

theorem integrand_erase [DecidableEq X] (r σ R : ℝ) (g z : X → ℝ) (s p : X) :
    integrand r σ R g z p - integrand r σ R g (Function.update z s 0) p =
      z s*coefficient r σ R g s p := by
  have hb := sum_erase_weight z (fun t => bumpB σ (dist t p/r)) s
  have ha := sum_erase_weight z (fun t => (1+g t)*bumpA σ R (dist t p/r)) s
  simp only [← mul_assoc] at ha
  have hb' := congrArg (fun u : ℝ => (1+g p)*u) hb
  unfold integrand coefficient
  nlinarith only [hb', ha]


end
end UniformKServer.PilotCompact
end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
theorem objective_erase [DecidableEq X] (r σ R : ℝ) (μ g z : X → ℝ) (s : X) :
    objective r σ R μ g z - objective r σ R μ g (Function.update z s 0) =
      r*z s*∑ p, μ p*coefficient r σ R g s p := by
  unfold objective
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, integrand_erase]
  have he : (∑ p, μ p*(z s*coefficient r σ R g s p)) =
      z s*∑ p, μ p*coefficient r σ R g s p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [he]
  ring

omit [Fintype X] in
theorem normalized_triangle (r : ℝ) (hr : 0 < r) (s x p : X) :
    dist s p/r ≤ dist s x/r + dist x p/r := by
  rw [← add_div]
  exact div_le_div_of_nonneg_right (dist_triangle s x p) hr.le

omit [Fintype X] in
theorem bumpB_outer_bound (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (x s p : X) (hfar : dist s x/r ≤ R/2) :
    bumpB σ (dist s p/r) ≤ if dist x p ≤ (100*R)*r then 1 else 0 := by
  split_ifs with hp
  · exact (bumpB_bounds _ _).2
  · have ht := normalized_triangle r hr x s p
    rw [dist_comm x s] at ht
    have hv : 100*R < dist x p/r := (lt_div_iff₀ hr).mpr (lt_of_not_ge hp)
    have hu : 2*σ ≤ dist s p/r := by linarith
    rw [bumpB_zero σ _ hσ hu]

def innerMoment (r γ : ℝ) (μ : X → ℝ) (x : X) : ℝ :=
  ∑ p, if dist x p ≤ γ*r then μ p*(dist x p/r) else 0

def insertUnit [DecidableEq X] (r R : ℝ) (z : X → ℝ) (x s : X) : ℝ :=
  if s=x then 1 else if dist s x ≤ (50*R)*r then 0 else z s


theorem gate_one (R v : ℝ) (hR : 0 < R) (hv : 20*R ≤ v) : gate R v = 1 := by
  have hd : 2 ≤ v/(10*R) := (le_div_iff₀ (by positivity : 0<10*R)).mpr (by linarith)
  unfold gate
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

omit [Fintype X] in
theorem insertUnit_at [DecidableEq X] (r R : ℝ) (z : X → ℝ) (x : X) :
    insertUnit r R z x x = 1 := by simp [insertUnit]

omit [Fintype X] in
theorem insertUnit_nonneg [DecidableEq X] (r R : ℝ) (z : X → ℝ)
    (hz : ∀ s, 0 ≤ z s) (x s : X) : 0 ≤ insertUnit r R z x s := by
  unfold insertUnit
  split_ifs <;> first | positivity | exact hz s

theorem bumpB_one (σ v : ℝ) (hσ : 0 < σ) (hv : v ≤ σ) : bumpB σ v = 1 := by
  have hd : v/σ ≤ 1 := (div_le_iff₀ hσ).mpr (by simpa using hv)
  unfold bumpB
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

def nearWeight (r σ : ℝ) (z : X → ℝ) (x : X) : ℝ :=
  ∑ s, if dist s x/r < σ/4 then z s else 0

theorem inner_bump_sum (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (z : X → ℝ) (x p : X) (hp : dist x p ≤ γ*r)
    (hmid : ∀ s, σ/4 ≤ dist s x/r → dist s x/r ≤ R/2 → z s = 0) :
    (∑ s, z s*bumpB σ (dist s p/r)) = nearWeight r σ z x := by
  unfold nearWeight
  apply Finset.sum_congr rfl
  intro s hs
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hp
  split_ifs with hn
  · have ht := normalized_triangle r hr s x p
    rw [bumpB_one σ _ hσ (by linarith), mul_one]
  · by_cases hf : dist s x/r ≤ R/2
    · rw [hmid s (le_of_not_gt hn) hf, zero_mul]
    · have ht := normalized_triangle r hr s p x
      rw [dist_comm p x] at ht
      rw [bumpB_zero σ _ hσ (by linarith), mul_zero]

theorem nearWeight_bounds (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγ : 0 < γ) (hγσ : γ ≤ σ/64)
    (z : X → ℝ) (hz : feasible r σ R z) (x : X)
    (hmid : ∀ s, σ/4 ≤ dist s x/r → dist s x/r ≤ R/2 → z s = 0) :
    nearWeight r σ z x ∈ Set.Icc (0:ℝ) 1 := by
  have he := inner_bump_sum r σ R γ hr hσ hσ1 hR hγσ z x x
    (by simp <;> positivity) hmid
  rw [← he]
  exact weighted_bumpB_sum r σ R hσ hσ1 hR z hz x


end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem near_positive_unique (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (z : X → ℝ) (hz : feasible r σ R z) (x s s' : X)
    (hs : 0 < z s) (hs' : 0 < z s') (hn : dist s x/r < σ/4)
    (hn' : dist s' x/r < σ/4) : s'=s := by
  by_contra hne
  have hsep : 5*σ ≤ dist s s'/r := (le_div_iff₀ hr).mpr (by
    convert hz.2.2 s s' (Ne.symm hne) hs hs' using 1)
  have ht := normalized_triangle r hr s x s'
  rw [dist_comm x s'] at ht
  linarith

/-! Scalar slope proofs for exact compact pilot. -/

theorem clamp_abs (u v : ℝ) :
    |max 0 (min 1 u)-max 0 (min 1 v)| ≤ |u-v| := by
  have hmin := abs_min_sub_min_le_max (1:ℝ) u 1 v
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min 1 u) 0 (min 1 v)
  simp only [sub_self, abs_zero] at hmin hmax
  rw [max_eq_right (abs_nonneg (u-v))] at hmin
  rw [max_eq_right (abs_nonneg (min 1 u-min 1 v))] at hmax
  exact hmax.trans hmin

theorem bumpB_lipschitz (σ u v : ℝ) (hσ : 0 < σ) :
    |bumpB σ u-bumpB σ v| ≤ |u-v|/σ := by
  have h := clamp_abs (2-u/σ) (2-v/σ)
  unfold bumpB
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  have he : (2-u/σ)-(2-v/σ) = -(u-v)/σ := by ring
  rw [he, abs_div, abs_neg, abs_of_pos hσ]

theorem gate_lipschitz (R u v : ℝ) (hR : 0 < R) :
    |gate R u-gate R v| ≤ |u-v|/(10*R) := by
  have h := clamp_abs (u/(10*R)-1) (v/(10*R)-1)
  unfold gate
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  have he : (u/(10*R)-1)-(v/(10*R)-1) = (u-v)/(10*R) := by ring
  rw [he, abs_div, abs_of_pos (by positivity : 0<10*R)]

theorem capped_square_order (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    0 ≤ min (v^2) 1-min (u^2) 1 ∧ min (v^2) 1-min (u^2) 1 ≤ 2*(v-u) := by
  have hv : 0 ≤ v := hu.trans huv
  have hsq : u^2 ≤ v^2 := by nlinarith
  refine ⟨sub_nonneg.mpr (min_le_min_right 1 hsq), ?_⟩
  by_cases hv1 : v ≤ 1
  · have hu1 : u ≤ 1 := huv.trans hv1
    rw [min_eq_left (by nlinarith : v^2 ≤ 1), min_eq_left (by nlinarith : u^2 ≤ 1)]
    nlinarith [mul_nonneg (show 0≤v-u by linarith) (show 0≤2-v-u by linarith)]
  · rw [min_eq_right (by nlinarith : 1 ≤ v^2)]
    by_cases hu1 : u ≤ 1
    · rw [min_eq_left (by nlinarith : u^2 ≤ 1)]
      nlinarith [sq_nonneg (1-u)]
    · rw [min_eq_right (by nlinarith : 1 ≤ u^2)]
      linarith

theorem capped_square_abs (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |min (u^2) 1-min (v^2) 1| ≤ 2*|u-v| := by
  rcases le_total u v with huv | hvu
  · have hh := capped_square_order u v hu huv
    rw [abs_sub_comm, abs_of_nonneg hh.1, abs_of_nonpos (sub_nonpos.mpr huv)]
    linarith [hh.2]
  · have hh := capped_square_order v u hv hvu
    rw [abs_of_nonneg hh.1, abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hh.2

theorem quadratic_abs (σ u v : ℝ) (hσ : 0 < σ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |min (u^2/σ^2) 1-min (v^2/σ^2) 1| ≤ (2/σ)*|u-v| := by
  have hh := capped_square_abs (u/σ) (v/σ) (div_nonneg hu hσ.le) (div_nonneg hv hσ.le)
  rw [div_pow, div_pow, ← sub_div, abs_div, abs_of_pos hσ] at hh
  calc
    _ ≤ 2*(|u-v|/σ) := hh
    _ = _ := by ring

theorem tail_abs (R u v : ℝ) (hR : 0 < R) :
    |max (2-u/R) 0-max (2-v/R) 0| ≤ (1/R)*|u-v| := by
  have hh := abs_max_sub_max_le_abs (2-u/R) (2-v/R) 0
  have he : (2-u/R)-(2-v/R) = -(u-v)/R := by ring
  rw [he, abs_div, abs_neg, abs_of_pos hR] at hh
  calc
    _ ≤ |u-v|/R := hh
    _ = _ := by ring


def relocate [DecidableEq X] (r R : ℝ) (z : X → ℝ) (s x t : X) : ℝ :=
  if t=x then z s else if t=s then 0 else
    if dist t x ≤ (50*R)*r then max (z t-(dist s x/r)/(10*R)) 0 else z t


theorem trim_contribution (z G q : ℝ) (hG : 0 ≤ G) (hq : 0 ≤ q) :
    max (max (z-q) 0-G) 0 = max (max (z-G) 0-q) 0 := by
  by_cases hzq : q ≤ z
  · rw [max_eq_left (sub_nonneg.mpr hzq)]
    by_cases hzG : G ≤ z
    · rw [max_eq_left (sub_nonneg.mpr hzG)]
      congr 1
      ring
    · rw [max_eq_right (by linarith : z-G≤0), max_eq_right (by linarith : 0-q≤0)]
      exact max_eq_right (by linarith)
  · rw [max_eq_right (by linarith : z-q≤0), max_eq_right (by linarith : 0-G≤0)]
    symm
    apply max_eq_right
    have hh : max (z-G) 0 ≤ q := max_le (by linarith) hq
    linarith

theorem trim_add_le (a b q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    max (a-q) 0+max (b-q) 0 ≤ max (a+b-q) 0 := by
  by_cases ha' : q ≤ a <;> by_cases hb' : q ≤ b
  · rw [max_eq_left (by linarith : 0≤a-q), max_eq_left (by linarith : 0≤b-q),
      max_eq_left (by linarith : 0≤a+b-q)]
    linarith
  · rw [max_eq_left (by linarith : 0≤a-q), max_eq_right (by linarith : b-q≤0)]
    exact (by linarith : a-q+0 ≤ a+b-q).trans (le_max_left _ _)
  · rw [max_eq_right (by linarith : a-q≤0), max_eq_left (by linarith : 0≤b-q)]
    exact (by linarith : 0+(b-q) ≤ a+b-q).trans (le_max_left _ _)
  · rw [max_eq_right (by linarith : a-q≤0), max_eq_right (by linarith : b-q≤0)]
    simp


end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

/-- Capacity controls all radii whose support meets either of two nearby points.
This is a weighted finite-sum statement, not an assumed HST drift estimate. -/
theorem weighted_radial_lipschitz (r R a C B : ℝ) (hr : 0 < r) (hR : 256 ≤ R)
    (ha : a ≤ 2*R) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (f : ℝ → ℝ) (hfzero : ∀ u, a ≤ u → f u = 0)
    (hfLip : ∀ u v, 0 ≤ u → 0 ≤ v → |f u-f v| ≤ C*|u-v|)
    (z θ : X → ℝ) (hz : ∀ s, 0 ≤ z s) (hθ : ∀ s, θ s ∈ Set.Icc (0:ℝ) B)
    (x y : X) (hcap : (∑ s, max (z s-gate R (dist s x/r)) 0) ≤ 1)
    (hxy : dist x y/r ≤ 1) :
    |(∑ s, z s*θ s*f (dist s x/r))-(∑ s, z s*θ s*f (dist s y/r))| ≤
      B*C*(dist x y/r) := by
  have hd : 0 ≤ dist x y/r := div_nonneg dist_nonneg hr.le
  have hs : ∀ s, |z s*θ s*(f (dist s x/r)-f (dist s y/r))| ≤
      max (z s-gate R (dist s x/r)) 0*(B*C*(dist x y/r)) := by
    intro s
    by_cases hx : dist s x/r ≤ 2*R+1
    · have hg : gate R (dist s x/r) = 0 := gate_eq_zero R _ (by linarith) (by linarith)
      rw [hg, sub_zero, max_eq_left (hz s), abs_mul, abs_mul,
        abs_of_nonneg (hz s), abs_of_nonneg (hθ s).1]
      have hdist : |dist s x/r-dist s y/r| ≤ dist x y/r := by
        rw [←sub_div, abs_div, abs_of_pos hr]
        exact div_le_div_of_nonneg_right (by simpa only [dist_comm] using abs_dist_sub_le x y s) hr.le
      have hf := (hfLip _ _ (div_nonneg dist_nonneg hr.le)
        (div_nonneg dist_nonneg hr.le)).trans (mul_le_mul_of_nonneg_left hdist hC)
      calc
        _ ≤ z s*θ s*(C*(dist x y/r)) :=
          mul_le_mul_of_nonneg_left hf (mul_nonneg (hz s) (hθ s).1)
        _ ≤ z s*B*(C*(dist x y/r)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hθ s).2 (hz s))
            (mul_nonneg hC hd)
        _ = _ := by ring
    · have htri := normalized_triangle r hr s y x
      rw [dist_comm y x] at htri
      have hfx := hfzero (dist s x/r) (by linarith)
      have hfy := hfzero (dist s y/r) (by linarith)
      rw [hfx, hfy, sub_self, mul_zero, abs_zero]
      exact mul_nonneg (le_max_right _ _) (by positivity)
  calc
    _ = |∑ s, z s*θ s*(f (dist s x/r)-f (dist s y/r))| := by
      rw [←Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ ∑ s, |z s*θ s*(f (dist s x/r)-f (dist s y/r))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, max (z s-gate R (dist s x/r)) 0*(B*C*(dist x y/r)) :=
      Finset.sum_le_sum fun s _ => hs s
    _ = (∑ s, max (z s-gate R (dist s x/r)) 0)*(B*C*(dist x y/r)) :=
      (Finset.sum_mul ..).symm
    _ ≤ 1*(B*C*(dist x y/r)) := mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := one_mul _


/-- The geometric bound is valid for an arbitrary finite selection of scales. -/
theorem radius_sum_le (r τ : ℝ) (hr : 0 ≤ r) (hτ : 2 ≤ τ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), r*τ^j) ≤ 2*(r*τ^n) := by
  induction n with
  | zero => simp <;> linarith
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hn : 0 ≤ r*τ^n := mul_nonneg hr (pow_nonneg (by linarith) n)
    have hmul := mul_le_mul_of_nonneg_left hτ hn
    nlinarith

theorem radius_subsum_le (r τ b : ℝ) (hr : 0 ≤ r) (hτ : 2 ≤ τ)
    (hb : 0 ≤ b) (s : Finset ℕ) (hs : ∀ j ∈ s, r*τ^j ≤ b) :
    (∑ j ∈ s, r*τ^j) ≤ 2*b := by
  classical
  by_cases hn : s.Nonempty
  · let m := s.max' hn
    have hm : m ∈ s := Finset.max'_mem s hn
    have hsub : s ⊆ Finset.range (m+1) := by
      intro j hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' s j hj))
    calc
      _ ≤ ∑ j ∈ Finset.range (m+1), r*τ^j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
      _ ≤ 2*(r*τ^m) := radius_sum_le r τ hr hτ m
      _ ≤ 2*b := by linarith [hs m hm]
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty]
    positivity

theorem drift_nonneg_bound [DecidableEq X] (r σ R : ℝ) (hr : 0 < r)
    (μ ν g z : X → ℝ) (hν : ∀ y, 0 ≤ ν y) (hν1 : ∑ y, ν y = 1)
    (x : X) (hz : feasible r σ R z) (hmin : objective r σ R μ g z = value r σ R μ g) :
    max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g-value r σ R μ g) 0 ≤
      r*∑ y, ν y*max (integrand r σ R g z x-integrand r σ R g z y) 0 := by
  exact max_le (candidate_drift r σ R hr μ ν g hν hν1 x z hz hmin)
    (mul_nonneg hr.le (Finset.sum_nonneg fun y _ => mul_nonneg (hν y) (le_max_right _ _)))


end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]
omit [MetricSpace X] in
theorem sum_trim_le (a : X → ℝ) (ha : ∀ t, 0 ≤ a t) (q : ℝ) (hq : 0 ≤ q) :
    (∑ t, max (a t-q) 0) ≤ max ((∑ t, a t)-q) 0 := by
  classical
  have hall : ∀ S : Finset X, (∑ t ∈ S, max (a t-q) 0) ≤ max ((∑ t ∈ S, a t)-q) 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [max_eq_right (neg_nonpos.mpr hq)]
    | @insert t S ht ih =>
      rw [Finset.sum_insert ht, Finset.sum_insert ht]
      exact (add_le_add_right ih _).trans (trim_add_le _ _ q (ha t)
        (Finset.sum_nonneg fun i hi => ha i) hq)
  exact hall Finset.univ

omit [MetricSpace X] in
theorem capacity_patch (a b : X → ℝ) (A A' q : ℝ)
    (ha : ∀ t, 0 ≤ a t) (hq : 0 ≤ q) (hcap : A+∑ t, a t ≤ 1)
    (hA' : A' ≤ 1) (hLip : A' ≤ A+q)
    (hmono : ∀ t, b t ≤ a t) (htrim : A < A' → ∀ t, b t ≤ max (a t-q) 0) :
    A'+∑ t, b t ≤ 1 := by
  by_cases hA : A' ≤ A
  · exact (add_le_add hA (Finset.sum_le_sum fun t _ => hmono t)).trans hcap
  · have hb : (∑ t, b t) ≤ max ((∑ t, a t)-q) 0 :=
      (Finset.sum_le_sum fun t _ => htrim (lt_of_not_ge hA) t).trans (sum_trim_le a ha q hq)
    apply le_trans (add_le_add_right hb _)
    by_cases hB : q ≤ ∑ t, a t
    · rw [max_eq_left (sub_nonneg.mpr hB)]
      linarith
    · rw [max_eq_right (by linarith : (∑ t, a t)-q≤0), add_zero]
      exact hA'

omit [MetricSpace X] in
theorem sum_split_pair [DecidableEq X] (f : X → ℝ) (s x : X) (hsx : s ≠ x) :
    (∑ t, f t) = f s+f x+∑ t, if t=s ∨ t=x then 0 else f t := by
  have he : ∀ t, f t = (if t=s then f s else 0)+(if t=x then f x else 0)+
      (if t=s ∨ t=x then 0 else f t) := by
    intro t
    by_cases hs : t=s <;> by_cases hx : t=x <;> simp_all
  calc
    _ = ∑ t, ((if t=s then f s else 0)+(if t=x then f x else 0)+
        (if t=s ∨ t=x then 0 else f t)) := Finset.sum_congr rfl (fun t _ => he t)
    _ = _ := by simp only [Finset.sum_add_distrib] <;> simp

theorem gate_positive_near (R v z : ℝ) (hR : 0 < R) (hz : z ≤ 1)
    (hp : 0 < max (z-gate R v) 0) : v < 20*R := by
  by_contra h
  rw [gate_one R v hR (le_of_not_gt h), max_eq_right (sub_nonpos.mpr hz)] at hp
  linarith

theorem zero_at_relocation_target (r σ R : ℝ) (_hr : 0 < r) (hR : 256 ≤ R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x : X) (hsx : s ≠ x)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r) : z x = 0 := by
  rcases (hz.1 x).eq_or_lt with he | hp
  · exact he.symm
  · have hh := hother x (Ne.symm hsx) hp
    simp only [dist_self, zero_div] at hh
    linarith

omit [Fintype X] in
theorem relocate_at_target [DecidableEq X] (r R : ℝ) (z : X → ℝ) (s x : X) :
    relocate r R z s x x = z s := by simp [relocate]

omit [Fintype X] in
theorem relocate_at_site [DecidableEq X] (r R : ℝ) (z : X → ℝ) (s x : X) (hsx : s ≠ x) :
    relocate r R z s x s = 0 := by simp [relocate, hsx]

omit [Fintype X] in
theorem relocate_nonneg [DecidableEq X] (r R : ℝ) (z : X → ℝ) (hz : ∀ t, 0 ≤ z t)
    (s x t : X) : 0 ≤ relocate r R z s x t := by
  unfold relocate
  split_ifs <;> first | exact hz _ | exact le_max_right _ _ | rfl

theorem integrand_affine (r σ R : ℝ) (g z : X → ℝ) (p : X) :
    integrand r σ R g z p = 1+g p+∑ t, z t*coefficient r σ R g t p := by
  unfold integrand coefficient
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  have ha : (∑ t, z t*(256*(1+g t)*bumpA σ R (dist t p/r))) =
      ∑ t, 256*(z t*(1+g t)*bumpA σ R (dist t p/r)) := by
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hb : (∑ t, z t*((1+g p)*bumpB σ (dist t p/r))) =
      ∑ t, (1+g p)*(z t*bumpB σ (dist t p/r)) := by
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [ha, hb]
  ring

theorem integrand_relocate [DecidableEq X] (r σ R : ℝ) (g z : X → ℝ) (s x p : X)
    (hsx : s ≠ x) (hzx : z x=0) :
    integrand r σ R g (relocate r R z s x) p-integrand r σ R g z p =
      z s*(coefficient r σ R g x p-coefficient r σ R g s p) +
      ∑ t, if t=s ∨ t=x then 0 else
        (relocate r R z s x t-z t)*coefficient r σ R g t p := by
  rw [integrand_affine, integrand_affine]
  have he : (∑ t, relocate r R z s x t*coefficient r σ R g t p) -
      (∑ t, z t*coefficient r σ R g t p) =
      ∑ t, (relocate r R z s x t-z t)*coefficient r σ R g t p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [show (1+g p+∑ t, relocate r R z s x t*coefficient r σ R g t p)-
        (1+g p+∑ t, z t*coefficient r σ R g t p) =
        (∑ t, relocate r R z s x t*coefficient r σ R g t p)-
        (∑ t, z t*coefficient r σ R g t p) by ring, he]
  rw [sum_split_pair _ s x hsx, relocate_at_site r R z s x hsx, relocate_at_target, hzx]
  ring

theorem positive_bump_unique (r σ R : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (z : X → ℝ) (hz : feasible r σ R z) (p u v : X)
    (hu : 0 < z u*bumpB σ (dist u p/r)) (hv : 0 < z v*bumpB σ (dist v p/r)) : u=v := by
  have hup := (mul_pos_iff.mp hu).resolve_right (fun h => (not_lt_of_ge (hz.1 u)) h.1)
  have hvp := (mul_pos_iff.mp hv).resolve_right (fun h => (not_lt_of_ge (hz.1 v)) h.1)
  have hdist : ∀ t, 0 < bumpB σ (dist t p/r) → dist t p/r < 2*σ := by
    intro t ht
    by_contra h
    rw [bumpB_zero σ _ hσ (le_of_not_gt h)] at ht
    linarith
  by_contra hne
  have hsep : 5*σ ≤ dist u v/r := (le_div_iff₀ hr).mpr (hz.2.2 u v hne hup.1 hvp.1)
  have htri := normalized_triangle r hr u p v
  rw [dist_comm p v] at htri
  linarith [hdist u hup.2, hdist v hvp.2]

omit [Fintype X] in
theorem normalized_dist_difference (r : ℝ) (hr : 0 < r) (s x p : X) :
    |dist s p/r-dist x p/r| ≤ dist s x/r := by
  rw [← sub_div, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (abs_dist_sub_le s x p) hr.le


end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotRelocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem quadratic_gain (gs gx u v w L : ℝ)
    (hgs : gs ∈ Set.Icc (0:ℝ) 1) (hLip : gx-gs ≤ L*w)
    (_hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (htri : w ≤ u+v) (htri' : v ≤ u+w) (hLv : L*v ≤ 1) :
    w^2-5*w*v ≤ (1+gs)*u^2-(1+gx)*v^2 := by
  have hsq : (w-v)^2 ≤ u^2 := by
    have hh := mul_nonneg (show 0≤u-w+v by linarith) (show 0≤u+w-v by linarith)
    nlinarith only [hh]
  have hh1 := mul_nonneg (show 0≤1+gs by linarith [hgs.1]) (sub_nonneg.mpr hsq)
  have hh2 := mul_nonneg (show 0≤L*w-(gx-gs) by linarith) (sq_nonneg v)
  have hh3 := mul_nonneg hgs.1 (sq_nonneg w)
  have hh4 := mul_nonneg (show 0≤1-gs by linarith [hgs.2]) (mul_nonneg hw hv)
  have hh5 := mul_nonneg (show 0≤1-L*v by linarith) (mul_nonneg hw hv)
  nlinarith only [hh1,hh2,hh3,hh4,hh5]

theorem other_inner_zero (r σ R γ : ℝ) (hr : 0 < r) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hR : 256 ≤ R) (hγσ : γ ≤ σ/64)
    (z : X → ℝ) (_hz : feasible r σ R z) (s x p t : X)
    (hother : ∀ t, t ≠ s → 0 < z t → R/2 < dist t x/r)
    (hinner : dist x p ≤ γ*r) (hts : t ≠ s) (htpos : 0 < z t) :
    bumpB σ (dist t p/r) = 0 := by
  have hv : dist x p/r ≤ γ := (div_le_iff₀ hr).mpr hinner
  have ht := hother t hts htpos
  have htri := normalized_triangle r hr t p x
  rw [dist_comm p x] at htri
  apply bumpB_zero σ _ hσ
  linarith

theorem relocation_constant_bound (σ R L z : ℝ) (hσ : 0<σ) (hσ1 : σ≤1)
    (hR : 256≤R) (hL : 0≤L) (hz : (1:ℝ)/2≤z) :
    z*(1026/σ+256*L)+2/(10*R) ≤ (256*z/σ^2)*(5+L) := by
  have hσsq : 0<σ^2 := sq_pos_of_pos hσ
  have hz0 : 0≤z := by linarith
  have hRpos : 0<10*R := by linarith
  have hσsq1 : σ^2≤1 := by nlinarith
  have hLsq : L*σ^2≤L := by nlinarith [mul_nonneg hL (sub_nonneg.mpr hσsq1)]
  have hlin : z*(1026*σ+256*L*σ^2) ≤ z*(1026+256*L) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hz0
  have hrat : 2/(10*R)≤1 := (div_le_iff₀ hRpos).mpr (by linarith)
  have hrat0 : 0≤2/(10*R) := by positivity
  have hrat' : (2/(10*R))*σ^2≤1 :=
    (mul_le_mul_of_nonneg_left hσsq1 hrat0).trans (by simpa using hrat)
  have he : (z*(1026/σ+256*L)+2/(10*R))*σ^2 =
      z*(1026*σ+256*L*σ^2)+(2/(10*R))*σ^2 := by
    field_simp
  apply (mul_le_mul_iff_left₀ hσsq).mp
  rw [he]
  have he' : (256*z/σ^2)*(5+L)*σ^2 = 256*z*(5+L) := by field_simp
  rw [he']
  nlinarith only [hlin,hrat',hz]



end
end UniformKServer.PilotCompact

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

omit [MetricSpace X] in
theorem sum_split_single [DecidableEq X] (f : X → ℝ) (s : X) :
    (∑ t, f t) = f s+∑ t, if t=s then 0 else f t := by
  classical
  have he : ∀ t, f t = (if t=s then f s else 0)+(if t=s then 0 else f t) := by
    intro t
    split_ifs with ht <;> simp_all
  calc
    _ = ∑ t, ((if t=s then f s else 0)+(if t=s then 0 else f t)) :=
      Finset.sum_congr rfl (fun t _ => he t)
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem local_bump_sum (r σ R : ℝ) (hr : 0 < r) (hσ : 0<σ) (hσ1 : σ≤1) (hR : 256≤R)
    (z : X → ℝ) (hz : feasible r σ R z) (s x p : X) (hnear : dist s x/r < σ/4)
    (hother : ∀ t, t≠s → 0<z t → R/2<dist t x/r) (hp : dist x p/r < σ/8) :
    (∑ t, z t*bumpB σ (dist t p/r)) = z s := by
  classical
  rw [Finset.sum_eq_single s]
  · have hh := normalized_triangle r hr s x p
    rw [bumpB_one σ _ hσ (by linarith),mul_one]
  · intro t ht hts
    rcases (hz.1 t).eq_or_lt with he | htpos
    · rw [←he,zero_mul]
    · have hfar := hother t hts htpos
      have hh := normalized_triangle r hr t p x
      rw [dist_comm p x] at hh
      rw [bumpB_zero σ _ hσ (by linarith),mul_zero]
  · simp

theorem square_difference (u w v : ℝ) (hu : 0≤u) (hw : 0≤w) (hv : 0≤v)
    (hd : w-u≤v) : w^2-u^2≤2*w*v := by
  by_cases hup : u≤w
  · have h1 := mul_nonneg (show 0≤w+u by linarith) (show 0≤v-(w-u) by linarith)
    have h2 := mul_nonneg (show 0≤w-u by linarith) hv
    nlinarith only [h1,h2]
  · nlinarith [mul_nonneg hw hv]

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotScales
noncomputable section

theorem scale_logarithms (A B : ℕ → ℝ) (N p : ℕ) (c K : ℝ)
    (hc : 0 < c) (hcK : c ≤ K)
    (hA : ∀ j < N, c ≤ A j)
    (hB : ∀ j < N, A j ≤ B j)
    (hshift : ∀ j < N, B j ≤ if j < p then K else A (j-p)) :
    ∑ j ∈ Finset.range N, Real.log (B j / A j) ≤
      (p : ℝ) * Real.log (K/c) := by
  have hK : 0 < K := lt_of_lt_of_le hc hcK
  have hlog : 0 ≤ Real.log K - Real.log c := by
    linarith [Real.log_le_log hc hcK]
  rw [Real.log_div hK.ne' hc.ne']
  have hpt : ∀ j < N, Real.log (B j/A j) ≤
      (if j < p then Real.log K else Real.log (A (j-p))) - Real.log (A j) := by
    intro j hj
    have ha : 0 < A j := lt_of_lt_of_le hc (hA j hj)
    have hb : 0 < B j := lt_of_lt_of_le ha (hB j hj)
    rw [Real.log_div hb.ne' ha.ne']
    apply sub_le_sub_right
    have hs := Real.log_le_log hb (hshift j hj)
    split_ifs at hs ⊢ <;> exact hs
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ((if j < p then Real.log K else Real.log (A (j-p))) - Real.log (A j)) :=
      Finset.sum_le_sum fun j hj => hpt j (Finset.mem_range.mp hj)
    _ ≤ (p : ℝ) * (Real.log K - Real.log c) := by
      rw [Finset.sum_sub_distrib]
      by_cases hpN : p ≤ N
      · have hs : (∑ j ∈ Finset.range N,
            if j < p then Real.log K else Real.log (A (j-p))) =
            (p : ℝ)*Real.log K + ∑ j ∈ Finset.range (N-p), Real.log (A j) := by
          conv_lhs => rw [show N = p+(N-p) by omega, Finset.sum_range_add]
          congr 1
          · calc
              _ = ∑ j ∈ Finset.range p, Real.log K := by
                apply Finset.sum_congr rfl
                intro j hj
                simp [Finset.mem_range.mp hj]
              _ = _ := by simp
          · apply Finset.sum_congr rfl
            intro j hj
            simp [show ¬p+j<p by omega]
        have ht : (∑ j ∈ Finset.range N, Real.log (A j)) =
            (∑ j ∈ Finset.range (N-p), Real.log (A j)) +
              ∑ j ∈ Finset.range p, Real.log (A (N-p+j)) := by
          conv_lhs => rw [show N = (N-p)+p by omega, Finset.sum_range_add]
        have hl : (p : ℝ)*Real.log c ≤
            ∑ j ∈ Finset.range p, Real.log (A (N-p+j)) := by
          calc
            _ = ∑ j ∈ Finset.range p, Real.log c := by simp
            _ ≤ _ := Finset.sum_le_sum fun j hj =>
              Real.log_le_log hc (hA _ (by have := Finset.mem_range.mp hj; omega))
        rw [hs, ht]
        nlinarith
      · have hs : (∑ j ∈ Finset.range N,
            if j < p then Real.log K else Real.log (A (j-p))) =
            (N : ℝ)*Real.log K := by
          calc
            _ = ∑ _j ∈ Finset.range N, Real.log K := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [show j<p by have := Finset.mem_range.mp hj; omega]
            _ = _ := by simp
        have hl : (N : ℝ)*Real.log c ≤
            ∑ j ∈ Finset.range N, Real.log (A j) := by
          calc
            _ = ∑ _j ∈ Finset.range N, Real.log c := by simp
            _ ≤ _ := Finset.sum_le_sum fun j hj =>
              Real.log_le_log hc (hA j (Finset.mem_range.mp hj))
        have hnp : (N : ℝ) ≤ p := by exact_mod_cast (show N ≤ p by omega)
        have hm := mul_le_mul_of_nonneg_right hnp hlog
        rw [hs]
        nlinarith

theorem capped_log (u : ℝ) (hu : 0 ≤ u) :
    min 1 u ≤ Real.log (1+u) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hl2).mpr
  by_cases hu1 : u ≤ 1
  · rw [min_eq_right hu1]
    have hh := strictConcaveOn_log_Ioi.concaveOn.2
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show 0 ≤ 1-u by linarith) hu (show (1-u)+u=1 by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1; ring)
  · rw [min_eq_left (by linarith : 1 ≤ u), one_mul]
    exact Real.log_le_log (by norm_num) (by linarith)

theorem shell_sum (A B : ℕ → ℝ) (N p : ℕ) (c K : ℝ)
    (hc : 0 < c) (hcK : c ≤ K)
    (hA : ∀ j < N, c ≤ A j)
    (hB : ∀ j < N, A j ≤ B j)
    (hshift : ∀ j < N, B j ≤ if j < p then K else A (j-p)) :
    ∑ j ∈ Finset.range N, min 1 ((B j-A j)/A j) ≤
      (p : ℝ) / Real.log 2 * Real.log (K/c) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ j ∈ Finset.range N, Real.log (B j/A j) / Real.log 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN := Finset.mem_range.mp hj
      have ha : 0 < A j := lt_of_lt_of_le hc (hA j hjN)
      have hpos : 0 ≤ (B j-A j)/A j := div_nonneg (sub_nonneg.mpr (hB j hjN)) ha.le
      have he : 1+(B j-A j)/A j = B j/A j := by field_simp <;> ring
      simpa only [he] using capped_log ((B j-A j)/A j) hpos
    _ = (∑ j ∈ Finset.range N, Real.log (B j/A j)) / Real.log 2 :=
      (Finset.sum_div ..).symm
    _ ≤ ((p : ℝ)*Real.log (K/c)) / Real.log 2 :=
      div_le_div_of_nonneg_right (scale_logarithms A B N p c K hc hcK hA hB hshift) hl2.le
    _ = _ := by ring

/-- Relative increments of positive monotone masses have only logarithmic total. -/
def increment (m : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then m 0 else m i-m (i-1)

theorem increment_nonneg (m : ℕ → ℝ) (hm : Monotone m) (h0 : 0 ≤ m 0) (i : ℕ) :
    0 ≤ increment m i := by
  unfold increment
  split_ifs with hi
  · exact h0
  · exact sub_nonneg.mpr (hm (by omega))

theorem relative_increment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (b-a)/b ≤ Real.log b - Real.log a := by
  have hh := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at hh
  have he : (b-a)/b = 1-a/b := by field_simp
  rw [he]
  linarith

theorem increment_sum (m : ℕ → ℝ) (hm : ∀ i, 0 < m i) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), increment m i/m i) ≤
      1+Real.log (m n/m 0) := by
  induction n with
  | zero => simp [increment, div_self (hm 0).ne']
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hstep := relative_increment (m n) (m (n+1)) (hm n) (hm (n+1))
      have he : increment m (n+1) = m (n+1)-m n := by simp [increment]
      rw [he]
      rw [Real.log_div (hm n).ne' (hm 0).ne'] at ih
      rw [Real.log_div (hm (n+1)).ne' (hm 0).ne']
      linarith

def convolution (m : ℕ → ℝ) (τ : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j+1), (1/τ)^(j-i)*increment m i

theorem geometric_bound (τ : ℝ) (hτ : 2 ≤ τ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (1/τ)^i ≤ 2 := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, (1/2 : ℝ)^i := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (by positivity : 0 ≤ 1/τ)
        (one_div_le_one_div_of_le (by norm_num) hτ) i
    _ ≤ 2 := sum_geometric_two_le n

theorem convolution_pointwise (m : ℕ → ℝ) (hm : Monotone m)
    (hpos : ∀ i, 0 < m i) (τ : ℝ) (hτ : 2 ≤ τ) (j : ℕ) :
    convolution m τ j/m j ≤ ∑ i ∈ Finset.range (j+1),
      (increment m i/m i)*(1/τ)^(j-i) := by
  have hτ0 : 0 < τ := by linarith
  unfold convolution
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  have hinc := increment_nonneg m hm (hpos 0).le i
  have hd := div_le_div_of_nonneg_left hinc (hpos i) (hm hij)
  have hp : 0 ≤ (1/τ)^(j-i) := by positivity
  have hh := mul_le_mul_of_nonneg_right hd hp
  convert hh using 1 <;> first | rfl | ring

theorem convolution_total (m : ℕ → ℝ) (hm : Monotone m)
    (hpos : ∀ i, 0 < m i) (τ : ℝ) (hτ : 2 ≤ τ) (N : ℕ) :
    (∑ j ∈ Finset.range N, convolution m τ j/m j) ≤
      2 * ∑ i ∈ Finset.range N, increment m i/m i := by
  have hinc : ∀ i, 0 ≤ increment m i := increment_nonneg m hm (hpos 0).le
  calc
    _ ≤ ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j+1),
          (increment m i/m i)*(1/τ)^(j-i) :=
      Finset.sum_le_sum fun j hj => convolution_pointwise m hm hpos τ hτ j
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range (N-i),
          (increment m i/m i)*(1/τ)^j :=
      Finset.sum_range_diag_flip N (fun i j => (increment m i/m i)*(1/τ)^j)
    _ ≤ ∑ i ∈ Finset.range N, 2*(increment m i/m i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      have hh := mul_le_mul_of_nonneg_left (geometric_bound τ hτ (N-i))
        (div_nonneg (hinc i) (hpos i).le)
      simpa only [mul_comm] using hh
    _ = _ := (Finset.mul_sum ..).symm

theorem convolution_succ (m : ℕ → ℝ) (τ : ℝ) (j : ℕ) :
    convolution m τ (j+1) = (1/τ)*convolution m τ j + increment m (j+1) := by
  unfold convolution
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : j+1-i = (j-i)+1 := by have := Finset.mem_range.mp hi; omega
  rw [he, pow_succ]
  ring

variable {ι : Type*} [Fintype ι]

def mass (μ d : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ x, if d x ≤ R then μ x else 0

def moment (μ d : ι → ℝ) (R : ℝ) : ℝ :=
  ∑ x, if d x ≤ R then μ x * d x else 0

def radius (r τ : ℝ) (j : ℕ) : ℝ := r * τ^j

theorem mass_nonneg (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) (R : ℝ) :
    0 ≤ mass μ d R := by
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact hμ x
  · exact le_rfl

theorem mass_mono (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) : Monotone (mass μ d) := by
  intro R S hRS
  unfold mass
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with hR hS hS
  · rfl
  · exact False.elim (hS (hR.trans hRS))
  · exact hμ x
  · rfl

theorem moment_bound (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) (R : ℝ) :
    moment μ d R ≤ R*mass μ d R := by
  unfold moment mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  split_ifs with ht
  · nlinarith [mul_le_mul_of_nonneg_left ht (hμ x)]
  · simp

theorem moment_shell (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (R S : ℝ) (hRS : R ≤ S) :
    moment μ d S ≤ moment μ d R + S*(mass μ d S-mass μ d R) := by
  unfold moment mass
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hR : d x ≤ R
  · have hS := hR.trans hRS
    simp [hR, hS]
  · by_cases hS : d x ≤ S
    · simp only [hR, hS, ↓reduceIte, zero_add, sub_zero]
      nlinarith [mul_le_mul_of_nonneg_left hS (hμ x)]
    · simp [hR, hS]

theorem radius_pos (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) (j : ℕ) :
    0 < radius r τ j := by unfold radius; positivity

theorem radius_mono (r τ : ℝ) (hr : 0 ≤ r) (hτ : 1 ≤ τ) : Monotone (radius r τ) := by
  apply monotone_nat_of_le_succ
  intro j
  unfold radius
  rw [pow_succ]
  have hp : 0 ≤ τ^j := pow_nonneg (by linarith) j
  have hb := mul_nonneg hr hp
  nlinarith

theorem moment_convolution (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (r τ γ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ) (hγ : 0 ≤ γ) (j : ℕ) :
    moment μ d (γ*radius r τ j) ≤
      γ*radius r τ j*convolution (fun i => mass μ d (γ*radius r τ i)) τ j := by
  let m := fun i => mass μ d (γ*radius r τ i)
  have hτ0 : 0 < τ := by linarith
  change _ ≤ γ*radius r τ j*convolution m τ j
  induction j with
  | zero =>
      simpa [convolution, increment, m] using moment_bound μ d hμ (γ*radius r τ 0)
  | succ j ih =>
      have hrs := radius_mono r τ hr.le (by linarith) (Nat.le_succ j)
      have hshell := moment_shell μ d hμ (γ*radius r τ j) (γ*radius r τ (j+1))
        (mul_le_mul_of_nonneg_left hrs hγ)
      have he : increment m (j+1) = m (j+1)-m j := by simp [increment]
      have hid : γ*radius r τ (j+1)*convolution m τ (j+1) =
          γ*radius r τ j*convolution m τ j + γ*radius r τ (j+1)*(m (j+1)-m j) := by
        rw [convolution_succ, he]
        unfold radius
        rw [pow_succ]
        field_simp

      rw [hid]
      change _ ≤ γ*radius r τ j*convolution m τ j +
        γ*radius r τ (j+1)*(mass μ d (γ*radius r τ (j+1))-mass μ d (γ*radius r τ j))
      linarith

theorem pilot_moment_sum (μ d : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (_hd : ∀ x, 0 ≤ d x) (r τ γ : ℝ) (hr : 0 < r) (hτ : 2 ≤ τ)
    (hγ : 0 < γ) (N : ℕ) (hN : 0 < N)
    (hm : 0 < mass μ d (γ*r)) :
    (∑ j ∈ Finset.range N,
      moment μ d (γ * radius r τ j) /
        (radius r τ j * mass μ d (γ * radius r τ j))) ≤
      2*γ*(1+Real.log
        (mass μ d (γ * radius r τ (N-1)) / mass μ d (γ*r))) := by
  let m : ℕ → ℝ := fun j => mass μ d (γ*radius r τ j)
  have hτ0 : 0 < τ := by linarith
  have hm0 : m 0 = mass μ d (γ*r) := by simp [m, radius]
  have hmono : Monotone m := by
    intro i j hij
    exact mass_mono μ d hμ (mul_le_mul_of_nonneg_left
      (radius_mono r τ hr.le (by linarith) hij) hγ.le)
  have hpos : ∀ i, 0 < m i := fun i =>
    lt_of_lt_of_le (by simpa [hm0] using hm) (hmono (Nat.zero_le i))
  have hconv := convolution_total m hmono hpos τ hτ N
  have hinc := increment_sum m hpos (N-1)
  have hn : N-1+1 = N := by omega
  rw [hn] at hinc
  have hpoint : ∀ j, moment μ d (γ*radius r τ j) /
      (radius r τ j*m j) ≤ γ*(convolution m τ j/m j) := by
    intro j
    have hrj := radius_pos r τ hr hτ0 j
    have hh := div_le_div_of_nonneg_right
      (moment_convolution μ d hμ r τ γ hr hτ hγ.le j)
      (mul_nonneg hrj.le (hpos j).le)
    change _ ≤ (γ*radius r τ j*convolution m τ j)/(radius r τ j*m j) at hh
    calc
      _ ≤ _ := hh
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j ∈ Finset.range N, γ*(convolution m τ j/m j) :=
      Finset.sum_le_sum fun j hj => hpoint j
    _ = γ*(∑ j ∈ Finset.range N, convolution m τ j/m j) :=
      (Finset.mul_sum ..).symm
    _ ≤ γ*(2*∑ j ∈ Finset.range N, increment m j/m j) :=
      mul_le_mul_of_nonneg_left hconv hγ.le
    _ ≤ γ*(2*(1+Real.log (m (N-1)/m 0))) := by
      gcongr
    _ = _ := by rw [hm0]; ring

end
end UniformKServer.PilotScales



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem innerMoment_mass (r γ : ℝ) (μ : X → ℝ) (x : X) :
    innerMoment r γ μ x = PilotScales.moment μ (dist x) (γ*r)/r := by
  rw [PilotScales.moment, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp [mul_div_assoc]

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotPersistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

def positiveDrift [DecidableEq X] (r σ R : ℝ) (μ ν g : X → ℝ) (x : X) : ℝ :=
  max (value r σ R (fun y => μ y-ν y+if y=x then 1 else 0) g - value r σ R μ g) 0

def exceptional (r σ : ℝ) (ν : X → ℝ) (x : X) : ℝ :=
  ∑ y, if r ≤ 8*dist x y/σ then 514*r*ν y else 0

theorem exceptional_nonneg (r σ : ℝ) (hr : 0 ≤ r) (ν : X → ℝ)
    (hν : ∀ y, 0 ≤ ν y) (x : X) : 0 ≤ exceptional r σ ν x := by
  apply Finset.sum_nonneg
  intro y _
  have hy := hν y
  split_ifs <;> positivity

theorem exceptional_sum (r τ σ : ℝ) (N : ℕ) (hr : 0 < r) (hτ : 2 ≤ τ)
    (hσ : 0 < σ) (ν : X → ℝ) (hν : ∀ y, 0 ≤ ν y) (x : X) :
    (∑ j ∈ Finset.range N, exceptional (r*τ^j) σ ν x) ≤
      (8224/σ)*(∑ y, ν y*dist x y) := by
  classical
  unfold exceptional
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  let s := (Finset.range N).filter (fun j => r*τ^j ≤ 8*dist x y/σ)
  have hs := radius_subsum_le r τ (8*dist x y/σ) hr.le hτ (by positivity) s
    (fun j hj => (Finset.mem_filter.mp hj).2)
  calc
    _ = 514*ν y*(∑ j ∈ s, r*τ^j) := by
      rw [Finset.mul_sum]
      simp only [s,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    _ ≤ 514*ν y*(2*(8*dist x y/σ)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) (hν y))
    _ = _ := by ring

end
end UniformKServer.PilotCompact


end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotCredits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniformKServer.PilotCompact
noncomputable section
variable {X : Type*} [Fintype X] [MetricSpace X]

theorem scale_cut (r τ γ e : ℝ) (N : ℕ) (hγ : 0 < γ) :
    ∃ m ≤ N, (∀ j < m, r*τ^j ≤ 2*e/γ) ∧ (m = N ∨ 2*e ≤ γ*(r*τ^m)) := by
  let P := fun j => j ≤ N ∧ (j=N ∨ 2*e ≤ γ*(r*τ^j))
  have hex : ∃ j, P j := ⟨N,le_rfl,Or.inl rfl⟩
  refine ⟨Nat.find hex,(Nat.find_spec hex).1,?_,(Nat.find_spec hex).2⟩
  intro j hj
  have hjN : j ≤ N := (le_of_lt hj).trans (Nat.find_spec hex).1
  have hnot : ¬ 2*e ≤ γ*(r*τ^j) := by
    intro h
    have hh := Nat.find_min' hex (show P j from ⟨hjN,Or.inr h⟩)
    omega
  apply (le_div_iff₀ hγ).mpr
  nlinarith only [lt_of_not_ge hnot]

end
end UniformKServer.PilotCompact



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotFiltering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                     
section
namespace UniformKServer.PilotCompact
noncomputable section
variable {X Ω : Type*} [Fintype X] [MetricSpace X] [Fintype Ω]

def minimizer (r σ R : ℝ) (μ g : X → ℝ) : X → ℝ :=
  Classical.choose (minimum_exists r σ R μ g)

theorem minimizer_feasible (r σ R : ℝ) (μ g : X → ℝ) :
    feasible r σ R (minimizer r σ R μ g) :=
  (Classical.choose_spec (minimum_exists r σ R μ g)).1

theorem minimizer_value (r σ R : ℝ) (μ g : X → ℝ) :
    objective r σ R μ g (minimizer r σ R μ g) = value r σ R μ g :=
  (Classical.choose_spec (minimum_exists r σ R μ g)).2.1

/-- The old template is measurable before the edit decision. In particular,
this theorem is never conditional on the event that an edit is selected. -/
theorem filtering (r σ R : ℝ) (w : Ω → ℝ) (F : Setoid Ω)
    (μold μminus g : Ω → X → ℝ)
    (hw : ∀ ω, 0 ≤ w ω)
    (hμ : ∀ ω ω', F.r ω ω' → μold ω = μold ω')
    (hg : ∀ ω ω', F.r ω ω' → g ω = g ω')
    (hfilter : ∀ (a : Ω → ℝ), (∀ ω ω', F.r ω ω' → a ω = a ω') →
      ∀ y, (∑ ω, w ω * a ω * (μminus ω y - μold ω y)) = 0) :
    (∑ ω, w ω * value r σ R (μminus ω) (g ω)) ≤
      ∑ ω, w ω * value r σ R (μold ω) (g ω) := by
  let z := fun ω => minimizer r σ R (μold ω) (g ω)
  have hmeas : ∀ y ω ω', F.r ω ω' →
      integrand r σ R (g ω) (z ω) y = integrand r σ R (g ω') (z ω') y := by
    intro y ω ω' h
    dsimp [z]
    rw [hμ ω ω' h,hg ω ω' h]
  have heq : (∑ ω, w ω * objective r σ R (μminus ω) (g ω) (z ω)) =
      ∑ ω, w ω * objective r σ R (μold ω) (g ω) (z ω) := by
    apply sub_eq_zero.mp
    rw [←Finset.sum_sub_distrib]
    have hx : ∀ ω, w ω*objective r σ R (μminus ω) (g ω) (z ω)-
        w ω*objective r σ R (μold ω) (g ω) (z ω) =
          r*∑ y, w ω*integrand r σ R (g ω) (z ω) y*(μminus ω y-μold ω y) := by
      intro ω
      simp only [objective,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    simp_rw [hx]
    rw [←Finset.mul_sum,Finset.sum_comm]
    have hz : ∀ y, (∑ ω, w ω*integrand r σ R (g ω) (z ω) y*(μminus ω y-μold ω y)) = 0 :=
      fun y => hfilter _ (hmeas y) y
    simp only [hz,Finset.sum_const_zero,mul_zero]
  calc
    _ ≤ ∑ ω, w ω*objective r σ R (μminus ω) (g ω) (z ω) :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
        (value_le r σ R (μminus ω) (g ω) (z ω) (minimizer_feasible ..)) (hw ω)
    _ = ∑ ω, w ω*objective r σ R (μold ω) (g ω) (z ω) := heq
    _ = _ := by simp only [z,minimizer_value]

end
end UniformKServer.PilotCompact

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PilotEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.PilotEdits

section
open PilotCompact
attribute [local instance] Classical.propDecidable

variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

def average (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω*f ω

end

section
open PilotCompact
attribute [local instance] Classical.propDecidable
variable {X Ω I : Type*} [Fintype X] [MetricSpace X] [Fintype Ω] [Fintype I]

lemma average_add (w f g : Ω → ℝ) :
    average w (fun ω => f ω+g ω) = average w f+average w g := by
  simp [average,mul_add,Finset.sum_add_distrib]

lemma average_sub (w f g : Ω → ℝ) :
    average w (fun ω => f ω-g ω) = average w f-average w g := by
  simp [average,mul_sub,Finset.sum_sub_distrib]

lemma average_smul (w f : Ω → ℝ) (c : ℝ) :
    average w (fun ω => c*f ω) = c*average w f := by
  simp only [average,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma average_mono (w f g : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h : ∀ ω, f ω ≤ g ω) :
    average w f ≤ average w g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)

end

end UniformKServer.PilotEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_FlowAuxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Linear adapted auxiliary potentials commute with posterior filtering. -/
namespace UniformKServer.PilotEdits
open Finset
open scoped Classical
variable {X Ω : Type} [Fintype X] [Fintype Ω] {k : ℕ}

def linearPotential (μ b : X→ℝ) : ℝ := ∑ p,μ p*b p

end UniformKServer.PilotEdits

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavySchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! The literal deterministic heavy-center recursion of companion §07.
The update decision depends only on the request, posterior, and old centers,
not on any radius, lifetime, allocation, or rounding variable. -/
noncomputable section
namespace UniformKServer.HeavySchedule
open Finset
open scoped Classical
variable {X : Type*} [MetricSpace X]

def Separated (r : ℝ) (H : Finset X) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, a ≠ b → 100*r < dist a b

theorem intersect_unique (r : ℝ) (hr : 0 ≤ r) (H : Finset X) (hs : Separated r H)
    (x a b : X) (ha : a ∈ H) (hb : b ∈ H)
    (hax : dist x a ≤ 40*r) (hbx : dist x b ≤ 40*r) : a=b := by
  by_contra hn
  have hh := hs a ha b hb hn
  have ht := dist_triangle a x b
  rw [dist_comm a x] at ht
  nlinarith

end UniformKServer.HeavySchedule

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavySeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                      
section

/-! Physical separation by the actual disjoint heavy balls. No factor equal
to the number of records is lost: for a short edge there is at most one
possible boundary ball, and its single birth-coordinate marginal is uniform. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset
open scoped Classical
variable {X Λ I : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] [Fintype I] {r : ℝ}
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)
local instance indexDecEq : DecidableEq I := fun a b => Classical.propDecidable (a=b)

end UniformKServer.HeavyRecords

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_HeavyTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                
section

/-! Every time slice of the same finite product tape, not a new resampling of
old balls. The slot universe remains independent of the analysis horizon. -/
noncomputable section
namespace UniformKServer.HeavyProcess
open Finset HeavyRecords
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}
local instance tapePairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

end UniformKServer.HeavyProcess

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RosterTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section
namespace UniformKServer.RosterTails

/-- The Taylor cubic suffices for both lifetime tail estimates; retaining an
explicit (loose) absolute constant avoids a separate asymptotic hypothesis. -/
theorem cubic_exp_bound (x : ℝ) (hx : 0 ≤ x) : x^3*Real.exp (-x/2) ≤ 48 := by
  have ht := Real.pow_div_factorial_le_exp (x/2) (by linarith : 0 ≤ x/2) 3
  norm_num at ht
  have hp := mul_le_mul_of_nonneg_right ht (Real.exp_nonneg (-x/2))
  have he : Real.exp (x/2)*Real.exp (-x/2) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [he] at hp
  nlinarith

theorem geometric_exp_bound (q : ℝ) (hq : q ≤ 1) (n : ℕ) :
    (1-q)^n ≤ Real.exp (-(n:ℝ)*q) := by
  have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1-q) (Real.one_sub_le_exp_neg q) n
  rw [←Real.exp_nat_mul] at h
  simpa only [mul_neg,neg_mul] using h

/-- Actual (long) lifetimes: deterministic through age K-1, probability 1/K
at ages K through K²-1, and compulsory retirement at K². -/
theorem actual_tail (K : ℕ) (hK : 2 ≤ K) :
    1/(K:ℝ)+(K:ℝ)^2*(1-1/(K:ℝ))^(K^2-K) ≤ 49/(K:ℝ) := by
  have hk : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hkpos : (0:ℝ) < K := by linarith
  have hkne : (K:ℝ) ≠ 0 := ne_of_gt hkpos
  have hnat : K ≤ K^2 := by nlinarith
  have hq : 1/(K:ℝ) ≤ 1 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hg := geometric_exp_bound (1/(K:ℝ)) hq (K^2-K)
  have hn : ((K^2-K:ℕ):ℝ) = (K:ℝ)^2-K := by
    rw [Nat.cast_sub hnat,Nat.cast_pow]
  rw [hn] at hg
  have hexp : -((K:ℝ)^2-K)*(1/(K:ℝ)) ≤ -(K:ℝ)/2 := by
    field_simp
    nlinarith
  have hgl := hg.trans (Real.exp_le_exp.mpr hexp)
  have hb := cubic_exp_bound (K:ℝ) hkpos.le
  have hm := mul_le_mul_of_nonneg_left hgl (sq_nonneg (K:ℝ))
  have hm' := mul_le_mul_of_nonneg_right hm hkpos.le
  apply (le_div_iff₀ hkpos).mpr
  rw [add_mul,div_mul_cancel₀ _ hkne]
  nlinarith

/-- Auxiliary short lifetimes: probability K^-1/2 at every age increment and
compulsory retirement at K. This is distinct from the actual partition law. -/
theorem short_tail (K : ℕ) (hK : 2 ≤ K) :
    1/Real.sqrt K+(K:ℝ)*(1-1/Real.sqrt K)^(K-1) ≤ 49/Real.sqrt K := by
  have hk : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0:ℝ) ≤ K := by positivity
  have hspos : 0 < Real.sqrt (K:ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsne : Real.sqrt (K:ℝ) ≠ 0 := ne_of_gt hspos
  have hsq := Real.sq_sqrt hk0
  have hs1 : 1 ≤ Real.sqrt (K:ℝ) := (Real.le_sqrt (by norm_num) hk0).mpr (by nlinarith)
  have hq : 1/Real.sqrt (K:ℝ) ≤ 1 := (div_le_iff₀ hspos).mpr (by linarith)
  have hg := geometric_exp_bound (1/Real.sqrt (K:ℝ)) hq (K-1)
  have hn : ((K-1:ℕ):ℝ) = (K:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hn] at hg
  have hexp : -((K:ℝ)-1)*(1/Real.sqrt (K:ℝ)) ≤ -Real.sqrt (K:ℝ)/2 := by
    rw [mul_one_div]
    apply (div_le_iff₀ hspos).mpr
    nlinarith
  have hgl := hg.trans (Real.exp_le_exp.mpr hexp)
  have hb := cubic_exp_bound (Real.sqrt (K:ℝ)) hspos.le
  have hm := mul_le_mul_of_nonneg_left hgl hk0
  have hm' := mul_le_mul_of_nonneg_right hm hspos.le
  apply (le_div_iff₀ hspos).mpr
  rw [add_mul,div_mul_cancel₀ _ hsne]
  nlinarith

end UniformKServer.RosterTails

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TierPilot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TierPilot

section
attribute [local instance] Classical.propDecidable
open PilotCompact

variable {X : Type*} [Fintype X] [MetricSpace X]

/-- Structural facts of the source short-roster expected parameter at an
insertion; its explicit finite-law construction is separate from this local
analytic gain. These are ramp/retirement facts, not a pilot gain premise. -/
structure Edit (r ε : ℝ) (x : X) (go gn : X → ℝ) : Prop where
  old_range : ∀ p, go p ∈ Set.Icc (0:ℝ) 1
  new_range : ∀ p, gn p ∈ Set.Icc (0:ℝ) 1
  unit_drop : ∀ p, dist x p ≤ r/8 → go p = 1 ∧ gn p = 0
  increase : ∀ p, gn p-go p ≤ ε
  support : ∀ p, go p < gn p → r/8 < dist x p ∧ dist x p ≤ 21*r

def variation (r σ : ℝ) (z f : X → ℝ) (p : X) : ℝ :=
  f p*(1-∑ s, z s*bumpB σ (dist s p/r)) +
    256*∑ s, z s*f s*bumpA σ 204800 (dist s p/r)

theorem variation_sub (r σ : ℝ) (z f g : X → ℝ) (p : X) :
    variation r σ z (fun s => f s-g s) p = variation r σ z f p-variation r σ z g p := by
  simp only [variation,sub_mul,mul_sub,Finset.sum_sub_distrib]
  ring

theorem integrand_variation (r σ : ℝ) (z go gn : X → ℝ) (p : X) :
    integrand r σ 204800 go z p-integrand r σ 204800 gn z p =
      variation r σ z (fun s => go s-gn s) p := by
  simp only [integrand,variation,mul_sub,sub_mul,mul_add,add_mul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  ring

def rise (go gn : X → ℝ) (p : X) : ℝ := max (gn p-go p) 0
def fall (go gn : X → ℝ) (p : X) : ℝ := max (go p-gn p) 0

omit [Fintype X] [MetricSpace X] in
theorem rise_nonneg (go gn : X → ℝ) (p : X) : 0 ≤ rise go gn p := le_max_right _ _
omit [Fintype X] [MetricSpace X] in
theorem fall_nonneg (go gn : X → ℝ) (p : X) : 0 ≤ fall go gn p := le_max_right _ _

omit [Fintype X] in
theorem rise_bound (r ε : ℝ) (hε : 0 ≤ ε) (x : X) (go gn : X → ℝ)
    (he : Edit r ε x go gn) (p : X) : rise go gn p ≤ ε :=
  max_le (he.increase p) hε

omit [Fintype X] [MetricSpace X] in
theorem rise_zero (go gn : X → ℝ) (p : X) (hp : gn p ≤ go p) : rise go gn p = 0 :=
  max_eq_right (sub_nonpos.mpr hp)

omit [Fintype X] in
theorem rise_support (r ε : ℝ) (x : X) (go gn : X → ℝ)
    (he : Edit r ε x go gn) (p : X) (hp : rise go gn p ≠ 0) :
    r/8 < dist x p ∧ dist x p ≤ 21*r := by
  apply he.support p
  by_contra hn
  exact hp (rise_zero go gn p (le_of_not_gt hn))

omit [Fintype X] in
theorem fall_unit (r ε : ℝ) (x : X) (go gn : X → ℝ)
    (he : Edit r ε x go gn) (p : X) (hp : dist x p ≤ r/8) : fall go gn p = 1 := by
  obtain ⟨ho,hn⟩ := he.unit_drop p hp
  norm_num [fall,ho,hn]

end
open PilotCompact

end UniformKServer.TierPilot

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_PartitionSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                          
section

/-! The actual one-level final-map separation estimate with its local mass
ratio, and the exact zero contribution at large heavy levels. -/
noncomputable section
namespace UniformKServer.PartitionLevel.Input
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N : ℕ}
local instance sepFinDecEq (m : ℕ) : DecidableEq (Fin m) := fun a b => Classical.propDecidable (a=b)

end UniformKServer.PartitionLevel.Input

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ReverseScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                    
section

/-! Finite geometric scale reversal for the pilot finance theorem. -/
namespace UniformKServer.GeometricMass
open Finset

 theorem reverse_sum {M : Type*} [AddCommMonoid M] (f : ℕ→M) (J : ℕ) :
    (∑ j∈range J, f (J-1-j))=∑ j∈range J, f j := sum_range_reflect f J

end UniformKServer.GeometricMass

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SmallScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                  
section

/-! A thresholded geometric scale sum with no dependence on the number of
scales. Used for designated-mover errors, not a per-level additive error. -/
noncomputable section
namespace UniformKServer.SmallScales
open Finset
open scoped Classical

theorem geometric (R q : ℝ) (hR : 0 ≤ R) (hq : 0 ≤ q) (hq1 : q<1) (n : ℕ) :
    (∑ j∈range n, R*q^j) ≤ R/(1-q) := by
  induction n generalizing R with
  | zero => simp only [sum_range_zero] <;> positivity
  | succ n ih =>
    rw [sum_range_succ']
    have hh := ih (R*q) (mul_nonneg hR hq)
    have he (j : ℕ) : R*q^(j+1)=(R*q)*q^j := by rw [pow_succ]; ring
    simp only [he,pow_zero,mul_one]
    have hd : 0<1-q := by linarith
    have hid : R*q/(1-q)+R=R/(1-q) := by field_simp <;> ring
    calc
      _ ≤ R*q/(1-q)+R := by linarith only [hh]
      _ = _ := hid

end UniformKServer.SmallScales

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_SortedRoster
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                   
section

noncomputable section
namespace UniformKServer.SortedRoster
open Finset
open scoped Classical
variable {I : Type*} [LinearOrder I]

theorem sort_filter (S : Finset I) (p : I → Prop) [DecidablePred p] :
    (S.filter p).sort (·≤·)=(S.sort (·≤·)).filter (fun i => decide (p i)) := by
  let l := (S.sort (·≤·)).filter (fun i => decide (p i))
  have he : l.toFinset=S.filter p := by ext i; simp [l]
  rw [←he]
  exact (List.toFinset_sort (·≤·) ((sort_nodup S _).filter _)).mpr
    ((pairwise_sort S _).filter _)

theorem sort_insert_last (S : Finset I) (n : I) (hn : ∀ i∈S, i<n) :
    (insert n S).sort (·≤·)=S.sort (·≤·)++[n] := by
  have hnot : n∉S := fun h => (lt_irrefl n) (hn n h)
  have hnodup : (S.sort (·≤·)++[n]).Nodup := by
    rw [List.nodup_append]
    refine ⟨sort_nodup S _,List.nodup_singleton n,?_⟩
    intro i hi j hj hij
    have hjn : j=n := by simpa using hj
    subst j
    subst i
    exact hnot ((mem_sort _).mp hi)
  have hp : (S.sort (·≤·)++[n]).Pairwise (·≤·) := by
    rw [List.pairwise_append]
    refine ⟨pairwise_sort S _,by simp,?_⟩
    intro i hi j hj
    have hjn : j=n := by simpa using hj
    subst j
    exact (hn i ((mem_sort _).mp hi)).le
  have he : (S.sort (·≤·)++[n]).toFinset=insert n S := by
    ext i
    simp only [List.mem_toFinset,List.mem_append,mem_sort,List.mem_singleton,mem_insert]
    exact or_comm
  rw [←he]
  exact (List.toFinset_sort _ hnodup).mpr hp

end UniformKServer.SortedRoster

end


end

end OAI
end


