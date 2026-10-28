-- Prove2me | Definitions.Def_OAIQ17Ks000
-- name    : OAIQ17Ks000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T14:58:42.126387+00:00
-- url     : https://prove2.me/theorems/99ebd18a-e764-4267-9cad-044eb1362175
-- title:
--   Definitions bundle OAIQ17Ks000 of the split of OpenAI, Squared-logarithmic randomized k-server on arbitrary metrics
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KServer.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Squared-logarithmic randomized k-server on arbitrary metrics*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1474 declarations of OpenAI's Lean: 742 definitions, 21 inductive types or structures, 22 instances and 689 theorems. The definitions and types are `OAI.KServer.ActualCaps.a`, `OAI.KServer.ActualCaps.cap`, `OAI.KServer.ActualCaps.ell`, `OAI.KServer.ActualCaps.flexCap`, `OAI.KServer.ActualCaps.z`, `OAI.KServer.ActualCharges.active`, `OAI.KServer.ActualCharges.activeConstant`, `OAI.KServer.ActualCharges.drift`, `OAI.KServer.ActualCharges.endpointConstant`, `OAI.KServer.ActualCharges.fineConstant`, `OAI.KServer.ActualCharges.flagConstant`, `OAI.KServer.ActualCharges.flags`, `OAI.KServer.ActualCharges.flat`, `OAI.KServer.ActualCharges.inventory`, `OAI.KServer.ActualCharges.localConstant`, `OAI.KServer.ActualCharges.movementConstant`, `OAI.KServer.ActualCharges.parentCharge`, `OAI.KServer.ActualCharges.parentConstant`, `OAI.KServer.ActualCharges.ruleConstant`, `OAI.KServer.ActualCharges.scaleConstant`, `OAI.KServer.ActualCharges.sideConstant`, `OAI.KServer.ActualCharges.sideRefresh`, `OAI.KServer.ActualCharges.sideRefreshConstant`, `OAI.KServer.ActualCharges.simplexConstant`, `OAI.KServer.ActualCharges.stock`, `OAI.KServer.ActualCharges.total`, `OAI.KServer.ActualCharges.wholesale`, `OAI.KServer.ActualCharges.wholesaleConstant`, `OAI.KServer.ActualOutput.B`, `OAI.KServer.ActualOutput.D`, `OAI.KServer.ActualOutput.S`, `OAI.KServer.ActualOutput.T`, `OAI.KServer.ActualOutput.capScale`, `OAI.KServer.ActualOutput.d`, `OAI.KServer.ActualOutput.e`, `OAI.KServer.ActualOutput.f`, `OAI.KServer.ActualOutput.fc`, `OAI.KServer.ActualOutput.flexcap`, `OAI.KServer.ActualOutput.lower`, `OAI.KServer.ActualOutput.marked` and 723 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KServer, in whole or in part: `KServer_Allocation`, `KServer_AllocationBudget`, `KServer_AllocationCausality`, `KServer_AllocationMovement`, `KServer_AllocationSchedule`, `KServer_Amplification`, `KServer_AnchorTravel`, `KServer_Basic`, `KServer_Behavior`, `KServer_Caps`, `KServer_CausalRounding`, `KServer_Coarse`, `KServer_Experiments`, `KServer_FiniteLaw`, `KServer_Hierarchy`, `KServer_JointBudget`, `KServer_JointExperiment`, `KServer_JointTravel`, `KServer_Main`, `KServer_MetricMatching`, `KServer_MetricService`, `KServer_Minimization`, `KServer_OutputDynamics`, `KServer_OutputRules`, `KServer_PartitionBudget`, `KServer_Partitions`, `KServer_Potential`, `KServer_PrefixAllocation`, `KServer_RankProportions`, `KServer_Ranks`, `KServer_RosterEdits`, `KServer_Rosters`, `KServer_Rounding`, `KServer_ScheduleBudget`, `KServer_Simplex`, `KServer_Tiers`, `KServer_Trees`.
--
--   **Imports.** It imports the published bundle `Def_KServer`.
--
--   **Imported by** (directly, in this split): the statements `OAI.KServer.JointBudget.quota_bound` and `OAI.KServer.JointEmbedding.key_bound`; the proofs of `OAI.KServer.JointBudget.quota_bound`, `OAI.KServer.JointEmbedding.key_bound` and `OAI.KServer.main_theorem`.
-- source:
--   OpenAI, Squared-logarithmic randomized k-server on arbitrary metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KServer at commit adc7f12

import Mathlib
import Definitions.Def_KServer

section
-- module Solutions.OAIQ17_KS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Ranks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RankTracking

variable {Ω : Type*} [Fintype Ω]

def avg (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω*f ω

lemma avg_sub (w f g : Ω → ℝ) : avg w (fun ω => f ω-g ω)=avg w f-avg w g := by
  simp [avg,mul_sub,sum_sub_distrib]

/-- Functions known from the observed finite history label. -/
def Adapted (H : Ω → ℕ) (f : Ω → ℝ) : Prop := ∀ ω ω', H ω=H ω' → f ω=f ω'

/-- Increasing history information, adapted ranks, and the literal finite
conditional tower relation for old counts under the new observation. -/
structure FilteredRanks (w : Ω → ℝ) where
  history : ℕ → Ω → ℕ
  refines : ∀ t ω ω', history (t+1) ω=history (t+1) ω' → history t ω=history t ω'
  p : ℕ → Ω → ℝ
  before : ℕ → Ω → ℝ
  range : ∀ t ω, p t ω ∈ Set.Icc 0 1
  before_range : ∀ t ω, before t ω ∈ Set.Icc 0 1
  adapted : ∀ t, Adapted (history t) (p t)
  filtering : ∀ t h, ∑ ω ∈ Finset.univ.filter (fun ω => history t ω=h),
    w ω*(before (t+1) ω-p t ω)=0

lemma fiber_weighted_zero (H : Ω → ℕ) (f g : Ω → ℝ)
    (hf : Adapted H f) (hg : ∀ h, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω=0) :
    ∑ ω, f ω*g ω=0 := by
  classical
  let c : ℕ → ℝ := fun h => if hh : ∃ ω, H ω=h then f hh.choose else 0
  have hc : ∀ ω, f ω=c (H ω) := by
    intro ω
    dsimp [c]
    rw [dite_eq_left ⟨ω,rfl⟩]
    exact hf ω _ (Exists.choose_spec (show ∃ ω', H ω'=H ω from ⟨ω,rfl⟩)).symm
  have hs : (∑ ω, f ω*g ω) =
      ∑ h ∈ Finset.univ.image H, ∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), f ω*g ω := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (by intro ω _; exact Finset.mem_image.mpr ⟨ω,Finset.mem_univ _,rfl⟩) _
  rw [hs]
  apply sum_eq_zero
  intro h _
  calc _ = c h*(∑ ω ∈ Finset.univ.filter (fun ω => H ω=h), g ω) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro ω hω
        rw [hc ω,(Finset.mem_filter.mp hω).2]
       _ = 0 := by rw [hg,mul_zero]

end KServer.RankTracking

/-! Construction of the rank martingales from the actual finite hidden law.
No filtering identity is postulated in the construction below. -/
namespace KServer.PosteriorRanks
open Finset
open RankTracking
variable {Ω : Type*} [Fintype Ω]

def fiber (H : Ω → ℕ) (h : ℕ) : Finset Ω := univ.filter (fun ω => H ω=h)
def mass (w : Ω → ℝ) (H : Ω → ℕ) (h : ℕ) : ℝ := ∑ ω ∈ fiber H h, w ω
def numerator (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) (h : ℕ) : ℝ :=
  ∑ ω ∈ fiber H h, w ω*f ω

def posterior (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  numerator w H f (H ω) / mass w H (H ω)

lemma mass_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H h) : 0 ≤ mass w H h :=
  sum_nonneg fun ω _ => hw ω

lemma numerator_zero {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) {H h}
    (hm : mass w H h=0) (f : Ω → ℝ) : numerator w H f h=0 := by
  have hzero : ∀ ω ∈ fiber H h, w ω=0 :=
    (sum_eq_zero_iff_of_nonneg (fun ω _ => hw ω)).mp hm
  exact sum_eq_zero fun ω hω => by rw [hzero ω hω,zero_mul]

lemma posterior_adapted (w : Ω → ℝ) (H : Ω → ℕ) (f : Ω → ℝ) :
    Adapted H (posterior w H f) := by
  intro ω ω' hh
  simp only [posterior,hh]

lemma posterior_range {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) {f : Ω → ℝ} (hf : ∀ ω, f ω ∈ Set.Icc 0 1) (ω : Ω) :
    posterior w H f ω ∈ Set.Icc 0 1 := by
  have hm := mass_nonneg hw H (H ω)
  have hn : 0 ≤ numerator w H f (H ω) := sum_nonneg fun z _ => mul_nonneg (hw z) (hf z).1
  have hnle : numerator w H f (H ω) ≤ mass w H (H ω) := by
    apply sum_le_sum
    intro z _
    exact mul_le_of_le_one_right (hw z) (hf z).2
  constructor
  · exact div_nonneg hn hm
  · by_cases hz : mass w H (H ω)=0
    · simp [posterior,hz]
    · exact (div_le_one (lt_of_le_of_ne hm (Ne.symm hz))).mpr hnle

lemma fiber_posterior {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f : Ω → ℝ) (h : ℕ) :
    ∑ ω ∈ fiber H h, w ω*posterior w H f ω = numerator w H f h := by
  calc _ = mass w H h*(numerator w H f h/mass w H h) := by
        unfold mass
        rw [sum_mul]
        apply sum_congr rfl
        intro ω hω
        simp only [fiber,mem_filter,mem_univ,true_and] at hω
        rw [posterior,hω]
        rfl
       _ = numerator w H f h := by
        by_cases hm : mass w H h=0
        · rw [hm,numerator_zero hw hm f]; norm_num
        · field_simp

lemma fiber_difference {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f : Ω → ℝ) (h : ℕ) :
    ∑ ω ∈ fiber H h, w ω*(posterior w H f ω-f ω)=0 := by
  simp only [mul_sub,sum_sub_distrib,fiber_posterior hw,numerator,sub_self]

lemma weighted_posterior {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : Ω → ℕ) (f g : Ω → ℝ) (hg : Adapted H g) :
    avg w (fun ω => g ω*posterior w H f ω)=avg w (fun ω => g ω*f ω) := by
  have hh := fiber_weighted_zero H g (fun ω => w ω*(posterior w H f ω-f ω)) hg
    (fiber_difference hw H f)
  simp only [mul_sub,mul_left_comm (g _) (w _),sum_sub_distrib] at hh
  exact sub_eq_zero.mp hh

lemma filtered_fiber {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (H H' : Ω → ℕ)
    (hr : ∀ ω ω', H' ω=H' ω' → H ω=H ω') (f : Ω → ℝ) (h : ℕ) :
    ∑ ω ∈ fiber H h, w ω*(posterior w H' f ω-posterior w H f ω)=0 := by
  let g := fun ω => if H ω=h then (1:ℝ) else 0
  have hga : Adapted H g := by intro ω z hz; simp [g,hz]
  have hgb : Adapted H' g := by intro ω z hz; simp [g,hr ω z hz]
  have ha := weighted_posterior hw H f g hga
  have hb := weighted_posterior hw H' f g hgb
  have hh : avg w (fun ω => g ω*posterior w H' f ω)-
      avg w (fun ω => g ω*posterior w H f ω)=0 := by rw [ha,hb,sub_self]
  rw [←avg_sub] at hh
  unfold avg at hh
  simpa only [fiber,sum_filter,g,ite_mul,one_mul,zero_mul,ite_sub_ite,sub_zero,
    mul_ite,mul_zero] using hh

/-- The true post-filtering, post-drift ranks and the filtered old ranks on an
arbitrary finite experiment with increasing observations. -/
def rank (N : Ω → ℕ) (a : ℕ) (ω : Ω) : ℝ := if N ω ≤ a then 1 else 0
omit [Fintype Ω] in
lemma rank_range (N : Ω → ℕ) (a : ℕ) (ω : Ω) : rank N a ω ∈ Set.Icc 0 1 := by
  unfold rank; split_ifs <;> norm_num

def rankProcess {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (H : ℕ → Ω → ℕ) (hr : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z)
    (N : ℕ → Ω → ℕ) (a : ℕ) : FilteredRanks w where
  history := H
  refines := hr
  p := fun t => posterior w (H t) (rank (N t) a)
  before := fun t => posterior w (H t) (rank (N (t-1)) a)
  range := fun t ω => posterior_range hw (H t) (rank_range (N t) a) ω
  before_range := fun t ω => posterior_range hw (H t) (rank_range (N (t-1)) a) ω
  adapted := fun t => posterior_adapted w (H t) (rank (N t) a)
  filtering := by
    intro t h
    simp only [Nat.add_sub_cancel]
    exact filtered_fiber hw (H t) (H (t+1)) (hr t) (rank (N t) a) h

end KServer.PosteriorRanks


/-! ## The actual finite hidden experiment of §02

The input is drawn once. Its selected optimum is hidden, whereas a finite
independent partition tape and the true request prefix are observed. No
conditioning on rounding outcomes enters this experiment. -/
namespace KServer.PosteriorRanks
variable {Ω : Type*} [Fintype Ω]

lemma posterior_nonneg {w : Ω → ℝ} (hw : ∀ ω, 0≤w ω) (H : Ω → ℕ)
    {f : Ω → ℝ} (hf : ∀ ω, 0≤f ω) (ω : Ω) : 0≤posterior w H f ω :=
  div_nonneg (sum_nonneg fun z _ => mul_nonneg (hw z) (hf z)) (mass_nonneg hw H _)

lemma posterior_fiber_const {w : Ω → ℝ} {H : Ω → ℕ} {f : Ω → ℝ}
    (ω : Ω) {c : ℝ} (hf : ∀ z,H z=H ω → f z=c) (hm : mass w H (H ω)≠0) :
    posterior w H f ω=c := by
  have hn : numerator w H f (H ω)=mass w H (H ω)*c := by
    unfold numerator mass
    rw [sum_mul]
    apply sum_congr rfl
    intro z hz
    rw [hf z (mem_filter.mp hz).2]
  rw [posterior,hn,mul_div_cancel_left₀ _ hm]

lemma posterior_mono_fiber {w : Ω → ℝ} (hw : ∀ ω,0≤w ω) {H : Ω → ℕ}
    {f g : Ω → ℝ} (ω : Ω) (hfg : ∀ z,H z=H ω → f z≤g z) :
    posterior w H f ω≤posterior w H g ω := by
  apply div_le_div_of_nonneg_right _ (mass_nonneg hw H _)
  apply sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_left (hfg z (mem_filter.mp hz).2) (hw z)

end KServer.PosteriorRanks

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Minimization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AdaptiveMinimization
open Finset KServer.RankTracking
variable {I J Θ : Type*} [Fintype I] [Fintype J]

/-- The source primitives are affine in the rank inputs when the held parameters
and the state are fixed.  Both simplex and side domains are compact. -/
structure Family (Θ : Type*) (I J : Type*) [Fintype I] [Fintype J] where
  domain : Θ → Set (J → ℝ)
  compact : ∀ θ, IsCompact (domain θ)
  seed : ∀ θ, {a // a ∈ domain θ}
  offset : Θ → (J → ℝ) → ℝ
  coefficient : Θ → (J → ℝ) → I → ℝ
  offset_continuous : ∀ θ, ContinuousOn (offset θ) (domain θ)
  coefficient_continuous : ∀ θ i, ContinuousOn (fun a => coefficient θ a i) (domain θ)

def Family.value (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (a : J → ℝ) : ℝ :=
  F.offset θ a + ∑ i, F.coefficient θ a i*p i

def movement (a b : J → ℝ) : ℝ := ∑ j, |a j-b j|

lemma Family.value_continuous (F : Family Θ I J) (θ : Θ) (p : I → ℝ) :
    ContinuousOn (F.value θ p) (F.domain θ) := by
  apply (F.offset_continuous θ).add
  exact continuousOn_finsetSum _ fun i _ => (F.coefficient_continuous θ i).mul_const _

lemma movement_continuous (b : J → ℝ) : Continuous (fun a => movement a b) :=
  continuous_finsetSum _ fun j _ => ((continuous_apply j).sub continuous_const).abs

lemma Family.exists_update (F : Family Θ I J) (θ : Θ) (p : I → ℝ)
    (c : ℝ) (a : J → ℝ) :
    ∃ b ∈ F.domain θ, IsMinOn (fun b => F.value θ p b+c*movement b a) (F.domain θ) b := by
  exact (F.compact θ).exists_isMinOn ⟨(F.seed θ).val,(F.seed θ).property⟩
    ((F.value_continuous θ p).add ((movement_continuous a).continuousOn.const_mul c))

/-- A fixed noncomputable selection, only from the currently supplied data. -/
def Family.update (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (c : ℝ) (a : J → ℝ) : J → ℝ :=
  (F.exists_update θ p c a).choose

lemma Family.update_mem (F : Family Θ I J) (θ : Θ) (p : I → ℝ) (c : ℝ) (a : J → ℝ) :
    F.update θ p c a ∈ F.domain θ := (F.exists_update θ p c a).choose_spec.1

variable {Ω : Type} [Fintype Ω]

/-- Domain transport is computed from old/new held parameters and new rank
inputs. For the manuscript it is the prepared update followed by deletion and
zero insertion. It is not permitted to depend on the unrealized future. -/
structure Transport (F : Family Θ I J) where
  map : Θ → Θ → (I → ℝ) → (J → ℝ) → (J → ℝ)
  mem : ∀ θ θ' p a, a ∈ F.domain θ → map θ θ' p a ∈ F.domain θ'

def state (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) : ℕ → Ω → J → ℝ
  | 0, ω => (F.seed (θ 0 ω)).val
  | t+1, ω => F.update (θ (t+1) ω) (p (t+1) ω) (c (t+1) ω)
      (T.map (θ t ω) (θ (t+1) ω) (p (t+1) ω) (state F T θ p c t ω))

omit [Fintype Ω] in
lemma state_mem (F : Family Θ I J) (T : Transport F) (θ : ℕ → Ω → Θ)
    (p : ℕ → Ω → I → ℝ) (c : ℕ → Ω → ℝ) :
    ∀ t ω, state F T θ p c t ω ∈ F.domain (θ t ω) := by
  intro t ω
  cases t with
  | zero => exact (F.seed _).property
  | succ t => exact F.update_mem _ _ _ _

end KServer.AdaptiveMinimization


/-! Actual zero-extension and synthetic-input operations in §04.  In particular
zero weight and singleton transitions are included, not divided away. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ChangingDomains
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

def variation (a b : J → ℝ) : ℝ := ∑ i, |a i-b i|

def simplex (A : Finset J) : Set (J → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ (∑ i, a i)=(if A.Nonempty then 1 else 0) ∧ ∀ i ∉ A, a i=0}

def canonical (A : Finset J) : J → ℝ :=
  if h : A.Nonempty then fun i => if i=h.choose then 1 else 0 else fun _ => 0

lemma canonical_mem (A : Finset J) : canonical A ∈ simplex A := by
  classical
  by_cases h : A.Nonempty
  · unfold canonical simplex
    rw [dite_eq_left h]
    refine ⟨fun i => by dsimp only; split_ifs <;> norm_num,?_,?_⟩
    · simp [h]
    · intro i hi
      have hn : i≠h.choose := by intro he; subst i; exact hi h.choose_spec
      simp [hn]
  · simp [canonical,simplex,h]

omit [DecidableEq J] in
lemma simplex_coordinate {A : Finset J} {a : J → ℝ} (ha : a ∈ simplex A) (i : J) :
    a i ∈ Set.Icc 0 1 := by
  refine ⟨ha.1 i,?_⟩
  have hh := single_le_sum (fun j _ => ha.1 j) (mem_univ i)
  rw [ha.2.1] at hh
  split_ifs at hh <;> linarith

omit [DecidableEq J] in
lemma simplex_compact (A : Finset J) : IsCompact (simplex A) := by
  have hc : IsClosed (simplex A) := by
    change IsClosed ({a : J → ℝ | ∀ i, 0 ≤ a i} ∩
      ({a : J → ℝ | ∑ i, a i=(if A.Nonempty then 1 else 0)} ∩
      {a : J → ℝ | ∀ i ∉ A, a i=0}))
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply i) continuous_const
  apply (isCompact_pi_infinite fun _ : J => isCompact_Icc (a := (0:ℝ)) (b := 1)).of_isClosed_subset hc
  intro a ha i
  exact simplex_coordinate ha i

/-- Deletion plus zero insertion. At zero synthetic total choose a fresh
canonical vector; this has exactly zero synthetic weighted movement. -/
def transposeSimplex (A : Finset J) (S : ℝ) (a : J → ℝ) : J → ℝ :=
  if S=0 then canonical A else a

def sideDomain (A : Finset J) (W : ℝ) : Set (J → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ (∑ i, a i) ≤ W ∧ ∀ i ∉ A, a i=0}

def transposeSide (A : Finset J) (a : J → ℝ) : J → ℝ := fun i => if i∈A then a i else 0

lemma transposeSide_mem {A B : Finset J} {W : ℝ} {a : J → ℝ}
    (ha : a ∈ sideDomain A W) : transposeSide B a ∈ sideDomain B W := by
  refine ⟨?_,?_,?_⟩
  · intro i
    simp only [transposeSide]
    split_ifs
    · exact ha.1 i
    · exact le_rfl
  · apply le_trans _ ha.2.1
    exact sum_le_sum fun i _ => by simp only [transposeSide]; split_ifs; rfl; exact ha.1 i
  · intro i hi; simp [transposeSide,hi]

def core (f : J → R → Bool) (p : J → R → ℝ) (i : J) : ℝ :=
  ∑ a, if f i a then p i a else 0

def syntheticFlags (A B : Finset J) (f : J → R → Bool) : J → R → Bool :=
  fun i a => if i∈A∩B then f i a else false

def changedFlags (f g : J → R → Bool) : ℝ :=
  ∑ i, ∑ a, if f i a=g i a then 0 else 1

omit [Fintype J] [DecidableEq J] in
lemma core_nonneg {f : J → R → Bool} {p : J → R → ℝ} (hp : ∀ i a, 0 ≤ p i a) (i : J) :
    0 ≤ core f p i := by
  apply sum_nonneg
  intro a _
  split_ifs
  · exact hp i a
  · rfl

end KServer.ChangingDomains

end
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Simplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Finset

/-! Exact analytic kernels of §04, necessary for the simplex minimization.
Only the point values of integrands at zero are irrelevant to the integrals. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace KServer.SimplexAnalytic

def regularF (h y : ℝ) : ℝ := (h + y)^2 / h

def markedF (u H y : ℝ) : ℝ := u + H * y * (1 + y)

def kernel (F : ℝ → ℝ) (s : ℝ) : ℝ := 1 / F (Real.log (1 / s))

def singularKernel (F : ℝ → ℝ) (s : ℝ) : ℝ := kernel F s / s

def primitive (F : ℝ → ℝ) (Cα ell η S B base a : ℝ) : ℝ :=
  Cα * ell * ∫ s in base..a, (S - (1 + η) * B / s) / F (Real.log (1 / s))

/-- Continuous primitive of the regular B/s term, including the improper endpoint. -/
def regularTail (h : ℝ) : ℝ → ℝ := Function.update (fun s => h / (h - Real.log s)) 0 0

lemma regularTail_of_ne {s : ℝ} (hs : s ≠ 0) (h : ℝ) :
    regularTail h s = h / (h - Real.log s) := by simp [regularTail, Function.update_of_ne hs]

lemma regularTail_continuousAt_zero (h : ℝ) : ContinuousAt (regularTail h) 0 := by
  apply continuousAt_update_same.mpr
  have ht : Tendsto (fun s : ℝ => h - Real.log s) (𝓝[≠] 0) atTop := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      tendsto_atTop_add_const_left (𝓝[≠] (0 : ℝ)) h
        (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero)
  exact tendsto_const_nhds.div_atTop ht

lemma regularTail_derivative {h s : ℝ} (hh : 0 < h) (hs : s ∈ Set.Ioc 0 1) :
    HasDerivAt (regularTail h) (h / (s * (h - Real.log s)^2)) s := by
  have hlog : Real.log s ≤ 0 := Real.log_nonpos hs.1.le hs.2
  have hn : h - Real.log s ≠ 0 := by linarith
  have hd := (hasDerivAt_const s h).div
    ((hasDerivAt_const s h).sub (Real.hasDerivAt_log hs.1.ne')) hn
  have heq : (0 * (h - Real.log s) - h * (0 - s⁻¹)) / (h - Real.log s)^2 =
      h / (s * (h - Real.log s)^2) := by
    field_simp
    ring
  dsimp at hd
  rw [heq] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hs.1.ne'] with x hx
  exact regularTail_of_ne hx h

lemma regularTail_continuousOn {h : ℝ} (hh : 0 < h) :
    ContinuousOn (regularTail h) (Set.Icc 0 1) := by
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst s
    exact (regularTail_continuousAt_zero h).continuousWithinAt
  · exact (regularTail_derivative hh ⟨h0, hs.2⟩).continuousAt.continuousWithinAt

lemma regular_singular_formula {h s : ℝ} :
    singularKernel (regularF h) s = h / (s * (h - Real.log s)^2) := by
  dsimp [singularKernel, kernel, regularF]
  have he : Real.log (1 / s) = -Real.log s := by rw [one_div, Real.log_inv]
  rw [he]
  simp only [← sub_eq_add_neg, div_eq_mul_inv, mul_inv_rev, inv_inv, one_mul]
  ring

lemma regular_singular_intervalIntegrable {h : ℝ} (hh : 0 < h) :
    IntervalIntegrable (singularKernel (regularF h)) volume 0 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := regularTail h)
  · simpa using regularTail_continuousOn hh
  · intro s hs
    simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
      max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    rw [regular_singular_formula]
    exact regularTail_derivative hh ⟨hs.1, hs.2.le⟩
  · intro s hs
    simp only [min_eq_left (show (0 : ℝ) ≤ 1 by norm_num),
      max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)] at hs
    rw [regular_singular_formula]
    exact div_nonneg hh.le (mul_nonneg hs.1.le (sq_nonneg _))

lemma kernel_measurable {F : ℝ → ℝ} (hF : Measurable F) : Measurable (kernel F) := by
  unfold kernel
  fun_prop

lemma singularKernel_measurable {F : ℝ → ℝ} (hF : Measurable F) :
    Measurable (singularKernel F) :=
  (kernel_measurable hF).div measurable_id

lemma log_inverse_nonneg {s : ℝ} (hs : s ∈ Set.Ioc 0 1) : 0 ≤ Real.log (1 / s) := by
  rw [one_div, Real.log_inv]
  exact neg_nonneg.mpr (Real.log_nonpos hs.1.le hs.2)

lemma marked_quadratic_lower {u H c y : ℝ} (hy : 0 ≤ y) (hc : 0 < c)
    (hcu : c ≤ u) (hcH : 2 * c ≤ H) : c * (1 + y)^2 ≤ markedF u H y := by
  unfold markedF
  nlinarith [mul_nonneg (sub_nonneg.mpr hcH) (mul_nonneg hy (show 0 ≤ 1 + y by linarith)),
    mul_nonneg hc.le (sq_nonneg y)]

lemma singular_dominated {F : ℝ → ℝ} {c s : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y) (hs : s ∈ Set.Ioc 0 1) :
    0 ≤ singularKernel F s ∧
      singularKernel F s ≤ (1 / c) * singularKernel (regularF 1) s := by
  have hy := log_inverse_nonneg hs
  have hp : 0 < c * (1 + Real.log (1 / s))^2 := by positivity
  have hden : 0 < F (Real.log (1 / s)) := hp.trans_le (hF _ hy)
  constructor
  · exact div_nonneg (div_nonneg (by norm_num) hden.le) hs.1.le
  · have hi := one_div_le_one_div_of_le hp (hF _ hy)
    have he : (1 / (c * (1 + Real.log (1 / s))^2)) / s =
        (1 / c) * singularKernel (regularF 1) s := by
      dsimp [singularKernel, kernel, regularF]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    rw [← he]
    exact div_le_div_of_nonneg_right hi hs.1.le

lemma singular_intervalIntegrable_of_quadratic {F : ℝ → ℝ} {c : ℝ}
    (hFm : Measurable F) (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y) :
    IntervalIntegrable (singularKernel F) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hreg := ((intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)).mp (regular_singular_intervalIntegrable (by norm_num : (0 : ℝ) < 1))).const_mul (1 / c)
  apply hreg.mono' (singularKernel_measurable hFm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (singular_dominated hc hF hs).1]
  exact (singular_dominated hc hF hs).2

lemma kernel_intervalIntegrable {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1) :
    IntervalIntegrable (kernel F) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)).mp hint
  apply hi.mono' (kernel_measurable hFm).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hk : 0 ≤ kernel F s := div_nonneg (by norm_num) (hF _ (log_inverse_nonneg hs)).le
  rw [Real.norm_eq_abs, abs_of_nonneg hk]
  apply (le_div_iff₀ hs.1).mpr
  exact mul_le_of_le_one_right hk hs.2

lemma integrand_affine (F : ℝ → ℝ) (η S B s : ℝ) :
    (S - (1 + η) * B / s) / F (Real.log (1 / s)) =
      S * kernel F s - (1 + η) * B * singularKernel F s := by
  dsimp [kernel, singularKernel]
  ring

lemma integrand_intervalIntegrable {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1) (η S B : ℝ) :
    IntervalIntegrable (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) volume 0 1 := by
  simp_rw [integrand_affine]
  exact ((kernel_intervalIntegrable hFm hF hint).const_mul S).sub
    (hint.const_mul ((1 + η) * B))

lemma primitive_continuousOn {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1)
    (Cα ell η S B : ℝ) {base : ℝ} (hb : base ∈ Set.Icc 0 1) :
    ContinuousOn (primitive F Cα ell η S B base) (Set.Icc 0 1) := by
  have hi := integrand_intervalIntegrable hFm hF hint η S B
  have he : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := uIcc_of_le (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (he.symm ▸ hb)
  rw [he] at hc
  exact hc.const_mul (Cα * ell)

lemma primitive_derivative {F : ℝ → ℝ} (hFc : Continuous F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1)
    (Cα ell η S B : ℝ) {base a : ℝ} (hb : base ∈ Set.Icc 0 1) (ha : a ∈ Set.Ioc 0 1) :
    HasDerivAt (primitive F Cα ell η S B base)
      (Cα * ell * ((S - (1 + η) * B / a) / F (Real.log (1 / a)))) a := by
  have hi := integrand_intervalIntegrable hFc.measurable hF hint η S B
  have him : Measurable (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) := by
    fun_prop
  have hc : ContinuousAt (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) a := by
    apply ContinuousAt.div
    · fun_prop (disch := exact ha.1.ne')
    · exact hFc.continuousAt.comp (((continuousAt_const.div continuousAt_id ha.1.ne').log
        (div_ne_zero one_ne_zero ha.1.ne')))
    · exact (hF _ (log_inverse_nonneg ha)).ne'
  have hi' : IntervalIntegrable (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) volume base a :=
    hi.mono_set (by
      rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact uIcc_subset_Icc hb ⟨ha.1.le, ha.2⟩)
  exact (intervalIntegral.integral_hasDerivAt_right hi'
    him.stronglyMeasurable.stronglyMeasurableAtFilter hc).const_mul (Cα * ell)

lemma log_inverse_tendsto : Tendsto (fun s : ℝ => Real.log (1 / s)) (𝓝[>] 0) atTop := by
  simpa only [one_div, Real.log_inv, Function.comp_def] using
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

lemma polynomial_log_decay (p : Polynomial ℝ) :
    Tendsto (fun s : ℝ => s * p.eval (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0) := by
  have ht := p.tendsto_div_exp_atTop.comp log_inverse_tendsto
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have he : Real.exp (Real.log (1 / s)) = 1 / s :=
    Real.exp_log (div_pos one_pos hs)
  dsimp only [Function.comp_def]
  rw [he]
  simp [div_eq_mul_inv, mul_comm]

lemma quadratic_lower_tendsto {F : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y) : Tendsto F atTop atTop := by
  have ht : Tendsto (fun y : ℝ => c * y) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  exact (show c * y ≤ c * (1 + y)^2 by nlinarith [sq_nonneg y]).trans (hF y hy)

lemma singular_tendsto {F : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y)
    (hdecay : Tendsto (fun s : ℝ => s * F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (singularKernel F) (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, s * F (Real.log (1 / s)) ∈ Set.Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with s hs hs1
    have hp : 0 < c * (1 + Real.log (1 / s))^2 := by
      have := log_inverse_nonneg ⟨hs, hs1⟩
      positivity
    exact mul_pos hs (hp.trans_le (hF _ (log_inverse_nonneg ⟨hs, hs1⟩)))
  have ht := tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdecay hpos)
  change Tendsto (fun s => (1 / F (Real.log (1 / s))) / s) (𝓝[>] 0) atTop
  simpa only [Function.comp_def, one_div, div_eq_mul_inv, mul_inv_rev, one_mul] using ht

lemma integrand_tendsto_atBot {F : ℝ → ℝ} {c η S B : ℝ} (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y)
    (hdecay : Tendsto (fun s : ℝ => s * F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0))
    (hη : 0 ≤ η) (hB : 0 < B) :
    Tendsto (fun s => (S - (1 + η) * B / s) / F (Real.log (1 / s))) (𝓝[>] 0) atBot := by
  have hk : Tendsto (kernel F) (𝓝[>] 0) (𝓝 0) := by
    change Tendsto (fun s : ℝ => 1 / F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0)
    exact
      (tendsto_const_nhds.div_atTop ((quadratic_lower_tendsto hc hF).comp log_inverse_tendsto) :
        Tendsto (fun s : ℝ => 1 / F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0))
  have hs := (singular_tendsto hc hF hdecay).const_mul_atTop
    (show 0 < (1 + η) * B by positivity)
  have hn := tendsto_neg_atTop_atBot.comp hs
  have ht := (hk.const_mul S).add_atBot hn
  simp_rw [integrand_affine]
  exact ht

lemma primitive_inward_atBot {F : ℝ → ℝ} {c Cα ell η B base : ℝ}
    (hFc : Continuous F) (hc : 0 < c)
    (hF : ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ F y)
    (hdecay : Tendsto (fun s : ℝ => s * F (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0))
    (hCα : 0 < Cα) (hell : 0 < ell) (hη : 0 ≤ η) (hB : 0 < B)
    (S : ℝ) (hb : base ∈ Set.Icc 0 1) :
    Tendsto (fun a => (primitive F Cα ell η S B base a -
      primitive F Cα ell η S B base 0) / a) (𝓝[>] 0) atBot := by
  have hp : ∀ y, 0 ≤ y → 0 < F y := fun y hy =>
    (show 0 < c * (1 + y)^2 by positivity).trans_le (hF y hy)
  have hi := singular_intervalIntegrable_of_quadratic hFc.measurable hc hF
  apply HasDerivAt.lhopital_zero_right_on_Ico (b := 1) (show (0 : ℝ) < 1 by norm_num)
    (f' := fun a => Cα * ell * ((S - (1 + η) * B / a) / F (Real.log (1 / a))))
    (g' := fun _ => 1)
  · intro a ha
    exact (primitive_derivative hFc hp hi Cα ell η S B hb ⟨ha.1, ha.2.le⟩).sub_const _
  · intro a _
    exact hasDerivAt_id a
  · exact ((primitive_continuousOn hFc.measurable hp hi Cα ell η S B hb).mono Ico_subset_Icc_self).sub continuousOn_const
  · exact continuous_id.continuousOn
  · intro _ _; exact one_ne_zero
  · simp
  · rfl
  · simpa only [div_one] using
      (integrand_tendsto_atBot hc hF hdecay hη hB).const_mul_atBot (mul_pos hCα hell)

lemma regular_quadratic_lower {h y : ℝ} (hh : 1 ≤ h) (hy : 0 ≤ y) :
    (1 / h) * (1 + y)^2 ≤ regularF h y := by
  dsimp [regularF]
  rw [one_div, mul_comm (h⁻¹), ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (by linarith)
  nlinarith

lemma regular_decay (h : ℝ) :
    Tendsto (fun s : ℝ => s * regularF h (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0) := by
  have ht := polynomial_log_decay ((Polynomial.C h + Polynomial.X)^2 * Polynomial.C (1 / h))
  simpa [regularF, div_eq_mul_inv] using ht

lemma marked_decay (u H : ℝ) :
    Tendsto (fun s : ℝ => s * markedF u H (Real.log (1 / s))) (𝓝[>] 0) (𝓝 0) := by
  have ht := polynomial_log_decay (Polynomial.C u + Polynomial.C H * Polynomial.X * (1 + Polynomial.X))
  simpa [markedF] using ht

lemma marked_lower_constant {u H : ℝ} (hu : 0 < u) (hH : 0 < H) :
    ∃ c, 0 < c ∧ ∀ y, 0 ≤ y → c * (1 + y)^2 ≤ markedF u H y := by
  refine ⟨min u (H / 2), lt_min hu (by positivity), ?_⟩
  intro y hy
  exact marked_quadratic_lower hy (lt_min hu (by positivity)) (min_le_left _ _)
    (by linarith [min_le_right u (H / 2)])

lemma marked_singular_intervalIntegrable {u H : ℝ} (hu : 0 < u) (hH : 0 < H) :
    IntervalIntegrable (singularKernel (markedF u H)) volume 0 1 := by
  obtain ⟨c, hc, hF⟩ := marked_lower_constant hu hH
  exact singular_intervalIntegrable_of_quadratic (by unfold markedF; fun_prop) hc hF

/-- Elementary exponential estimate giving the marked contribution's side cancellation. -/
lemma exp_marked_bound {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) * y * (1 + y) ≤ 2 * (1 - Real.exp (-y)) := by
  have he := mul_le_mul_of_nonneg_left (Real.quadratic_le_exp_of_nonneg hy)
    (Real.exp_nonneg (-y))
  have hid : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  rw [hid] at he
  nlinarith [mul_nonneg (Real.exp_nonneg (-y)) hy]

lemma exp_square_bound {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-y) * y^2 ≤ 8 * Real.exp (-y / 2) := by
  have hp := Real.quadratic_le_exp_of_nonneg (show 0 ≤ y / 2 by positivity)
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-y))
  have he : Real.exp (-y) * Real.exp (y / 2) = Real.exp (-y / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he] at hm
  nlinarith [Real.exp_nonneg (-y), mul_nonneg (Real.exp_nonneg (-y)) hy]

lemma regular_exp_tail {h y : ℝ} (hh : 1 ≤ h) (hy : 4 * h < y) :
    Real.exp (-y) * regularF h y ≤ 32 * Real.exp (-h) := by
  have hh0 : 0 < h := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hp : regularF h y ≤ 4 * y^2 := by
    apply (div_le_iff₀ hh0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg y)]
  calc
    _ ≤ Real.exp (-y) * (4 * y^2) := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
    _ = 4 * (Real.exp (-y) * y^2) := by ring
    _ ≤ 32 * Real.exp (-y / 2) := by nlinarith [exp_square_bound hy0]
    _ ≤ 32 * Real.exp (-h) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

lemma regular_coordinate_bound {h a : ℝ} (hh : 1 ≤ h) (ha : a ∈ Set.Icc 0 1) :
    a * regularF h (Real.log (1 / a)) ≤ 25 * a * h + 32 * Real.exp (-h) := by
  rcases eq_or_lt_of_le ha.1 with h0 | hp
  · subst a; simp only [zero_mul]; positivity
  have hlog := log_inverse_nonneg ⟨hp, ha.2⟩
  by_cases hc : Real.log (1 / a) ≤ 4 * h
  · have hreg : regularF h (Real.log (1 / a)) ≤ 25 * h := by
      apply (div_le_iff₀ (show 0 < h by linarith)).mpr
      nlinarith [sq_nonneg (4 * h - Real.log (1 / a))]
    have := mul_le_mul_of_nonneg_left hreg ha.1
    have := Real.exp_nonneg (-h)
    nlinarith
  · have he : Real.exp (-Real.log (1 / a)) = a := by
      rw [Real.exp_neg, Real.exp_log (div_pos one_pos hp)]
      simp
    have ht := regular_exp_tail hh (lt_of_not_ge hc)
    rw [he] at ht
    have : 0 ≤ 25 * a * h := by positivity
    linarith

lemma marked_coordinate_bound {u H a : ℝ} (hH : 0 ≤ H) (ha : a ∈ Set.Icc 0 1) :
    a * markedF u H (Real.log (1 / a)) ≤ a * u + 2 * H * (1 - a) := by
  rcases eq_or_lt_of_le ha.1 with h0 | hp
  · subst a; simp only [zero_mul, sub_zero, zero_add, mul_one]; positivity
  have he : Real.exp (-Real.log (1 / a)) = a := by
    rw [Real.exp_neg, Real.exp_log (div_pos one_pos hp)]
    simp
  have ht := exp_marked_bound (log_inverse_nonneg ⟨hp, ha.2⟩)
  rw [he] at ht
  have hm := mul_le_mul_of_nonneg_left ht hH
  dsimp [markedF]
  nlinarith

/-- Logarithmic comparison primitive on the upper half of the marked integral. -/
def affineLogTail (u H s : ℝ) : ℝ := -Real.log (u - H * Real.log s) / H

open scoped BigOperators

lemma regular_denominator_sum {ι : Type*} [Fintype ι] {a h : ι → ℝ} {C : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1) (hh : ∀ i, 1 ≤ h i)
    (hC : ∑ i, Real.exp (-h i) ≤ C) :
    ∑ i, a i * regularF (h i) (Real.log (1 / a i)) ≤
      (25 + 32 * C) * ∑ i, a i * h i := by
  have hmax : ∀ i, a i ≤ 1 := fun i => by
    simpa only [hasum] using Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hT : 1 ≤ ∑ i, a i * h i := by
    rw [← hasum]
    exact Finset.sum_le_sum fun i _ => le_mul_of_one_le_right (ha i) (hh i)
  have hCn : 0 ≤ C := (Finset.sum_nonneg fun i _ => Real.exp_nonneg _).trans hC
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => regular_coordinate_bound (hh i) ⟨ha i, hmax i⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hs
  have he := mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 32)
  have hCT := mul_le_mul_of_nonneg_left hT (show 0 ≤ 32 * C by positivity)
  nlinarith

lemma marked_denominator_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a h : ι → ℝ} {u H c C : ℝ} (o : ι)
    (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1)
    (hu : 0 ≤ u) (huH : u ≤ H) (hc : 0 < c) (hc1 : c ≤ 1)
    (hh : ∀ i ≠ o, 1 ≤ h i) (hside : ∀ i ≠ o, c * H ≤ h i)
    (hC0 : 0 ≤ C) (hC : ∑ i ∈ Finset.univ.erase o, Real.exp (-h i) ≤ C * u) :
    a o * markedF u H (Real.log (1 / a o)) +
      ∑ i ∈ Finset.univ.erase o, a i * regularF (h i) (Real.log (1 / a i)) ≤
    ((25 * c + 2 + 32 * C) / c) *
      (a o * u + ∑ i ∈ Finset.univ.erase o, a i * h i) := by
  let T := a o * u + ∑ i ∈ Finset.univ.erase o, a i * h i
  have hmax : ∀ i, a i ≤ 1 := fun i => by
    simpa only [hasum] using Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hsum : (∑ i ∈ Finset.univ.erase o, a i) = 1 - a o := by
    have he := Finset.sum_erase_add Finset.univ a (Finset.mem_univ o)
    rw [hasum] at he
    linarith
  have hside0 : 0 ≤ ∑ i ∈ Finset.univ.erase o, a i * h i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i) (le_trans (by norm_num) (hh i (Finset.mem_erase.mp hi).1))
  have hT0 : 0 ≤ T := add_nonneg (mul_nonneg (ha o) hu) hside0
  have hTs : c * H * (1 - a o) ≤ ∑ i ∈ Finset.univ.erase o, a i * h i := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith [mul_le_mul_of_nonneg_left (hside i (Finset.mem_erase.mp hi).1) (ha i)]
  have hcuT : c * u ≤ T := by
    dsimp [T]
    have hcuH := mul_le_mul_of_nonneg_left huH hc.le
    have hm := mul_le_mul_of_nonneg_right hcuH (sub_nonneg.mpr (hmax o))
    have hca := mul_le_mul_of_nonneg_right hc1 (mul_nonneg (ha o) hu)
    nlinarith
  have hsm := marked_coordinate_bound (hu.trans huH) ⟨ha o, hmax o⟩ (u := u)
  have hsr := Finset.sum_le_sum fun i (hi : i ∈ Finset.univ.erase o) =>
    regular_coordinate_bound (hh i (Finset.mem_erase.mp hi).1) ⟨ha i, hmax i⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hsr
  have htail := mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 32)
  have hraw : a o * markedF u H (Real.log (1 / a o)) +
      ∑ i ∈ Finset.univ.erase o, a i * regularF (h i) (Real.log (1 / a i)) ≤
      25 * T + 2 * H * (1 - a o) + 32 * C * u := by
    dsimp [T]
    nlinarith [mul_nonneg (ha o) hu]
  have hHpay : c * (H * (1 - a o)) ≤ T := by
    dsimp [T]
    nlinarith [mul_nonneg (ha o) hu]
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    _ ≤ c * (25 * T + 2 * H * (1 - a o) + 32 * C * u) := mul_le_mul_of_nonneg_left hraw hc.le
    _ ≤ (25 * c + 2 + 32 * C) * T := by
      have ht := mul_le_mul_of_nonneg_left hcuT (show 0 ≤ 32 * C by positivity)
      nlinarith
    _ = c * (((25 * c + 2 + 32 * C) / c) * T) := by field_simp

end KServer.SimplexAnalytic

namespace KServer.SimplexAnalytic
open Set MeasureTheory
open scoped BigOperators

lemma primitive_affine {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : ∀ y, 0 ≤ y → 0 < F y)
    (hint : IntervalIntegrable (singularKernel F) volume 0 1)
    (Cα ell η S B : ℝ) {base a : ℝ} (hb : base ∈ Set.Icc 0 1) (ha : a ∈ Set.Icc 0 1) :
    primitive F Cα ell η S B base a = Cα * ell *
      (S * (∫ s in base..a, kernel F s) -
        (1 + η) * B * (∫ s in base..a, singularKernel F s)) := by
  have hsub : Set.uIcc base a ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact uIcc_subset_Icc hb ha
  unfold primitive
  simp_rw [integrand_affine]
  rw [intervalIntegral.integral_sub (((kernel_intervalIntegrable hFm hF hint).mono_set hsub).const_mul S)
    ((hint.mono_set hsub).const_mul ((1 + η) * B))]
  simp only [intervalIntegral.integral_const_mul]

lemma regularF_lower {h y : ℝ} (hh : 0 < h) (hy : 0 ≤ y) : h ≤ regularF h y := by
  unfold regularF
  apply (le_div_iff₀ hh).mpr
  nlinarith

lemma marked_positive {u H : ℝ} (hu : 0 < u) (hH : 0 ≤ H) :
    ∀ y, 0 ≤ y → 0 < markedF u H y := by
  intro y hy
  unfold markedF
  positivity

end KServer.SimplexAnalytic

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Allocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Finset Set Filter MeasureTheory

/-! The exact source primitives installed in the actual affine minimizer
recursion. The coefficients use raw core flags; fine caps are deliberately
absent. The zero-potential cases do not evaluate the marked denominator. -/
namespace KServer.SimplexFamilies
open scoped BigOperators
open Finset Set MeasureTheory
open KServer.SimplexAnalytic KServer.AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

structure Data (J R : Type*) [Fintype J] where
  active : Finset J
  flags : J → R → Bool
  F : J → ℝ → ℝ
  eta : J → ℝ
  base : J → ℝ
  zeroPotential : Bool
  measurable : ∀ i, Measurable (F i)
  positive : ∀ i y, 0 ≤ y → 0 < F i y
  integrable : ∀ i, IntervalIntegrable (singularKernel (F i)) volume 0 1
  base_mem : ∀ i, base i ∈ Set.Icc 0 1

omit [DecidableEq J] [Fintype R] in
def K (d : Data J R) (a : J → ℝ) (i : J) : ℝ := ∫ s in d.base i..a i, kernel (d.F i) s
omit [DecidableEq J] [Fintype R] in
def Z (d : Data J R) (a : J → ℝ) (i : J) : ℝ := ∫ s in d.base i..a i, singularKernel (d.F i) s

def core (d : Data J R) (p : J × R → ℝ) (i : J) : ℝ := ∑ r, if d.flags i r then p (i,r) else 0

def potential (C ell : ℝ) (d : Data J R) (B a : J → ℝ) : ℝ :=
  if d.zeroPotential then 0 else ∑ i, primitive (d.F i) C ell (d.eta i) (∑ j, B j) (B i) (d.base i) (a i)

def coefficient (C ell : ℝ) (d : Data J R) (a : J → ℝ) (ir : J × R) : ℝ :=
  if d.zeroPotential then 0 else if d.flags ir.1 ir.2 then
    C*ell*((∑ i, K d a i)-(1+d.eta ir.1)*Z d a ir.1) else 0

omit [DecidableEq J] [Fintype R] in
lemma K_continuous (d : Data J R) (i : J) :
    ContinuousOn (fun a => K d a i) (ChangingDomains.simplex d.active) := by
  have hi := kernel_intervalIntegrable (d.measurable i) (d.positive i) (d.integrable i)
  have he : Set.uIcc (0:ℝ) 1=Set.Icc 0 1 := uIcc_of_le (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (he.symm ▸ d.base_mem i)
  rw [he] at hc
  exact hc.comp (continuous_apply i).continuousOn (fun a ha => ChangingDomains.simplex_coordinate ha i)

omit [DecidableEq J] [Fintype R] in
lemma Z_continuous (d : Data J R) (i : J) :
    ContinuousOn (fun a => Z d a i) (ChangingDomains.simplex d.active) := by
  have he : Set.uIcc (0:ℝ) 1=Set.Icc 0 1 := uIcc_of_le (by norm_num)
  have hc := intervalIntegral.continuousOn_primitive_interval' (d.integrable i) (he.symm ▸ d.base_mem i)
  rw [he] at hc
  exact hc.comp (continuous_apply i).continuousOn (fun a ha => ChangingDomains.simplex_coordinate ha i)

omit [DecidableEq J] [Fintype R] in
lemma coefficient_continuous (C ell : ℝ) (d : Data J R) (ir : J × R) :
    ContinuousOn (fun a => coefficient C ell d a ir) (ChangingDomains.simplex d.active) := by
  unfold coefficient
  split_ifs
  · exact continuousOn_const
  · exact ((continuousOn_finsetSum _ fun i _ => K_continuous d i).sub
      ((Z_continuous d ir.1).const_mul _)).const_mul _
  · exact continuousOn_const

def family (C ell : ℝ) : Family (Data J R) (J × R) J where
  domain d := ChangingDomains.simplex d.active
  compact d := ChangingDomains.simplex_compact d.active
  seed d := ⟨ChangingDomains.canonical d.active,ChangingDomains.canonical_mem d.active⟩
  offset _ _ := 0
  coefficient := coefficient C ell
  offset_continuous _ := continuousOn_const
  coefficient_continuous := coefficient_continuous C ell

/-- Algebraic equality with the literal sum of the source's improper
integrals. In particular the family does not substitute another potential. -/
lemma value_eq (C ell : ℝ) (d : Data J R) (p : J × R → ℝ) (a : J → ℝ)
    (ha : a ∈ ChangingDomains.simplex d.active) :
    (family C ell).value d p a=potential C ell d (core d p) a := by
  by_cases hz : d.zeroPotential=true
  · simp [Family.value,family,coefficient,potential,hz]
  · have hi : ∀ i, primitive (d.F i) C ell (d.eta i) (∑ j, core d p j) (core d p i) (d.base i) (a i)=
        C*ell*((∑ j, core d p j)*K d a i-(1+d.eta i)*core d p i*Z d a i) := by
      intro i
      exact primitive_affine (d.measurable i) (d.positive i) (d.integrable i) C ell _ _ _
        (d.base_mem i) (ChangingDomains.simplex_coordinate ha i)
    simp only [Family.value,family,coefficient,potential,hz,Bool.false_eq_true,ite_false,zero_add]
    rw [Fintype.sum_prod_type]
    have hr (i : J) : (∑ r, (if d.flags i r=true then C*ell*((∑ j, K d a j)-(1+d.eta i)*Z d a i) else 0)*p (i,r))=
        C*ell*((∑ j, K d a j)-(1+d.eta i)*Z d a i)*core d p i := by
      rw [core,mul_sum]
      exact sum_congr rfl fun r _ => by split_ifs <;> simp_all
    simp_rw [hr,hi]
    have heL (i : J) : C*ell*((∑ j, K d a j)-(1+d.eta i)*Z d a i)*core d p i =
        (C*ell*(∑ j, K d a j))*core d p i-C*ell*((1+d.eta i)*core d p i*Z d a i) := by ring
    have heR (i : J) : C*ell*((∑ j, core d p j)*K d a i-(1+d.eta i)*core d p i*Z d a i) =
        (C*ell*(∑ j, core d p j))*K d a i-C*ell*((1+d.eta i)*core d p i*Z d a i) := by ring
    simp_rw [heL,heR]
    simp only [sum_sub_distrib,←mul_sum]
    ring

def regular (A : Finset J) (flags : J → R → Bool) (h eta : J → ℝ)
    (hh : ∀ i, 1 ≤ h i) : Data J R where
  active := A
  flags := flags
  F i := regularF (h i)
  eta := eta
  base _ := 0
  zeroPotential := false
  measurable i := by unfold regularF; fun_prop
  positive i y hy := (show 0 < h i by linarith [hh i]).trans_le (regularF_lower (by linarith [hh i]) hy)
  integrable i := regular_singular_intervalIntegrable (by linarith [hh i])
  base_mem _ := ⟨le_rfl,by norm_num⟩


/-- The marked base point is exactly one; no value with `u=0` is accepted. -/
def marked (A : Finset J) (flags : J → R → Bool) (o : J) (h eta : J → ℝ)
    (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) (hh : ∀ i ≠ o, 1 ≤ h i) : Data J R where
  active := A
  flags := flags
  F i := if i=o then markedF u (1+Real.log (1/u)) else regularF (h i)
  eta := eta
  base i := if i=o then 1 else 0
  zeroPotential := false
  measurable i := by
    by_cases hi : i=o
    · simpa only [ite_eq_left hi] using (show Measurable (markedF u (1+Real.log (1/u))) by unfold markedF; fun_prop)
    · simpa only [ite_eq_right hi] using (show Measurable (regularF (h i)) by unfold regularF; fun_prop)
  positive i y hy := by
    split_ifs with hi
    · apply marked_positive hu _ y hy
      have := log_inverse_nonneg ⟨hu,hu1⟩
      linarith
    · exact (show 0 < h i by linarith [hh i hi]).trans_le
        (regularF_lower (by linarith [hh i hi]) hy)
  integrable i := by
    split_ifs with hi
    · apply marked_singular_intervalIntegrable hu
      have := log_inverse_nonneg ⟨hu,hu1⟩
      linarith
    · exact regular_singular_intervalIntegrable (by linarith [hh i hi])
  base_mem i := by split_ifs <;> constructor <;> norm_num

end KServer.SimplexFamilies


noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace KServer.SimplexTracker

variable {ι : Type*} [Fintype ι]

def simplex : Set (ι → ℝ) := {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1}

def potential (f : ι → ℝ → ℝ) (a : ι → ℝ) : ℝ := ∑ i, f i (a i)

def movement (a b : ι → ℝ) : ℝ := ∑ i, |a i - b i|

def objective (f : ι → ℝ → ℝ) (S : ℝ) (a₀ a : ι → ℝ) : ℝ :=
  potential f a + S * movement a a₀

lemma max_coordinate {a : ι → ℝ} (ha : a ∈ simplex) (i : ι) : a i ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => ha.1 j) (Finset.mem_univ i)
  rwa [ha.2] at h

/-- Quantitative deficit from replacing alpha_i by alpha_i/(1+eta_i). -/
lemma weighted_deficit {a h η : ι → ℝ} {ct ell ηmax : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 0 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hη : ∀ i, η i = ct * h i / ell) (hmax : ∀ i, η i ≤ ηmax) :
    ∑ i, a i / (1 + η i) ≤
      1 - ct / (ell * (1 + ηmax)) * ∑ i, a i * h i := by
  by_cases he : IsEmpty ι
  · let := he
    have : (0 : ℝ) = 1 := by simpa using ha.2
    norm_num at this
  have : Nonempty ι := not_isEmpty_iff.mp he
  have hη0 : ∀ i, 0 ≤ η i := fun i => by rw [hη i]; exact div_nonneg (mul_nonneg hc.le (hh i)) hl.le
  have hmax0 : 0 ≤ ηmax := (hη0 (Classical.arbitrary ι)).trans (hmax _)
  have hi : ∀ i, a i / (1 + η i) ≤
      a i - ct / (ell * (1 + ηmax)) * (a i * h i) := by
    intro i
    have hden : 0 < 1 + η i := by linarith [hη0 i]
    have hdm : 0 < 1 + ηmax := by linarith
    have hle := mul_le_mul_of_nonneg_left (hmax i) (ha.1 i)
    have hhi : ell * η i = ct * h i := by rw [hη i]; field_simp
    apply (div_le_iff₀ hden).mpr
    apply (mul_le_mul_iff_right₀ (mul_pos hl hdm)).mp
    field_simp
    rw [← hhi]
    nlinarith [mul_nonneg (mul_nonneg (ha.1 i) hl.le)
      (mul_nonneg (hη0 i) (sub_nonneg.mpr (hmax i)))]
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hi i
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, ha.2] using hs

/-- The derivative contradiction in eq:alpha-derivative-contradiction,
with coefficients general enough to include the marked denominator. -/
lemma exists_negative_derivative {a h η F B γ : ι → ℝ}
    {ct ell ηmax Cα CF S : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 0 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hη : ∀ i, η i = ct * h i / ell) (hmax : ∀ i, η i ≤ ηmax)
    (hCa : 0 < Cα) (_hCF : 0 ≤ CF) (hS : 0 < S)
    (hB : ∑ i, B i = S) (hF : ∀ i, 0 ≤ F i)
    (hT : 0 < ∑ i, a i * h i)
    (hden : ∑ i, a i * F i ≤ CF * ∑ i, a i * h i)
    (hgap : 2 * CF * (1 + ηmax) < Cα * ct)
    (hidentity : ∀ i, a i * F i / (1 + η i) * γ i =
      Cα * ell * (S * (a i / (1 + η i)) - B i)) :
    ∃ i, γ i < -2 * S := by
  have hη0 : ∀ i, 0 ≤ η i := fun i => by rw [hη i]; exact div_nonneg (mul_nonneg hc.le (hh i)) hl.le
  have hdef := weighted_deficit ha hh hc hl hη hmax
  by_contra hall
  push Not at hall
  have hlow : -2 * S * (CF * ∑ i, a i * h i) ≤
      ∑ i, a i * F i / (1 + η i) * γ i := by
    calc
      _ ≤ -2 * S * ∑ i, a i * F i :=
        mul_le_mul_of_nonpos_left hden (by linarith)
      _ ≤ ∑ i, a i * F i / (1 + η i) * γ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hp : 0 ≤ a i * F i := mul_nonneg (ha.1 i) (hF i)
        have hd : 0 < 1 + η i := by linarith [hη0 i]
        have hdiv : a i * F i / (1 + η i) ≤ a i * F i := by
          apply (div_le_iff₀ hd).mpr
          nlinarith [mul_nonneg hp (hη0 i)]
        have hmul := mul_le_mul_of_nonneg_left (hall i) (div_nonneg hp hd.le)
        nlinarith
  have heq : (∑ i, a i * F i / (1 + η i) * γ i) =
      Cα * ell * (S * ∑ i, a i / (1 + η i) - S) := by
    simp_rw [hidentity]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hB]
  rw [heq] at hlow
  have hnon : Nonempty ι := by
    by_contra hn
    have : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hT
  let := hnon
  have hmax0 : 0 ≤ ηmax := (hη0 (Classical.arbitrary ι)).trans (hmax _)
  have hdm : 0 < ell * (1 + ηmax) := by positivity
  have hup := mul_le_mul_of_nonneg_left hdef (show 0 ≤ Cα * ell * S by positivity)
  have hstrict := mul_pos (sub_pos.mpr hgap) (mul_pos hS hT)
  have hid : ell * (1 + ηmax) * (ct / (ell * (1 + ηmax))) = ct := by
    field_simp
  have hlow' := mul_le_mul_of_nonneg_right hlow (show 0 ≤ 1 + ηmax by linarith)
  have hup' := mul_le_mul_of_nonneg_right hup (show 0 ≤ 1 + ηmax by linarith)
  have hr : Cα * ell * S * (1 - ct / (ell * (1 + ηmax)) * ∑ i, a i * h i) *
      (1 + ηmax) = Cα * ell * S * (1 + ηmax) - Cα * ct * S * ∑ i, a i * h i := by
    field_simp
  rw [hr] at hup'
  nlinarith

lemma sum_replace [DecidableEq ι] (f : ι → ℝ → ℝ) (w : ι → ℝ) (i : ι) (y : ℝ) :
    (∑ j, f j (Function.update w i y j)) = (∑ j, f j (w j)) - f i (w i) + f i y := by
  have he : (∑ j ∈ Finset.univ.erase i, f j (Function.update w i y j)) =
      ∑ j ∈ Finset.univ.erase i, f j (w j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, (Finset.mem_erase.mp hj).1]
  have h₁ := Finset.sum_erase_add Finset.univ (fun j => f j (Function.update w i y j))
    (Finset.mem_univ i)
  have h₂ := Finset.sum_erase_add Finset.univ (fun j => f j (w j)) (Finset.mem_univ i)
  simp only [Function.update_self, he] at h₁
  linarith

/-- Transfer epsilon from donor i to receiver j, exactly as in §04. -/
def transfer [DecidableEq ι] (a : ι → ℝ) (i j : ι) (ε : ℝ) : ι → ℝ :=
  Function.update (Function.update a i (a i - ε)) j (a j + ε)

lemma sum_transfer [DecidableEq ι] (f : ι → ℝ → ℝ) (a : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (ε : ℝ) :
    (∑ l, f l (transfer a i j ε l)) =
      (∑ l, f l (a l)) - f i (a i) + f i (a i - ε) - f j (a j) + f j (a j + ε) := by
  simp only [transfer, sum_replace, Function.update_of_ne hij.symm]

lemma transfer_mem_simplex [DecidableEq ι] {a : ι → ℝ} (ha : a ∈ simplex) {i j : ι}
    (hij : i ≠ j) {ε : ℝ} (hε : ε ∈ Set.Icc 0 (a i)) : transfer a i j ε ∈ simplex := by
  constructor
  · intro l
    by_cases hlj : l = j
    · subst l; simp only [transfer, Function.update_self]; linarith [ha.1 j, hε.1]
    by_cases hli : l = i
    · subst l; simp [transfer, Function.update_of_ne hij, sub_nonneg.mpr hε.2]
    · simpa [transfer, Function.update_of_ne hlj, Function.update_of_ne hli] using ha.1 l
  · rw [sum_transfer (fun _ x => x) a hij ε, ha.2]
    ring

lemma transfer_min_comparison [DecidableEq ι] {f : ι → ℝ → ℝ} {S : ℝ} {a₀ a : ι → ℝ}
    (hS : 0 ≤ S) (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    {i j : ι} (hij : i ≠ j) {ε : ℝ} (hε : ε ∈ Set.Icc 0 (a i)) :
    f i (a i) + f j (a j) ≤ f i (a i - ε) + f j (a j + ε) + 2 * S * ε := by
  have h := hm (transfer_mem_simplex ha hij hε)
  change potential f a + S * movement a a₀ ≤ potential f (transfer a i j ε) +
    S * movement (transfer a i j ε) a₀ at h
  dsimp [potential, movement] at h
  rw [sum_transfer f a hij ε, sum_transfer (fun l x => |x - a₀ l|) a hij ε] at h
  have hi := abs_sub_le (a i - ε) (a i) (a₀ i)
  have hj := abs_sub_le (a j + ε) (a j) (a₀ j)
  have hei : |a i - ε - a i| = ε := by rw [show a i - ε - a i = -ε by ring, abs_neg, abs_of_nonneg hε.1]
  have hej : |a j + ε - a j| = ε := by rw [show a j + ε - a j = ε by ring, abs_of_nonneg hε.1]
  rw [hei] at hi
  rw [hej] at hj
  have hi' := mul_le_mul_of_nonneg_left hi hS
  have hj' := mul_le_mul_of_nonneg_left hj hS
  linarith

lemma minimizer_derivative_gap [DecidableEq ι] {f : ι → ℝ → ℝ} {S : ℝ} {a₀ a : ι → ℝ}
    (hS : 0 ≤ S) (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    {i j : ι} (hij : i ≠ j) (hi : 0 < a i) {di dj : ℝ}
    (hdi : HasDerivAt (f i) di (a i)) (hdj : HasDerivAt (f j) dj (a j)) :
    di ≤ dj + 2 * S := by
  have hc : IsLocalMinOn (fun ε => f i (a i - ε) + f j (a j + ε) + 2 * S * ε)
      (Icc 0 (a i)) 0 := by
    apply IsMinOn.localize
    intro ε hε
    simpa using transfer_min_comparison hS ha hm hij hε
  have hd : HasDerivAt (fun ε => f i (a i - ε) + f j (a j + ε) + 2 * S * ε)
      (-di + dj + 2 * S) 0 := by
    have hi' : HasDerivAt (fun ε => f i (a i - ε)) (-di) 0 := by
      convert (hdi.comp_of_eq 0 ((hasDerivAt_id 0).const_sub (a i)) (by simp)) using 1 <;> first | rfl | simp
    have hj' : HasDerivAt (fun ε => f j (a j + ε)) dj 0 := by
      convert (hdj.comp_of_eq 0 ((hasDerivAt_id 0).const_add (a j)) (by simp)) using 1 <;> first | rfl | simp
    convert (hi'.add hj').add ((hasDerivAt_id 0).const_mul (2 * S)) using 1 <;> first | rfl | simp
  have ht : a i - 0 ∈ posTangentConeAt (Icc 0 (a i)) 0 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 (a i)).segment_subset ⟨le_rfl, hi.le⟩ ⟨hi.le, le_rfl⟩)
  have h := hc.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt ht
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, sub_zero] at h
  nlinarith

/-- A singular inward slope cannot occur at a constrained global minimum:
there is always a positive donor in the unit simplex. -/
lemma minimizer_not_inward_atBot [DecidableEq ι] {f : ι → ℝ → ℝ} {S : ℝ} {a₀ a : ι → ℝ}
    (hS : 0 ≤ S) (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    (hderiv : ∀ i, 0 < a i → DifferentiableAt ℝ (f i) (a i))
    {j : ι} (hj : a j = 0) :
    ¬ Tendsto (fun ε : ℝ => (f j ε - f j 0) / ε) (𝓝[>] 0) atBot := by
  intro hsing
  have hex : ∃ i, 0 < a i := by
    by_contra hn
    push Not at hn
    have hsum : (∑ i, a i) ≤ 0 := Finset.sum_nonpos fun i _ => hn i
    linarith [ha.2]
  obtain ⟨i, hi⟩ := hex
  have hij : i ≠ j := by intro he; subst i; linarith
  have hdi := (hderiv i hi).hasDerivAt
  have hd : HasDerivAt (fun ε : ℝ => f i (a i - ε)) (-deriv (f i) (a i)) 0 := by
    convert hdi.comp_of_eq 0 ((hasDerivAt_id 0).const_sub (a i)) (by simp) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | simp
  have hdl : Tendsto (fun ε : ℝ => (f i (a i - ε) - f i (a i)) / ε)
      (𝓝[>] 0) (𝓝 (-deriv (f i) (a i))) := by
    convert hd.tendsto_slope_zero_right using 1
    all_goals try with_reducible_and_instances rfl
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hbot := tendsto_atBot_add_const_right (𝓝[>] (0 : ℝ)) (2 * S) (hdl.add_atBot hsing)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      0 < ε ∧ ε ≤ a i ∧
      (f i (a i - ε) - f i (a i)) / ε + (f j ε - f j 0) / ε + 2 * S < 0 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_le_nhds hi).filter_mono nhdsWithin_le_nhds,
      hbot.eventually (eventually_lt_atBot 0)] with ε hε hεi hneg
    exact ⟨hε, hεi, hneg⟩
  obtain ⟨ε, hε, hεi, hneg⟩ := hev.exists
  have h := transfer_min_comparison hS ha hm hij ⟨hε.le, hεi⟩
  rw [hj, zero_add] at h
  have hmul := mul_neg_of_neg_of_pos hneg hε
  have hid : ((f i (a i - ε) - f i (a i)) / ε + (f j ε - f j 0) / ε + 2 * S) * ε =
      f i (a i - ε) - f i (a i) + (f j ε - f j 0) + 2 * S * ε := by
    field_simp
  rw [hid] at hmul
  linarith

/-- Complete minimizer feasibility reduction, using the genuine derivative and
singular endpoint properties of the source primitives. -/
lemma minimizer_feasible [DecidableEq ι]
    {f : ι → ℝ → ℝ} {a₀ a h η F B : ι → ℝ} {ct ell ηmax Cα CF S : ℝ}
    (ha : a ∈ simplex) (hm : IsMinOn (objective f S a₀) simplex a)
    (hh : ∀ i, 0 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hη : ∀ i, η i = ct * h i / ell) (hmax : ∀ i, η i ≤ ηmax)
    (hCa : 0 < Cα) (hCF : 0 ≤ CF) (hS : 0 < S)
    (hB0 : ∀ i, 0 ≤ B i) (hB : ∑ i, B i = S)
    (hF : ∀ i, 0 ≤ F i) (hFp : ∀ i, 0 < a i → 0 < F i)
    (hT : 0 < ∑ i, a i * h i)
    (hden : ∑ i, a i * F i ≤ CF * ∑ i, a i * h i)
    (hgap : 2 * CF * (1 + ηmax) < Cα * ct)
    (hderiv : ∀ i, 0 < a i → HasDerivAt (f i)
      (Cα * ell * ((S - (1 + η i) * B i / a i) / F i)) (a i))
    (hsing : ∀ i, a i = 0 → 0 < B i →
      Tendsto (fun ε : ℝ => (f i ε - f i 0) / ε) (𝓝[>] 0) atBot) :
    ∀ i, S * a i ≤ (1 + η i) * B i := by
  have hη0 : ∀ i, 0 ≤ η i := fun i => by
    rw [hη i]; exact div_nonneg (mul_nonneg hc.le (hh i)) hl.le
  have hz : ∀ i, a i = 0 → B i = 0 := by
    intro i hi
    by_contra hBi
    have hp : 0 < B i := lt_of_le_of_ne (hB0 i) (Ne.symm hBi)
    exact minimizer_not_inward_atBot hS.le ha hm
      (fun j hj => (hderiv j hj).differentiableAt) hi (hsing i hi hp)
  let γ : ι → ℝ := fun i => if 0 < a i then
    Cα * ell * ((S - (1 + η i) * B i / a i) / F i) else 0
  have hid : ∀ i, a i * F i / (1 + η i) * γ i =
      Cα * ell * (S * (a i / (1 + η i)) - B i) := by
    intro i
    by_cases hi : 0 < a i
    · have hηi : 1 + η i ≠ 0 := by linarith [hη0 i]
      dsimp [γ]; rw [ite_eq_left hi]
      field_simp [hi.ne', (hFp i hi).ne', hηi]
    · have hzero : a i = 0 := le_antisymm (le_of_not_gt hi) (ha.1 i)
      simp only [γ, ite_eq_right hi, hzero, hz i hzero, zero_mul, zero_div, mul_zero, sub_self]
  obtain ⟨j, hj⟩ := exists_negative_derivative ha hh hc hl hη hmax hCa hCF hS hB hF hT hden hgap hid
  have hjp : 0 < a j := by
    by_contra hjp
    simp only [γ, ite_eq_right hjp] at hj
    linarith
  intro i
  by_contra hbad
  have hbad' : (1 + η i) * B i < S * a i := lt_of_not_ge hbad
  have hi : 0 < a i := by
    have hp : 0 ≤ (1 + η i) * B i := mul_nonneg (by linarith [hη0 i]) (hB0 i)
    nlinarith
  have hγi : 0 < γ i := by
    dsimp [γ]; rw [ite_eq_left hi]
    apply mul_pos (mul_pos hCa hl)
    apply div_pos _ (hFp i hi)
    exact sub_pos.mpr ((div_lt_iff₀ hi).mpr hbad')
  have hij : i ≠ j := by intro he; subst i; linarith
  have h := minimizer_derivative_gap hS.le ha hm hij hi (hderiv i hi) (hderiv j hjp)
  have hei : γ i = Cα * ell * ((S - (1 + η i) * B i / a i) / F i) := ite_eq_left hi
  have hej : γ j = Cα * ell * ((S - (1 + η j) * B j / a j) / F j) := ite_eq_left hjp
  rw [← hei, ← hej] at h
  linarith

end KServer.SimplexTracker


namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic

variable {ι : Type*} [Fintype ι]

lemma simplex_weight_pos {a h : ι → ℝ} (ha : a ∈ simplex) (hh : ∀ i, 0 < h i) :
    0 < ∑ i, a i * h i := by
  have hex : ∃ i, 0 < a i := by
    by_contra hn
    push Not at hn
    have : (∑ i, a i) ≤ 0 := Finset.sum_nonpos fun i _ => hn i
    linarith [ha.2]
  obtain ⟨i, hi⟩ := hex
  exact lt_of_lt_of_le (mul_pos hi (hh i))
    (Finset.single_le_sum (fun j _ => mul_nonneg (ha.1 j) (hh j).le) (Finset.mem_univ i))

lemma log_inverse_nonneg_closed {a : ℝ} (ha : a ∈ Set.Icc 0 1) : 0 ≤ Real.log (1 / a) := by
  rcases eq_or_lt_of_le ha.1 with hz | hp
  · subst a; simp
  · exact log_inverse_nonneg ⟨hp, ha.2⟩

end KServer.Allocation


namespace KServer.SupportedAllocation
open scoped BigOperators
open Finset
variable {J : Type*} [Fintype J] [DecidableEq J]

def restrict (A : Finset J) (a : J → ℝ) : A → ℝ := fun i => a i

def extend (A : Finset J) (a : A → ℝ) : J → ℝ := fun i => if hi : i∈A then a ⟨i,hi⟩ else 0

omit [Fintype J] in
lemma extend_apply_mem (A : Finset J) (a : A → ℝ) (i : A) : extend A a i=a i := by
  simp [extend,i.property]

omit [Fintype J] in
lemma extend_apply_not_mem (A : Finset J) (a : A → ℝ) {i : J} (hi : i∉A) : extend A a i=0 := by
  simp [extend,hi]

omit [Fintype J] in
lemma restrict_extend (A : Finset J) (a : A → ℝ) : restrict A (extend A a)=a := by
  funext i; exact extend_apply_mem A a i

omit [DecidableEq J] in
lemma sum_restrict (A : Finset J) (a : J → ℝ) (ha : ∀ i∉A, a i=0) :
    (∑ i : A, a i)=∑ i, a i := by
  rw [←Finset.sum_subtype A (fun _ => Iff.rfl)]
  exact Finset.sum_subset (subset_univ A) fun i _ hi => ha i hi

lemma sum_extend (A : Finset J) (a : A → ℝ) : (∑ i, extend A a i)=∑ i, a i := by
  have he := sum_restrict A (extend A a) (fun i hi => extend_apply_not_mem A a hi)
  simpa only [extend_apply_mem] using he.symm

omit [DecidableEq J] in
lemma restrict_simplex {A : Finset J} (hA : A.Nonempty) {a : J → ℝ}
    (ha : a ∈ ChangingDomains.simplex A) : restrict A a ∈ SimplexTracker.simplex := by
  refine ⟨fun i => ha.1 i,?_⟩
  change (∑ i : A, a i)=1
  rw [sum_restrict A a ha.2.2,ha.2.1,ite_eq_left hA]

lemma extend_simplex {A : Finset J} (hA : A.Nonempty) {a : A → ℝ}
    (ha : a ∈ SimplexTracker.simplex) : extend A a ∈ ChangingDomains.simplex A := by
  refine ⟨?_,?_,fun i hi => extend_apply_not_mem A a hi⟩
  · intro i
    unfold extend
    split_ifs with hi
    · exact ha.1 ⟨i,hi⟩
    · exact le_rfl
  · rw [sum_extend,ite_eq_left hA]; exact ha.2

omit [DecidableEq J] in
lemma movement_restrict {A : Finset J} {a b : J → ℝ}
    (ha : ∀ i∉A, a i=0) (hb : ∀ i∉A, b i=0) :
    SimplexTracker.movement (restrict A a) (restrict A b)=ChangingDomains.variation a b := by
  apply sum_restrict A (fun i => |a i-b i|)
  intro i hi; simp [ha i hi,hb i hi]

omit [DecidableEq J] in
lemma potential_restrict {A : Finset J} {f : J → ℝ → ℝ} {a : J → ℝ}
    (ha : ∀ i∉A, a i=0) (hf : ∀ i∉A, f i 0=0) :
    SimplexTracker.potential (fun i : A => f i) (restrict A a)=∑ i, f i (a i) := by
  apply sum_restrict A (fun i => f i (a i))
  intro i hi; rw [ha i hi,hf i hi]

/-- Restriction is exact, including both the movement penalty and the literal
source potentials. No dummy inactive coordinate enters the denominator bound. -/
lemma restrict_isMin {A : Finset J} (hA : A.Nonempty) {f : J → ℝ → ℝ}
    {S : ℝ} {a a₀ : J → ℝ} (ha : a ∈ ChangingDomains.simplex A)
    (ha₀ : a₀ ∈ ChangingDomains.simplex A) (hf : ∀ i∉A, f i 0=0)
    (hm : IsMinOn (fun b => (∑ i, f i (b i))+S*ChangingDomains.variation b a₀)
      (ChangingDomains.simplex A) a) :
    IsMinOn (SimplexTracker.objective (fun i : A => f i) S (restrict A a₀))
      SimplexTracker.simplex (restrict A a) := by
  intro b hb
  have he := extend_simplex hA hb
  have hh := hm he
  change SimplexTracker.potential (fun i : A => f i) (restrict A a)+
      S*SimplexTracker.movement (restrict A a) (restrict A a₀) ≤
    SimplexTracker.potential (fun i : A => f i) b+S*SimplexTracker.movement b (restrict A a₀)
  rw [potential_restrict ha.2.2 hf,movement_restrict ha.2.2 ha₀.2.2]
  have hp := potential_restrict he.2.2 hf
  have hmove := movement_restrict he.2.2 ha₀.2.2
  rw [restrict_extend] at hp hmove
  rw [hp,hmove]
  exact hh

end KServer.SupportedAllocation

namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The feasibility argument holds for every attained minimizer, in particular
for the fixed noncomputable choice in the causal recurrence. -/
lemma every_simplex_minimizer_feasible
    {F : ι → ℝ → ℝ} {a₀ a h c B base : ι → ℝ} {ct ell ηmax Cα CF : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 0 < h i) (hc : 0 < ct) (hl : 0 < ell)
    (hmax : ∀ i, ct*h i/ell ≤ ηmax) (hCa : 0 < Cα) (hCF : 0 ≤ CF)
    (hB0 : ∀ i, 0 ≤ B i) (hb : ∀ i, base i ∈ Set.Icc 0 1)
    (hFc : ∀ i, Continuous (F i)) (hci : ∀ i, 0 < c i)
    (hF : ∀ i y, 0 ≤ y → c i*(1+y)^2 ≤ F i y)
    (hdecay : ∀ i, Tendsto (fun s : ℝ => s*F i (Real.log (1/s))) (𝓝[>] 0) (𝓝 0))
    (hden : ∀ b ∈ simplex, ∑ i, b i*F i (Real.log (1/b i)) ≤ CF*∑ i, b i*h i)
    (hgap : 2*CF*(1+ηmax) < Cα*ct)
    (hm : IsMinOn (objective (fun i => primitive (F i) Cα ell (ct*h i/ell)
      (∑ j, B j) (B i) (base i)) (∑ i, B i) a₀) simplex a) :
    ∀ i, (∑ j, B j)*a i ≤ (1+ct*h i/ell)*B i := by
  let S := ∑ i, B i
  let η := fun i => ct*h i/ell
  have hη : ∀ i, 0 ≤ η i := fun i => div_nonneg (mul_nonneg hc.le (hh i).le) hl.le
  have hp : ∀ i y, 0 ≤ y → 0 < F i y := fun i y hy =>
    (show 0 < c i*(1+y)^2 by have := hci i; positivity).trans_le (hF i y hy)
  have hint := fun i => singular_intervalIntegrable_of_quadratic (hFc i).measurable (hci i) (hF i)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hB0 i
  rcases eq_or_lt_of_le hS0 with hS | hS
  · intro i
    change S*a i ≤ (1+η i)*B i
    rw [←hS,zero_mul]
    exact mul_nonneg (by linarith [hη i]) (hB0 i)
  have hF0 : ∀ i, 0 ≤ F i (Real.log (1/a i)) := fun i =>
    (hp i _ (log_inverse_nonneg_closed ⟨ha.1 i,max_coordinate ha i⟩)).le
  apply minimizer_feasible ha hm (fun i => (hh i).le) hc hl (fun _ => rfl) hmax
    hCa hCF hS hB0 rfl hF0
    (fun i hi => hp i _ (log_inverse_nonneg ⟨hi,max_coordinate ha i⟩))
    (simplex_weight_pos ha hh) (hden a ha) hgap
  · intro i hi
    exact primitive_derivative (hFc i) (hp i) (hint i) Cα ell (η i) S (B i)
      (hb i) ⟨hi,max_coordinate ha i⟩
  · intro i _ hBi
    exact primitive_inward_atBot (hFc i) (hci i) (hF i) (hdecay i)
      hCa hl (hη i) hBi S (hb i)

end KServer.Allocation

namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma every_regular_minimizer_feasible
    {a₀ a h B : ι → ℝ} {ct ell ηmax Cα Cexp : ℝ}
    (ha : a ∈ simplex) (hh : ∀ i, 1≤h i) (hc : 0 < ct) (hl : 0<ell)
    (hmax : ∀ i, ct*h i/ell≤ηmax) (hCa : 0<Cα) (hB0 : ∀ i, 0≤B i)
    (hCexp : 0≤Cexp) (htail : ∑ i, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<Cα*ct)
    (hm : IsMinOn (objective (fun i => primitive (regularF (h i)) Cα ell (ct*h i/ell)
      (∑ j, B j) (B i) 0) (∑ i, B i) a₀) simplex a) :
    ∀ i, (∑ j, B j)*a i≤(1+ct*h i/ell)*B i := by
  apply every_simplex_minimizer_feasible (c := fun i => 1/h i) (CF := 25+32*Cexp)
    ha (fun i => by linarith [hh i]) hc hl hmax hCa (by positivity) hB0
    (fun _ => ⟨le_rfl,by norm_num⟩)
    (fun i => by unfold regularF; fun_prop)
    (fun i => by have := hh i; positivity)
    (fun i _ hy => regular_quadratic_lower (hh i) hy)
    (fun i => regular_decay (h i))
  · intro b hb; exact regular_denominator_sum hb.1 hb.2 hh htail
  · exact hgap
  · exact hm

end KServer.Allocation

namespace KServer.SupportedAllocation
open scoped BigOperators
open SimplexTracker SimplexAnalytic
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Uniform feasibility on the changing active domain. Its exp-tail hypothesis
is a sum over active children only, exactly as in the source. -/
lemma regular_supported_minimizer_feasible {A : Finset J} (hA : A.Nonempty)
    {a₀ a h B : J → ℝ} {ct ell ηmax Cα Cexp : ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ha₀ : a₀ ∈ ChangingDomains.simplex A)
    (hh : ∀ i∈A, 1≤h i) (hc : 0 < ct) (hl : 0<ell)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCa : 0<Cα) (hB0 : ∀ i, 0≤B i)
    (hBout : ∀ i∉A, B i=0) (hCexp : 0≤Cexp) (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<Cα*ct)
    (hm : IsMinOn (fun b => (∑ i, primitive (regularF (h i)) Cα ell (ct*h i/ell)
      (∑ j, B j) (B i) 0 (b i))+(∑ i, B i)*ChangingDomains.variation b a₀)
       (ChangingDomains.simplex A) a) :
    ∀ i, (∑ j, B j)*a i≤(1+ct*h i/ell)*B i := by
  have hsum : (∑ j : A, B j)=∑ j, B j := sum_restrict A B hBout
  have htail' : (∑ i : A, Real.exp (-h i))≤Cexp := by
    rw [←Finset.sum_subtype A (fun _ => Iff.rfl) (fun i => Real.exp (-h i))]
    exact htail
  have hm' := restrict_isMin hA ha ha₀ (fun i _ => by simp [primitive]) hm
  have he := Allocation.every_regular_minimizer_feasible
    (a₀ := restrict A a₀) (a := restrict A a) (h := fun i : A => h i) (B := fun i : A => B i)
    (restrict_simplex hA ha) (fun i => hh i i.property) hc hl (fun i => hmax i i.property)
    hCa (fun i => hB0 i) hCexp htail' hgap
  have hh' : ∀ i : A, (∑ j, B j)*a i≤(1+ct*h i/ell)*B i := by
    have hm'' : IsMinOn (objective (fun i : A => primitive (regularF (h i)) Cα ell (ct*h i/ell)
        (∑ j : A, B j) (B i) 0) (∑ i : A, B i) (restrict A a₀))
        simplex (restrict A a) := by simpa only [hsum] using hm'
    simpa only [hsum,restrict] using he hm''
  intro i
  by_cases hi : i∈A
  · exact hh' ⟨i,hi⟩
  · simp [ha.2.2 i hi,hBout i hi]

end KServer.SupportedAllocation

namespace KServer.Allocation
open Set Filter
open scoped BigOperators Topology
open SimplexTracker SimplexAnalytic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma every_marked_minimizer_feasible
    {a₀ a h B : ι → ℝ} {ct ell ηmax Cα Cexp c u H : ℝ} (o : ι)
    (ha : a ∈ simplex) (hu : 0 < u) (hu1 : u ≤ 1)
    (hH : H = 1 + Real.log (1 / u)) (ho : h o = u)
    (hh : ∀ i ≠ o, 1 ≤ h i) (hc : 0 < ct) (hl : 0 < ell)
    (hmax : ∀ i, ct * h i / ell ≤ ηmax) (hCa : 0 < Cα)
    (hB0 : ∀ i, 0 ≤ B i) (hCexp : 0 ≤ Cexp)
    (hsideC : 0 < c) (hsideC1 : c ≤ 1) (hside : ∀ i ≠ o, c * H ≤ h i)
    (htail : ∑ i ∈ Finset.univ.erase o, Real.exp (-h i) ≤ Cexp * u)
    (hgap : 2 * ((25 * c + 2 + 32 * Cexp) / c) * (1 + ηmax) < Cα * ct)
    (hm : IsMinOn (objective (fun i => primitive (if i = o then markedF u H else regularF (h i))
      Cα ell (ct*h i/ell) (∑ j, B j) (B i) (if i=o then 1 else 0))
      (∑ j, B j) a₀) simplex a) :
    ∀ i, (∑ j, B j)*a i ≤ (1+ct*h i/ell)*B i := by
  have hH1 : 1 ≤ H := by
    rw [hH]; linarith [log_inverse_nonneg ⟨hu, hu1⟩]
  have hHp : 0 < H := by linarith
  have hhp : ∀ i, 0 < h i := by
    intro i
    by_cases hi : i = o
    · simpa [hi, ho] using hu
    · linarith [hh i hi]
  obtain ⟨cm, hcm, hFm⟩ := marked_lower_constant hu hHp
  apply every_simplex_minimizer_feasible
    (F := fun i => if i=o then markedF u H else regularF (h i))
    (base := fun i => if i=o then 1 else 0)
    (c := fun i => if i = o then cm else 1 / h i)
    (CF := (25 * c + 2 + 32 * Cexp) / c) ha hhp hc hl hmax hCa
    (by positivity) hB0
  · intro i; split_ifs <;> norm_num
  · intro i
    split_ifs
    · unfold markedF; fun_prop
    · unfold regularF; fun_prop
  · intro i
    split_ifs
    · exact hcm
    · exact one_div_pos.mpr (hhp i)
  · intro i y hy
    by_cases hi : i = o
    · simpa [hi] using hFm y hy
    · simpa [hi] using regular_quadratic_lower (hh i hi) hy
  · intro i
    by_cases hi : i = o
    · simpa [hi] using marked_decay u H
    · simpa [hi] using regular_decay (h i)
  · intro a ha
    have hd := marked_denominator_sum o ha.1 ha.2 hu.le (hu1.trans hH1)
      hsideC hsideC1 hh hside hCexp htail
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
    simp only [ite_true]
    have hs : (∑ i ∈ Finset.univ.erase o,
        a i * (if i = o then markedF u H else regularF (h i)) (Real.log (1 / a i))) =
        ∑ i ∈ Finset.univ.erase o, a i * regularF (h i) (Real.log (1 / a i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_right (Finset.mem_erase.mp hi).1]
    rw [hs]
    have ht : (∑ i, a i * h i) = a o * u + ∑ i ∈ Finset.univ.erase o, a i * h i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o), ho]
    rw [ht]
    exact hd
  · exact hgap

  · exact hm

end KServer.Allocation

namespace KServer.SupportedAllocation
open SimplexTracker SimplexAnalytic
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Feasibility for the actual changing marked domain; inactive coordinates
are zero instead of being assigned a spurious positive denominator weight. -/
lemma marked_supported_minimizer_feasible {A : Finset J} {o : J} (hoA : o ∈ A)
    {a₀ a h B : J → ℝ} {ct ell ηmax Cα Cexp c u H : ℝ}
    (ha : a ∈ ChangingDomains.simplex A) (ha₀ : a₀ ∈ ChangingDomains.simplex A)
    (hu : 0 < u) (hu1 : u ≤ 1) (hH : H = 1 + Real.log (1 / u)) (ho : h o = u)
    (hh : ∀ i∈A, i ≠ o → 1 ≤ h i) (hc : 0 < ct) (hl : 0<ell)
    (hmax : ∀ i∈A, ct*h i/ell ≤ ηmax) (hCa : 0<Cα)
    (hB0 : ∀ i, 0≤B i) (hBout : ∀ i∉A, B i=0) (hCexp : 0≤Cexp)
    (hsideC : 0 < c) (hsideC1 : c≤1) (hside : ∀ i∈A, i≠o → c*H≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i) ≤ Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<Cα*ct)
    (hm : IsMinOn (fun b => (∑ i, primitive (if i=o then markedF u H else regularF (h i))
      Cα ell (ct*h i/ell) (∑ j, B j) (B i) (if i=o then 1 else 0) (b i))+
      (∑ i, B i)*ChangingDomains.variation b a₀) (ChangingDomains.simplex A) a) :
    ∀ i, (∑ j, B j)*a i ≤ (1+ct*h i/ell)*B i := by
  have hA : A.Nonempty := ⟨o,hoA⟩
  let o' : A := ⟨o,hoA⟩
  have hsum : (∑ j : A, B j)=∑ j, B j := sum_restrict A B hBout
  have hcon (i : A) : (i=o') ↔ ((i : J)=o) := Subtype.ext_iff
  have hm' := restrict_isMin hA ha ha₀
    (fun i hi => by simp [ite_eq_right (show i≠o by intro he; exact hi (he ▸ hoA)), primitive]) hm
  have htail' : (∑ i∈Finset.univ.erase o', Real.exp (-h (i : J))) ≤ Cexp*u := by
    have he : (∑ i∈Finset.univ.erase o', Real.exp (-h (i : J))) =
        ∑ i∈A.erase o, Real.exp (-h i) := by
      apply Finset.sum_bij (fun (i : A) (_ : i∈Finset.univ.erase o') => (i : J))
      · intro i hi
        exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hi).1
          (Subtype.ext he), i.property⟩
      · intro i _ j _ hij
        exact Subtype.ext hij
      · intro i hi
        refine ⟨⟨i,(Finset.mem_erase.mp hi).2⟩, ?_,rfl⟩
        exact Finset.mem_erase.mpr ⟨fun he => (Finset.mem_erase.mp hi).1
          (congrArg Subtype.val he),Finset.mem_univ _⟩
      · intro i _; rfl
    rw [he]; exact htail
  have hm'' : IsMinOn (objective (fun i : A => primitive
      (if i=o' then markedF u H else regularF (h i)) Cα ell (ct*h i/ell)
      (∑ j : A, B j) (B i) (if i=o' then 1 else 0))
      (∑ i : A, B i) (restrict A a₀)) simplex (restrict A a) := by
    simpa only [hcon,hsum] using hm'
  have he := Allocation.every_marked_minimizer_feasible o'
    (restrict_simplex hA ha) hu hu1 hH ho
    (fun i hi => hh i i.property (fun he => hi (Subtype.ext he))) hc hl
    (fun i => hmax i i.property) hCa (fun i => hB0 i) hCexp hsideC hsideC1
    (fun i hi => hside i i.property (fun he => hi (Subtype.ext he))) htail' hgap hm''
  intro i
  by_cases hi : i∈A
  · simpa only [hsum,restrict] using he ⟨i,hi⟩
  · simp [ha.2.2 i hi,hBout i hi]
end KServer.SupportedAllocation

/-! The literal two-stage update of §04: prepare with the new core flags on
common coordinates, minimize on the old simplex, transpose at exactly zero
cost, then minimize on the new simplex. The bounds below calculate its edit
charge from the actual flags and held parameters, not from an assumed drift
or policy bound. -/
namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

lemma update_isMin (C ell : ℝ) (d : Data J R) (p : J × R → ℝ) (c : ℝ) (a : J → ℝ) :
    IsMinOn (fun b => potential C ell d (core d p) b+c*ChangingDomains.variation b a)
      (ChangingDomains.simplex d.active) ((family C ell).update d p c a) := by
  have hm := ((family C ell).exists_update d p c a).choose_spec
  intro b hb
  have hm' := hm.2 hb
  change (family C ell).value d p ((family C ell).update d p c a)+c*movement ((family C ell).update d p c a) a ≤
    (family C ell).value d p b+c*movement b a at hm'
  rw [value_eq C ell d p ((family C ell).update d p c a)
      ((family C ell).update_mem d p c a), value_eq C ell d p b hb] at hm'
  exact hm'

lemma regular_update_feasible {A : Finset J} (hA : A.Nonempty)
    (f : J → R → Bool) (h : J → ℝ) (hh : ∀ i, 1≤h i)
    {C ell ct ηmax Cexp : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (htail : ∑ i∈A, Real.exp (-h i)≤Cexp)
    (hgap : 2*(25+32*Cexp)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (hf : ∀ i∉A, ∀ r, f i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d := regular A f h (fun i => ct*h i/ell) hh
    let B := core d p
    let a' := (family C ell).update d p (∑ i, B i) a
    ∀ i, (∑ j, B j)*a' i≤(1+ct*h i/ell)*B i := by
  intro d B a'
  have hB : ∀ i, 0≤B i := by
    intro i
    exact ChangingDomains.core_nonneg (fun i r => hp (i,r)) i
  have hBz : ∀ i∉A, B i=0 := by
    intro i hi
    simp [B,core,d,regular,hf i hi]
  apply SupportedAllocation.regular_supported_minimizer_feasible hA
    ((family C ell).update_mem d p (∑ i, B i) a) ha
    (fun i _ => hh i) hc hl hmax hC hB hBz hCexp htail hgap
  exact update_isMin C ell d p (∑ i, B i) a

/-- The prepared input is concrete and uses only new flags on the common
old/new active domain, as in §04 (not intersection of old and new flags). -/
def preparedFlags (A B : Finset J) (g : J → R → Bool) : J → R → Bool :=
  ChangingDomains.syntheticFlags A B g

def preparedInput (A B : Finset J) (g : J → R → Bool) (p : J × R → ℝ) : J → ℝ :=
  ChangingDomains.core (preparedFlags A B g) (fun i r => p (i,r))

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

/-- This is the prepared minimizer from the manuscript; no drift inequality
is an input to its definition. -/
def regularPrepare (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (h : J → ℝ) (hh : ∀ i, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update (regular A (preparedFlags A B g) h (fun i => ct*h i/ell) hh)
    p (∑ i, preparedInput A B g p i) a

/-- Delete and insert zero coordinates following the prepared minimizing
update, with a canonical simplex state only when its weight is exactly zero. -/
def regularTransport (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (h : J → ℝ) (hh : ∀ i, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSimplex B (∑ i, preparedInput A B g p i)
    (regularPrepare C ell ct A B g h hh p a)

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

/-- The final update after genuine preparation and transport. -/
def regularStep (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (h h' : J → ℝ) (hh : ∀ i, 1≤h i) (hh' : ∀ i, 1≤h' i)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update (regular B g h' (fun i => ct*h' i/ell) hh') p
    (∑ i, ChangingDomains.core g (fun i r => p (i,r)) i)
    (regularTransport C ell ct A B g h hh p a)

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

lemma marked_update_feasible {A : Finset J} {o : J} (hoA : o∈A)
    (f : J → R → Bool) (h : J → ℝ) {u : ℝ} (hu : 0<u) (hu1 : u≤1)
    (ho : h o=u) (hh : ∀ i≠o, 1≤h i)
    {C ell ct ηmax Cexp c : ℝ} (hC : 0<C) (hl : 0<ell) (hc : 0 < ct)
    (hmax : ∀ i∈A, ct*h i/ell≤ηmax) (hCexp : 0≤Cexp)
    (hsideC : 0 < c) (hsideC1 : c≤1)
    (hside : ∀ i∈A, i≠o → c*(1+Real.log (1/u))≤h i)
    (htail : ∑ i∈A.erase o, Real.exp (-h i)≤Cexp*u)
    (hgap : 2*((25*c+2+32*Cexp)/c)*(1+ηmax)<C*ct)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir) (hf : ∀ i∉A, ∀ r, f i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex A) :
    let d := marked A f o h (fun i => ct*h i/ell) u hu hu1 hh
    let B := core d p
    let a' := (family C ell).update d p (∑ i, B i) a
    ∀ i, (∑ j, B j)*a' i≤(1+ct*h i/ell)*B i := by
  intro d B a'
  have hB : ∀ i, 0≤B i := fun i => ChangingDomains.core_nonneg (fun i r => hp (i,r)) i
  have hBz : ∀ i∉A, B i=0 := by
    intro i hi
    simp [B,core,d,marked,hf i hi]
  apply SupportedAllocation.marked_supported_minimizer_feasible hoA
    ((family C ell).update_mem d p (∑ i, B i) a) ha hu hu1 rfl ho
    (fun i _ hi => hh i hi) hc hl hmax hC hB hBz hCexp hsideC hsideC1 hside htail hgap
  exact update_isMin C ell d p (∑ i, B i) a

end KServer.AdaptiveAllocation

namespace KServer.AdaptiveAllocation
open Finset SimplexAnalytic SimplexFamilies AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

def markedPrepare (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (o : J) (h : J → ℝ) (u : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hh : ∀ i≠o, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update
    (marked A (preparedFlags A B g) o h (fun i => ct*h i/ell) u hu hu1 hh)
    p (∑ i, preparedInput A B g p i) a

def markedTransport (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (o : J) (h : J → ℝ) (u : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hh : ∀ i≠o, 1≤h i) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSimplex B (∑ i, preparedInput A B g p i)
    (markedPrepare C ell ct A B g o h u hu hu1 hh p a)

def markedStep (C ell ct : ℝ) (A B : Finset J) (g : J → R → Bool)
    (o : J) (h h' : J → ℝ) (u u' : ℝ) (hu : 0<u) (hu1 : u≤1)
    (hu' : 0<u') (hu1' : u'≤1) (hh : ∀ i≠o, 1≤h i) (hh' : ∀ i≠o, 1≤h' i)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family C ell).update (marked B g o h' (fun i => ct*h' i/ell) u' hu' hu1' hh') p
    (∑ i, ChangingDomains.core g (fun i r => p (i,r)) i)
    (markedTransport C ell ct A B g o h u hu hu1 hh p a)

end KServer.AdaptiveAllocation

/-! Exact side primitive and compact minimizing update of §04,
    eq:side-primitive-explicit and lem:side-tracker. This is an allocation
    dependency of the absent main, not a separately counted main theorem. -/
noncomputable section
open scoped BigOperators
open Set Filter
namespace KServer.SideTracker

/-- The explicit integral in eq:side-primitive-explicit. -/
def primitive (c b θ z B D w : ℝ) : ℝ :=
  c * (D / θ * (w - z * Real.log (1 + w / z)) +
    D * z * Real.log (1 + w / z) / 2 -
    (b + θ / 2) * B * Real.log (1 + w / z) / θ)

lemma primitive_derivative {c b θ z B D w : ℝ} (hθ : 0 < θ) (hz : 0 < z)
    (hw : 0 ≤ w) :
    HasDerivAt (primitive c b θ z B D)
      (c * (D * w - (b + θ / 2) * B + D * θ * z / 2) /
        (θ * (w + z))) w := by
  have hl : 0 < 1 + w / z := by positivity
  have hd := (((hasDerivAt_id w).div_const z).const_add 1).log hl.ne'
  have he : 1 / z / (1 + w / z) = 1 / (w + z) := by
    field_simp
    ring
  simp only [id_eq] at hd
  rw [he] at hd
  have H := ((((hasDerivAt_id w).sub (hd.const_mul z)).const_mul (D / θ)).add
    ((hd.const_mul (D * z)).div_const 2)).sub
      ((hd.const_mul ((b + θ / 2) * B)).div_const θ)
  have hwz : w + z ≠ 0 := by positivity
  have he' : c * (D * w - (b + θ / 2) * B + D * θ * z / 2) / (θ * (w + z)) =
      c * (D / θ * (1 - z * (1 / (w + z))) + D * z * (1 / (w + z)) / 2 -
        (b + θ / 2) * B * (1 / (w + z)) / θ) := by
    field_simp [hθ.ne', hwz]
    ring
  rw [he']
  exact H.const_mul c

/-- One-sided necessary optimality, allowing a nondifferentiable movement cost. -/
lemma derivative_le_of_left_comparison {f : ℝ → ℝ} {f' D x : ℝ}
    (hx : 0 < x) (hd : HasDerivAt f f' x)
    (hc : ∀ y ∈ Set.Icc 0 x, f x ≤ f y + D * (x - y)) : f' ≤ D := by
  have hm : IsLocalMinOn (fun y => f y - D * y) (Set.Icc 0 x) x := by
    apply IsMinOn.localize
    intro y hy
    have h := hc y hy
    change f x - D * x ≤ f y - D * y
    linarith
  have ht : 0 - x ∈ posTangentConeAt (Set.Icc 0 x) x :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 x).segment_subset ⟨hx.le, le_rfl⟩ ⟨le_rfl, hx.le⟩)
  have h := hm.hasFDerivWithinAt_nonneg
    ((hd.sub ((hasDerivAt_id x).const_mul D)).hasFDerivAt.hasFDerivWithinAt) ht
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  nlinarith

lemma neg_derivative_le_of_right_comparison {f : ℝ → ℝ} {f' D x ε : ℝ}
    (hε : 0 < ε) (hd : HasDerivAt f f' x)
    (hc : ∀ y ∈ Set.Icc x (x + ε), f x ≤ f y + D * (y - x)) : -D ≤ f' := by
  have hm : IsLocalMinOn (fun y => f y + D * y) (Set.Icc x (x + ε)) x := by
    apply IsMinOn.localize
    intro y hy
    have h := hc y hy
    change f x + D * x ≤ f y + D * y
    linarith
  have ht : (x + ε) - x ∈ posTangentConeAt (Set.Icc x (x + ε)) x :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc x (x + ε)).segment_subset ⟨le_rfl, by linarith⟩
        ⟨by linarith, le_rfl⟩)
  have h := hm.hasFDerivWithinAt_nonneg
    ((hd.add ((hasDerivAt_id x).const_mul D)).hasFDerivAt.hasFDerivWithinAt) ht
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
  nlinarith

variable {ι : Type*} [Fintype ι]

def domain (Cw : ℝ) : Set (ι → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i ≤ Cw}

def potential (c b : ℝ) (θ z B : ι → ℝ) (D : ℝ) (w : ι → ℝ) : ℝ :=
  ∑ i, primitive c b (θ i) (z i) (B i) D (w i)

def movement (w v : ι → ℝ) : ℝ := ∑ i, |w i - v i|

def objective (c b : ℝ) (θ z B : ι → ℝ) (D : ℝ) (w₀ w : ι → ℝ) : ℝ :=
  potential c b θ z B D w + D * movement w w₀

lemma domain_isCompact (Cw : ℝ) : IsCompact (domain (ι := ι) Cw) := by
  have hc : IsClosed (domain (ι := ι) Cw) := by
    change IsClosed ({w : ι → ℝ | ∀ i, 0 ≤ w i} ∩ {w : ι → ℝ | ∑ i, w i ≤ Cw})
    apply IsClosed.inter
    · simp only [ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  apply (isCompact_pi_infinite fun _ : ι => isCompact_Icc (a := (0 : ℝ)) (b := Cw)).of_isClosed_subset hc
  intro w hw i
  exact ⟨hw.1 i, (Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)).trans hw.2⟩

lemma primitive_continuousOn {c b θ z B D : ℝ} (hθ : 0 < θ) (hz : 0 < z) :
    ContinuousOn (primitive c b θ z B D) (Ici 0) := by
  intro w hw
  exact (primitive_derivative hθ hz hw).continuousAt.continuousWithinAt

lemma sum_replace [DecidableEq ι] (f : ι → ℝ → ℝ) (w : ι → ℝ) (i : ι) (y : ℝ) :
    (∑ j, f j (Function.update w i y j)) = (∑ j, f j (w j)) - f i (w i) + f i y := by
  have he : (∑ j ∈ Finset.univ.erase i, f j (Function.update w i y j)) =
      ∑ j ∈ Finset.univ.erase i, f j (w j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, (Finset.mem_erase.mp hj).1]
  have h₁ := Finset.sum_erase_add Finset.univ (fun j => f j (Function.update w i y j))
    (Finset.mem_univ i)
  have h₂ := Finset.sum_erase_add Finset.univ (fun j => f j (w j)) (Finset.mem_univ i)
  simp only [Function.update_self, he] at h₁
  linarith

lemma replace_mem_domain [DecidableEq ι] {Cw : ℝ} {w : ι → ℝ}
    (hw : w ∈ domain Cw) (i : ι) {y : ℝ} (hy : 0 ≤ y)
    (hs : y ≤ w i + (Cw - ∑ j, w j)) : Function.update w i y ∈ domain Cw := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hy
    · simpa [Function.update, h] using hw.1 j
  · rw [sum_replace (fun _ x => x)]
    linarith

lemma coordinate_min_comparison [DecidableEq ι] {c b D Cw : ℝ} {θ z B w₀ w : ι → ℝ}
    (hD : 0 ≤ D)
    (hm : IsMinOn (objective c b θ z B D w₀) (domain Cw) w)
    (i : ι) {y : ℝ} (hy : Function.update w i y ∈ domain Cw) :
    primitive c b (θ i) (z i) (B i) D (w i) ≤
      primitive c b (θ i) (z i) (B i) D y + D * |y - w i| := by
  have h := hm hy
  change potential c b θ z B D w + D * movement w w₀ ≤
    potential c b θ z B D (Function.update w i y) +
      D * movement (Function.update w i y) w₀ at h
  dsimp [potential, movement] at h
  rw [sum_replace (fun j x => primitive c b (θ j) (z j) (B j) D x),
    sum_replace (fun j x => |x - w₀ j|)] at h
  have ht := mul_le_mul_of_nonneg_left (abs_sub_le y (w i) (w₀ i)) hD
  linarith

lemma derivative_upper_violation {M b θ z B D w : ℝ}
    (hb : 1 ≤ b) (hθ : 0 < θ) (hz : 0 < z) (hB : 0 ≤ B)
    (hD : 0 < D) (hw : 0 ≤ w) (hM : b + θ ≤ M)
    (hv : (b + θ) * B < D * w) :
    D < 8 * M * (D * w - (b + θ / 2) * B + D * θ * z / 2) / (θ * (w + z)) := by
  let N := D * w - (b + θ / 2) * B + D * θ * z / 2
  have hN : 0 < N := by
    dsimp [N]
    nlinarith [mul_nonneg hθ.le hB, mul_pos (mul_pos hD hθ) hz]
  have h1 : D * θ * w + D * θ * (b + θ) * z < 2 * (b + θ) * N := by
    have hh : 0 < (2 * b + θ) * (D * w - (b + θ) * B) :=
      mul_pos (by linarith) (sub_pos.mpr hv)
    dsimp [N]
    nlinarith
  have h2 : D * θ * (w + z) ≤ D * θ * w + D * θ * (b + θ) * z := by
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ b + θ by linarith)
      (mul_nonneg (mul_nonneg hD.le hθ.le) hz.le)
    nlinarith
  have h3 : 2 * (b + θ) * N ≤ 8 * M * N := by
    have hh := mul_le_mul_of_nonneg_right hM hN.le
    nlinarith [mul_pos (show 0 < M by linarith) hN]
  apply (lt_div_iff₀ (mul_pos hθ (by linarith : 0 < w + z))).mpr
  dsimp [N] at h2 h1 h3
  nlinarith [h2.trans_lt (h1.trans_le h3)]

lemma derivative_lower_violation {M b θ z B D w : ℝ}
    (hb : 1 ≤ b) (hθ : 0 < θ) (hz : 0 < z)
    (hD : 0 < D) (hw : 0 ≤ w) (hM : b + θ ≤ M)
    (hv : D * w < b * B - θ * z * D) :
    8 * M * (D * w - (b + θ / 2) * B + D * θ * z / 2) / (θ * (w + z)) < -D := by
  let N := D * w - (b + θ / 2) * B + D * θ * z / 2
  have hB : 0 < B := by
    have : 0 < b * B := by nlinarith [mul_nonneg hD.le hw, mul_pos (mul_pos hθ hz) hD]
    exact (mul_pos_iff.mp this).resolve_right (by rintro ⟨h, _⟩; linarith) |>.2
  have hN : N < 0 := by
    dsimp [N]
    nlinarith [mul_pos hθ hB, mul_pos (mul_pos hD hθ) hz]
  have h1 : 2 * b * N < -(D * θ * w + D * θ * b * z) := by
    have hh : 0 < (2 * b + θ) * (b * B - D * w - θ * z * D) :=
      mul_pos (by linarith) (by linarith)
    dsimp [N]
    nlinarith [mul_pos (mul_pos (mul_pos hD hθ) hθ) hz]
  have h2 : -(D * θ * w + D * θ * b * z) ≤ -(D * θ * (w + z)) := by
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg hD.le hθ.le) hz.le)
    nlinarith
  have h3 : 8 * M * N ≤ 2 * b * N := by
    have hh := mul_le_mul_of_nonpos_right (show b ≤ M by linarith) hN.le
    nlinarith [mul_neg_of_pos_of_neg (show 0 < M by linarith) hN]
  apply (div_lt_iff₀ (mul_pos hθ (by linarith : 0 < w + z))).mpr
  dsimp [N] at h1 h3
  nlinarith [h3.trans_lt (h1.trans_le h2)]

/-- Every minimizing update has the source's upper side feasibility. -/
lemma minimizer_upper {M b D Cw : ℝ} {θ z B w₀ w : ι → ℝ}
    (hb : 1 ≤ b) (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i)
    (hB : ∀ i, 0 ≤ B i) (hD : 0 ≤ D) (hM : ∀ i, b + θ i ≤ M)
    (hw : w ∈ domain Cw)
    (hm : IsMinOn (objective (8 * M) b θ z B D w₀) (domain Cw) w) :
    ∀ i, D * w i ≤ (b + θ i) * B i := by
  classical
  intro i
  by_cases hD0 : D = 0
  · rw [hD0, zero_mul]
    exact mul_nonneg (by linarith [hθ i]) (hB i)
  have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
  by_contra h
  have hv := lt_of_not_ge h
  have hwi : 0 < w i := by
    nlinarith [mul_nonneg (show 0 ≤ b + θ i by linarith [hθ i]) (hB i)]
  have hc : ∀ y ∈ Set.Icc 0 (w i),
      primitive (8 * M) b (θ i) (z i) (B i) D (w i) ≤
        primitive (8 * M) b (θ i) (z i) (B i) D y + D * (w i - y) := by
    intro y hy
    have hh := coordinate_min_comparison hD hm i
      (replace_mem_domain hw i hy.1 (by linarith [hw.2, hy.2]))
    rw [abs_of_nonpos (sub_nonpos.mpr hy.2)] at hh
    linarith
  have hder := derivative_le_of_left_comparison hwi
    (primitive_derivative (c := 8 * M) (b := b) (B := B i) (D := D)
      (hθ i) (hz i) (hw.1 i)) hc
  have hvder := derivative_upper_violation hb (hθ i) (hz i) (hB i) hDp
    (hw.1 i) (hM i) hv
  linarith

/-- The lower bound uses the slack proved from the upper bound, not a new
    assumption that the simplex constraint is inactive. -/
lemma minimizer_lower {M b D Cw : ℝ} {θ z B w₀ w : ι → ℝ}
    (hb : 1 ≤ b) (hθ : ∀ i, 0 < θ i) (hz : ∀ i, 0 < z i)
    (hB : ∀ i, 0 ≤ B i) (hD : 0 ≤ D) (hM : ∀ i, b + θ i ≤ M)
    (hCw : 2 * M < Cw) (hS : ∑ i, B i ≤ 2 * D)
    (hw : w ∈ domain Cw)
    (hm : IsMinOn (objective (8 * M) b θ z B D w₀) (domain Cw) w) :
    ∀ i, b * B i - θ i * z i * D ≤ D * w i := by
  classical
  intro i
  by_cases hD0 : D = 0
  · have hBi : B i = 0 := by
      have hh := Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ i)
      rw [hD0, mul_zero] at hS
      linarith [hB i]
    simp [hD0, hBi]
  have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
  have hupper := minimizer_upper hb hθ hz hB hD hM hw hm
  have hs : ∑ j, w j ≤ 2 * M := by
    have hs₁ : D * ∑ j, w j ≤ M * ∑ j, B j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => (hupper j).trans
        (mul_le_mul_of_nonneg_right (hM j) (hB j))
    have hMp : 0 ≤ M := by linarith [hM i, hθ i]
    have hh := mul_le_mul_of_nonneg_left hS hMp
    nlinarith
  have hgap : 0 < Cw - ∑ j, w j := by linarith
  have hc : ∀ y ∈ Set.Icc (w i) (w i + (Cw - ∑ j, w j)),
      primitive (8 * M) b (θ i) (z i) (B i) D (w i) ≤
        primitive (8 * M) b (θ i) (z i) (B i) D y + D * (y - w i) := by
    intro y hy
    have hh := coordinate_min_comparison hD hm i
      (replace_mem_domain hw i ((hw.1 i).trans hy.1) hy.2)
    rwa [abs_of_nonneg (sub_nonneg.mpr hy.1)] at hh
  have hder := neg_derivative_le_of_right_comparison hgap
    (primitive_derivative (c := 8 * M) (b := b) (B := B i) (D := D)
      (hθ i) (hz i) (hw.1 i)) hc
  by_contra h
  have hvder := derivative_lower_violation hb (hθ i) (hz i) hDp
    (hw.1 i) (hM i) (lt_of_not_ge h)
  linarith

end KServer.SideTracker

namespace KServer.SideTracker
open scoped BigOperators

/-- Coefficients of the actual primitive; all are nonnegative on the side
    domain. Their estimates use size-derived logarithmic cancellation. -/
def Dcoef (c θ z w : ℝ) : ℝ :=
  c * ((w - z * Real.log (1 + w / z)) / θ + z * Real.log (1 + w / z) / 2)
def Bcoef (c b θ z w : ℝ) : ℝ :=
  c * (b + θ / 2) * Real.log (1 + w / z) / θ

lemma primitive_coefficients (c b θ z B D w : ℝ) :
    primitive c b θ z B D w = Dcoef c θ z w * D - Bcoef c b θ z w * B := by
  unfold primitive Dcoef Bcoef
  ring

end KServer.SideTracker

namespace KServer.SideSupported
open Finset
variable {J : Type*} [Fintype J] [DecidableEq J]
def restrict (A : Finset J) (a : J → ℝ) : A → ℝ := fun i => a i

def extend (A : Finset J) (a : A → ℝ) : J → ℝ := fun i => if hi : i∈A then a ⟨i,hi⟩ else 0

omit [Fintype J] in
lemma extend_apply_mem (A : Finset J) (a : A → ℝ) (i : A) : extend A a i=a i := by
  simp [extend,i.property]

omit [Fintype J] in
lemma extend_apply_not_mem (A : Finset J) (a : A → ℝ) {i : J} (hi : i∉A) : extend A a i=0 := by
  simp [extend,hi]

omit [Fintype J] in
lemma restrict_extend (A : Finset J) (a : A → ℝ) : restrict A (extend A a)=a := by
  funext i; exact extend_apply_mem A a i

omit [DecidableEq J] in
lemma sum_restrict (A : Finset J) (a : J → ℝ) (ha : ∀ i∉A, a i=0) :
    (∑ i : A, a i)=∑ i, a i := by
  rw [←Finset.sum_subtype A (fun _ => Iff.rfl)]
  exact Finset.sum_subset (subset_univ A) fun i _ hi => ha i hi

lemma sum_extend (A : Finset J) (a : A → ℝ) : (∑ i, extend A a i)=∑ i, a i := by
  have he := sum_restrict A (extend A a) (fun i hi => extend_apply_not_mem A a hi)
  simpa only [extend_apply_mem] using he.symm


end KServer.SideSupported

namespace KServer.SideSupported
open Finset SideTracker
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma restrict_mem {A : Finset J} {W : ℝ} {a : J → ℝ}
    (ha : a∈ChangingDomains.sideDomain A W) : restrict A a∈domain W := by
  refine ⟨fun i => ha.1 i, ?_⟩
  simpa only [restrict,sum_restrict A a ha.2.2] using ha.2.1

lemma extend_mem {A : Finset J} {W : ℝ} {a : A → ℝ}
    (ha : a∈domain W) : extend A a∈ChangingDomains.sideDomain A W := by
  refine ⟨?_,?_,?_⟩
  · intro i
    simp only [extend]
    split_ifs with hi
    · exact ha.1 ⟨i,hi⟩
    · exact le_rfl
  · simpa only [sum_extend] using ha.2
  · exact fun i hi => extend_apply_not_mem A a hi

omit [DecidableEq J] in
lemma sideDomain_compact (A : Finset J) (W : ℝ) :
    IsCompact (ChangingDomains.sideDomain A W) := by
  have he : ChangingDomains.sideDomain A W=
      (domain W)∩{a : J → ℝ | ∀ i∉A, a i=0} := by
    ext a
    simp only [ChangingDomains.sideDomain,domain,Set.mem_ofPred_eq,Set.mem_inter_iff]
    tauto
  rw [he]
  apply IsCompact.inter_right (domain_isCompact W)
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const

omit [DecidableEq J] in
lemma movement_restrict {A : Finset J} {a b : J → ℝ}
    (ha : ∀ i∉A, a i=0) (hb : ∀ i∉A, b i=0) :
    movement (restrict A a) (restrict A b)=ChangingDomains.variation a b := by
  exact sum_restrict A (fun i => |a i-b i|) (fun i hi => by simp [ha i hi,hb i hi])

omit [DecidableEq J] in
lemma potential_restrict {A : Finset J} {c b D : ℝ} {θ z B a : J → ℝ}
    (ha : ∀ i∉A, a i=0) :
    potential c b (restrict A θ) (restrict A z) (restrict A B) D (restrict A a)=
      potential c b θ z B D a := by
  unfold potential restrict
  exact sum_restrict A (fun i => primitive c b (θ i) (z i) (B i) D (a i))
    (fun i hi => by simp [ha i hi,primitive])

lemma restrict_isMin {A : Finset J} {c b D W : ℝ} {θ z B a a₀ : J → ℝ}
    (ha : a∈ChangingDomains.sideDomain A W) (ha₀ : a₀∈ChangingDomains.sideDomain A W)
    (hm : IsMinOn (fun v => potential c b θ z B D v+D*ChangingDomains.variation v a₀)
      (ChangingDomains.sideDomain A W) a) :
    IsMinOn (objective c b (restrict A θ) (restrict A z) (restrict A B) D (restrict A a₀))
      (domain W) (restrict A a) := by
  intro v hv
  have he := extend_mem hv
  have hh := hm he
  change potential c b (restrict A θ) (restrict A z) (restrict A B) D (restrict A a)+
    D*movement (restrict A a) (restrict A a₀) ≤
    potential c b (restrict A θ) (restrict A z) (restrict A B) D v+
    D*movement v (restrict A a₀)
  rw [potential_restrict ha.2.2,movement_restrict ha.2.2 ha₀.2.2]
  have hp := potential_restrict (c := c) (b := b) (D := D) (θ := θ) (z := z) (B := B) he.2.2
  have hmove := movement_restrict he.2.2 ha₀.2.2
  rw [restrict_extend] at hp hmove
  rw [hp,hmove]
  exact hh

lemma supported_feasible {A : Finset J} {M b D W : ℝ} {θ z B a a₀ : J → ℝ}
    (ha : a∈ChangingDomains.sideDomain A W) (ha₀ : a₀∈ChangingDomains.sideDomain A W)
    (hb : 1≤b) (hθ : ∀ i, 0<θ i) (hz : ∀ i, 0<z i)
    (hB : ∀ i, 0≤B i) (hBz : ∀ i∉A, B i=0) (hD : 0≤D)
    (hM : ∀ i∈A, b+θ i≤M) (hW : 2*M<W)
    (hm : IsMinOn (fun v => potential (8*M) b θ z B D v+D*ChangingDomains.variation v a₀)
      (ChangingDomains.sideDomain A W) a) :
    (∀ i, D*a i≤(b+θ i)*B i) ∧
      ((∑ i, B i)≤2*D → ∀ i, b*B i-θ i*z i*D≤D*a i) := by
  have hm' := restrict_isMin ha ha₀ hm
  have hupper := minimizer_upper hb (fun i : A => hθ i) (fun i : A => hz i)
    (fun i : A => hB i) hD (fun i : A => hM i i.property) (restrict_mem ha) hm'
  constructor
  · intro i
    by_cases hi : i∈A
    · exact hupper ⟨i,hi⟩
    · simp [ha.2.2 i hi,hBz i hi]
  · intro hS
    have hS' : (∑ i : A, B i)≤2*D := by simpa only [sum_restrict A B hBz] using hS
    have hlower := minimizer_lower hb (fun i : A => hθ i) (fun i : A => hz i)
      (fun i : A => hB i) hD (fun i : A => hM i i.property) hW hS' (restrict_mem ha) hm'
    intro i
    by_cases hi : i∈A
    · exact hlower ⟨i,hi⟩
    · simp only [ha.2.2 i hi,hBz i hi,mul_zero,zero_sub]
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (hθ i).le (hz i).le) hD)

end KServer.SideSupported

namespace KServer.SideFamilies
open Finset SideTracker AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

structure Data (J R : Type*) where
  active : Finset J
  flags : J → R → Bool
  W : ℝ
  b : ℝ
  D : ℝ
  θ : J → ℝ
  z : J → ℝ
  W_nonneg : 0≤W
  θ_pos : ∀ i, 0<θ i
  z_pos : ∀ i, 0<z i

def core (d : Data J R) (p : J × R → ℝ) (i : J) : ℝ :=
  ∑ r, if d.flags i r then p (i,r) else 0

def coefficient (c : ℝ) (d : Data J R) (a : J → ℝ) (ir : J × R) : ℝ :=
  if d.flags ir.1 ir.2 then -Bcoef c d.b (d.θ ir.1) (d.z ir.1) (a ir.1) else 0

def offset (c : ℝ) (d : Data J R) (a : J → ℝ) : ℝ :=
  d.D * ∑ i, Dcoef c (d.θ i) (d.z i) (a i)

lemma Dcoef_continuousOn {c θ z : ℝ} (hθ : 0<θ) (hz : 0<z) :
    ContinuousOn (Dcoef c θ z) (Set.Ici 0) := by
  have he : Dcoef c θ z=primitive c 0 θ z 0 1 := by
    funext w
    unfold Dcoef primitive
    ring
  rw [he]
  exact primitive_continuousOn hθ hz

lemma Bcoef_continuousOn {c b θ z : ℝ} (hθ : 0<θ) (hz : 0<z) :
    ContinuousOn (Bcoef c b θ z) (Set.Ici 0) := by
  have he : Bcoef c b θ z=fun w => -primitive c b θ z 1 0 w := by
    funext w
    unfold Bcoef primitive
    ring
  rw [he]
  exact (primitive_continuousOn hθ hz).neg

omit [DecidableEq J] [Fintype R] in
lemma coefficient_continuous (c : ℝ) (d : Data J R) (ir : J × R) :
    ContinuousOn (fun a => coefficient c d a ir) (ChangingDomains.sideDomain d.active d.W) := by
  unfold coefficient
  split_ifs
  · exact ((Bcoef_continuousOn (d.θ_pos ir.1) (d.z_pos ir.1)).comp
      (continuous_apply ir.1).continuousOn (fun a ha => ha.1 ir.1)).neg
  · exact continuousOn_const

omit [DecidableEq J] [Fintype R] in
lemma offset_continuous (c : ℝ) (d : Data J R) :
    ContinuousOn (offset c d) (ChangingDomains.sideDomain d.active d.W) := by
  unfold offset
  apply ContinuousOn.const_mul
  exact continuousOn_finsetSum _ fun i _ =>
    (Dcoef_continuousOn (d.θ_pos i) (d.z_pos i)).comp
      (continuous_apply i).continuousOn (fun a ha => ha.1 i)

def family (c : ℝ) : Family (Data J R) (J × R) J where
  domain d := ChangingDomains.sideDomain d.active d.W
  compact d := SideSupported.sideDomain_compact d.active d.W
  seed d := ⟨fun _ => 0,by
    refine ⟨fun _ => le_rfl,?_,fun _ _ => rfl⟩
    simpa using d.W_nonneg⟩
  offset := offset c
  coefficient := coefficient c
  offset_continuous := offset_continuous c
  coefficient_continuous := coefficient_continuous c

omit [DecidableEq J] in
lemma value_eq (c : ℝ) (d : Data J R) (p : J × R → ℝ) (a : J → ℝ) :
    (family c).value d p a=potential c d.b d.θ d.z (core d p) d.D a := by
  simp only [Family.value,family,offset,coefficient,potential]
  rw [Fintype.sum_prod_type]
  have hi (i : J) : (∑ r, (if d.flags i r then -Bcoef c d.b (d.θ i) (d.z i) (a i) else 0)*p (i,r))=
      -Bcoef c d.b (d.θ i) (d.z i) (a i)*core d p i := by
    rw [core,mul_sum]
    exact sum_congr rfl fun r _ => by split_ifs <;> simp_all
  simp_rw [hi,primitive_coefficients]
  rw [mul_sum,←sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

lemma update_feasible (d : Data J R) {M : ℝ} (hb : 1≤d.b) (hD : 0≤d.D)
    (hM : ∀ i∈d.active, d.b+d.θ i≤M) (hW : 2*M<d.W)
    (p : J × R → ℝ) (hp : ∀ ir, 0≤p ir)
    (hf : ∀ i∉d.active, ∀ r, d.flags i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.sideDomain d.active d.W) :
    let a' := (family (8*M)).update d p d.D a
    (∀ i, d.D*a' i≤(d.b+d.θ i)*core d p i) ∧
      ((∑ i, core d p i)≤2*d.D → ∀ i,
        d.b*core d p i-d.θ i*d.z i*d.D≤d.D*a' i) := by
  intro a'
  have hB : ∀ i, 0 ≤ core d p i := by
    intro i
    unfold core
    apply sum_nonneg
    intro r _
    split_ifs
    · exact hp (i,r)
    · exact le_rfl
  have hBz : ∀ i∉d.active, core d p i=0 := by
    intro i hi
    simp [core,hf i hi]
  apply SideSupported.supported_feasible ((family (8*M)).update_mem _ _ _ _) ha hb
    d.θ_pos d.z_pos hB hBz hD hM hW
  intro v hv
  have hm := ((family (8*M)).exists_update d p d.D a).choose_spec.2 hv
  change (family (8*M)).value d p a'+d.D*AdaptiveMinimization.movement a' a ≤
    (family (8*M)).value d p v+d.D*AdaptiveMinimization.movement v a at hm
  simpa only [value_eq,AdaptiveMinimization.movement,ChangingDomains.variation, a', Set.mem_ofPred_eq] using hm

end KServer.SideFamilies

namespace KServer.SideFamilies
open Finset SideTracker AdaptiveMinimization
variable {J R : Type*} [Fintype J] [DecidableEq J] [Fintype R]

/-- The exact side regularizers obtained from the stored log size. -/
def fromLog (A : Finset J) (f : J → R → Bool) (W b D cw ell : ℝ)
    (h : J → ℝ) (hW : 0≤W) (hcw : 0 < cw) (hell : 0<ell) (hh : ∀ i, 1≤h i) : Data J R where
  active := A
  flags := f
  W := W
  b := b
  D := D
  θ i := cw*h i/ell
  z i := Real.exp (1-h i)/h i
  W_nonneg := hW
  θ_pos i := div_pos (mul_pos hcw (lt_of_lt_of_le zero_lt_one (hh i))) hell
  z_pos i := div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (hh i))

/-- Synthetic ranks use the new flags on the intersection of active sets. -/
def prepareData (old new : Data J R) : Data J R :=
  {old with flags := ChangingDomains.syntheticFlags old.active new.active new.flags, D := new.D}

def prepare (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family c).update (prepareData old new) p new.D a

def transport (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSide new.active (prepare c old new p a)

def step (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (family c).update new p new.D (transport c old new p a)

lemma prepare_mem (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ) :
    prepare c old new p a∈ChangingDomains.sideDomain old.active old.W :=
  (family c).update_mem _ _ _ _

lemma transport_mem (c : ℝ) (old new : Data J R) (p : J × R → ℝ) (a : J → ℝ)
    (hW : old.W=new.W) :
    transport c old new p a∈ChangingDomains.sideDomain new.active new.W := by
  rw [←hW]
  exact ChangingDomains.transposeSide_mem (prepare_mem c old new p a)

end KServer.SideFamilies

end
end
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_RankProportions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RankTracking
variable {Ω : Type*} [Fintype Ω]
/-- Reference reset policy run on every input step. -/
def held (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, ω => p 0 ω
  | t+1, ω => if test (p (t+1) ω) (held test p t ω) then p (t+1) ω else held test p t ω

omit [Fintype Ω] in
lemma held_range (test : ℝ → ℝ → Prop) [DecidableRel test] {p : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω ∈ Set.Icc 0 1) : ∀ t ω, held test p t ω ∈ Set.Icc 0 1 := by
  intro t
  induction t with
  | zero => exact hp 0
  | succ t ih => intro ω; dsimp [held]; split_ifs <;> [exact hp _ _; exact ih ω]

/-- Exact bounded affine potential used in the manuscript. -/
def potential (p r : ℝ) : ℝ := p*(1-p)+(p-r)^2

def credit (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if test (p (t+1) ω) (held test p t ω) then (p (t+1) ω-held test p t ω)^2 else 0

def factorTest (f : ℝ → ℝ) (ξ p r : ℝ) : Prop :=
  (1+ξ)*f p < f r ∨ (1+ξ)*f r < f p

instance instDecidableRelRealFactorTest (f : ℝ → ℝ) (ξ : ℝ) : DecidableRel (factorTest f ξ) := Classical.decRel _

omit [Fintype Ω] in
lemma factor_held_accurate (f : ℝ → ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (hf : ∀ p ∈ Set.Icc (0:ℝ) 1, 0 ≤ f p) {p : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω ∈ Set.Icc 0 1) (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*f (p t ω) ≤ f (held (factorTest f ξ) p t ω) ∧
      f (held (factorTest f ξ) p t ω) ≤ (1+ξ)*f (p t ω) := by
  have hself (x : ℝ) (hx : 0 ≤ x) : (1+ξ)⁻¹*x ≤ x ∧ x ≤ (1+ξ)*x := by
    constructor
    · rw [inv_mul_le_iff₀ (by linarith : 0<1+ξ)]
      nlinarith [mul_nonneg hξ.le hx]
    · nlinarith [mul_nonneg hξ.le hx]
  cases t with
  | zero => exact hself _ (hf _ (hp 0 ω))
  | succ t =>
    simp only [held]
    split_ifs with ht
    · exact hself _ (hf _ (hp _ _))
    · rw [factorTest,not_or,not_lt,not_lt] at ht
      constructor
      · rw [inv_mul_le_iff₀ (by linarith : 0<1+ξ)]
        exact ht.2
      · exact ht.1


def absoluteTest (δ p r : ℝ) : Prop := δ < |p-r|
instance instDecidableRelRealAbsoluteTest (δ : ℝ) : DecidableRel (absoluteTest δ) := Classical.decRel _

def resetIndicator (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if test (p (t+1) ω) (held test p t ω) then 1 else 0

end KServer.RankTracking
namespace KServer.CoreFlags
open KServer.RankTracking
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

/-- §03: the literal absolute reference tolerance p*/8, p*=1/24. -/
def tolerance : ℝ := (1/24)/8
lemma tolerance_pos : 0 < tolerance := by norm_num [tolerance]
def flag (R : FilteredRanks w) (t : ℕ) (ω : Ω) : Bool :=
  decide (held (absoluteTest tolerance) R.p t ω ≤ (1/24 : ℝ)/2)

def change (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  if flag R (t+1) ω = flag R t ω then 0 else 1

lemma flag_accuracy (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |R.p t ω - held (absoluteTest tolerance) R.p t ω| ≤ tolerance := by
  cases t with
  | zero => simp [held,tolerance_pos.le]
  | succ t =>
    simp only [held]
    split_ifs with ht
    · simp [tolerance_pos.le]
    · exact le_of_not_gt ht

lemma core_upper (R : FilteredRanks w) {t : ℕ} {ω : Ω} (hf : flag R t ω = true) :
    R.p t ω ≤ 5*(1/24 : ℝ)/8 := by
  have hh : held (absoluteTest tolerance) R.p t ω ≤ (1/24 : ℝ)/2 := by simpa [flag] using hf
  have ha := (abs_le.mp (flag_accuracy R t ω)).2
  norm_num [tolerance] at *
  linarith

lemma noncore_lower (R : FilteredRanks w) {t : ℕ} {ω : Ω} (hf : flag R t ω = false) :
    3*(1/24 : ℝ)/8 < R.p t ω := by
  have hh : (1/24 : ℝ)/2 < held (absoluteTest tolerance) R.p t ω := by
    simpa [flag,not_le] using hf
  have ha := (abs_le.mp (flag_accuracy R t ω)).1
  norm_num [tolerance] at *
  linarith

end KServer.CoreFlags
end


/- Rank functions for dominated allocation, as in §03, equation explicit-rank. -/


noncomputable section
open Set Filter
namespace KServer.RankFunctions

def pstar : ℝ := 1 / 24
def sstar : ℝ := 5 / 8

def A (z : ℝ) : ℝ := 18 / 7 - z * (102 / 49)
def B (z : ℝ) : ℝ := z * (1152 / 343)
def middle (z p : ℝ) : ℝ :=
  A z * (sstar - p) ^ 2 + B z * (sstar - p) ^ 3

def rank (z p : ℝ) : ℝ :=
  if p ≤ pstar then 1 - (3 + z) * p
  else if p ≤ sstar then middle z p else 0

def slope (z p : ℝ) : ℝ :=
  if p ≤ pstar then -(3 + z)
  else if p ≤ sstar then -2 * A z * (sstar - p) - 3 * B z * (sstar - p) ^ 2 else 0

lemma middle_literal (z p : ℝ) :
    middle z p = (sstar - p) ^ 2 *
      (18 / 7 - z * (6 / 49 + 1152 / 343 * (p - pstar))) := by
  unfold middle A B sstar pstar
  ring

/-- C¹ gluing at a scalar threshold, applied twice to the rank formula. -/
lemma derivative_ite_le {f g f' g' : ℝ → ℝ} {c : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : f c = g c) (hd : f' c = g' c) (x : ℝ) :
    HasDerivAt (fun p => if p ≤ c then f p else g p)
      (if x ≤ c then f' x else g' x) x := by
  rcases lt_trichotomy x c with hx | hx | hx
  · rw [ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with p hp
    exact ite_eq_left hp.le
  · subst x
    rw [ite_eq_left le_rfl]
    have hleft : HasDerivWithinAt (fun p => if p ≤ c then f p else g p)
        (f' c) (Iic c) c := by
      apply (hf c).hasDerivWithinAt.congr
      · intro p hp
        exact ite_eq_left hp
      · exact ite_eq_left le_rfl
    have hright : HasDerivWithinAt (fun p => if p ≤ c then f p else g p)
        (f' c) (Ici c) c := by
      rw [hd]
      apply (hg c).hasDerivWithinAt.congr
      · intro p hp
        by_cases ht : p ≤ c
        · have : p = c := le_antisymm ht hp
          subst p
          simpa using he
        · exact ite_eq_right ht
      · simpa using he
    have h := hleft.union hright
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using h
  · rw [ite_eq_right hx.not_ge]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with p hp
    exact ite_eq_right hp.not_ge

lemma middle_derivative (z p : ℝ) :
    HasDerivAt (middle z) (-2 * A z * (sstar - p) - 3 * B z * (sstar - p) ^ 2) p := by
  have h := (((hasDerivAt_id p).const_sub sstar).pow 2).const_mul (A z)
  have h' := (((hasDerivAt_id p).const_sub sstar).pow 3).const_mul (B z)
  convert h.add h' using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (norm_num [id_eq]; ring)

lemma rank_derivative (z p : ℝ) : HasDerivAt (rank z) (slope z p) p := by
  have hcut (x : ℝ) : HasDerivAt (fun p => if p ≤ sstar then middle z p else 0)
      (if x ≤ sstar then -2 * A z * (sstar - x) - 3 * B z * (sstar - x) ^ 2 else 0) x := by
    apply derivative_ite_le (middle_derivative z) (fun x => hasDerivAt_const x 0)
    · simp [middle]
    · simp
  apply derivative_ite_le (f' := fun _ => -(3 + z))
    (fun x => by simpa using ((hasDerivAt_id x).const_mul (3 + z)).const_sub 1)
    hcut
  · norm_num [pstar, sstar, middle, A, B]
    ring
  · norm_num [pstar, sstar, A, B]
    ring

lemma coefficients {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    2 ≤ A z ∧ 0 ≤ B z := by
  dsimp [A, B]
  constructor <;> nlinarith [hz.1, hz.2]

lemma middle_slope_monotone {z x y : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ))
    (hxy : x ≤ y) (hys : y ≤ sstar) :
    -2 * A z * (sstar - x) - 3 * B z * (sstar - x) ^ 2 ≤
      -2 * A z * (sstar - y) - 3 * B z * (sstar - y) ^ 2 := by
  obtain ⟨hA, hB⟩ := coefficients hz
  have hlin : A z * (sstar - y) ≤ A z * (sstar - x) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hsq : (sstar - y) ^ 2 ≤ (sstar - x) ^ 2 := by nlinarith
  have hquad := mul_le_mul_of_nonneg_left hsq hB
  nlinarith

lemma slope_monotone {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    Monotone (slope z) := by
  have hps : pstar ≤ sstar := by norm_num [pstar, sstar]
  have hmatch : -2 * A z * (sstar - pstar) - 3 * B z * (sstar - pstar) ^ 2 = -(3 + z) := by
    unfold A B sstar pstar
    ring
  intro x y hxy
  by_cases hx : x ≤ pstar
  · by_cases hy : y ≤ pstar
    · simp [slope, hx, hy]
    · by_cases hys : y ≤ sstar
      · simp only [slope, ite_eq_left hx, ite_eq_right hy, ite_eq_left hys]
        rw [← hmatch]
        exact middle_slope_monotone hz (le_of_not_ge hy) hys
      · simp only [slope, ite_eq_left hx, ite_eq_right hy, ite_eq_right hys]
        linarith [hz.1]
  · have hy : ¬ y ≤ pstar := by linarith
    by_cases hys : y ≤ sstar
    · have hxs : x ≤ sstar := hxy.trans hys
      simp only [slope, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxs, ite_eq_left hys]
      exact middle_slope_monotone hz hxy hys
    · by_cases hxs : x ≤ sstar
      · simp only [slope, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxs, ite_eq_right hys]
        have h := middle_slope_monotone hz hxs (le_refl sstar)
        simpa using h
      · simp [slope, hx, hy, hxs, hys]

lemma rank_convex {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    ConvexOn ℝ univ (rank z) := by
  apply Monotone.convexOn_univ_of_deriv (fun p => (rank_derivative z p).differentiableAt)
  have he : deriv (rank z) = slope z := funext fun p => (rank_derivative z p).deriv
  rw [he]
  exact slope_monotone hz

lemma rank_antitone {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    Antitone (rank z) := by
  apply antitone_of_hasDerivAt_nonpos (rank_derivative z)
  intro p
  dsimp only [Pi.zero_apply]
  have hps : pstar < sstar := by norm_num [pstar, sstar]
  have hzero : slope z sstar = 0 := by simp [slope, not_le.mpr hps]
  by_cases hp : p ≤ sstar
  · exact (slope_monotone hz hp).trans_eq hzero
  · have hpp : ¬p ≤ pstar := by linarith
    simp [slope, hpp, hp]

lemma rank_zero (z : ℝ) : rank z 0 = 1 := by norm_num [rank, pstar]

lemma rank_cutoff (z : ℝ) {p : ℝ} (hp : sstar ≤ p) : rank z p = 0 := by
  have hpp : ¬ p ≤ pstar := by norm_num [sstar, pstar] at *; linarith
  simp only [rank, ite_eq_right hpp]
  split_ifs with h
  · have : p = sstar := le_antisymm h hp
    simp [this, middle]
  · rfl

lemma rank_pos {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (hp : p < sstar) :
    0 < rank z p := by
  by_cases h : p ≤ pstar
  · rw [rank, ite_eq_left h]
    have hmul := mul_le_mul_of_nonneg_left h (by linarith [hz.1] : 0 ≤ 3 + z)
    norm_num [pstar] at hmul
    nlinarith [hz.2]
  · rw [rank, ite_eq_right h, ite_eq_left hp.le]
    obtain ⟨hA, hB⟩ := coefficients hz
    have hx : 0 < sstar - p := sub_pos.mpr hp
    have h2 : 0 < A z * (sstar - p)^2 := mul_pos (by linarith) (sq_pos_of_pos hx)
    have h3 : 0 ≤ B z * (sstar - p)^3 := mul_nonneg hB (pow_nonneg hx.le _)
    dsimp [middle]
    linarith

lemma rank_nonneg {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (p : ℝ) :
    0 ≤ rank z p := by
  by_cases hp : p < sstar
  · exact (rank_pos hz hp).le
  · rw [rank_cutoff z (le_of_not_gt hp)]

lemma rank_range {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (hp : 0 ≤ p) :
    rank z p ∈ Set.Icc 0 1 := by
  exact ⟨rank_nonneg hz p, (rank_antitone hz hp).trans_eq (rank_zero z)⟩

/-- Minus the derivative in beta, exactly as defined after eq:explicit-rank. -/
def parameterSlope (p : ℝ) : ℝ :=
  if p ≤ pstar then p else if p ≤ sstar then
    (sstar - p)^2 * (6 / 49 + 1152 / 343 * (p - pstar)) else 0

lemma rank_parameter_affine (z p : ℝ) :
    rank z p = rank 0 p - z * parameterSlope p := by
  dsimp [rank, parameterSlope]
  split_ifs <;> simp [middle, A, B, sstar, pstar] <;> ring

lemma parameterSlope_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ parameterSlope p := by
  dsimp [parameterSlope]
  split_ifs with h h'
  · exact hp
  · have : 0 ≤ 6 / 49 + 1152 / 343 * (p - pstar) := by linarith
    exact mul_nonneg (sq_nonneg _) this
  · rfl

lemma rank_parameter_antitone {p : ℝ} (hp : 0 ≤ p) :
    Antitone (fun z => rank z p) := by
  intro x y hxy
  change rank y p ≤ rank x p
  rw [rank_parameter_affine x, rank_parameter_affine y]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hxy (parameterSlope_nonneg hp)) _

lemma parameterSlope_compare {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ))
    (hp : pstar / 4 ≤ p) :
    rank z p / 96 ≤ parameterSlope p ∧ parameterSlope p ≤ rank z p := by
  by_cases h : p ≤ pstar
  · simp only [rank, parameterSlope, ite_eq_left h]
    norm_num [pstar] at h hp
    have hzp : 0 ≤ z * p := mul_nonneg hz.1 (by linarith)
    have hmul := mul_le_mul_of_nonneg_left h (by linarith [hz.1] : 0 ≤ 3 + z)
    constructor <;> nlinarith [hz.2]
  · by_cases h' : p ≤ sstar
    · simp only [rank, parameterSlope, ite_eq_right h, ite_eq_left h', middle_literal]
      let c : ℝ := 6 / 49 + 1152 / 343 * (p - pstar)
      have hc0 : 6 / 49 ≤ c := by dsimp [c]; linarith
      have hc1 : c ≤ 102 / 49 := by dsimp [c]; norm_num [pstar, sstar] at *; linarith
      have hzc0 : 0 ≤ z * c := mul_nonneg hz.1 (by linarith)
      have hzc1 : z * c ≤ (1 / 100) * (102 / 49) :=
        mul_le_mul hz.2 hc1 (by linarith) (by norm_num)
      have hlo : (18 / 7 - z * c) / 96 ≤ c := by linarith
      have hhi : c ≤ 18 / 7 - z * c := by linarith
      constructor
      · have hh := mul_le_mul_of_nonneg_left hlo (sq_nonneg (sstar - p))
        change (sstar - p)^2 * (18 / 7 - z*c) / 96 ≤ (sstar - p)^2 * c
        nlinarith [hh]
      · exact mul_le_mul_of_nonneg_left hhi (sq_nonneg _)
    · simp [rank, parameterSlope, h, h']


/-- The broader size function, literally as in §03. -/
def sizeRank (p : ℝ) : ℝ := (max (3 / 4 - p) 0)^2 / (3 / 4)^2

lemma sizeRank_piece (p : ℝ) :
    sizeRank p = if p ≤ 3 / 4 then (3 / 4 - p)^2 / (3 / 4)^2 else 0 := by
  by_cases h : p ≤ 3 / 4
  · simp [sizeRank, h]
  · simp [sizeRank, h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

lemma sizeRank_derivative (p : ℝ) :
    HasDerivAt sizeRank (-(32 / 9) * max (3 / 4 - p) 0) p := by
  have hf (x : ℝ) : HasDerivAt (fun p : ℝ => (3 / 4 - p)^2 / (3 / 4)^2)
      (-(32 / 9) * (3 / 4 - x)) x := by
    convert (((hasDerivAt_id x).const_sub (3 / 4)).pow 2).div_const ((3 / 4)^2) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (norm_num [id_eq]; ring)
  have ht := derivative_ite_le hf (fun x => hasDerivAt_const x (0 : ℝ))
    (c := 3 / 4) (by norm_num) (by norm_num) p
  convert ht using 1
  · exact funext sizeRank_piece
  · by_cases h : p ≤ 3 / 4
    · simp [h]
    · simp [h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

lemma sizeRank_convex : ConvexOn ℝ univ sizeRank := by
  apply Monotone.convexOn_univ_of_deriv (fun p => (sizeRank_derivative p).differentiableAt)
  intro x y hxy
  rw [(sizeRank_derivative x).deriv, (sizeRank_derivative y).deriv]
  exact mul_le_mul_of_nonpos_left (max_le_max (by linarith) le_rfl) (by norm_num)

lemma sizeRank_one : sizeRank 1 = 0 := by norm_num [sizeRank]
lemma sizeRank_nonneg (p : ℝ) : 0 ≤ sizeRank p := div_nonneg (sq_nonneg _) (sq_nonneg _)

lemma sizeRank_le_complement {p : ℝ} (hp : p ∈ Set.Icc 0 1) : sizeRank p ≤ 1 - p := by
  rw [sizeRank_piece]
  split_ifs with h
  · norm_num
    have hm := mul_nonneg hp.1 (sub_nonneg.mpr h)
    nlinarith
  · linarith [hp.2]

end KServer.RankFunctions

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FineCaps
open KServer.RankTracking KServer.RankFunctions KServer.CoreFlags
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

def estimate (ξ z : ℝ) (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  rank z (held (factorTest (rank z) ξ) R.p t ω)

lemma estimate_range {ξ z : ℝ} (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : estimate ξ z R t ω ∈ Set.Icc 0 1 :=
  rank_range hz (held_range (factorTest (rank z) ξ) R.range t ω).1

lemma estimate_accuracy {ξ z : ℝ} (hξ : 0 < ξ) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*rank z (R.p t ω) ≤ estimate ξ z R t ω ∧
      estimate ξ z R t ω ≤ (1+ξ)*rank z (R.p t ω) :=
  factor_held_accurate (rank z) hξ (fun _ hp => (rank_range hz hp.1).1) R.range t ω

lemma relative_absolute {ξ f E : ℝ} (hξ : 0 ≤ ξ) (hf : 0 ≤ f)
    (hl : (1+ξ)⁻¹*f ≤ E) (hu : E ≤ (1+ξ)*f) : |E-f| ≤ ξ*f := by
  have hx : 0 < 1+ξ := by linarith
  have hh := mul_le_mul_of_nonneg_left hl hx.le
  have he : (1+ξ)*((1+ξ)⁻¹*f)=f := by rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hx),one_mul]
  rw [he] at hh
  apply abs_le.mpr
  constructor
  · by_cases hEf : E ≤ f
    · have := mul_le_mul_of_nonneg_left hEf hξ
      nlinarith
    · have := mul_nonneg hξ hf
      linarith
  · nlinarith

lemma estimate_absolute {ξ z : ℝ} (hξ : 0 < ξ) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |estimate ξ z R t ω-rank z (R.p t ω)| ≤ ξ*rank z (R.p t ω) :=
  relative_absolute hξ.le (rank_range hz (R.range t ω).1).1
    (estimate_accuracy hξ hz R t ω).1 (estimate_accuracy hξ hz R t ω).2

lemma interpolate_rank (a p : ℝ) :
    (1-a)*rank 0 p+a*rank (1/100) p = rank (a/100) p := by
  rw [rank_parameter_affine (1/100),rank_parameter_affine (a/100)]
  ring

def interpolated (ξ a : ℝ) (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  (1-a)*estimate ξ 0 R t ω+a*estimate ξ (1/100) R t ω

lemma interpolated_range {ξ a : ℝ} (ha : a ∈ Set.Icc 0 1)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : interpolated ξ a R t ω ∈ Set.Icc 0 1 := by
  have h0 := estimate_range (ξ := ξ) (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have h1 := estimate_range (ξ := ξ) (by norm_num : (1/100:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have hA : 0 ≤ 1-a := by linarith [ha.2]
  have l0 := mul_nonneg hA h0.1
  have l1 := mul_nonneg ha.1 h1.1
  have u0 := mul_le_mul_of_nonneg_left h0.2 hA
  have u1 := mul_le_mul_of_nonneg_left h1.2 ha.1
  constructor <;> dsimp [interpolated] <;> nlinarith

lemma interpolated_accuracy {ξ a : ℝ} (hξ : 0 < ξ) (ha : a ∈ Set.Icc 0 1)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |interpolated ξ a R t ω-rank (a/100) (R.p t ω)| ≤ ξ*rank (a/100) (R.p t ω) := by
  have h0 := estimate_absolute hξ (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have h1 := estimate_absolute hξ (by norm_num : (1/100:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have hA : 0 ≤ 1-a := by linarith [ha.2]
  rw [←interpolate_rank]
  calc |interpolated ξ a R t ω-((1-a)*rank 0 (R.p t ω)+a*rank (1/100) (R.p t ω))| =
      |(1-a)*(estimate ξ 0 R t ω-rank 0 (R.p t ω)) +
        a*(estimate ξ (1/100) R t ω-rank (1/100) (R.p t ω))| := by
          unfold interpolated; congr 1; ring
    _ ≤ |(1-a)*(estimate ξ 0 R t ω-rank 0 (R.p t ω))| +
        |a*(estimate ξ (1/100) R t ω-rank (1/100) (R.p t ω))| := abs_add_le _ _
    _ = (1-a)*|estimate ξ 0 R t ω-rank 0 (R.p t ω)| +
        a*|estimate ξ (1/100) R t ω-rank (1/100) (R.p t ω)| := by
          rw [abs_mul,abs_mul,abs_of_nonneg hA,abs_of_nonneg ha.1]
    _ ≤ (1-a)*(ξ*rank 0 (R.p t ω))+a*(ξ*rank (1/100) (R.p t ω)) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hA) (mul_le_mul_of_nonneg_left h1 ha.1)
    _ = _ := by ring

/-- §03 flex-estimate error, including exact zero at the common cutoff. -/
lemma noncore_interpolation_error {ξ a z ε : ℝ} (hξ : 0 < ξ) (ha : a ∈ Set.Icc 0 1)
    (hz : z ∈ Set.Icc 0 (1/100 : ℝ)) (hza : z ≤ a/100) (hea : a/100-z ≤ ε)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) (hf : flag R t ω=false) :
    |interpolated ξ a R t ω-rank z (R.p t ω)| ≤ (ξ+ε)*rank z (R.p t ω) := by
  have hp : pstar/4 ≤ R.p t ω := by
    have := noncore_lower R hf
    norm_num [pstar] at *
    linarith
  have hg := parameterSlope_compare hz hp
  have hg0 := parameterSlope_nonneg (R.range t ω).1
  have hm := rank_parameter_antitone (R.range t ω).1 hza
  have hre : rank z (R.p t ω)-rank (a/100) (R.p t ω) =
      (a/100-z)*parameterSlope (R.p t ω) := by
    rw [rank_parameter_affine z,rank_parameter_affine (a/100)]; ring
  have hs : |rank (a/100) (R.p t ω)-rank z (R.p t ω)| ≤ ε*rank z (R.p t ω) := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hm),hre]
    exact (mul_le_mul_of_nonneg_left hg.2 (sub_nonneg.mpr hza)).trans
      (mul_le_mul_of_nonneg_right hea (rank_range hz (R.range t ω).1).1)
  calc _ ≤ |interpolated ξ a R t ω-rank (a/100) (R.p t ω)| +
       |rank (a/100) (R.p t ω)-rank z (R.p t ω)| := abs_sub_le _ _ _
    _ ≤ ξ*rank (a/100) (R.p t ω)+ε*rank z (R.p t ω) :=
      add_le_add (interpolated_accuracy hξ ha R t ω) hs
    _ ≤ ξ*rank z (R.p t ω)+ε*rank z (R.p t ω) :=
      add_le_add (mul_le_mul_of_nonneg_left hm hξ.le) (le_refl _)
    _ = _ := by ring

/-- Deterministic scaling of an accurately tracked flex term. Parameters here
are already normalized by ell: l=lambda_b/ell, e=error/ell,
g=gamma/ell, b=epsilon_b/ell. All zero-flex cases are included. -/
lemma cap_scaling {F E Fc l e g b : ℝ}
    (hF : 0 ≤ F) (hE : |E-F| ≤ e*F) (he : 0 ≤ e)
    (hl : 0 < l) (hls : l ≤ 1/4) (hel : e ≤ l/4)
    (hg : 4*l ≤ g) (hb : 4*l ≤ b) (hfc : Fc ≤ (1-g)*F) :
    (Fc ≤ (1-l)*E ∧ (1-l)*E ≤ F) ∧
    (F ≤ (1+l)*E ∧ (1+l)*E ≤ (1+b)*F) := by
  have hnear := abs_le.mp hE
  have hl1 : 0 ≤ 1-l := by linarith
  have hl2 : 0 ≤ 1+l := by linarith
  have low := mul_le_mul_of_nonneg_left hnear.1 hl1
  have up := mul_le_mul_of_nonneg_left hnear.2 hl1
  have low' := mul_le_mul_of_nonneg_left hnear.1 hl2
  have up' := mul_le_mul_of_nonneg_left hnear.2 hl2
  have hle : l*e ≤ e/4 := by nlinarith
  have hge : l+e ≤ g := by linarith
  have hbe : l+e+l*e ≤ b := by nlinarith
  have hpos : e+l*e ≤ l := by nlinarith
  have h01 := mul_le_mul_of_nonneg_right hge hF
  have h02 := mul_le_mul_of_nonneg_right hbe hF
  have h03 := mul_le_mul_of_nonneg_right hpos hF
  have h04 : e ≤ l := by linarith
  have h05 := mul_le_mul_of_nonneg_right h04 hF
  have h06 := mul_nonneg (mul_nonneg hl.le he) hF
  constructor <;> constructor <;> nlinarith

/-- One rank's core-plus-scaled-flex contribution to the actual cap. -/
def capTerm (ξ a κ : ℝ) (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  if flag R t ω then 1 else κ*interpolated ξ a R t ω

/-- Fine changes can be selected pathwise; wholesale changes are excluded only
when the interpolation and scale parameters are actually held fixed. -/
def fineVariation (ξ : ℝ) (a κ : ℕ → Ω → ℝ) (wholesale : ℕ → Ω → Bool)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  if wholesale t ω then 0 else
    |capTerm ξ (a (t+1) ω) (κ (t+1) ω) R (t+1) ω-capTerm ξ (a t ω) (κ t ω) R t ω|

end KServer.FineCaps
end

end

/- Finite-law rank superadditivity and summation by parts. -/


noncomputable section
open Finset
open scoped BigOperators
namespace KServer.RankOrder

lemma convex_tangent {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hd : ∀ x, DifferentiableAt ℝ f x) (x y : ℝ) :
    deriv f x * (y - x) ≤ f y - f x := by
  rcases lt_trichotomy x y with h | h | h
  · have hh := hf.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h (hd x).hasDerivAt
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hh
  · subst y
    simp
  · have hh := hf.slope_le_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) h (hd x).hasDerivAt
    rw [slope_def_field] at hh
    have ht := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

lemma convex_sum_of_prefix {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hd : ∀ x, DifferentiableAt ℝ f x) {n : ℕ} {x y : ℕ → ℝ}
    (hmono : ∀ a b, a ≤ b → b < n → x a ≤ x b)
    (hprefix : ∀ m ≤ n, ∑ i ∈ range m, y i ≤ ∑ i ∈ range m, x i)
    (htotal : ∑ i ∈ range n, y i = ∑ i ∈ range n, x i) :
    ∑ i ∈ range n, f (x i) ≤ ∑ i ∈ range n, f (y i) := by
  have hD : ∀ m ≤ n, ∑ i ∈ range m, (y i - x i) ≤ 0 := by
    intro m hm
    rw [sum_sub_distrib]
    exact sub_nonpos.mpr (hprefix m hm)
  have hD0 : ∑ i ∈ range n, (y i - x i) = 0 := by
    rw [sum_sub_distrib, htotal, sub_self]
  have hmonod := hf.monotoneOn_deriv (fun x _ => hd x)
  have hnonneg : 0 ≤ ∑ i ∈ range n, deriv f (x i) * (y i - x i) := by
    have he := sum_range_by_parts (fun i => deriv f (x i)) (fun i => y i - x i) n
    simp only [smul_eq_mul, hD0, mul_zero, zero_sub] at he
    rw [he]
    apply neg_nonneg.mpr
    apply sum_nonpos
    intro i hi
    have hi' : i + 1 < n := by have := mem_range.mp hi; omega
    have hdif : 0 ≤ deriv f (x (i + 1)) - deriv f (x i) := by
      exact sub_nonneg.mpr (hmonod (Set.mem_univ _) (Set.mem_univ _) (hmono i (i + 1) (by omega) hi'))
    exact mul_nonpos_of_nonneg_of_nonpos hdif (hD (i + 1) hi'.le)
  have hsum := sum_le_sum (s := range n) (fun i _ => convex_tangent hf hd (x i) (y i))
  rw [sum_sub_distrib] at hsum
  linarith

def extend {n : ℕ} (v : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then v ⟨i, hi⟩ else 0

lemma extend_fin {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : extend v i = v i := by
  simp [extend, i.isLt]

lemma sum_outside {ι : Type*} [DecidableEq ι] (S B : Finset ι) :
    (∑ i ∈ S, if i ∈ B then (0 : ℝ) else 1) = ((S \ B).card : ℝ) := by
  rw [sum_ite]
  simp only [sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one]
  have he : S.filter (fun i => i ∉ B) = S \ B := by ext i; simp
  rw [he]

lemma sum_rank_indicators (m N : ℕ) :
    (∑ i ∈ range m, if N ≤ i then (1 : ℝ) else 0) = (m - N : ℕ) := by
  rw [sum_ite]
  simp only [sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have he : (range m).filter (fun i => N ≤ i) = Ico N m := by
    ext i
    simp [and_comm]
  rw [he, Nat.card_Ico]

lemma outside_card_bound {ι : Type*} [DecidableEq ι] (S B : Finset ι) :
    S.card - B.card ≤ (S \ B).card := by
  rw [card_sdiff]
  exact Nat.sub_le_sub_left (card_le_card inter_subset_left) _

/-- Pool rank probabilities, then sort them. Every prefix is bounded below
by the corresponding parent rank prefix. Dependence between ranks is arbitrary. -/
lemma rank_prefix {Ω : Type*} [Fintype Ω] {n : ℕ}
    (B : Ω → Finset (Fin n)) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) :
    (∑ j ∈ range m, ∑ ω, w ω * (if (B ω).card ≤ j then (1 : ℝ) else 0)) ≤
      ∑ j ∈ range m, extend (fun i => ∑ ω, w ω * (if σ i ∈ B ω then (0 : ℝ) else 1)) j := by
  classical
  let e : Fin m → Fin n := fun i => σ ⟨i, lt_of_lt_of_le i.isLt hm⟩
  have heinj : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have ht := σ.injective h
    exact congrArg (fun i : Fin n => i.val) ht
  let S : Finset (Fin n) := univ.image e
  have hScard : S.card = m := by simp [S, card_image_of_injective _ heinj]
  have hright : (∑ j ∈ range m, extend (fun i => ∑ ω, w ω * (if σ i ∈ B ω then (0 : ℝ) else 1)) j) =
      ∑ i ∈ S, ∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    rw [show S = univ.image e from rfl, sum_image]
    · apply sum_congr rfl
      intro i _
      simp [extend, e, lt_of_lt_of_le i.isLt hm]
    · exact heinj.injOn
  rw [hright, sum_comm, sum_comm (s := S)]
  apply sum_le_sum
  intro ω _
  rw [← mul_sum, ← mul_sum, sum_rank_indicators, sum_outside]
  apply mul_le_mul_of_nonneg_left _ (hw ω)
  exact_mod_cast hScard ▸ outside_card_bound S (B ω)

lemma rank_total {Ω : Type*} [Fintype Ω] {n : ℕ}
    (B : Ω → Finset (Fin n)) (w : Ω → ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ j ∈ range n, ∑ ω, w ω * (if (B ω).card ≤ j then (1 : ℝ) else 0)) =
      ∑ j ∈ range n, extend (fun i => ∑ ω, w ω * (if σ i ∈ B ω then (0 : ℝ) else 1)) j := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (extend _)]
  simp only [extend_fin]
  rw [Equiv.sum_comp σ (fun i => ∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1)), sum_comm, sum_comm (s := (univ : Finset (Fin n)))]
  apply sum_congr rfl
  intro ω _
  rw [← mul_sum, ← mul_sum, sum_rank_indicators, sum_outside]
  congr 2
  rw [card_sdiff]
  simp

/-- The convex superadditivity comparison for an arbitrary joint distribution
of integer rank indicators. Padding of parent ranks is automatic. -/
lemma convex_rank_sum {Ω : Type*} [Fintype Ω] {n : ℕ}
    (B : Ω → Finset (Fin n)) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hd : ∀ x, DifferentiableAt ℝ f x) :
    (∑ i : Fin n, f (∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1))) ≤
      ∑ j : Fin n, f (∑ ω, w ω * (if (B ω).card ≤ j.val then (1 : ℝ) else 0)) := by
  classical
  let p : Fin n → ℝ := fun i => ∑ ω, w ω * (if i ∈ B ω then 0 else 1)
  let σ := Tuple.sort p
  let x := extend (fun i => p (σ i))
  let y : ℕ → ℝ := fun j => ∑ ω, w ω * (if (B ω).card ≤ j then 1 else 0)
  have hmono : ∀ a b, a ≤ b → b < n → x a ≤ x b := by
    intro a b hab hbn
    have han : a < n := lt_of_le_of_lt hab hbn
    change extend _ a ≤ extend _ b
    simp only [extend, dite_eq_left han, dite_eq_left hbn]
    exact Tuple.monotone_sort p hab
  have hprefix : ∀ m ≤ n, ∑ i ∈ range m, y i ≤ ∑ i ∈ range m, x i :=
    fun m hm => rank_prefix B w hw σ m hm
  have htotal : ∑ i ∈ range n, y i = ∑ i ∈ range n, x i := rank_total B w σ
  have ht := convex_sum_of_prefix hf hd hmono hprefix htotal
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (x i)),
    ← Fin.sum_univ_eq_sum_range (fun i => f (y i))] at ht
  change (∑ i : Fin n, f (extend (fun j => p (σ j)) i.val)) ≤ _ at ht
  simp only [extend_fin] at ht
  rw [Equiv.sum_comp σ (fun i => f (p i))] at ht
  exact ht


lemma convex_rank_sum_type {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (B : Ω → Finset ι) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hd : ∀ x, DifferentiableAt ℝ f x) :
    (∑ i : ι, f (∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1))) ≤
      ∑ j : Fin (Fintype.card ι), f (∑ ω, w ω * (if (B ω).card ≤ j.val then (1 : ℝ) else 0)) := by
  classical
  let e := Fintype.equivFin ι
  let B' := fun ω => (B ω).image e
  have h := convex_rank_sum B' w hw hf hd
  have he : (∑ i : ι, f (∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1))) =
      ∑ i : Fin (Fintype.card ι), f (∑ ω, w ω * (if i ∈ B' ω then (0 : ℝ) else 1)) := by
    apply Fintype.sum_equiv e
    intro i
    simp [B', e.injective.mem_finset_image]
  rw [he]
  simpa only [B', card_image_of_injective _ e.injective] using h

lemma sum_below {k N : ℕ} (hN : N ≤ k) :
    (∑ a : Fin k, if a.val < N then (1 : ℕ) else 0) = N := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < N then (1 : ℕ) else 0), ← sum_filter]
  have h : (range k).filter (fun a => a < N) = range N := by
    ext a
    simp only [mem_filter, mem_range]
    omega
  rw [h]
  simp

/-- Source integer ranks: rank a (with zero-based index) is P(N ≤ a).
The probability law is joint, without independent-child assumptions. -/
def countRank {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (N : Ω → ℕ) (a : ℕ) : ℝ :=
  ∑ ω, w ω * (if N ω ≤ a then 1 else 0)

lemma countRank_range {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hws : ∑ ω, w ω = 1) (N : Ω → ℕ) (a : ℕ) : countRank w N a ∈ Set.Icc 0 1 := by
  constructor
  · exact sum_nonneg fun ω _ => mul_nonneg (hw ω) (by split_ifs <;> norm_num)
  · calc countRank w N a ≤ ∑ ω, w ω := by
           apply sum_le_sum
           intro ω _
           split_ifs <;> simp [hw ω]
         _ = 1 := hws

lemma countRank_expected {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hws : ∑ ω, w ω = 1)
    {k : ℕ} (N : Ω → ℕ) (hN : ∀ ω, N ω ≤ k) :
    (∑ a : Fin k, (1 - countRank w N a.val)) = ∑ ω, w ω * N ω := by
  classical
  have hcoord (a : Fin k) : 1 - countRank w N a.val =
      ∑ ω, w ω * (if a.val < N ω then (1 : ℝ) else 0) := by
    conv_lhs => lhs; rw [← hws]
    rw [countRank, ← sum_sub_distrib]
    apply sum_congr rfl
    intro ω _
    by_cases h : N ω ≤ a.val
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  simp_rw [hcoord]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [← mul_sum]
  congr 1
  exact_mod_cast sum_below (hN ω)

lemma convex_count_superadditivity {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hws : ∑ ω, w ω = 1)
    {k : ℕ} (N : Ω → I → ℕ) (hN : ∀ ω, ∑ i, N ω i ≤ k)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hd : ∀ x, DifferentiableAt ℝ f x)
    (hf1 : f 1 = 0) :
    (∑ i : I, ∑ a : Fin k, f (countRank w (fun ω => N ω i) a.val)) ≤
      ∑ a : Fin k, f (countRank w (fun ω => ∑ i, N ω i) a.val) := by
  classical
  let B : Ω → Finset (I × Fin k) := fun ω => univ.filter (fun ia => ia.2.val < N ω ia.1)
  have hNi (ω : Ω) (i : I) : N ω i ≤ k :=
    (single_le_sum (fun j _ => Nat.zero_le (N ω j)) (mem_univ i)).trans (hN ω)
  have hB (ω : Ω) : (B ω).card = ∑ i, N ω i := by
    change (univ.filter (fun ia : I × Fin k => ia.2.val < N ω ia.1)).card = _
    rw [card_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    exact sum_below (hNi ω i)
  have ht := convex_rank_sum_type B w hw hf hd
  have hleft : (∑ ia : I × Fin k, f (∑ ω, w ω * (if ia ∈ B ω then (0 : ℝ) else 1))) =
      ∑ i : I, ∑ a : Fin k, f (countRank w (fun ω => N ω i) a.val) := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro a _
    congr 1
    apply sum_congr rfl
    intro ω _
    simp only [B, mem_filter, mem_univ, true_and]
    by_cases h : a.val < N ω i
    · simp [h, not_le.mpr h]
    · simp [h, le_of_not_gt h]
  rw [hleft] at ht
  have hright : (∑ a : Fin (Fintype.card (I × Fin k)), f (∑ ω, w ω *
      (if (B ω).card ≤ a.val then (1 : ℝ) else 0))) =
      ∑ a : Fin k, f (countRank w (fun ω => ∑ i, N ω i) a.val) := by
    simp_rw [hB]
    change (∑ a : Fin (Fintype.card (I × Fin k)), f (countRank w (fun ω => ∑ i, N ω i) a.val)) = _
    rw [Fin.sum_univ_eq_sum_range (fun a => f (countRank w (fun ω => ∑ i, N ω i) a)) (Fintype.card (I × Fin k)),
      Fin.sum_univ_eq_sum_range (fun a => f (countRank w (fun ω => ∑ i, N ω i) a)) k]
    by_cases hcard : k ≤ Fintype.card (I × Fin k)
    · symm
      apply sum_subset (range_mono hcard)
      intro a ha han
      have hak : k ≤ a := by simpa using han
      have hc : countRank w (fun ω => ∑ i, N ω i) a = 1 := by
        simp only [countRank, ite_eq_left ((hN _).trans hak), mul_one, hws]
      rw [hc, hf1]
    · have hempty : Fintype.card I = 0 := by
        simp only [Fintype.card_prod, Fintype.card_fin] at hcard
        nlinarith
      have : IsEmpty I := Fintype.card_eq_zero_iff.mp hempty
      simp [countRank, hws, hf1]
  rw [hright] at ht
  exact ht

end KServer.RankOrder

end
noncomputable section

namespace KServer.CompatibleBounds
open Finset
open KServer.RankFunctions KServer.RankOrder

/-- The two actual lower-bound sums on a conditional count distribution. -/
def L {Ω : Type*} [Fintype Ω] (k : ℕ) (w : Ω → ℝ) (N : Ω → ℕ) (z : ℝ) : ℝ :=
  ∑ a : Fin k, rank z (countRank w N a.val)
def M {Ω : Type*} [Fintype Ω] (k : ℕ) (w : Ω → ℝ) (N : Ω → ℕ) : ℝ :=
  ∑ a : Fin k, sizeRank (countRank w N a.val)

/-- Lemma superadditivity, with arbitrary dependence and empty child sets. -/
theorem compatible_bounds {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hws : ∑ ω, w ω = 1)
    {k : ℕ} (N : Ω → I → ℕ) (hN : ∀ ω, ∑ i, N ω i ≤ k)
    {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    (∑ i, L k w (fun ω => N ω i) z) ≤ L k w (fun ω => ∑ i, N ω i) z ∧
    (∑ i, M k w (fun ω => N ω i)) ≤ M k w (fun ω => ∑ i, N ω i) ∧
    M k w (fun ω => ∑ i, N ω i) ≤ ∑ ω, w ω * (∑ i, N ω i) := by
  refine ⟨convex_count_superadditivity w hw hws N hN (rank_convex hz)
    (fun p => (rank_derivative z p).differentiableAt) (rank_cutoff z (by norm_num [sstar])),
    convex_count_superadditivity w hw hws N hN sizeRank_convex
    (fun p => (sizeRank_derivative p).differentiableAt) sizeRank_one, ?_⟩
  calc M k w (fun ω => ∑ i, N ω i) ≤
      ∑ a : Fin k, (1 - countRank w (fun ω => ∑ i, N ω i) a.val) := by
        exact sum_le_sum fun a _ => sizeRank_le_complement (countRank_range w hw hws _ _)
    _ = _ := countRank_expected w hws _ hN

lemma sizeRank_antitone : Antitone sizeRank := by
  apply antitone_of_hasDerivAt_nonpos sizeRank_derivative
  intro p
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (le_max_right _ _)

lemma sizeRank_at_cutoff : sizeRank sstar = 1 / 36 := by norm_num [sizeRank, sstar]

lemma sizeRank_below_cutoff {p : ℝ} (hp : p ≤ sstar) : 1 / 36 ≤ sizeRank p := by
  rw [← sizeRank_at_cutoff]
  exact sizeRank_antitone hp

end KServer.CompatibleBounds

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Coarse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.CoarseSchedule
open Finset

structure State where
  active : Bool
  value : ℝ

def Valid (s : State) : Prop := 0 ≤ s.value ∧ (s.active = false → s.value = 0)

noncomputable def update (c δ x : ℝ) (s : State) : State :=
  if s.active then
    if x ≤ 2*c then ⟨false,0⟩
    else if (1+δ)*s.value < x ∨ (1+δ)*x < s.value then ⟨true,x⟩ else s
  else if 5*c ≤ x then ⟨true,x⟩ else s

noncomputable def charge (s t : State) : ℝ := if s.value = t.value then 0 else s.value+t.value
noncomputable def factor (δ : ℝ) : ℝ := 1+2/δ
noncomputable def potential (c δ x : ℝ) (s : State) : ℝ :=
  factor δ * |x-s.value| + (if s.active then 2*(factor δ+1)*c else 0)

lemma update_valid {s : State} (hs : Valid s) {c δ x : ℝ} (hx : 0 ≤ x) :
    Valid (update c δ x s) := by
  unfold update
  split_ifs <;> simp_all [Valid]

noncomputable def run (c δ : ℝ) (x : ℕ → ℝ) (initial : State) : ℕ → State
  | 0 => initial
  | t+1 => update c δ (x (t+1)) (run c δ x initial t)

lemma run_valid {c δ : ℝ} {x : ℕ → ℝ} {initial : State}
    (hx : ∀ t, 0 ≤ x t) (hi : Valid initial) : ∀ t, Valid (run c δ x initial t)
  | 0 => hi
  | t+1 => update_valid (run_valid hx hi t) (hx (t+1))

end KServer.CoarseSchedule


/-! The actual epoch/wholesale recurrence of §03. The old credit is discarded
on a parent refresh, never spent twice. Empty transitions are forced by the
same variation test. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EpochSchedule
variable {J K : Type*} [Fintype J]

def total (x : J → ℝ) : ℝ := ∑ i, x i
def variation (x y : J → ℝ) : ℝ := ∑ i, |x i-y i|
lemma variation_nonneg (x y : J → ℝ) : 0 ≤ variation x y := sum_nonneg fun _ _ => abs_nonneg _
lemma total_nonneg {x : J → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ total x := sum_nonneg fun _ _ => hx _
lemma total_change (x y : J → ℝ) : |total x-total y| ≤ variation x y := by
  rw [total,total,←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _
lemma coordinate_change (x y : J → ℝ) (i : J) : |x i-y i| ≤ variation x y :=
  single_le_sum (fun j _ => abs_nonneg (x j-y j)) (mem_univ i)
lemma variation_triangle (x y z : J → ℝ) : variation x z ≤ variation x y+variation y z := by
  rw [variation,variation,variation,←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

structure State (J : Type*) where
  reference : J → ℝ
  credit : ℝ

def Valid (x : J → ℝ) (s : State J) : Prop :=
  (∀ i, 0 ≤ s.reference i) ∧ 0 ≤ s.credit ∧ s.credit ≤ total s.reference/100 ∧
    variation x s.reference ≤ s.credit

def reset (x y : J → ℝ) (a b : K) (s : State J) : Prop :=
  a≠b ∨ total s.reference/100 < s.credit+variation y x

instance instDecidableReset (x y : J → ℝ) (a b : K) (s : State J) : Decidable (reset x y a b s) := Classical.propDecidable _

def update (x y : J → ℝ) (a b : K) (s : State J) : State J :=
  if reset x y a b s then ⟨y,0⟩ else ⟨s.reference,s.credit+variation y x⟩

lemma update_valid {x y : J → ℝ} {a b : K} {s : State J}
    (hy : ∀ i, 0 ≤ y i) (hs : Valid x s) : Valid y (update x y a b s) := by
  unfold update
  split_ifs with hr
  · refine ⟨hy,le_rfl,div_nonneg (total_nonneg hy) (by norm_num),?_⟩
    simp [variation]
  · have hh := not_or.mp hr
    refine ⟨hs.1,add_nonneg hs.2.1 (variation_nonneg _ _),le_of_not_gt hh.2,?_⟩
    exact (variation_triangle y x s.reference).trans (by linarith [hs.2.2.2])

lemma valid_total {x : J → ℝ} {s : State J} (hs : Valid x s) :
    (99/100:ℝ)*total s.reference ≤ total x ∧ total x ≤ (101/100:ℝ)*total s.reference := by
  have hd := (abs_le.mp ((total_change x s.reference).trans hs.2.2.2))
  constructor <;> linarith [hs.2.2.1]

lemma valid_coordinate {x : J → ℝ} {s : State J} (hs : Valid x s) (i : J) :
    s.reference i-total s.reference/100 ≤ x i ∧ x i ≤ s.reference i+total s.reference/100 := by
  have hd := abs_le.mp ((coordinate_change x s.reference i).trans hs.2.2.2)
  constructor <;> linarith [hs.2.2.1]

def wholesale (x y : J → ℝ) (a b : K) (s : State J) : ℝ :=
  if reset x y a b s then total x+total y else 0

def parentCharge (x y : J → ℝ) (a b : K) : ℝ := by
  classical
  exact if a≠b then total x+total y else 0

def run (x : ℕ → J → ℝ) (key : ℕ → K) : ℕ → State J
  | 0 => ⟨x 0,0⟩
  | t+1 => update (x t) (x (t+1)) (key t) (key (t+1)) (run x key t)

lemma run_valid (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) :
    ∀ t, Valid (x t) (run x key t) := by
  intro t
  induction t with
  | zero => refine ⟨hx 0,le_rfl,by exact div_nonneg (total_nonneg (hx 0)) (by norm_num),?_⟩; simp [run,variation]
  | succ t ih => exact update_valid (hx (t+1)) ih

/-- Exact dominant selection; the same reference, hence the same mark, is
held until a wholesale event. -/
def dominant (s : State J) : Option J :=
  if h : ∃ i, 0 < total s.reference ∧ (85/100:ℝ)*total s.reference ≤ s.reference i
  then some h.choose else none

lemma dominant_large {x : J → ℝ} {s : State J} {o : J} (hs : Valid x s)
    (ho : dominant s=some o) : (84/100:ℝ)*total s.reference ≤ x o := by
  unfold dominant at ho
  split_ifs at ho with h
  · have he : h.choose=o := Option.some.inj ho
    have hh := h.choose_spec
    rw [he] at hh
    linarith [(valid_coordinate hs o).1]

lemma regular_small {x : J → ℝ} {s : State J} {i : J} (hs : Valid x s)
    (hi : dominant s≠some i) : x i ≤ (86/100:ℝ)*total s.reference := by
  classical
  have ha := total_nonneg hs.1
  have hh : s.reference i ≤ (85/100:ℝ)*total s.reference := by
    by_cases hp : 0 < total s.reference
    · by_contra hle
      have hbig : (85/100:ℝ)*total s.reference ≤ s.reference i := le_of_lt (lt_of_not_ge hle)
      have hex : ∃ j, 0 < total s.reference ∧ (85/100:ℝ)*total s.reference ≤ s.reference j := ⟨i,hp,hbig⟩
      have heq : hex.choose=i := by
        by_contra hn
        have hsum := sum_le_sum_of_subset_of_nonneg (show ({hex.choose,i} : Finset J) ⊆ univ by simp)
          (fun j _ _ => hs.1 j)
        simp only [sum_pair hn] at hsum
        change s.reference hex.choose+s.reference i ≤ total s.reference at hsum
        linarith [hex.choose_spec.2]
      exact hi (by simp [dominant,hex,heq])
    · have hz : total s.reference=0 := le_antisymm (le_of_not_gt hp) ha
      have hb := single_le_sum (fun j _ => hs.1 j) (mem_univ i)
      change s.reference i ≤ total s.reference at hb
      rw [hz] at hb ⊢
      simpa using hb
  linarith [(valid_coordinate hs i).2]

lemma side_total [DecidableEq J] {x : J → ℝ} {s : State J} {o : J} (hs : Valid x s)
    (ho : dominant s=some o) : (∑ i ∈ univ.erase o, x i) ≤ (16/100:ℝ)*total s.reference := by
  classical
  have hr : (85/100:ℝ)*total s.reference ≤ s.reference o := by
    unfold dominant at ho
    split_ifs at ho with h
    · have he : h.choose=o := Option.some.inj ho
      simpa only [he] using h.choose_spec.2
  have hd : (∑ i ∈ univ.erase o, x i) ≤ (∑ i ∈ univ.erase o, s.reference i)+variation x s.reference := by
    calc _ ≤ (∑ i ∈ univ.erase o, s.reference i)+(∑ i ∈ univ.erase o, |x i-s.reference i|) := by
          rw [←sum_add_distrib]
          exact sum_le_sum fun i _ => by linarith [le_abs_self (x i-s.reference i)]
         _ ≤ _ := by
          have hn : (∑ i ∈ univ.erase o, |x i-s.reference i|) ≤ variation x s.reference :=
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _ => abs_nonneg _)
          exact add_le_add le_rfl hn
  have he := sum_erase_add univ s.reference (mem_univ o)
  change (∑ i ∈ univ.erase o, s.reference i)+s.reference o=total s.reference at he
  linarith [hs.2.2.1,hs.2.2.2]

end KServer.EpochSchedule

namespace KServer.CoarseProcess
open RankTracking RankFunctions CoarseSchedule
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Literal sum of the independently maintained size-rank references. -/
def estimate (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, sizeRank (held (factorTest sizeRank δ) (P a).p t ω)
def size (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, sizeRank ((P a).p t ω)

lemma estimate_nonneg (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ estimate δ P t ω := sum_nonneg fun _ _ => sizeRank_nonneg _
lemma size_nonneg (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ size P t ω := sum_nonneg fun _ _ => sizeRank_nonneg _

lemma estimate_accuracy {δ : ℝ} (hδ : 0 < δ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    size P t ω ≤ (1+δ)*estimate δ P t ω ∧
      estimate δ P t ω ≤ (1+δ)*size P t ω := by
  constructor
  · rw [estimate,mul_sum]
    apply sum_le_sum
    intro a _
    have hh := (factor_held_accurate sizeRank hδ (fun _ _ => sizeRank_nonneg _) (P a).range t ω).1
    exact (inv_mul_le_iff₀ (by linarith : 0 < 1+δ)).mp hh
  · rw [size,mul_sum]
    exact sum_le_sum fun a _ =>
      (factor_held_accurate sizeRank hδ (fun _ _ => sizeRank_nonneg _) (P a).range t ω).2

/-- All invariants are established after actually executing the hysteretic rule. -/
lemma update_accuracy {c δ x : ℝ} {s : CoarseSchedule.State}
    (hc : 0 < c) (hδ : 0 < δ) (hx : 0 ≤ x) (hs : CoarseSchedule.Valid s) :
    let a := CoarseSchedule.update c δ x s
    (a.active=true → 2*c < x ∧ x ≤ (1+δ)*a.value ∧ a.value ≤ (1+δ)*x) ∧
    (a.active=false → x < 5*c ∧ a.value=0) := by
  have he : x ≤ (1+δ)*x := by nlinarith [mul_nonneg hδ.le hx]
  cases ha : s.active with
  | false =>
    by_cases ht : 5*c ≤ x
    · simp only [CoarseSchedule.update,ha,Bool.false_eq_true,ite_false,ite_eq_left ht]
      simp only [Bool.true_eq_false, false_implies, and_true, true_implies]
      exact ⟨by linarith,he,he⟩
    · simp [CoarseSchedule.update,ha,ht,hs.2 ha,lt_of_not_ge ht]
  | true =>
    by_cases ht : x ≤ 2*c
    · simp [CoarseSchedule.update,ha,ht,show x < 5*c by linarith]
    · by_cases hf : (1+δ)*s.value < x ∨ (1+δ)*x < s.value
      · simp only [CoarseSchedule.update,ha,ite_true,ite_eq_right ht,ite_eq_left hf]
        simp only [Bool.true_eq_false,false_implies,and_true,true_implies]
        exact ⟨lt_of_not_ge ht,he,he⟩
      · simp only [CoarseSchedule.update,ha,ite_true,ite_eq_right ht,ite_eq_right hf]
        simp only [Bool.true_eq_false,false_implies,and_true,true_implies]
        have hh := not_or.mp hf
        exact ⟨lt_of_not_ge ht,le_of_not_gt hh.1,le_of_not_gt hh.2⟩

/-- Trackers are not reinitialized; the active state alone is updated. -/
def active (c δ : ℝ) (P : R → FilteredRanks w) (ω : Ω) : ℕ → CoarseSchedule.State :=
  CoarseSchedule.run c δ (fun t => estimate δ P t ω)
    (CoarseSchedule.update c δ (estimate δ P 0 ω) ⟨false,0⟩)

lemma active_valid (c δ : ℝ) (P : R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    CoarseSchedule.Valid (active c δ P ω t) :=
  run_valid (fun t => estimate_nonneg δ P t ω)
    (update_valid (by simp [CoarseSchedule.Valid]) (estimate_nonneg δ P 0 ω)) t

lemma active_accuracy {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    let a := active c δ P ω t
    (a.active=true → (9/10)*size P t ω ≤ a.value ∧ a.value ≤ (11/10)*size P t ω ∧ c ≤ size P t ω) ∧
    (10*c ≤ size P t ω → a.active=true) := by
  have hx := estimate_nonneg δ P t ω
  have hm := size_nonneg P t ω
  have hh : let a := active c δ P ω t
      (a.active=true → 2*c < estimate δ P t ω ∧ estimate δ P t ω ≤ (1+δ)*a.value ∧
        a.value ≤ (1+δ)*estimate δ P t ω) ∧
      (a.active=false → estimate δ P t ω < 5*c ∧ a.value=0) := by
    cases t with
    | zero => exact update_accuracy hc hδ hx (by simp [CoarseSchedule.Valid])
    | succ t => exact update_accuracy hc hδ hx (active_valid c δ P ω t)
  have hrough : (1+δ)^2 ≤ 11/10 := by nlinarith [sq_nonneg (δ-1/1000)]
  have hs := estimate_accuracy hδ P t ω
  have hav : 0 ≤ (active c δ P ω t).value := (active_valid c δ P ω t).1
  constructor
  · intro ha
    have h := hh.1 ha
    have hmul₁ := mul_le_mul_of_nonneg_left h.2.1 (by linarith : 0 ≤ 1+δ)
    have hmul₂ := mul_le_mul_of_nonneg_left hs.2 (by linarith : 0 ≤ 1+δ)
    have hbound := mul_le_mul_of_nonneg_right hrough hav
    have hbound₂ := mul_le_mul_of_nonneg_right hrough hm
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1-δ) hm]
  · intro hM
    by_contra hn
    have hf : (active c δ P ω t).active=false := Bool.eq_false_of_not_eq_true hn
    have hhf := hh.2 hf
    have hmul := mul_le_mul_of_nonneg_right (show 1+δ ≤ 2 by linarith) hx
    nlinarith


/-- The parent's scalar relative reference, and later the side-total reference,
use exactly the manuscript's two-sided factor test, including zero crossings. -/
def relative (δ : ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := held (factorTest id δ) x

omit [Fintype Ω] in
lemma relative_nonneg {δ : ℝ} (x : ℕ → Ω → ℝ) (hx : ∀ t ω, 0 ≤ x t ω) (t : ℕ) (ω : Ω) :
    0 ≤ relative δ x t ω := by
  induction t with
  | zero => exact hx 0 ω
  | succ t ih =>
    simp only [relative,held]
    split_ifs
    · exact hx (t+1) ω
    · exact ih

omit [Fintype Ω] in
lemma relative_accuracy {δ : ℝ} (hδ : 0 < δ) (x : ℕ → Ω → ℝ)
    (hx : ∀ t ω, 0 ≤ x t ω) (t : ℕ) (ω : Ω) :
    x t ω ≤ (1+δ)*relative δ x t ω ∧ relative δ x t ω ≤ (1+δ)*x t ω := by
  have he (y : ℝ) (hy : 0 ≤ y) : y ≤ (1+δ)*y := by nlinarith [mul_nonneg hδ.le hy]
  cases t with
  | zero => exact ⟨he _ (hx _ _),he _ (hx _ _)⟩
  | succ t =>
    simp only [relative,held]
    split_ifs with ht
    · exact ⟨he _ (hx _ _),he _ (hx _ _)⟩
    · simp only [factorTest,id_eq,not_or,not_lt] at ht
      exact ⟨ht.2,ht.1⟩

def relativeCharge (δ : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if relative δ x t ω=relative δ x (t+1) ω then 0 else
    relative δ x t ω+relative δ x (t+1) ω

end KServer.CoarseProcess

end
end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseEpoch
open RankTracking CoarseSchedule CoarseProcess
variable {Ω R J : Type} [Fintype Ω] [Fintype R] [Fintype J]
variable {w : Ω → ℝ}

def clipped (c δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  max c (estimate δ P t ω)

def parent (c δ : ℝ) (P : R → FilteredRanks w) : ℕ → Ω → ℝ :=
  relative δ (clipped c δ P)

lemma clipped_nonneg {c : ℝ} (hc : 0 ≤ c) (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ clipped c δ P t ω := hc.trans (le_max_left _ _)

lemma clipped_accuracy {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    max c (size P t ω) ≤ (1+δ)*clipped c δ P t ω ∧
      clipped c δ P t ω ≤ (1+δ)*max c (size P t ω) := by
  have h := estimate_accuracy hδ P t ω
  have he : 0 ≤ 1+δ := by linarith
  have hcc : c ≤ (1+δ)*c := by nlinarith [mul_nonneg hδ.le hc]
  constructor
  · apply max_le
    · exact hcc.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) he)
    · exact h.1.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) he)
  · apply max_le
    · exact (le_max_left _ _).trans (by nlinarith [mul_nonneg hδ.le (hc.trans (le_max_left c (size P t ω)))])
    · exact h.2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) he)

lemma parent_accuracy {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    max c (size P t ω) ≤ (1+δ)^2*parent c δ P t ω ∧
      parent c δ P t ω ≤ (1+δ)^2*max c (size P t ω) := by
  have ha := clipped_accuracy hc hδ P t ω
  have hb := relative_accuracy hδ (clipped c δ P) (clipped_nonneg hc δ P) t ω
  change clipped c δ P t ω ≤ (1+δ)*parent c δ P t ω ∧ parent c δ P t ω ≤ (1+δ)*clipped c δ P t ω at hb
  have he : 0 ≤ 1+δ := by linarith
  constructor
  · exact ha.1.trans (by nlinarith [mul_le_mul_of_nonneg_left hb.1 he])
  · exact hb.2.trans (by nlinarith [mul_le_mul_of_nonneg_left ha.2 he])

lemma parent_nonneg {c : ℝ} (hc : 0 ≤ c) (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ parent c δ P t ω := relative_nonneg _ (clipped_nonneg hc δ P) t ω

def vector (c δ : ℝ) (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) : J → ℝ :=
  fun i => (active c δ (P i) ω t).value

omit [Fintype J] in
lemma vector_nonneg (c δ : ℝ) (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) (i : J) :
    0 ≤ vector c δ P ω t i := (active_valid c δ (P i) ω t).1

lemma value_bound {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    (active c δ P ω t).value ≤ (11/10)*size P t ω := by
  cases ha : (active c δ P ω t).active with
  | true => exact ((active_accuracy hc hδ hδu P ω t).1 ha).2.1
  | false => rw [(active_valid c δ P ω t).2 ha]; exact mul_nonneg (by norm_num) (size_nonneg P t ω)

end KServer.CoarseEpoch

end


noncomputable section
open scoped BigOperators
open Finset
local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p
namespace KServer.CoarseSide
open RankTracking CoarseSchedule EpochSchedule

/-- Relative reference with genuine wholesale resets. Resetting discards,
rather than spends, the unused scalar variation credit. -/
def held (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Prop) : ℕ → ℝ
  | 0 => x 0
  | t+1 => if reset t ∨ factorTest id δ (x (t+1)) (held δ x reset t)
      then x (t+1) else held δ x reset t

lemma held_nonneg (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Prop) (hx : ∀ t, 0 ≤ x t) (t : ℕ) :
    0 ≤ held δ x reset t := by
  induction t with
  | zero => exact hx 0
  | succ t ih => simp only [held]; split_ifs; exact hx (t+1); exact ih

lemma held_accuracy {δ : ℝ} (hδ : 0 < δ) (x : ℕ → ℝ) (reset : ℕ → Prop)
    (hx : ∀ t, 0 ≤ x t) (t : ℕ) :
    x t ≤ (1+δ)*held δ x reset t ∧ held δ x reset t ≤ (1+δ)*x t := by
  have he (t : ℕ) : x t ≤ (1+δ)*x t := by nlinarith [mul_nonneg hδ.le (hx t)]
  cases t with
  | zero => exact ⟨he 0,he 0⟩
  | succ t =>
    simp only [held]
    split_ifs with hr
    · exact ⟨he (t+1),he (t+1)⟩
    · have hf := (not_or.mp hr).2
      simp only [factorTest,id_eq,not_or,not_lt] at hf
      exact ⟨hf.2,hf.1⟩

def charge (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Prop) (t : ℕ) : ℝ :=
  if ¬reset t ∧ factorTest id δ (x (t+1)) (held δ x reset t) then x t+x (t+1) else 0

def stepVariation (x : ℕ → ℝ) (reset : ℕ → Prop) (t : ℕ) : ℝ :=
  if reset t then 0 else |x (t+1)-x t|

def C (δ : ℝ) : ℝ := (1+δ)*factor δ

variable {J K : Type} [Fintype J]

def side (x : J → ℝ) (s : EpochSchedule.State J) : ℝ :=
  ∑ i, if dominant s=some i then 0 else if (dominant s).isSome then x i else 0

lemma side_nonneg {x : J → ℝ} (hx : ∀ i, 0 ≤ x i) (s : EpochSchedule.State J) :
    0 ≤ side x s := by
  apply sum_nonneg; intro i _; split_ifs; rfl; exact hx i; rfl

/-- Actual side totals and reset times are derived from the epoch recurrence. -/
def sideInput (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : ℝ := side (x t) (run x key t)
def epochReset (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : Prop :=
  EpochSchedule.reset (x t) (x (t+1)) (key t) (key (t+1)) (run x key t)

end KServer.CoarseSide

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseParameters

lemma regular_log_comparison {x : ℝ} (hx : (50/43:ℝ) ≤ x) :
    (1/20:ℝ)*(1+Real.log x) ≤ Real.log ((81/100:ℝ)*x+2/11) := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < (81/100:ℝ)*x+2/11 := by positivity
  have hs : x ≤ ((81/100:ℝ)*x+2/11)^2 := by nlinarith [sq_nonneg (x-50/43)]
  have hl := Real.log_le_log hx0 hs
  rw [Real.log_pow] at hl
  have hl₀ : (7/50:ℝ) ≤ Real.log x := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < (50/43:ℝ) by norm_num)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) hx)
  nlinarith

lemma dominant_log_comparison {u m : ℝ} (hu : 0 ≤ u) (huu : u ≤ 1/4)
    (hm : 1+u/2 ≤ m) : u/3 ≤ Real.log m := by
  have hpos : 0 < 1+u/2 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hi : (1+u/2)⁻¹ ≤ 1-u/3 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  have hl := Real.log_le_log hpos hm
  linarith

variable {J : Type} [Fintype J]

/-- Quantitative size-ratio estimate from the genuine superadditive parent
size, without discarding the child's own true size. -/
lemma size_ratio {M a : J → ℝ} {V : ℝ} (hM : ∀ i, 0 ≤ M i)
    (_ : ∀ i, 0 ≤ a i) (hupper : ∀ i, a i ≤ (11/10)*M i)
    (hV : (∑ i,M i) ≤ V) (i : J) (hMi : 0 < M i) (hai : 0 < a i)
    (hlower : (9/10)*M i ≤ a i) :
    1+(9/11)*((∑ j,a j)/a i-1) ≤ V/M i := by
  classical
  have hs : (∑ j,a j)-a i ≤ (11/10)*(V-M i) := by
    have h := sum_le_sum (s:=univ.erase i) (f:=a) (g:=fun j => (11/10:ℝ)*M j) (fun j _ => hupper j)
    rw [←mul_sum,sum_erase_eq_sub (mem_univ i),sum_erase_eq_sub (mem_univ i)] at h
    nlinarith
  have hVm : M i ≤ V := (single_le_sum (fun j _ => hM j) (mem_univ i)).trans hV
  have hx := mul_le_mul_of_nonneg_right hlower (sub_nonneg.mpr hVm)
  apply (le_div_iff₀ hMi).mpr
  apply (mul_le_mul_iff_left₀ hai).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hs hMi.le]

lemma regular_gap {M a : J → ℝ} {V A : ℝ} (hM : ∀ i, 0 ≤ M i)
    (ha : ∀ i, 0 ≤ a i) (hupper : ∀ i, a i ≤ (11/10)*M i)
    (hV : (∑ i,M i) ≤ V) (i : J) (hMi : 0 < M i) (hai : 0 < a i)
    (hlower : (9/10)*M i ≤ a i) (hA : (99/100)*A ≤ ∑ j,a j)
    (hreg : a i ≤ (86/100)*A) :
    (1/20:ℝ)*(1+Real.log (A/a i)) ≤ Real.log (V/M i) := by
  have hx : (50/43:ℝ) ≤ A/a i := (le_div_iff₀ hai).mpr (by linarith)
  have hr := size_ratio hM ha hupper hV i hMi hai hlower
  have hm : (81/100:ℝ)*(A/a i)+2/11 ≤ V/M i := by
    have h := div_le_div_of_nonneg_right hA hai.le
    rw [mul_div_assoc] at h
    nlinarith
  exact (regular_log_comparison hx).trans (Real.log_le_log (by positivity) hm)

lemma dominant_gap {M a : J → ℝ} {V A U : ℝ} (hM : ∀ i, 0 ≤ M i)
    (ha : ∀ i, 0 ≤ a i) (hupper : ∀ i, a i ≤ (11/10)*M i)
    (hV : (∑ i,M i) ≤ V) (i : J) (hMi : 0 < M i) (hai : 0 < a i)
    (hlower : (9/10)*M i ≤ a i) (hA : 0 < A) (haA : a i ≤ (101/100)*A)
    (hU : 0 ≤ U) (hUs : U ≤ (1001/1000)*((∑ j,a j)-a i))
    (hUu : U/A ≤ 1/4) :
    (1/20:ℝ)*(U/A) ≤ Real.log (V/M i) := by
  have hu : 0 ≤ U/A := div_nonneg hU hA.le
  have hr := size_ratio hM ha hupper hV i hMi hai hlower
  have hs : 0 ≤ (∑ j,a j)-a i := sub_nonneg.mpr (single_le_sum (fun j _ => ha j) (mem_univ i))
  have hb : U*a i ≤ (18/11)*A*((∑ j,a j)-a i) := by
    have h₁ := mul_le_mul_of_nonneg_right hUs hai.le
    have h₂ := mul_le_mul_of_nonneg_left haA hs
    nlinarith
  have hratio : U/A/2 ≤ (9/11)*((∑ j,a j)/a i-1) := by
    apply (mul_le_mul_iff_right₀ hA).mp
    apply (mul_le_mul_iff_right₀ hai).mp
    field_simp
    nlinarith
  have hl := dominant_log_comparison hu hUu (by linarith : 1+(U/A)/2 ≤ V/M i)
  linarith

/-- Literal true and held beta parameters. Their coefficient is chosen only
once; these functions do not depend on the horizon or posterior law. -/
def beta (k c cb ell M : ℝ) : ℝ := 3+cb/ell*Real.log (k/max M c)
def lowerSize (c δ H : ℝ) : ℝ := max c (H/(1+δ)^2)
def upperBeta (k c cb ell δ H : ℝ) : ℝ := 3+cb/ell*Real.log (k/lowerSize c δ H)

lemma beta_difference {k c cb ell M V : ℝ} (hk : 0 < k) (hc : 0 < c) (hM : c ≤ M) (hMV : M ≤ V) :
    beta k c cb ell M-beta k c cb ell V=cb/ell*Real.log (V/M) := by
  have hM0 : 0 < M := hc.trans_le hM
  have hV0 : 0 < V := hM0.trans_le hMV
  simp only [beta,max_eq_left hM,max_eq_left (hM.trans hMV)]
  rw [Real.log_div hk.ne' hM0.ne',Real.log_div hk.ne' hV0.ne',Real.log_div hV0.ne' hM0.ne']
  ring

lemma lowerSize_accuracy {c δ X H : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hX : c ≤ X)
    (_ : 0 ≤ H) (hlo : X ≤ (1+δ)^2*H) (hhi : H ≤ (1+δ)^2*X) :
    0 < lowerSize c δ H ∧ lowerSize c δ H ≤ X ∧ X ≤ (1+δ)^4*lowerSize c δ H := by
  have he : 0 < 1+δ := by linarith
  have he2 : 0 < (1+δ)^2 := sq_pos_of_pos he
  have hlow : H/(1+δ)^2 ≤ X := (div_le_iff₀ he2).mpr (by nlinarith)
  have hmax : H/(1+δ)^2 ≤ lowerSize c δ H := le_max_right _ _
  have hm : H ≤ (1+δ)^2*lowerSize c δ H := by
    have h := (div_le_iff₀ he2).mp hmax
    nlinarith
  refine ⟨hc.trans_le (le_max_left _ _),max_le hX hlow,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hm he2.le]

lemma beta_upper_error {k c cb ell δ X H : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hcb : 0 ≤ cb) (hell : 0 < ell) (hδ : 0 < δ) (hX : c ≤ X)
    (hH : 0 ≤ H) (hlo : X ≤ (1+δ)^2*H) (hhi : H ≤ (1+δ)^2*X) :
    beta k c cb ell X ≤ upperBeta k c cb ell δ H ∧
      upperBeta k c cb ell δ H ≤ beta k c cb ell X+4*cb*δ/ell := by
  have h := lowerSize_accuracy hc hδ hX hH hlo hhi
  have hX0 : 0 < X := hc.trans_le hX
  have hfac : 0 ≤ cb/ell := div_nonneg hcb hell.le
  have he : 0 < 1+δ := by linarith
  have hlog : 0 ≤ Real.log (X/lowerSize c δ H) ∧ Real.log (X/lowerSize c δ H) ≤ 4*δ := by
    constructor
    · apply Real.log_nonneg
      exact (one_le_div h.1).mpr h.2.1
    · have hb : X/lowerSize c δ H ≤ (1+δ)^4 := (div_le_iff₀ h.1).mpr (by nlinarith [h.2.2])
      have hl := Real.log_le_log (div_pos hX0 h.1) hb
      rw [Real.log_pow] at hl
      have hh := Real.log_le_sub_one_of_pos he
      nlinarith
  have hd : upperBeta k c cb ell δ H-beta k c cb ell X=cb/ell*Real.log (X/lowerSize c δ H) := by
    simp only [beta,upperBeta,max_eq_left hX]
    rw [Real.log_div hk.ne' h.1.ne',Real.log_div hk.ne' hX0.ne',Real.log_div hX0.ne' h.1.ne']
    ring
  constructor
  · nlinarith [mul_nonneg hfac hlog.1]
  · have hh := mul_le_mul_of_nonneg_left hlog.2 hfac
    have heq : cb/ell*(4*δ)=4*cb*δ/ell := by ring
    rw [heq] at hh
    linarith

end KServer.CoarseParameters

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseScale
open RankTracking RankFunctions CoreFlags
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

lemma size_antitone : Antitone sizeRank := by
  apply antitone_of_hasDerivAt_nonpos sizeRank_derivative
  intro p
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (le_max_right _ _)

lemma rank_size {z p : ℝ} (hz : z ∈ Set.Icc 0 (1/100:ℝ)) (hp : 0 ≤ p) :
    rank z p ≤ 36*sizeRank p := by
  by_cases hs : p ≤ sstar
  · have h := size_antitone hs
    have he : sizeRank sstar=1/36 := by norm_num [sizeRank,sstar]
    rw [he] at h
    linarith [(rank_range hz hp).2]
  · rw [rank_cutoff z (le_of_not_ge hs)]
    exact mul_nonneg (by norm_num) (sizeRank_nonneg p)

def noncore (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if flag (P a) t ω then 0 else FineCaps.estimate δ 0 (P a) t ω

def scale (δ : ℝ) (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (s : EpochSchedule.State J) : ℝ :=
  (EpochSchedule.dominant s).elim 0 (fun i => noncore δ (P i) t ω)

end KServer.CoarseScale

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_OutputDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- The two output formulas, finite-star algebra and static cap-proportion feasibility. -/


noncomputable section
open Finset
open scoped BigOperators
namespace KServer.OutputDynamics
variable {I : Type*} [Fintype I]

def variation (x y : I → ℝ) : ℝ := ∑ i, |x i - y i|
def excess (d : I → ℝ) (q : ℝ) : ℝ := max ((∑ i, d i) - q) 0

def holesI (R : ℝ) (a : I → ℝ) : I → ℝ := fun i => R * a i
def outputI (d : I → ℝ) (q : ℝ) (a : I → ℝ) : I → ℝ :=
  fun i => d i - holesI (excess d q) a i

lemma excess_nonneg (d : I → ℝ) (q : ℝ) : 0 ≤ excess d q := le_max_right _ _

omit [Fintype I] in
lemma holesI_nonneg {R : ℝ} {a : I → ℝ} (hR : 0 ≤ R) (ha : ∀ i, 0 ≤ a i) :
    ∀ i, 0 ≤ holesI R a i := fun i => mul_nonneg hR (ha i)

lemma holesI_sum {a : I → ℝ} (ha : ∑ i, a i = 1) (R : ℝ) :
    ∑ i, holesI R a i = R := by simp [holesI, ← mul_sum, ha]

lemma outputI_budget {a : I → ℝ} (ha : ∑ i, a i = 1) (d : I → ℝ) (q : ℝ) :
    ∑ i, outputI d q a i = min (∑ i, d i) q := by
  unfold outputI
  rw [sum_sub_distrib, holesI_sum ha]
  unfold excess
  by_cases h : (∑ i, d i) ≤ q
  · rw [max_eq_right (by linarith), min_eq_left h]; ring
  · rw [max_eq_left (by linarith), min_eq_right (le_of_not_ge h)]; ring

lemma hole_bound {n B f b : I → ℝ} {β e q : ℝ}
    (hp : (∑ i, (n i - β * B i + f i)) ≤ q)
    (hc : (∑ i, (b i - f i)) ≤ e) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hB : ∀ i, 0 ≤ B i) :
    excess (fun i => n i + b i) q ≤ β * (∑ i, B i) + e := by
  apply max_le
  · have hi : (∑ i, (n i + b i)) - q ≤
        β * (∑ i, B i) + ∑ i, (b i - f i) := by
      have hs : (∑ i, (n i + b i)) - (∑ i, (n i - β * B i + f i)) =
          β * (∑ i, B i) + ∑ i, (b i - f i) := by
        rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl; intro i _; ring
      linarith
    linarith
  · exact add_nonneg (mul_nonneg hβ (sum_nonneg fun i _ => hB i)) he

/-- Rule I at a regular coordinate. This includes S=0 without division. -/
lemma regular_hole {S R β βi e η B a : ℝ}
    (hS : 0 ≤ S) (hR : 0 ≤ R) (he : 0 ≤ e) (hB : 0 ≤ B)
    (ha : 0 ≤ a) (_hη : 0 ≤ 1 + η) (hβ : 0 ≤ β) (hβi : 0 ≤ βi)
    (hr : R ≤ β * S + e) (hp : S * a ≤ (1 + η) * B)
    (hroom : (β * S + e) * (1 + η) ≤ βi * S)
    (hzero : S = 0 → e = 0) : R * a ≤ βi * B := by
  by_cases hs : S = 0
  · have he0 := hzero hs
    have hr0 : R = 0 := by rw [hs, he0] at hr; nlinarith
    rw [hr0, zero_mul]
    exact mul_nonneg hβi hB
  · have hsp : 0 < S := lt_of_le_of_ne hS (Ne.symm hs)
    have h1 := mul_le_mul_of_nonneg_left hp (add_nonneg (mul_nonneg hβ hS) he)
    have h2 := mul_le_mul_of_nonneg_right hroom hB
    have h3 := mul_le_mul_of_nonneg_right hr ha
    nlinarith

lemma dominant_hole {S R β βi e η B a : ℝ}
    (he : 0 ≤ e) (hB : 0 ≤ B) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hβ : 0 ≤ β)
    (hr : R ≤ β * S + e) (hp : S * a ≤ (1 + η) * B)
    (hroom : β * (1 + η) ≤ βi) : R * a ≤ βi * B + e := by
  have h1 := mul_le_mul_of_nonneg_right hr ha
  have h2 := mul_le_mul_of_nonneg_left hp hβ
  have h3 := mul_le_mul_of_nonneg_right hroom hB
  have h4 := mul_le_mul_of_nonneg_left ha1 he
  nlinarith

/-- The error margin used on regular children, including zero core mass. -/
lemma regular_parameter_room {S β βi e η g : ℝ}
    (hS : 0 ≤ S) (he : 0 ≤ e) (hη : η ≤ 1)
    (hgap : β + g ≤ βi) (hηgap : β * η ≤ g / 2)
    (herr : 4 * e ≤ g * S) : (β * S + e) * (1 + η) ≤ βi * S := by
  have hp := mul_le_mul_of_nonneg_right hηgap hS
  have hq := mul_le_mul_of_nonneg_right hgap hS
  have hr := mul_le_mul_of_nonneg_left hη he
  nlinarith

/-- Literal regular-coordinate lower bound for Rule I, and its upper cap. -/
lemma outputI_regular {n B f b a η βi : I → ℝ} {β e q : ℝ}
    (hp : (∑ i, (n i - β * B i + f i)) ≤ q)
    (hc : (∑ i, (b i - f i)) ≤ e) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hB : ∀ i, 0 ≤ B i) (ha : ∀ i, 0 ≤ a i)
    (hprop : ∀ i, (∑ j, B j) * a i ≤ (1 + η i) * B i)
    (hzero : (∑ i, B i) = 0 → e = 0)
    (i : I) (hβi : 0 ≤ βi i) (hη : 0 ≤ 1 + η i)
    (hroom : (β * (∑ j, B j) + e) * (1 + η i) ≤ βi i * (∑ j, B j))
    (fc : ℝ) (hfc : fc ≤ b i) :
    n i - βi i * B i + fc ≤ outputI (fun j => n j + b j) q a i ∧
      outputI (fun j => n j + b j) q a i ≤ n i + b i := by
  have hr := hole_bound hp hc hβ he hB
  have hh := regular_hole (sum_nonneg fun j _ => hB j) (excess_nonneg _ _)
    he (hB i) (ha i) hη hβ hβi hr (hprop i) hroom hzero
  have hn := holesI_nonneg (excess_nonneg (fun j => n j + b j) q) ha i
  unfold outputI holesI at *
  constructor <;> dsimp at * <;> linarith

lemma outputI_dominant {n B f b a η βi : I → ℝ} {β e q : ℝ}
    (hp : (∑ i, (n i - β * B i + f i)) ≤ q)
    (hc : (∑ i, (b i - f i)) ≤ e) (hβ : 0 ≤ β) (he : 0 ≤ e)
    (hB : ∀ i, 0 ≤ B i) (ha : ∀ i, 0 ≤ a i) (has : ∑ i, a i = 1)
    (hprop : ∀ i, (∑ j, B j) * a i ≤ (1 + η i) * B i)
    (o : I) (hroom : β * (1 + η o) ≤ βi o)
    (fc : ℝ) (hfc : fc ≤ b o - e) :
    n o - βi o * B o + fc ≤ outputI (fun j => n j + b j) q a o ∧
      outputI (fun j => n j + b j) q a o ≤ n o + b o := by
  have ha1 : a o ≤ 1 := by
    rw [← has]
    exact single_le_sum (fun j _ => ha j) (mem_univ o)
  have hh := dominant_hole he (hB o) (ha o) ha1 hβ
    (hole_bound hp hc hβ he hB) (hprop o) hroom
  have hn := holesI_nonneg (excess_nonneg (fun j => n j + b j) q) ha o
  unfold outputI holesI at *
  constructor <;> dsimp at * <;> linarith

/-! Rule II: the finite type I here indexes sides only, with the dominant
coordinate stored separately. Thus the formulation includes an empty side set. -/

end KServer.OutputDynamics
end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeldWeights

/-- Literal regular gap weight; zero coordinates are harmless placeholders. -/
def regular (A a : ℝ) : ℝ := 1+max 0 (Real.log (A/a))

lemma regular_one (A a : ℝ) : 1 ≤ regular A a := by
  unfold regular; linarith [le_max_left (0:ℝ) (Real.log (A/a))]

lemma regular_log (A a : ℝ) : 1+Real.log (A/a) ≤ regular A a := by
  unfold regular; exact add_le_add le_rfl (le_max_right (0:ℝ) (Real.log (A/a)))

lemma regular_eq {A a : ℝ} (ha : 0<a) (hA : a≤A) :
    regular A a=1+Real.log (A/a) := by
  exact congrArg (fun x : ℝ => 1+x) (max_eq_right (Real.log_nonneg ((one_le_div ha).mpr hA)))

lemma regular_exp {A a : ℝ} (hA : 0<A) (ha : 0<a) :
    Real.exp (-regular A a) ≤ a/A := by
  have h : Real.log (A/a) ≤ regular A a := by linarith [regular_log A a]
  have he := Real.exp_le_exp.mpr (neg_le_neg h)
  rw [Real.exp_neg (Real.log (A/a)),Real.exp_log (div_pos hA ha)] at he
  simpa only [inv_div] using he

lemma regular_upper {A a k : ℝ} (hk : 1≤k) (hA : 0≤A)
    (hAk : A≤(11/10)*k) (ha : (9/100000:ℝ)≤a) :
    regular A a ≤ 20002*(1+Real.log (k+1)) := by
  have hk0 : 0<k := by linarith
  have ha0 : 0<a := by linarith
  have he : 0≤Real.log (k+1) := Real.log_nonneg (by linarith)
  have hlog : Real.log (A/a) ≤ 20000+Real.log (k+1) := by
    by_cases hAz : A=0
    · simp [hAz]; linarith
    have hA0 : 0<A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hx : A/a ≤ 20000*(k+1) := by
      apply (div_le_iff₀ ha0).mpr
      have hm := mul_le_mul_of_nonneg_left ha (show 0≤20000*(k+1) by positivity)
      nlinarith
    have hl := Real.log_le_log (div_pos hA0 ha0) hx
    rw [Real.log_mul (by norm_num : (20000:ℝ)≠0) (by positivity : k+1≠0)] at hl
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<20000)
    linarith
  have hm : max 0 (Real.log (A/a)) ≤ 20000+Real.log (k+1) := max_le (by linarith) hlog
  unfold regular
  nlinarith

lemma log_reciprocal_lower {u : ℝ} (hu : 0<u) (hu1 : u≤1/4) :
    1 ≤ Real.log (1/u) := by
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hr : (4:ℝ)≤1/u := (le_div_iff₀ hu).mpr (by linarith)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<4) hr
  have he : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  rw [he] at hl
  norm_num at h2
  linarith

lemma side_lower {A a u : ℝ} (_hA : 0<A) (ha : 0<a) (hu : 0<u)
    (hu1 : u≤1/4) (has : a≤2*u*A) :
    (1/2:ℝ)*(1+Real.log (1/u)) ≤ regular A a := by
  have hx : 1/(2*u)≤A/a := by
    apply (div_le_div_iff₀ (show 0<2*u by positivity) ha).mpr
    nlinarith
  have hl := Real.log_le_log (by positivity : 0<1/(2*u)) hx
  rw [Real.log_div (by norm_num) (by positivity),Real.log_one,
    Real.log_mul (by norm_num) hu.ne'] at hl
  have hr : Real.log (1/u) = -Real.log u := by simp
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hrec := log_reciprocal_lower hu hu1
  have hr2 : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh; exact hh
  -- The sharper logarithm relation avoids any numerical estimate of e.
  have hrec2 : 2*Real.log 2≤Real.log (1/u) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4)
      ((le_div_iff₀ hu).mpr (by linarith) : (4:ℝ)≤1/u)
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hw := regular_log A a
  rw [hr] at hrec2 ⊢
  linarith

variable {J : Type} [Fintype J]

omit [Fintype J] in
lemma exp_sum {A : ℝ} {a : J → ℝ} (S : Finset J) (hA : 0<A)
    (ha : ∀ i∈S, 0<a i) (hS : (∑ i∈S,a i)≤(101/100)*A) :
    (∑ i∈S, Real.exp (-regular A (a i))) ≤ 2 := by
  have h := sum_le_sum (s:=S) (fun i hi => regular_exp hA (ha i hi))
  rw [←sum_div] at h
  have hh := (div_le_iff₀ hA).mpr hS
  linarith

omit [Fintype J] in
lemma side_exp_sum {A U : ℝ} {a : J → ℝ} (S : Finset J) (hA : 0<A)
    (ha : ∀ i∈S, 0<a i) (hS : (∑ i∈S,a i)≤2*U) :
    (∑ i∈S, Real.exp (-regular A (a i))) ≤ 2*(U/A) := by
  have h := sum_le_sum (s:=S) (fun i hi => regular_exp hA (ha i hi))
  rw [←sum_div] at h
  have hh := div_le_div_of_nonneg_right hS hA.le
  simpa only [mul_div_assoc] using h.trans hh

end KServer.HeldWeights

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalSimplex
open AdaptiveMinimization SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

/-- Current held parameters and raw ranks. The latter are used only for the
initial minimizing selection, never substituted for the affine rank input. -/
structure Input (J R : Type) [Fintype J] where
  data : SimplexFamilies.Data J R
  ranks : J × R → ℝ
  epoch : ℕ

def prepared (old new : SimplexFamilies.Data J R) : SimplexFamilies.Data J R :=
  { old with flags := preparedFlags old.active new.active new.flags }

def prepare (C ell : ℝ) (old new : SimplexFamilies.Data J R)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  (SimplexFamilies.family C ell).update (prepared old new) p
    (∑ i, core (prepared old new) p i) a

def candidate (C ell : ℝ) (old new : SimplexFamilies.Data J R)
    (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  ChangingDomains.transposeSimplex new.active (∑ i, core (prepared old new) p i) (prepare C ell old new p a)

/-- The membership branch totalizes the mathematical rule off its admitted
rank/parameter domain. The ordinary regular/marked lemmas below prove it is
never used on genuine source data. Wholesale steps use the canonical base. -/
def move (C ell : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ := by
  classical
  exact if old.epoch = new.epoch then
    if candidate C ell old.data new.data p a ∈ ChangingDomains.simplex new.data.active
      then candidate C ell old.data new.data p a else ChangingDomains.canonical new.data.active
  else ChangingDomains.canonical new.data.active

lemma move_mem (C ell : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) :
    move C ell old new p a ∈ ChangingDomains.simplex new.data.active := by
  classical
  unfold move
  split_ifs with he hm
  · exact hm
  · exact ChangingDomains.canonical_mem _
  · exact ChangingDomains.canonical_mem _

/-- Only initialization changes the seed; the potential and coefficient are
the exact source primitives already proved affine in the raw ranks. -/
def model (C ell : ℝ) : Family (Input J R) (J × R) J where
  domain d := ChangingDomains.simplex d.data.active
  compact _data := ChangingDomains.simplex_compact _
  seed d := ⟨(SimplexFamilies.family C ell).update d.data d.ranks
    (∑ i, core d.data d.ranks i) (ChangingDomains.canonical d.data.active),
    (SimplexFamilies.family C ell).update_mem _ _ _ _⟩
  offset _ _ := 0
  coefficient d := SimplexFamilies.coefficient C ell d.data
  offset_continuous _ := continuousOn_const
  coefficient_continuous d := SimplexFamilies.coefficient_continuous C ell d.data

def transport (C ell : ℝ) : Transport (model (J:=J) (R:=R) C ell) where
  map := move C ell
  mem old new p a _ := move_mem C ell old new p a

variable {Ω : Type} [Fintype Ω]

def mass (d : Input J R) : ℝ := ∑ i, core d.data d.ranks i

def run (C ell : ℝ) (d : ℕ → Ω → Input J R) : ℕ → Ω → J → ℝ :=
  state (model C ell) (transport C ell) d (fun t ω => (d t ω).ranks)
    (fun t ω => mass (d t ω))

omit [Fintype Ω] in
lemma run_mem (C ell : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run C ell d t ω ∈ ChangingDomains.simplex (d t ω).data.active :=
  state_mem (model C ell) (transport C ell) d (fun t ω => (d t ω).ranks)
    (fun t ω => mass (d t ω)) t ω

omit [Fintype Ω] in
lemma run_initial (C ell : ℝ) (d : ℕ → Ω → Input J R) (ω : Ω) :
    run C ell d 0 ω=(SimplexFamilies.family C ell).update (d 0 ω).data (d 0 ω).ranks
      (mass (d 0 ω)) (ChangingDomains.canonical (d 0 ω).data.active) := rfl

omit [Fintype Ω] in
lemma run_successor (C ell : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run C ell d (t+1) ω=(SimplexFamilies.family C ell).update (d (t+1) ω).data (d (t+1) ω).ranks
      (mass (d (t+1) ω)) (move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks (run C ell d t ω)) := rfl

end KServer.CausalSimplex

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AllocationSchedule
open EpochSchedule
variable {J K : Type} [Fintype J] [DecidableEq J]

/-- Active domain and literal held epoch mass, rather than a bound supplied to
an allocation interface. -/
def activeSet (x : J → ℝ) : Finset J := univ.filter fun i => 0<x i

def mass (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : ℝ := total (run x key t).reference

def sideHeld (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) : ℕ → ℝ :=
  CoarseSide.held δ (CoarseSide.sideInput x key) (CoarseSide.epochReset x key)

def sideRatio (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : ℝ :=
  sideHeld δ x key t/mass x key t

def weight (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J) : ℝ :=
  if dominant (run x key t)=some i then sideRatio δ x key t
  else HeldWeights.regular (mass x key t) (x t i)

omit [DecidableEq J] in
lemma mem_activeSet (x : J → ℝ) (i : J) : i∈activeSet x ↔ 0<x i := by simp [activeSet]

omit [DecidableEq J] in
lemma sum_activeSet {x : J → ℝ} (hx : ∀ i, 0 ≤ x i) : (∑ i∈activeSet x,x i)=total x := by
  apply sum_subset (by simp [activeSet])
  intro i _ hi
  have hh : ¬0<x i := by simpa [activeSet] using hi
  exact le_antisymm (le_of_not_gt hh) (hx i)

omit [DecidableEq J] in
lemma mass_nonneg (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) :
    0 ≤ mass x key t := total_nonneg (run_valid x key hx t).1

omit [DecidableEq J] in
lemma mass_accuracy (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) :
    (99/100:ℝ)*mass x key t ≤ total (x t) ∧ total (x t) ≤ (101/100:ℝ)*mass x key t :=
  valid_total (run_valid x key hx t)

omit [DecidableEq J] in
lemma dominant_mass_pos {s : State J} {o : J} (ho : dominant s=some o) :
    0<total s.reference := by
  unfold dominant at ho
  split_ifs at ho with h
  exact h.choose_spec.1

omit [DecidableEq J] in
lemma marked_active (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) : o∈activeSet (x t) := by
  rw [mem_activeSet]
  have hA := dominant_mass_pos ho
  have hm := dominant_large (run_valid x key hx t) ho
  linarith

local instance instDecidable_solutions_r1c558b_1 (p : Prop) : Decidable p := Classical.propDecidable p
lemma side_eq_erase (x : J → ℝ) (s : State J) {o : J} (ho : dominant s=some o) :
    CoarseSide.side x s=∑ i∈univ.erase o,x i := by
  unfold CoarseSide.side
  simp only [ho,Option.isSome_some,ite_true,Option.some.injEq]
  rw [sum_ite]
  simp only [sum_const_zero,zero_add]
  congr 1
  ext i
  simp [eq_comm]

omit [DecidableEq J] in
lemma side_held_nonneg (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) : 0 ≤ sideHeld δ x key t :=
  CoarseSide.held_nonneg δ _ _ (fun t => CoarseSide.side_nonneg (hx t) _) t

omit [DecidableEq J] in
lemma side_held_accuracy {δ : ℝ} (hδ : 0<δ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) :
    CoarseSide.sideInput x key t ≤ (1+δ)*sideHeld δ x key t ∧
      sideHeld δ x key t ≤ (1+δ)*CoarseSide.sideInput x key t :=
  CoarseSide.held_accuracy hδ _ _ (fun t => CoarseSide.side_nonneg (hx t) _) t

omit [DecidableEq J] in
lemma side_ratio_nonneg (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) : 0 ≤ sideRatio δ x key t :=
  div_nonneg (side_held_nonneg δ x key hx t) (mass_nonneg x key hx t)

lemma side_ratio_upper {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) : sideRatio δ x key t ≤ 1/4 := by
  have hA := dominant_mass_pos ho
  have hs := side_total (run_valid x key hx t) ho
  have hU := (side_held_accuracy hδ x key hx t).2
  change sideHeld δ x key t ≤ (1+δ)*CoarseSide.side (x t) (run x key t) at hU
  rw [side_eq_erase _ _ ho] at hU
  have he : (1+δ)*((16/100:ℝ)*mass x key t)  ≤  mass x key t/4 := by
    dsimp [mass]
    nlinarith [mul_nonneg hA.le (show 0 ≤ 1/1000-δ by linarith)]
  apply (div_le_iff₀ hA).mpr
  exact (hU.trans (mul_le_mul_of_nonneg_left hs (by linarith))).trans (by simpa [mass,div_eq_mul_inv,mul_comm] using he)

omit [DecidableEq J] in
lemma side_zero_iff {δ : ℝ} (hδ : 0<δ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) :
    sideRatio δ x key t=0 ↔ CoarseSide.sideInput x key t=0 := by
  have hA := dominant_mass_pos ho
  have hU := side_held_accuracy hδ x key hx t
  have hN := side_held_nonneg δ x key hx t
  have hT := CoarseSide.side_nonneg (hx t) (run x key t)
  change 0 ≤ CoarseSide.sideInput x key t at hT
  rw [sideRatio,div_eq_zero_iff]
  have hm : mass x key t≠0 := ne_of_gt hA
  simp only [hm,or_false]
  constructor <;> intro hz
  · rw [hz,mul_zero] at hU
    exact le_antisymm hU.1 hT
  · rw [hz,mul_zero] at hU
    exact le_antisymm hU.2 hN

lemma marked_zero_singleton {δ : ℝ} (hδ : 0<δ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) {o : J} (ho : dominant (run x key t)=some o)
    (hu : sideRatio δ x key t=0) : activeSet (x t)={o} := by
  have hz := (side_zero_iff hδ x key hx t ho).mp hu
  change CoarseSide.side (x t) (run x key t)=0 at hz
  rw [side_eq_erase _ _ ho] at hz
  ext i
  simp only [mem_singleton]
  constructor
  · intro hi
    by_contra hn
    have hb := single_le_sum (fun j _ => hx t j) (show i∈univ.erase o by simp [hn])
    rw [hz] at hb
    exact (not_lt_of_ge hb) ((mem_activeSet _ _).mp hi)
  · intro hi
    subst i
    exact marked_active x key hx t ho

/-- On the true active sides, held logarithmic weights satisfy the special
marked profile condition used in the decrement-gap argument. -/
lemma weight_side_lower {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o i : J} (ho : dominant (run x key t)=some o)
    (hi : i∈activeSet (x t)) (hio : i≠o) (hu : 0 < sideRatio δ x key t) :
    (1/2:ℝ)*(1+Real.log (1/sideRatio δ x key t)) ≤ weight δ x key t i := by
  have hA := dominant_mass_pos ho
  have hf : dominant (run x key t)≠some i := by rw [ho]; simpa [eq_comm] using hio
  rw [weight,ite_eq_right hf]
  apply HeldWeights.side_lower hA ((mem_activeSet _ _).mp hi) hu (side_ratio_upper hδ hδu x key hx t ho)
  have hb := single_le_sum (fun j _ => hx t j) (show i∈univ.erase o by simp [hio])
  have hU := (side_held_accuracy hδ x key hx t).1
  change CoarseSide.side (x t) (run x key t) ≤ (1+δ)*sideHeld δ x key t at hU
  rw [side_eq_erase _ _ ho] at hU
  have hN := side_held_nonneg δ x key hx t
  have he : 2*sideRatio δ x key t*mass x key t=2*sideHeld δ x key t := by
    unfold sideRatio
    have hm : mass x key t≠0 := ne_of_gt hA
    field_simp [hm]
  change x t i ≤ 2*sideRatio δ x key t*mass x key t
  rw [he]
  nlinarith [mul_nonneg hN (show 0 ≤ 1-δ by linarith)]

end KServer.AllocationSchedule

namespace KServer.AllocationSchedule
local instance instDecidable_solutions_1 (p : Prop) : Decidable p := Classical.propDecidable p
open EpochSchedule
variable {J K : Type} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma mass_upper (x : ℕ → J → ℝ) (key : ℕ → K) {b : ℝ}
    (hb : ∀ t, total (x t) ≤ b) (t : ℕ) : mass x key t ≤ b := by
  induction t with
  | zero => exact hb 0
  | succ t ih =>
    change total (update _ _ _ _ _).reference ≤ b
    unfold update
    split_ifs
    · exact hb (t+1)
    · exact ih

lemma regular_weight (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J)
    (hi : dominant (run x key t)≠some i) :
    weight δ x key t i=HeldWeights.regular (mass x key t) (x t i) := ite_eq_right hi

lemma marked_weight (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J)
    (hi : dominant (run x key t)=some i) :
    weight δ x key t i=sideRatio δ x key t := ite_eq_left hi

lemma weight_regular_one (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) (i : J)
    (hi : dominant (run x key t)≠some i) : 1 ≤ weight δ x key t i := by
  rw [regular_weight δ x key t i hi]
  exact HeldWeights.regular_one _ _

lemma weight_nonneg (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) (i : J) : 0 ≤ weight δ x key t i := by
  unfold weight
  split_ifs
  · exact side_ratio_nonneg δ x key hx t
  · exact (by norm_num : (0:ℝ) ≤ 1).trans (HeldWeights.regular_one _ _)

lemma weight_upper {δ k : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (hk : 1 ≤ k)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (hxk : ∀ t, total (x t) ≤ (11/10)*k)
    (hfloor : ∀ t i, 0<x t i → (9/100000:ℝ) ≤ x t i) (t : ℕ) (i : J) :
    weight δ x key t i ≤ 20002*(1+Real.log (k+1)) := by
  have hl : 0 ≤ Real.log (k+1) := Real.log_nonneg (by linarith)
  by_cases ho : dominant (run x key t)=some i
  · rw [marked_weight δ x key t i ho]
    linarith [side_ratio_upper hδ hδu x key hx t ho]
  · rw [regular_weight δ x key t i ho]
    by_cases hi : 0<x t i
    · exact HeldWeights.regular_upper hk (mass_nonneg x key hx t) (mass_upper x key hxk t) (hfloor t i hi)
    · have hz : x t i=0 := le_antisymm (le_of_not_gt hi) (hx t i)
      simp only [HeldWeights.regular,hz,div_zero,Real.log_zero,max_self]
      linarith

lemma regular_exp_sum (δ : ℝ) (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i, 0 ≤ x t i) (t : ℕ) (hA : 0 < mass x key t)
    (ho : dominant (run x key t)=none) :
    (∑ i∈activeSet (x t),Real.exp (-weight δ x key t i)) ≤ 2 := by
  have hw (i : J) : weight δ x key t i=HeldWeights.regular (mass x key t) (x t i) :=
    regular_weight δ x key t i (by simp [ho])
  simp_rw [hw]
  apply HeldWeights.exp_sum _ hA (fun i hi => (mem_activeSet _ _).mp hi)
  rw [sum_activeSet (hx t)]
  exact (mass_accuracy x key hx t).2

lemma side_exp_sum {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (t : ℕ) {o : J} (ho : dominant (run x key t)=some o) :
    (∑ i∈(activeSet (x t)).erase o, Real.exp (-weight δ x key t i)) ≤ 2*sideRatio δ x key t := by
  have hA := dominant_mass_pos ho
  have he : (∑ i∈(activeSet (x t)).erase o, Real.exp (-weight δ x key t i))=
      ∑ i∈(activeSet (x t)).erase o, Real.exp (-HeldWeights.regular (mass x key t) (x t i)) := by
    apply sum_congr rfl
    intro i hi
    rw [regular_weight δ x key t i (by rw [ho]; simpa [eq_comm] using (mem_erase.mp hi).1)]
  rw [he]
  apply HeldWeights.side_exp_sum _ hA (fun i hi => (mem_activeSet _ _).mp (mem_erase.mp hi).2)
  have hs : (∑ i∈(activeSet (x t)).erase o,x t i) ≤ ∑ i∈univ.erase o,x t i :=
    sum_le_sum_of_subset_of_nonneg (erase_subset_erase o (subset_univ _)) (fun i _ _ => hx t i)
  have hU := (side_held_accuracy hδ x key hx t).1
  change CoarseSide.side (x t) (run x key t) ≤ (1+δ)*sideHeld δ x key t at hU
  rw [side_eq_erase _ _ ho] at hU
  have hN := side_held_nonneg δ x key hx t
  nlinarith [mul_nonneg hN (show 0 ≤ 1-δ by linarith)]

/-- Epoch labels record the actual wholesale test. -/
def epoch (x : ℕ → J → ℝ) (key : ℕ → K) : ℕ → ℕ
  | 0 => 0
  | t+1 => if CoarseSide.epochReset x key t then epoch x key t+1 else epoch x key t

variable {R : Type} [Fintype R]

/-- Empty and genuinely side-free marked domains have the source's zero
potential. The dummy regular kernel is never evaluated by that potential. -/
def zeroData (A : Finset J) (flags : J → R → Bool) : SimplexFamilies.Data J R :=
  { SimplexFamilies.regular A flags (fun _ => 1) (fun _ => 0) (fun _ => le_rfl) with zeroPotential := true }

def data {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (_C ell ct : ℝ)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ) : SimplexFamilies.Data J R := by
  classical
  let A := activeSet (x t)
  let h := weight δ x key t
  exact if A.Nonempty then
    match ho : dominant (run x key t) with
    | none => SimplexFamilies.regular A (flags t) h (fun i => ct*h i/ell)
        (fun i => weight_regular_one δ x key t i (by simp [ho]))
    | some o => if hu : 0 < sideRatio δ x key t then
        SimplexFamilies.marked A (flags t) o h (fun i => ct*h i/ell) (sideRatio δ x key t) hu
          (by linarith [side_ratio_upper hδ hδu x key hx t ho])
          (fun i hi => weight_regular_one δ x key t i (by rw [ho]; simpa [eq_comm] using hi))
      else zeroData A (flags t)
  else zeroData A (flags t)

omit [Fintype R] in
lemma data_active {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (C ell ct : ℝ)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ) :
    (data hδ hδu C ell ct x key hx flags t).active=activeSet (x t) := by
  unfold data
  dsimp only
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

omit [Fintype R] in
lemma data_flags {δ : ℝ} (hδ : 0<δ) (hδu : δ ≤ 1/1000) (C ell ct : ℝ)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ) :
    (data hδ hδu C ell ct x key hx flags t).flags=flags t := by
  unfold data
  dsimp only
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

end KServer.AllocationSchedule

end

/-! Binding the literal filtered-rank size schedule to the live child domain.
In particular no core or positive lower-envelope rank is silently discarded
when the coarse active state turns off. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarProfile
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

def cutoff : ℝ := 1/10000

lemma live_iff {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0<(active cutoff δ P ω t).value ↔ (active cutoff δ P ω t).active=true := by
  have hv:=active_valid cutoff δ P ω t
  have ha:=active_accuracy (by norm_num [cutoff] : 0 < cutoff) hδ hδu P ω t
  constructor
  · intro h
    cases hh : (active cutoff δ P ω t).active with
    | false => have hz:=hv.2 hh; linarith
    | true => rfl
  · intro h
    obtain ⟨hl,_,hf⟩:=ha.1 h
    have hc : 0 < cutoff := by norm_num [cutoff]
    nlinarith

lemma too_small_inactive {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) : size P t ω<10*cutoff := by
  by_contra! h
  have ha:=(active_accuracy (by norm_num [cutoff] : 0 < cutoff) hδ hδu P ω t).2 h
  exact hn ((live_iff hδ hδu P t ω).mpr ha)

lemma inactive_rank_cutoff {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) (r : R) : sstar<(P r).p t ω := by
  have hs:=too_small_inactive hδ hδu P hn
  by_contra! h
  have hr:=CompatibleBounds.sizeRank_below_cutoff h
  have ht : sizeRank ((P r).p t ω)≤ size P t ω :=
    single_le_sum (fun a _=>sizeRank_nonneg ((P a).p t ω)) (mem_univ r)
  norm_num [cutoff] at hs
  linarith

lemma inactive_lower_zero {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) (z : ℝ) :
    (∑ r,rank z ((P r).p t ω))=0 := by
  exact sum_eq_zero fun r _=>rank_cutoff z (inactive_rank_cutoff hδ hδu P hn r).le

lemma inactive_flag_false {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : R → FilteredRanks w) {t : ℕ} {ω : Ω}
    (hn : ¬0<(active cutoff δ P ω t).value) (r : R) : CoreFlags.flag (P r) t ω=false := by
  cases hf : CoreFlags.flag (P r) t ω with
  | false => rfl
  | true =>
    have hl:=inactive_rank_cutoff hδ hδu P hn r
    have hu:=CoreFlags.core_upper (P r) hf
    norm_num [sstar] at hl
    linarith

omit [Fintype J] in
lemma vector_floor {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω) (i : J)
    (hi : 0<vector cutoff δ P ω t i) : (9/100000:ℝ)≤vector cutoff δ P ω t i := by
  have hl:=(live_iff hδ hδu (P i) t ω).mp hi
  obtain ⟨hb,_,hc⟩:=(active_accuracy (by norm_num [cutoff] : 0 < cutoff) hδ hδu (P i) ω t).1 hl
  change (9/100000:ℝ)≤(active cutoff δ (P i) ω t).value
  norm_num [cutoff] at hc
  linarith

lemma vector_total {δ k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (hk : (∑ i,size (P i) t ω)≤k) :
    EpochSchedule.total (vector cutoff δ P ω t)≤(11/10)*k := by
  calc _ ≤ ∑ i,(11/10:ℝ)*size (P i) t ω :=
        sum_le_sum fun i _=>value_bound (by norm_num [cutoff]) hδ hδu (P i) ω t
       _ = (11/10:ℝ)*(∑ i,size (P i) t ω) := (mul_sum _ _ _).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left hk (by norm_num)

lemma flags_supported {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (i : J) (hi : i∉activeSet (vector cutoff δ P ω t)) (r : R) :
    CoreFlags.flag (P i r) t ω=false :=
  inactive_flag_false hδ hδu (P i) (fun h=>hi ((mem_activeSet _ _).mpr h)) r

end KServer.StarProfile

end


/-! Feasibility of the literal held-size scheduler's minimizing simplex law,
including empty and side-free marked epochs. Constants are uniform in degree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledSimplex
attribute [local instance] Classical.propDecidable
open AllocationSchedule EpochSchedule SimplexFamilies AdaptiveAllocation
variable {J R K : Type} [Fintype J] [DecidableEq J] [Fintype R]

lemma singleton_feasible {o : J} {B a : J → ℝ}
    (hB : ∀ i,i≠o → B i=0) (ha : a∈ChangingDomains.simplex {o}) (i : J) :
    (∑ j,B j)*a i=B i := by
  classical
  have hs : (∑ j,B j)=B o := by
    apply sum_eq_single o
    · intro j _ hj; exact hB j hj
    · intro h; exact (h (mem_univ o)).elim
  rw [hs]
  by_cases hi : i=o
  · subst i
    have hsum : (∑ j,a j)=a o := by
      apply sum_eq_single o
      · intro j _ hj; exact ha.2.2 j (by simpa using hj)
      · intro h; exact (h (mem_univ o)).elim
    have hh : a o=1 := by simpa only [hsum,singleton_nonempty,ite_true] using ha.2.1
    rw [hh,mul_one]
  · rw [ha.2.2 i (by simpa [eq_comm] using hi),mul_zero,hB i hi]

omit [DecidableEq J] in
lemma nonempty_mass (x : ℕ → J → ℝ) (key : ℕ → K)
    (hx : ∀ t i,0≤x t i) (t : ℕ) (hn : (activeSet (x t)).Nonempty) :
    0 < mass x key t := by
  classical
  obtain ⟨i,hi⟩:=hn
  have hp: 0<x t i := (mem_activeSet _ _).mp hi
  have hs : x t i≤total (x t) := single_le_sum (fun j _=>hx t j) (mem_univ i)
  have hU: total (x t)≤(101/100:ℝ)*mass x key t := (mass_accuracy x key hx t).2
  linarith

lemma update_feasible {δ C ell ct : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hel : 0<ell) (hct : 0 < ct) (hgap : 700<C*ct)
    (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i,0≤x t i)
    (flags : ℕ → J → R → Bool) (t : ℕ)
    (hmax : ∀ i∈activeSet (x t),ct*weight δ x key t i/ell≤1)
    (p : J × R → ℝ) (hp : ∀ ir,0≤p ir)
    (hf : ∀ i∉activeSet (x t),∀ r,flags t i r=false)
    (a : J → ℝ) (ha : a∈ChangingDomains.simplex (activeSet (x t))) :
    let d:=data hδ hδu C ell ct x key hx flags t
    let B:=core d p
    let a':=(family C ell).update d p (∑ i,B i) a
    ∀ i,(∑ j,B j)*a' i≤(1+ct*weight δ x key t i/ell)*B i := by
  classical
  intro d B a'
  have hB : ∀ i,0≤B i := fun i=>ChangingDomains.core_nonneg (fun i r=>hp (i,r)) i
  have hz : ∀ i∉activeSet (x t),B i=0 := by
    intro i hi
    simp only [B,core,d,data_flags,hf i hi,Bool.false_eq_true,ite_false,sum_const_zero]
  have ha' : a'∈ChangingDomains.simplex (activeSet (x t)) := by
    have h:=(family C ell).update_mem d p (∑ i,B i) a
    change a'∈ChangingDomains.simplex d.active at h
    simpa only [d,data_active] using h
  by_cases hn : (activeSet (x t)).Nonempty
  · cases ho : dominant (run x key t) with
    | none =>
      have hh : ∀ i,1≤weight δ x key t i := fun i=>
        weight_regular_one δ x key t i (by simp [ho])
      have hd : d=regular (activeSet (x t)) (flags t) (weight δ x key t)
          (fun i=>ct*weight δ x key t i/ell) hh := by
        unfold d data
        dsimp only
        rw [ite_eq_left hn]
        split <;> simp_all
      have ht:=regular_exp_sum δ x key hx t (nonempty_mass x key hx t hn) ho
      have hg : 2*(25+32*(2:ℝ))*(1+1)<C*ct := by linarith
      simpa only [a',B,hd] using regular_update_feasible hn (flags t) (weight δ x key t)
        hh hC hel hct hmax (by norm_num : (0:ℝ)≤2) ht hg p hp hf a ha
    | some o =>
      by_cases hu : 0 < sideRatio δ x key t
      · have hh : ∀ i≠o,1≤weight δ x key t i := fun i hi=>
          weight_regular_one δ x key t i (by rw [ho]; simpa [eq_comm] using hi)
        have hum : sideRatio δ x key t≤1 := by linarith [side_ratio_upper hδ hδu x key hx t ho]
        have hd : d=marked (activeSet (x t)) (flags t) o (weight δ x key t)
            (fun i=>ct*weight δ x key t i/ell) (sideRatio δ x key t) hu hum hh := by
          unfold d data
          dsimp only
          rw [ite_eq_left hn]
          split <;> simp_all
        have hg : 2*((25*(1/2:ℝ)+2+32*2)/(1/2))*(1+1)<C*ct := by linarith
        simpa only [a',B,hd] using marked_update_feasible (marked_active x key hx t ho)
          (flags t) (weight δ x key t) hu hum (marked_weight δ x key t o ho) hh
          hC hel hct hmax (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/2)
          (by norm_num : (1/2:ℝ)≤1)
          (fun i hi hio=>weight_side_lower hδ hδu x key hx t ho hi hio hu)
          (side_exp_sum hδ hδu x key hx t ho) hg p hp hf a ha
      · have hu0 : sideRatio δ x key t=0 := le_antisymm (le_of_not_gt hu) (side_ratio_nonneg δ x key hx t)
        have hA:=marked_zero_singleton hδ x key hx t ho hu0
        intro i
        have he:=singleton_feasible (fun j hj=>hz j (by simpa [hA] using hj)) (hA ▸ ha') i
        rw [he]
        have he0 : 0 ≤ ct*weight δ x key t i/ell :=
          div_nonneg (mul_nonneg hct.le (weight_nonneg δ x key hx t i)) hel.le
        nlinarith [mul_nonneg he0 (hB i)]
  · have he : activeSet (x t)=∅ := not_nonempty_iff_eq_empty.mp hn
    have hzero : ∀ i,B i=0 := fun i=>hz i (by simp [he])
    intro i
    simp [hzero]

end KServer.ScheduledSimplex

end


/-! Actual true and held beta parameters. Their gaps follow from the true
parent/child size relation and the literal coarse epoch, not an output oracle. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualParameters
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open CoarseParameters
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

omit [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R] in
lemma log_bound {k M:ℝ} (hk:1≤k) (hM:M≤k) :
    0≤Real.log (k/max M cutoff) ∧ Real.log (k/max M cutoff)≤10000*(1+Real.log (k+1)) := by
  have hc:0 < cutoff:=by norm_num [cutoff]
  have hck:cutoff≤k:=by norm_num [cutoff]; linarith
  have hm:0 < max M cutoff:=hc.trans_le (le_max_right _ _)
  have hmk:max M cutoff≤k:=max_le hM hck
  have hkn:0<k:=by linarith
  have hl:0≤Real.log (k+1):=Real.log_nonneg (by linarith)
  refine ⟨Real.log_nonneg ((one_le_div hm).mpr hmk),?_⟩
  have hq:k/max M cutoff≤10000*(k+1) := by
    apply (div_le_iff₀ hm).mpr
    have h:=mul_le_mul_of_nonneg_left (le_max_right M cutoff) (show 0≤10000*(k+1) by positivity)
    change 10000*(k+1)*(1/10000)≤10000*(k+1)*max M cutoff at h
    linarith
  have hs:=Real.log_le_log (div_pos hkn hm) hq
  rw [Real.log_mul (by norm_num : (10000:ℝ)≠0) (by positivity : k+1≠0)] at hs
  have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10000)
  nlinarith

omit [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R] in
lemma beta_bounds {k M cb:ℝ} (hk:1≤k) (hM:M≤k) (hcb:0 ≤ cb) :
    3≤beta k cutoff cb (1+Real.log (k+1)) M ∧
      beta k cutoff cb (1+Real.log (k+1)) M≤3+10000*cb := by
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  have h:=log_bound hk hM
  have hfac:0 ≤ cb/(1+Real.log (k+1)):=div_nonneg hcb hel.le
  have hm:=mul_le_mul_of_nonneg_left h.2 hfac
  have he:cb/(1+Real.log (k+1))*(10000*(1+Real.log (k+1)))=10000*cb:=by field_simp
  rw [he] at hm
  unfold beta
  constructor
  · linarith [mul_nonneg hfac h.1]
  · linarith

lemma gap {δ k cb:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k) (hcb:0 ≤ cb)
    (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (V:ℕ→Ω→ℝ)
    (hV:∀ t ω,(∑ i,size (P i) t ω)≤V t ω) (t:ℕ) (ω:Ω) (i:J)
    (hi:i∈activeSet (vector cutoff δ P ω t)) :
    cb/20*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/(1+Real.log (k+1))≤
      beta k cutoff cb (1+Real.log (k+1)) (size (P i) t ω)-
      beta k cutoff cb (1+Real.log (k+1)) (V t ω) := by
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  let M:=fun j=>size (P j) t ω
  have hx:=vector_nonneg cutoff δ P ω
  have hc:0 < cutoff:=by norm_num [cutoff]
  have hip:0<x t i:=(mem_activeSet _ _).mp hi
  have ha:=(active_accuracy hc hδ hδu (P i) ω t).1 ((live_iff hδ hδu (P i) t ω).mp hip)
  have hMi:0<M i:=hc.trans_le ha.2.2
  have hMn:∀ j,0≤M j:=fun j=>size_nonneg (P j) t ω
  have hMV:M i≤V t ω:=(single_le_sum (fun j _=>hMn j) (mem_univ i)).trans (hV t ω)
  have hupper:∀ j,x t j≤(11/10)*M j:=fun j=>value_bound hc hδ hδu (P j) ω t
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  rw [beta_difference (by linarith : 0<k) hc ha.2.2 hMV]
  have hfac:0 ≤ cb/(1+Real.log (k+1)):=div_nonneg hcb hel.le
  have hg:(1/20:ℝ)*weight δ x ky t i≤Real.log (V t ω/M i) := by
    by_cases ho:EpochSchedule.dominant (EpochSchedule.run x ky t)=some i
    · rw [marked_weight δ x ky t i ho]
      have hA:0 < mass x ky t:=ScheduledSimplex.nonempty_mass x ky hx t ⟨i,hi⟩
      have hxi:x t i≤(101/100)*mass x ky t:=
        (single_le_sum (fun j _=>hx t j) (mem_univ i)).trans (mass_accuracy x ky hx t).2
      have hUn:0 ≤ sideHeld δ x ky t:=side_held_nonneg δ x ky hx t
      have hUs:sideHeld δ x ky t≤(1001/1000)*((∑ j,x t j)-x t i) := by
        have h:=(side_held_accuracy hδ x ky hx t).2
        change sideHeld δ x ky t≤(1+δ)*CoarseSide.side (x t) (EpochSchedule.run x ky t) at h
        rw [side_eq_erase _ _ ho,sum_erase_eq_sub (mem_univ i)] at h
        have hn:0≤(∑ j,x t j)-x t i:=sub_nonneg.mpr (single_le_sum (fun j _=>hx t j) (mem_univ i))
        nlinarith
      exact dominant_gap hMn (hx t) hupper (hV t ω) i hMi hip ha.1 hA hxi hUn hUs
        (side_ratio_upper hδ hδu x ky hx t ho)
    · rw [regular_weight δ x ky t i ho]
      have hs:=EpochSchedule.regular_small (EpochSchedule.run_valid x ky hx t) ho
      change x t i≤(86/100:ℝ)*mass x ky t at hs
      have hA:0 ≤ mass x ky t:=mass_nonneg x ky hx t
      rw [HeldWeights.regular_eq hip (by linarith)]
      exact regular_gap hMn (hx t) hupper (hV t ω) i hMi hip ha.1 (mass_accuracy x ky hx t).1 hs
  have h:=mul_le_mul_of_nonneg_left hg hfac
  calc _ = cb/(1+Real.log (k+1))*((1/20)*weight δ x ky t i) := by dsimp [x,ky]; ring
       _ ≤ _ := h

omit [Fintype J] [DecidableEq J] in
lemma held_error {δ k cb:ℝ} (hδ:0<δ) (hk:1≤k) (hcb:0 ≤ cb)
    (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    beta k cutoff cb (1+Real.log (k+1)) (size Q t ω)≤
      upperBeta k cutoff cb (1+Real.log (k+1)) δ (parent cutoff δ Q t ω) ∧
      upperBeta k cutoff cb (1+Real.log (k+1)) δ (parent cutoff δ Q t ω)≤
      beta k cutoff cb (1+Real.log (k+1)) (size Q t ω)+4*cb*δ/(1+Real.log (k+1)) := by
  have hc:0 < cutoff:=by norm_num [cutoff]
  have hel:0<1+Real.log (k+1):=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); linarith
  have ha:=parent_accuracy hc.le hδ Q t ω
  have h:=beta_upper_error (by linarith : 0<k) hc hcb hel hδ
    (le_max_left cutoff (size Q t ω)) (parent_nonneg hc.le δ Q t ω) ha.1 ha.2
  have he:max (max cutoff (size Q t ω)) cutoff=max cutoff (size Q t ω) := max_eq_left (le_max_left _ _)
  simp only [beta] at h ⊢
  rw [he] at h
  simpa only [max_comm cutoff (size Q t ω)] using h

end KServer.ActualParameters

end


/-! Prefix causality of the literal epoch, mark, side-total, log-size and
simplex-data recurrences. These equalities use the real input prefix; there
is no reinitialization at a fictitious conditional prefix. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduleCausality
attribute [local instance] Classical.propDecidable
open AllocationSchedule EpochSchedule
variable {J K R : Type} [Fintype J] [DecidableEq J] [Fintype R]

def PrefixEq {A : Type*} (t : ℕ) (a b : ℕ → A) : Prop := ∀ s≤t,a s=b s

end KServer.ScheduleCausality

end


/-! The actual held-profile simplex proportion process, tied to the filtered
child ranks. Inactive coordinates are proved harmless, and feasibility holds
for its actual state at every time, including initialization and wholesale
restarts. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarSimplex
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch
open AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

def flags (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) : J → R → Bool :=
  fun i r=>CoreFlags.flag (P i r) t ω

def input {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (t : ℕ) (ω : Ω) : CausalSimplex.Input J R :=
  ⟨data hδ hδu C ell ct (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (flags P ω) t,
    fun ir=>(P ir.1 ir.2).p t ω,
    epoch (vector cutoff δ P ω) (fun s=>key s ω) t⟩

def proportion {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) : ℕ → Ω → J → ℝ :=
  CausalSimplex.run C ell (input hδ hδu C ell ct P key)

lemma proportion_mem {δ : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (C ell ct : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (t : ℕ) (ω : Ω) :
    proportion hδ hδu C ell ct P key t ω ∈ ChangingDomains.simplex (activeSet (vector cutoff δ P ω t)) := by
  have h:=CausalSimplex.run_mem C ell (input hδ hδu C ell ct P key) t ω
  simpa only [proportion,input,data_active] using h

lemma feasible {δ C ct k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000)
    (hC : 0<C) (hct : 0 < ct) (hctu : ct*20002≤1) (hgap : 700<C*ct) (hk : 1≤k)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω) :
    let ell:=1+Real.log (k+1)
    let B:=fun i=>∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0
    ∀ i,(∑ j,B j)*proportion hδ hδu C ell ct P key t ω i ≤
      (1+ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell)*B i := by
  let ell:=1+Real.log (k+1)
  let d:=input hδ hδu C ell ct P key
  have hel : 0<ell := by
    have h:=Real.log_nonneg (show 1≤k+1 by linarith)
    dsimp [ell]; linarith
  have hm (i:J) (_hi:i∈activeSet (vector cutoff δ P ω t)) :
      ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell≤1 := by
    apply (div_le_iff₀ hel).mpr
    have h:=weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
      (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i
    have hmul:=mul_le_mul_of_nonneg_left h hct.le
    have hmul2:=mul_le_mul_of_nonneg_right hctu hel.le
    change _≤20002*ell at h
    nlinarith
  have hstep (a:J→ℝ) (ha:a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) :=
    ScheduledSimplex.update_feasible hδ hδu hC hel hct hgap
      (vector cutoff δ P ω) (fun s=>key s ω) (vector_nonneg cutoff δ P ω)
      (flags P ω) t hm (d t ω).ranks (fun ir=>(P ir.1 ir.2).range t ω|>.1)
      (fun i hi r=>flags_supported hδ hδu P t ω i hi r) a ha
  have hu (a:J→ℝ) (ha:a∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω t))) :
      ∀ i,(∑ j,∑ r,if CoreFlags.flag (P j r) t ω then (P j r).p t ω else 0)*
        (SimplexFamilies.family C ell).update (d t ω).data (d t ω).ranks
          (CausalSimplex.mass (d t ω)) a i≤
        (1+ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell)*
          (∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0) := by
    simpa only [d,input,CausalSimplex.mass,SimplexFamilies.core,data_flags,flags] using hstep a ha
  change ∀ i,(∑ j,∑ r,if CoreFlags.flag (P j r) t ω then (P j r).p t ω else 0)*
    CausalSimplex.run C ell d t ω i≤
    (1+ct*weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i/ell)*
      (∑ r,if CoreFlags.flag (P i r) t ω then (P i r).p t ω else 0)
  cases t with
  | zero =>
    rw [CausalSimplex.run_initial]
    have hm : ChangingDomains.canonical (d 0 ω).data.active∈
        ChangingDomains.simplex (activeSet (vector cutoff δ P ω 0)) := by
      simpa only [d,input,data_active] using ChangingDomains.canonical_mem (d 0 ω).data.active
    exact hu _ hm
  | succ t =>
    rw [CausalSimplex.run_successor]
    have hm:=CausalSimplex.move_mem C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks
      (CausalSimplex.run C ell d t ω)
    have hm':CausalSimplex.move C ell (d t ω) (d (t+1) ω) (d (t+1) ω).ranks
        (CausalSimplex.run C ell d t ω)∈ChangingDomains.simplex (activeSet (vector cutoff δ P ω (t+1))) := by
      simpa only [d,input,data_active] using hm
    exact hu _ hm'

end KServer.StarSimplex

end


/-! Literal causal side minimizers, including pre-minimization, zero deletion,
wholesale restart, and minimization on the new domain. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalSide
open AdaptiveMinimization SideFamilies
attribute [local instance] Classical.propDecidable Classical.decEq
variable {J R Ω : Type} [Fintype J] [Fintype R]

structure Input (J R : Type) where
  data : SideFamilies.Data J R
  ranks : J × R → ℝ
  epoch : ℕ

def move (c : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) : J → ℝ :=
  if old.epoch=new.epoch ∧ old.data.W=new.data.W then
    SideFamilies.transport c old.data new.data p a else fun _=>0

omit [Fintype R] in
lemma zero_mem (d : SideFamilies.Data J R) :
    (fun _=>0)∈ChangingDomains.sideDomain d.active d.W :=
  ⟨fun _=>le_rfl,by simpa using d.W_nonneg,fun _ _=>rfl⟩

lemma move_mem (c : ℝ) (old new : Input J R) (p : J × R → ℝ) (a : J → ℝ) :
    move c old new p a∈ChangingDomains.sideDomain new.data.active new.data.W := by
  unfold move
  split_ifs with h
  · exact SideFamilies.transport_mem c old.data new.data p a h.2
  · exact zero_mem new.data

def model (c : ℝ) : Family (Input J R) (J × R) J where
  domain d := ChangingDomains.sideDomain d.data.active d.data.W
  compact _ := SideSupported.sideDomain_compact _ _
  seed d := ⟨(SideFamilies.family c).update d.data d.ranks d.data.D (fun _=>0),
    (SideFamilies.family c).update_mem _ _ _ _⟩
  offset d := SideFamilies.offset c d.data
  coefficient d := SideFamilies.coefficient c d.data
  offset_continuous d := SideFamilies.offset_continuous c d.data
  coefficient_continuous d := SideFamilies.coefficient_continuous c d.data

def transport (c : ℝ) : Transport (model (J:=J) (R:=R) c) where
  map := move c
  mem old new p a _ := move_mem c old new p a

def run (c : ℝ) (d : ℕ → Ω → Input J R) : ℕ → Ω → J → ℝ :=
  state (model c) (transport c) d (fun t ω=>(d t ω).ranks) (fun t ω=>(d t ω).data.D)

lemma run_mem (c : ℝ) (d : ℕ → Ω → Input J R) (t : ℕ) (ω : Ω) :
    run c d t ω∈ChangingDomains.sideDomain (d t ω).data.active (d t ω).data.W :=
  state_mem (model c) (transport c) d (fun t ω=>(d t ω).ranks)
    (fun t ω=>(d t ω).data.D) t ω

lemma run_feasible (d : ℕ → Ω → Input J R) {M : ℝ} (t : ℕ) (ω : Ω)
    (hb : 1≤(d t ω).data.b) (hD : 0≤(d t ω).data.D)
    (hM : ∀ i∈(d t ω).data.active,(d t ω).data.b+(d t ω).data.θ i≤M)
    (hW : 2*M<(d t ω).data.W) (hp : ∀ ir,0≤(d t ω).ranks ir)
    (hf : ∀ i∉(d t ω).data.active,∀ r,(d t ω).data.flags i r=false) :
    (∀ i,(d t ω).data.D*run (8*M) d t ω i≤
      ((d t ω).data.b+(d t ω).data.θ i)*core (d t ω).data (d t ω).ranks i) ∧
    ((∑ i,core (d t ω).data (d t ω).ranks i)≤2*(d t ω).data.D → ∀ i,
      (d t ω).data.b*core (d t ω).data (d t ω).ranks i-
        (d t ω).data.θ i*(d t ω).data.z i*(d t ω).data.D≤(d t ω).data.D*run (8*M) d t ω i) := by
  cases t with
  | zero => exact update_feasible _ hb hD hM hW _ hp hf _ (zero_mem _)
  | succ t => exact update_feasible _ hb hD hM hW _ hp hf _ (move_mem _ _ _ _ _)

end KServer.CausalSide

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Caps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rankwise caps used by the star construction: core flags and
both endpoint trackers run for the full history, not only at output times. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TrackedCaps
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoreFlags
variable {Ω R : Type} [Fintype Ω] [Fintype R] {w : Ω → ℝ}

def count (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then 1 else 0

def core (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then (P r).p t ω else 0

def flex (P : R → FilteredRanks w) (z : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then 0 else rank z ((P r).p t ω)

def estimate (P : R → FilteredRanks w) (ξ a : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r, if flag (P r) t ω then 0 else FineCaps.interpolated ξ a (P r) t ω

def cap (P : R → FilteredRanks w) (ξ a κ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r,FineCaps.capTerm ξ a κ (P r) t ω

lemma count_nonneg (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : 0 ≤ count P t ω := by
  exact sum_nonneg fun r _=>by split_ifs <;> norm_num

lemma core_nonneg (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : 0 ≤ core P t ω := by
  exact sum_nonneg fun r _=>by split_ifs; exact ((P r).range t ω).1; rfl

lemma flex_nonneg (P : R → FilteredRanks w) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ))
    (t : ℕ) (ω : Ω) : 0≤flex P z t ω := by
  exact sum_nonneg fun r _=>by split_ifs; rfl; exact rank_nonneg hz _

lemma decomposition (P : R → FilteredRanks w) (z : ℝ) (t : ℕ) (ω : Ω) :
    (∑ r,rank z ((P r).p t ω))=count P t ω-(3+z)*core P t ω+flex P z t ω := by
  unfold count core flex
  rw [mul_sum,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro r _
  cases hf : flag (P r) t ω with
  | false => simp
  | true =>
    have h:=core_upper (P r) hf
    have hp : (P r).p t ω≤pstar := by norm_num [pstar] at *; linarith
    simp only [ite_true,add_zero,rank,ite_eq_left hp]

lemma domination (P : R → FilteredRanks w) {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ))
    (t : ℕ) (ω : Ω) : count P t ω+flex P z t ω≤36*CoarseProcess.size P t ω := by
  unfold count flex CoarseProcess.size
  rw [←sum_add_distrib,mul_sum]
  apply sum_le_sum
  intro r _
  cases hf : flag (P r) t ω with
  | false => simpa using CoarseScale.rank_size hz ((P r).range t ω).1
  | true =>
    have hp : (P r).p t ω ≤ sstar := by
      have h:=core_upper (P r) hf
      norm_num [sstar] at *
      linarith
    have h:=CompatibleBounds.sizeRank_below_cutoff hp
    simp only [ite_true,add_zero]
    linarith

lemma flex_antitone (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    Antitone (fun z=>flex P z t ω) := by
  intro z z' h
  apply sum_le_sum
  intro r _
  split_ifs
  · rfl
  · exact rank_parameter_antitone ((P r).range t ω).1 h

lemma flex_slack (P : R → FilteredRanks w) {z z' : ℝ}
    (hz : z∈Set.Icc 0 (1/100:ℝ)) (hzz : z≤z') (t : ℕ) (ω : Ω) :
    (z'-z)/96*flex P z t ω≤flex P z t ω-flex P z' t ω := by
  unfold flex
  rw [mul_sum,←sum_sub_distrib]
  apply sum_le_sum
  intro r _
  cases hf : flag (P r) t ω with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    have hp : pstar/4≤(P r).p t ω := by
      have h:=noncore_lower (P r) hf
      norm_num [pstar] at *
      linarith
    have h:=mul_le_mul_of_nonneg_left (parameterSlope_compare hz hp).1 (sub_nonneg.mpr hzz)
    rw [rank_parameter_affine z,rank_parameter_affine z']
    rw [rank_parameter_affine z] at h
    nlinarith

lemma estimate_error (P : R → FilteredRanks w) {ξ a z ε : ℝ}
    (hξ : 0<ξ) (ha : a∈Set.Icc 0 1) (hz : z∈Set.Icc 0 (1/100:ℝ))
    (hza : z≤a/100) (hea : a/100-z≤ε) (t : ℕ) (ω : Ω) :
    |estimate P ξ a t ω-flex P z t ω|≤(ξ+ε)*flex P z t ω := by
  unfold estimate flex
  rw [←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro r _
  cases hf : flag (P r) t ω with
  | true => simp
  | false =>
    simpa using FineCaps.noncore_interpolation_error hξ ha hz hza hea (P r) t ω hf

lemma scaled_bounds (P : R → FilteredRanks w) {ξ a z z' ε l g b : ℝ}
    (hξ : 0<ξ) (ha : a∈Set.Icc 0 1) (hz : z∈Set.Icc 0 (1/100:ℝ))
    (hza : z≤a/100) (hea : a/100-z≤ε) (hε : 0≤ε)
    (hl : 0<l) (hls : l≤1/4) (hel : ξ+ε≤l/4)
    (hg : 4*l≤g) (hb : 4*l≤b) (hzz : z≤z') (hgap : g≤(z'-z)/96)
    (t : ℕ) (ω : Ω) :
    (flex P z' t ω≤(1-l)*estimate P ξ a t ω ∧ (1-l)*estimate P ξ a t ω≤flex P z t ω) ∧
    (flex P z t ω≤(1+l)*estimate P ξ a t ω ∧ (1+l)*estimate P ξ a t ω≤(1+b)*flex P z t ω) := by
  have hn:=flex_nonneg P hz t ω
  have hs:=flex_slack P hz hzz t ω
  have hfc : flex P z' t ω≤(1-g)*flex P z t ω := by
    have h:=mul_le_mul_of_nonneg_right hgap hn
    nlinarith
  exact FineCaps.cap_scaling hn (estimate_error P hξ ha hz hza hea t ω)
    (add_nonneg hξ.le hε) hl hls hel hg hb hfc

end KServer.TrackedCaps

end


/-! Literal side process at a filtered star. The scale is the independently
running coarse tracker of the marked child's noncore rank values, as in
( dominant-scale-definition ), not a retrospectively selected comparator. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.StarSide
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseProcess CoarseEpoch AllocationSchedule StarProfile
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω → ℝ}

def mark (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : Option J :=
  EpochSchedule.dominant (EpochSchedule.run (vector cutoff δ P ω) (fun s=>key s ω) t)

def sides (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : Finset J :=
  match mark δ P key t ω with
  | none=>∅
  | some o=>(activeSet (vector cutoff δ P ω t)).erase o

def coarseFlex (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ r,if CoreFlags.flag (P r) t ω then 0 else FineCaps.estimate δ 0 (P r) t ω

def scale (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : ℝ :=
  match mark δ P key t ω with
  | none=>0
  | some o=>coarseFlex δ (P o) t ω

def sideFlags (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : J → R → Bool :=
  fun i r=>if i∈sides δ P key t ω then CoreFlags.flag (P i r) t ω else false

def logs (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : J → ℝ :=
  fun i=>max 1 (weight δ (vector cutoff δ P ω) (fun s=>key s ω) t i)

def input {cw ell : ℝ} (hcw : 0 < cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : CausalSide.Input J R :=
  ⟨SideFamilies.fromLog (sides δ P key t ω) (sideFlags δ P key t ω)
    16 (b t ω) (scale δ P key t ω) cw ell (logs δ P key t ω)
    (by norm_num) hcw hel (fun i=>le_max_left _ _),
    fun ir=>(P ir.1 ir.2).p t ω,
    epoch (vector cutoff δ P ω) (fun s=>key s ω) t⟩

def proportion {cw ell : ℝ} (hcw : 0 < cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ) : ℕ → Ω → J → ℝ :=
  CausalSide.run 40 (input hcw hel δ P key b)

lemma coarseFlex_nonneg (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ coarseFlex δ P t ω := by
  apply sum_nonneg
  intro r _
  split_ifs
  · rfl
  · exact (FineCaps.estimate_range (by norm_num : (0:ℝ)∈Set.Icc 0 (1/100:ℝ)) (P r) t ω).1

omit [DecidableEq J] in
lemma scale_nonneg (δ : ℝ) (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (t : ℕ) (ω : Ω) : 0 ≤ scale δ P key t ω := by
  unfold scale
  split
  · rfl
  · exact coarseFlex_nonneg _ _ _ _

lemma proportion_mem {cw ell : ℝ} (hcw : 0 < cw) (hel : 0<ell) (δ : ℝ)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : proportion hcw hel δ P key b t ω∈ChangingDomains.sideDomain (sides δ P key t ω) 16 :=
  CausalSide.run_mem 40 (input hcw hel δ P key b) t ω

lemma logs_upper {δ k : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (hk : 1≤k)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω) (i : J) :
    logs δ P key t ω i≤20002*(1+Real.log (k+1)) := by
  apply max_le
  · have hl:=Real.log_nonneg (show 1≤k+1 by linarith)
    nlinarith
  · exact weight_upper hδ hδu hk (vector cutoff δ P ω) (fun s=>key s ω)
      (vector_nonneg cutoff δ P ω) (fun s=>vector_total hδ hδu P s ω (hs s ω))
      (fun s i hi=>vector_floor hδ hδu P s ω i hi) t i

lemma feasible {δ k cw : ℝ} (hδ : 0<δ) (hδu : δ≤1/1000) (hk : 1≤k)
    (hcw : 0 < cw) (hcwu : cw*20002≤1)
    (P : J → R → FilteredRanks w) (key : ℕ → Ω → K) (b : ℕ → Ω → ℝ)
    (hs : ∀ t ω,(∑ i,size (P i) t ω)≤k) (t : ℕ) (ω : Ω)
    (hb : 1≤b t ω) (hbu : b t ω≤4) :
    let ell:=1+Real.log (k+1)
    let hel:0<ell:=by have h:=Real.log_nonneg (show 1≤k+1 by linarith); dsimp [ell]; linarith
    let d:=input hcw hel δ P key b t ω
    let a:=proportion hcw hel δ P key b t ω
    (∀ i,d.data.D*a i≤(d.data.b+d.data.θ i)*SideFamilies.core d.data d.ranks i) ∧
    ((∑ i,SideFamilies.core d.data d.ranks i)≤2*d.data.D → ∀ i,
      d.data.b*SideFamilies.core d.data d.ranks i-d.data.θ i*d.data.z i*d.data.D≤d.data.D*a i) := by
  intro ell hel d a
  have hM : ∀ i∈d.data.active,d.data.b+d.data.θ i≤5 := by
    intro i _
    change b t ω+cw*logs δ P key t ω i/ell≤5
    have hl:=logs_upper hδ hδu hk P key hs t ω i
    have hh:=mul_le_mul_of_nonneg_left hl hcw.le
    have he:=mul_le_mul_of_nonneg_right hcwu hel.le
    have hu : cw*logs δ P key t ω i/ell≤1 := by
      apply (div_le_iff₀ hel).mpr
      dsimp [ell] at *
      nlinarith
    linarith
  have hW : 2*(5:ℝ)<d.data.W := by norm_num [d,input,SideFamilies.fromLog]
  have hp : ∀ ir,0≤d.ranks ir := fun ir=>((P ir.1 ir.2).range t ω).1
  have hf : ∀ i∉d.data.active,∀ r,d.data.flags i r=false := by
    intro i hi r
    change i∉sides δ P key t ω at hi
    change sideFlags δ P key t ω i r=false
    simp only [sideFlags,ite_eq_right hi]
  have h:=CausalSide.run_feasible (input hcw hel δ P key b) (M:=5) t ω hb
    (scale_nonneg δ P key t ω) hM hW hp hf
  dsimp only [a,proportion,d]
  simpa only [show (8:ℝ)*5=40 by norm_num] using h

end KServer.StarSide

end


/-! The literal held dominant noncore scale is uniformly comparable to the
current parameterized flex mass; zeros coincide without a positive-mass
assumption. This is (dominant-scale-definition) / (D-comparison) in §03. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseFineBridge
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile StarSide CoreFlags
variable {Ω R:Type} [Fintype Ω] [Fintype R] {w:Ω→ℝ}

lemma base_compare (P:R→FilteredRanks w) {z:ℝ} (hz:z∈Set.Icc 0 (1/100:ℝ))
    (t:ℕ) (ω:Ω) :
    TrackedCaps.flex P z t ω≤TrackedCaps.flex P 0 t ω ∧
    TrackedCaps.flex P 0 t ω≤(1+z)*TrackedCaps.flex P z t ω := by
  refine ⟨TrackedCaps.flex_antitone P t ω hz.1,?_⟩
  unfold TrackedCaps.flex
  rw [mul_sum]
  apply sum_le_sum
  intro r _
  cases hf:flag (P r) t ω with
  | true=>simp
  | false=>
    simp only [Bool.false_eq_true,ite_false]
    have hp:pstar/4≤(P r).p t ω:=by
      have h:=noncore_lower (P r) hf
      norm_num [pstar] at *
      linarith
    have hg:parameterSlope ((P r).p t ω) ≤ rank z ((P r).p t ω):=(parameterSlope_compare hz hp).2
    have hm:=mul_le_mul_of_nonneg_left hg hz.1
    rw [rank_parameter_affine z] at hm ⊢
    nlinarith

lemma estimate_compare {δ:ℝ} (hδ:0<δ) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    (1+δ)⁻¹*TrackedCaps.flex P 0 t ω ≤ coarseFlex δ P t ω ∧
    coarseFlex δ P t ω≤(1+δ)*TrackedCaps.flex P 0 t ω := by
  constructor <;> unfold TrackedCaps.flex coarseFlex
  · rw [mul_sum]
    apply sum_le_sum
    intro r _
    split_ifs
    · simp
    · exact (FineCaps.estimate_accuracy hδ (by norm_num) (P r) t ω).1
  · rw [mul_sum]
    apply sum_le_sum
    intro r _
    split_ifs
    · simp
    · exact (FineCaps.estimate_accuracy hδ (by norm_num) (P r) t ω).2

lemma compare {δ z:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hz:z∈Set.Icc 0 (1/100:ℝ))
    (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    (1/2:ℝ)*TrackedCaps.flex P z t ω ≤ coarseFlex δ P t ω ∧
    coarseFlex δ P t ω≤2*TrackedCaps.flex P z t ω := by
  have h:=estimate_compare hδ P t ω
  have hb:=base_compare P hz t ω
  have hF:=TrackedCaps.flex_nonneg P hz t ω
  have hD:=coarseFlex_nonneg δ P t ω
  have hpos:0<1+δ:=by linarith
  have hh:=mul_le_mul_of_nonneg_left h.1 hpos.le
  rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hpos),one_mul] at hh
  have hhalf:=mul_le_mul_of_nonneg_left hδu hD
  have hzF:=mul_le_mul_of_nonneg_right hz.2 hF
  have hbase:=mul_le_mul_of_nonneg_left hb.2 hpos.le
  have hδF:=mul_le_mul_of_nonneg_left hδu hF
  have hδz:=mul_le_mul_of_nonneg_left hzF hδ.le
  constructor <;> nlinarith only [h.2,hb.1,hbase,hhalf,hh,hzF,hδF,hδz]

end KServer.CoarseFineBridge

end


/-! One fixed absolute choice in the order required by §05; neither the
separation ratio nor any finite input parameter enters these constants. -/
noncomputable section
namespace KServer.LocalConstants
def cb:ℝ:=1/100000000
def cg:ℝ:=cb/20
def ct:ℝ:=cb/1000000
def cw:ℝ:=cb/1000000000
def C:ℝ:=1000/ct
def eb:ℝ:=cb/1000000
def lb:ℝ:=cb/100000000
def rho:ℝ:=lb/16
def dp:ℝ:=lb/(64*cb)
def ds:ℝ:=1/1000

lemma positive : 0 < cb ∧ 0 < cg ∧ 0 < ct ∧ 0 < cw ∧ 0<C ∧ 0<eb ∧ 0<lb ∧ 0 < rho ∧ 0<dp ∧ 0<ds := by
  norm_num [cb,cg,ct,cw,C,eb,lb,rho,dp,ds]
lemma small : ct*20002≤1 ∧ cw*20002≤1 ∧ 700<C*ct ∧
    10000*cb+4*cb*dp≤1/100 ∧ lb≤1/4 ∧ rho+4*cb*dp≤lb/4 ∧
    4*lb ≤ cg/96 ∧ 4*lb≤eb ∧ 4*ct ≤ cg/4 ∧ 8*eb ≤ cg/4 ∧ 4*cb*dp+cw ≤ cg/2 ∧
    256*cw ≤ cg/192 := by
  norm_num [cb,cg,ct,cw,C,eb,lb,rho,dp]
end KServer.LocalConstants

end


/-! Endpoint-only fine caps with the actual held parent parameter. These
estimates are run for every rank and time, not just during output epochs. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCaps
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile CoarseParameters
open LocalConstants
variable {Ω R:Type} [Fintype Ω] [Fintype R] {w:Ω→ℝ}

def ell (k:ℝ):ℝ:=1+Real.log (k+1)
def z (k:ℝ) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=beta k cutoff cb (ell k) (size Q t ω)-3
def a (k:ℝ) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  100*(upperBeta k cutoff cb (ell k) dp (parent cutoff dp Q t ω)-3)
def flexCap (k:ℝ) (Q P:R→FilteredRanks w) (dominant:Bool) (t:ℕ) (ω:Ω):ℝ:=
  (if dominant then 1+lb/ell k else 1-lb/ell k)*TrackedCaps.estimate P (rho/ell k) (a k Q t ω) t ω

def cap (k:ℝ) (Q P:R→FilteredRanks w) (dominant:Bool) (t:ℕ) (ω:Ω):ℝ:=
  TrackedCaps.count P t ω+flexCap k Q P dominant t ω

lemma ell_ge_one {k:ℝ} (hk:1≤k):1≤ell k:=by
  unfold ell
  linarith [Real.log_nonneg (show 1≤k+1 by linarith)]
lemma ell_pos {k:ℝ} (hk:1≤k):0<ell k:=lt_of_lt_of_le zero_lt_one (ell_ge_one hk)

lemma ranges {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size Q t ω≤k):
    z k Q t ω∈Set.Icc 0 (1/100:ℝ) ∧ a k Q t ω∈Set.Icc 0 1 ∧
      z k Q t ω≤a k Q t ω/100 ∧ a k Q t ω/100-z k Q t ω≤4*cb*dp/ell k := by
  have h:=ActualParameters.beta_bounds hk hs positive.1.le
  have he:=ActualParameters.held_error positive.2.2.2.2.2.2.2.2.1 hk positive.1.le Q t ω
  have hell:=ell_ge_one hk
  have herr:4*cb*dp/ell k≤4*cb*dp:=by
    apply (div_le_iff₀ (ell_pos hk)).mpr
    have hp:0≤4*cb*dp:=by norm_num [cb,dp,lb]
    nlinarith
  have hc:10000*cb+4*cb*dp≤1/100:=small.2.2.2.1
  unfold z a ell at *
  constructor
  · constructor <;> nlinarith [he.1,he.2,h.1,h.2]
  · refine ⟨?_,?_,?_⟩
    · constructor <;> nlinarith [he.1,he.2,h.1,h.2]
    · linarith [he.1]
    · linarith [he.2]

lemma scalar_errors {k:ℝ} (hk:1≤k):
    0 < rho/ell k ∧ 0<lb/ell k ∧ lb/ell k≤1/4 ∧
    rho/ell k+4*cb*dp/ell k≤(lb/ell k)/4 ∧
    4*(lb/ell k)≤(cg/ell k)/96 ∧ 4*(lb/ell k)≤eb/ell k := by
  have hel:=ell_pos hk
  have he1:=ell_ge_one hk
  have hl:0<lb:=by norm_num [lb,cb]
  have hr:0 < rho:=by norm_num [rho,lb,cb]
  have hvals:=small
  refine ⟨div_pos hr hel,div_pos hl hel,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ hel).mpr
    have hh:lb≤1/4:=hvals.2.2.2.2.1
    nlinarith
  · rw [←add_div,div_right_comm]
    exact div_le_div_of_nonneg_right hvals.2.2.2.2.2.1 hel.le
  · rw [←mul_div_assoc,div_right_comm]
    exact (div_le_div_iff_of_pos_right hel).mpr hvals.2.2.2.2.2.2.1
  · rw [←mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hel).mpr hvals.2.2.2.2.2.2.2.1

lemma regular_bounds {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) (hg:cg/ell k≤z k P t ω-z k Q t ω) :
    TrackedCaps.flex P (z k P t ω) t ω≤flexCap k Q P false t ω ∧
      flexCap k Q P false t ω≤TrackedCaps.flex P (z k Q t ω) t ω := by
  have hp:=ranges hk Q t ω hs
  have he:=scalar_errors hk
  have hgap:0 ≤ cg/ell k:=div_nonneg (by norm_num [cg,cb]) (ell_pos hk).le
  have hzz:z k Q t ω≤z k P t ω:=by linarith
  have hε:0≤4*cb*dp/ell k:=div_nonneg (by norm_num [cb,dp,lb]) (ell_pos hk).le
  exact (TrackedCaps.scaled_bounds P he.1 hp.2.1 hp.1 hp.2.2.1 hp.2.2.2 hε
    he.2.1 he.2.2.1 he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2 hzz
    (div_le_div_of_nonneg_right hg (by norm_num)) t ω).1

lemma dominant_bounds {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) :
    TrackedCaps.flex P (z k Q t ω) t ω≤flexCap k Q P true t ω ∧
      flexCap k Q P true t ω≤(1+eb/ell k)*TrackedCaps.flex P (z k Q t ω) t ω := by
  have hp:=ranges hk Q t ω hs
  have he:=scalar_errors hk
  have hF:=TrackedCaps.flex_nonneg P hp.1 t ω
  have herror:=TrackedCaps.estimate_error P he.1 hp.2.1 hp.1 hp.2.2.1 hp.2.2.2 t ω
  have hε:0≤4*cb*dp/ell k:=div_nonneg (by norm_num [cb,dp,lb]) (ell_pos hk).le
  have hfc:0≤(1-4*(lb/ell k))*TrackedCaps.flex P (z k Q t ω) t ω:=
    mul_nonneg (by linarith [he.2.2.1]) hF
  exact (FineCaps.cap_scaling hF herror (add_nonneg he.1.le hε) he.2.1 he.2.2.1 he.2.2.2.1
    le_rfl he.2.2.2.2.2 hfc).2

end KServer.ActualCaps

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCaps
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile CoarseParameters LocalConstants
variable {Ω R:Type} [Fintype Ω] [Fintype R] {w:Ω→ℝ}

lemma estimate_nonneg {ξ a:ℝ} (ha:a∈Set.Icc 0 1) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) :
    0≤TrackedCaps.estimate P ξ a t ω := by
  unfold TrackedCaps.estimate
  apply sum_nonneg
  intro r _
  split_ifs
  · rfl
  · exact (FineCaps.interpolated_range ha (P r) t ω).1

lemma flexCap_nonneg {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) : 0≤flexCap k Q P d t ω := by
  have he:=scalar_errors hk
  have ha:=(ranges hk Q t ω hs).2.1
  unfold flexCap
  apply mul_nonneg _ (estimate_nonneg ha P t ω)
  cases d <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith [he.2.1,he.2.2.1]

lemma flexCap_upper {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) : flexCap k Q P d t ω≤2*TrackedCaps.flex P (z k Q t ω) t ω := by
  have he:=scalar_errors hk
  have hh:=dominant_bounds hk Q P t ω hs
  have hz:=(ranges hk Q t ω hs).1
  have hf:=TrackedCaps.flex_nonneg P hz t ω
  have hb:eb/ell k≤1:=by
    apply (div_le_iff₀ (ell_pos hk)).mpr
    have hb:eb≤1:=by norm_num [eb,cb]
    linarith [ell_ge_one hk]
  have hu:(1+eb/ell k)*TrackedCaps.flex P (z k Q t ω) t ω≤2*TrackedCaps.flex P (z k Q t ω) t ω:=by
    have hm:=mul_le_mul_of_nonneg_right hb hf
    nlinarith
  apply le_trans _ (hh.2.trans hu)
  cases d with
  | true=>rfl
  | false=>
    unfold flexCap
    simp only [Bool.false_eq_true,ite_false,ite_true]
    exact mul_le_mul_of_nonneg_right (by linarith [he.2.1]) (estimate_nonneg (ranges hk Q t ω hs).2.1 P t ω)

lemma cap_bounds {k:ℝ} (hk:1≤k) (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) : 0 ≤ cap k Q P d t ω ∧ cap k Q P d t ω≤72*size P t ω := by
  have hn:=TrackedCaps.count_nonneg P t ω
  have hf:=flexCap_nonneg hk Q P d t ω hs
  have hu:=flexCap_upper hk Q P d t ω hs
  have hm:=TrackedCaps.domination P (ranges hk Q t ω hs).1 t ω
  dsimp [cap]
  constructor <;> linarith

lemma inactive_cap {δ k:ℝ} (hδ:0<δ) (hδu:δ≤1/1000) (hk:1≤k)
    (Q P:R→FilteredRanks w) (d:Bool) (t:ℕ) (ω:Ω) (hs:size Q t ω≤k)
    (hi:¬0<(active cutoff δ P ω t).value) : cap k Q P d t ω=0 := by
  have ha:=(ranges hk Q t ω hs).2.1
  have hp:0 < rho/ell k:=(scalar_errors hk).1
  have hcount:TrackedCaps.count P t ω=0:=by
    apply sum_eq_zero
    intro r _
    simp only [inactive_flag_false hδ hδu P hi r,Bool.false_eq_true,ite_false]
  have he:TrackedCaps.estimate P (rho/ell k) (a k Q t ω) t ω=0:=by
    apply sum_eq_zero
    intro r _
    rw [inactive_flag_false hδ hδu P hi r]
    simp only [Bool.false_eq_true,ite_false]
    have h:=FineCaps.interpolated_accuracy hp ha (P r) t ω
    have hz:=rank_cutoff (a k Q t ω/100) (inactive_rank_cutoff hδ hδu P hi r).le
    rw [hz,sub_zero,mul_zero] at h
    exact abs_nonpos_iff.mp h
  simp only [cap,flexCap,hcount,he,mul_zero,add_zero]

lemma held_beta_bounds {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    (hs:size Q t ω≤k) :
    3≤upperBeta k cutoff cb (ell k) dp (parent cutoff dp Q t ω) ∧
    upperBeta k cutoff cb (ell k) dp (parent cutoff dp Q t ω)≤301/100 := by
  have hh:=(ranges hk Q t ω hs).2.1
  unfold a at hh
  constructor <;> linarith [hh.1,hh.2]

end KServer.ActualCaps

end


/-! Binding the local numerical choices to the literal star processes. The
only input relation is conservation/superadditivity of the parent's rank size. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualStar
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule LocalConstants
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def key (Q:R→FilteredRanks w) : ℕ→Ω→ℝ := parent cutoff dp Q

def b (k:ℝ) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  CoarseParameters.upperBeta k cutoff cb (ActualCaps.ell k) dp (key Q t ω)

def β (k:ℝ) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=3+ActualCaps.z k P t ω

def h (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):ℝ:=
  weight ds (vector cutoff ds P ω) (fun s=>key Q s ω) t i

def active (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):Finset J:=activeSet (vector cutoff ds P ω t)
def mark (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):Option J:=
  StarSide.mark ds P (key Q) t ω

def α (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) : ℕ→Ω→J→ℝ:=
  StarSimplex.proportion (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) C (ActualCaps.ell k) ct P (key Q)

lemma h_nonneg (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):0≤h P Q t ω i:=
  weight_nonneg ds _ _ (vector_nonneg cutoff ds P ω) t i
lemma h_one (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J)
    (hi:mark P Q t ω≠some i):1≤h P Q t ω i:=
  weight_regular_one ds _ _ t i hi
lemma h_upper {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J):
    h P Q t ω i≤20002*ActualCaps.ell k:=
  weight_upper (by norm_num [ds]) (by norm_num [ds]) hk _ _ (vector_nonneg cutoff ds P ω)
    (fun s=>vector_total (by norm_num [ds]) (by norm_num [ds]) P s ω (hs s ω))
    (fun s j hj=>vector_floor (by norm_num [ds]) (by norm_num [ds]) P s ω j hj) t i
lemma beta_range {k:ℝ} (hk:1≤k) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size P t ω≤k):
    3≤β k P t ω ∧ β k P t ω≤4 := by
  have hr:=(ActualCaps.ranges hk P t ω hs).1
  unfold β
  constructor <;> linarith [hr.1,hr.2]
lemma b_range {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size Q t ω≤k):
    3≤b k Q t ω ∧ b k Q t ω≤4 := by
  have hr:=ActualCaps.held_beta_bounds hk Q t ω hs
  exact ⟨hr.1,hr.2.trans (by norm_num)⟩
lemma b_error {k:ℝ} (hk:1≤k) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    β k Q t ω≤b k Q t ω ∧ b k Q t ω-β k Q t ω≤4*cb*dp/ActualCaps.ell k := by
  have hh:=ActualParameters.held_error (δ:=dp) (cb:=cb) (by norm_num [dp,lb,cb]) hk (by norm_num [cb]) Q t ω
  dsimp only [β,ActualCaps.z,b,key,ActualCaps.ell]
  constructor <;> linarith [hh.1,hh.2]
lemma parameter_gap {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (i:J) (hi:i∈active P t ω):
    cg*h P Q t ω i/ActualCaps.ell k≤β k (P i) t ω-β k Q t ω := by
  have hh:=ActualParameters.gap (δ:=ds) (cb:=cb) (by norm_num [ds]) (by norm_num [ds]) hk (by norm_num [cb])
    P (key Q) (size Q) hs t ω i hi
  dsimp only [β,ActualCaps.z,ActualCaps.ell,h,cg]
  linarith only [hh]
lemma α_mem (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    α k P Q t ω∈ChangingDomains.simplex (active P t ω):=
  StarSimplex.proportion_mem _ _ _ _ _ _ _ _ _
lemma α_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤k) (t:ℕ) (ω:Ω) (i:J):
    (∑ j,TrackedCaps.core (P j) t ω)*α k P Q t ω i≤
      (1+ct*h P Q t ω i/ActualCaps.ell k)*TrackedCaps.core (P i) t ω:=
  StarSimplex.feasible (δ:=ds) (by norm_num [ds]) (by norm_num [ds]) positive.2.2.2.2.1 positive.2.2.1
    small.1 small.2.2.1 hk P (key Q) hs t ω i
end KServer.ActualStar

end


/-! Scalar constant choices used when the genuine minimizer proportions are
converted to allocations. All constants are the fixed absolute choices, not
parameters fitted to the finite law. -/
noncomputable section
namespace KServer.OutputConstants
open LocalConstants

lemma eta_nonneg {h ell:ℝ} (hh:0≤h) (hel:0<ell) : 0 ≤ ct*h/ell := by
  exact div_nonneg (mul_nonneg positive.2.2.1.le hh) hel.le
lemma eta_upper {h ell:ℝ} (hh:h≤20002*ell) (hel:0<ell) : ct*h/ell≤1 := by
  apply (div_le_iff₀ hel).mpr
  have h1:=mul_le_mul_of_nonneg_left hh positive.2.2.1.le
  have h2:=mul_le_mul_of_nonneg_right small.1 hel.le
  nlinarith
lemma beta_eta {β h ell:ℝ} (hβ:β≤4) (hh:0≤h) (hel:0<ell) :
    β*(ct*h/ell)≤(cg*h/ell)/2 := by
  have hn:=div_nonneg hh hel.le
  have hc:4*ct ≤ cg/2:=by norm_num [ct,cg,cb]
  have h1:=mul_le_mul_of_nonneg_right hβ (eta_nonneg hh hel)
  have h2:=mul_le_mul_of_nonneg_right hc hn
  calc
    β*(ct*h/ell)≤4*(ct*h/ell):=h1
    _≤(cg*h/ell)/2:=by simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h2
lemma dominant_room {β βi h ell:ℝ} (hβ:β≤4) (hh:0≤h) (hel:0<ell)
    (hg:cg*h/ell≤βi-β) : β*(1+ct*h/ell)≤βi := by
  have hη:=beta_eta hβ hh hel
  have hn:0 ≤ cg*h/ell:=div_nonneg (mul_nonneg positive.2.1.le hh) hel.le
  nlinarith
lemma regular_error {S T e h ell:ℝ} (hS:0≤S) (hT:T≤4*S)
    (hh:1≤h) (hel:0<ell) (he:e≤eb/ell*T) : 4*e≤(cg*h/ell)*S := by
  have hb:0≤eb/ell:=div_nonneg positive.2.2.2.2.2.1.le hel.le
  have h1:=mul_le_mul_of_nonneg_left hT hb
  have hc:16*eb ≤ cg:=by norm_num [eb,cg,cb]
  have h2:=mul_le_mul_of_nonneg_left hh positive.2.1.le
  rw [mul_one] at h2
  have h3:16*eb/ell ≤ cg*h/ell:=div_le_div_of_nonneg_right (hc.trans h2) hel.le
  have h4:=mul_le_mul_of_nonneg_right h3 hS
  simp only [div_eq_mul_inv] at he h1 h4 ⊢
  nlinarith only [he,h1,h4]
lemma regular_room {S T e β βi h ell:ℝ} (hS:0≤S) (he:0≤e) (hT:T≤4*S)
    (hh:1≤h) (hhu:h≤20002*ell) (hel:0<ell) (hβ:β≤4)
    (herr:e≤eb/ell*T) (hg:cg*h/ell≤βi-β) :
    (β*S+e)*(1+ct*h/ell)≤βi*S := by
  exact OutputDynamics.regular_parameter_room hS he (eta_upper hhu hel)
    (by linarith) (beta_eta hβ (by linarith) hel) (regular_error hS hT hh hel herr)
lemma side_room {β βi b h ell:ℝ} (hh:1≤h) (hel:0<ell)
    (hb:b-β≤4*cb*dp/ell) (hg:cg*h/ell≤βi-β) : b+cw*h/ell≤βi := by
  have hc:4*cb*dp+cw ≤ cg:=by norm_num [cb,dp,lb,cw,cg]
  have hcn:0≤4*cb*dp:=by norm_num [cb,dp,lb]
  have h1:=mul_le_mul_of_nonneg_left hh hcn
  have h2:=mul_le_mul_of_nonneg_right hc (show 0≤h by linarith)
  have h3:4*cb*dp/ell+cw*h/ell ≤ cg*h/ell:=by
    rw [←add_div]
    apply div_le_div_of_nonneg_right _ hel.le
    nlinarith only [h1,h2]
  linarith
lemma residual_room {u T D ell:ℝ} (hu:0≤u) (hT:0≤T) (hD:D≤2*T) (hel:0<ell) :
    D*(128*cw*u/ell)≤(cg*u/ell)/96*T := by
  have hc:256*cw ≤ cg/96:=by norm_num [cw,cg,cb]
  have h0:0≤128*cw*u/ell:=by have hcw:=positive.2.2.2.1; positivity
  have h1:=mul_le_mul_of_nonneg_right hD h0
  have h2:=mul_le_mul_of_nonneg_right hc (div_nonneg hu hel.le)
  have h3:=mul_le_mul_of_nonneg_right h2 hT
  simp only [div_eq_mul_inv] at h1 h3 ⊢
  nlinarith only [h1,h3]
end KServer.OutputConstants

end


/-! The actual cap vector, lower envelopes, and single dominant error used by
§05. No aggregate cap or parameter inequalities are assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def B (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ := fun i=>TrackedCaps.core (P i) t ω
def n (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ := fun i=>TrackedCaps.count (P i) t ω
def S (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=∑ i,B P t ω i
def f (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>TrackedCaps.flex (P i) (ActualCaps.z k Q t ω) t ω
def fc (k:ℝ) (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>TrackedCaps.flex (P i) (ActualCaps.z k (P i) t ω) t ω
def flexcap (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>ActualCaps.flexCap k Q (P i) (decide (mark P Q t ω=some i)) t ω
def d (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) : J→ℝ :=
  fun i=>n P t ω i+flexcap k P Q t ω i
def lower (k:ℝ) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  ∑ r,rank (ActualCaps.z k P t ω) ((P r).p t ω)
def T (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  match mark P Q t ω with | none=>0 | some o=>f k P Q t ω o
def e (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  match mark P Q t ω with | none=>0 | some o=>flexcap k P Q t ω o-f k P Q t ω o
def D (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) : ℕ→Ω→ℝ:=
  StarSide.scale ds P (key Q)

lemma S_nonneg (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω):0≤S P t ω:=
  sum_nonneg fun i _=>TrackedCaps.core_nonneg (P i) t ω
lemma D_nonneg (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):0≤D P Q t ω:=
  StarSide.scale_nonneg ds P (key Q) t ω
lemma mark_active (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    {o:J} (ho:mark P Q t ω=some o):o∈ActualStar.active P t ω:=
  marked_active _ _ (vector_nonneg cutoff ds P ω) t ho
lemma inactive (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) {i:J}
    (hi:i∉ActualStar.active P t ω):¬0<(CoarseProcess.active cutoff ds (P i) ω t).value:=by
  exact fun hh=>hi ((AllocationSchedule.mem_activeSet _ _).mpr hh)
lemma inactive_lower (k:ℝ) (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) {i:J}
    (hi:i∉ActualStar.active P t ω):lower k (P i) t ω=0:=
  inactive_lower_zero (by norm_num [ds]) (by norm_num [ds]) (P i) (inactive P t ω hi) _
lemma inactive_f (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) {i:J}
    (hi:i∉ActualStar.active P t ω):f k P Q t ω i=0:=by
  apply sum_eq_zero
  intro r _
  rw [inactive_flag_false (by norm_num [ds]) (by norm_num [ds]) (P i) (inactive P t ω hi) r]
  simp only [Bool.false_eq_true,ite_false]
  exact rank_cutoff _ (inactive_rank_cutoff (by norm_num [ds]) (by norm_num [ds]) (P i) (inactive P t ω hi) r).le
omit [Fintype J] in
lemma lower_decomposition (k:ℝ) (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    lower k (P i) t ω=n P t ω i-β k (P i) t ω*B P t ω i+fc k P t ω i:=
  TrackedCaps.decomposition (P i) _ t ω
lemma child_size (P:J→R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    size (P i) t ω≤∑ j,size (P j) t ω:=
  single_le_sum (fun j _=>size_nonneg (P j) t ω) (mem_univ i)
lemma lower_nonneg {k:ℝ} (hk:1≤k) (P:R→FilteredRanks w) (t:ℕ) (ω:Ω) (hs:size P t ω≤k):
    0≤lower k P t ω:=sum_nonneg fun _ _=>rank_nonneg (ActualCaps.ranges hk P t ω hs).1 _
lemma d_bounds {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hs:size Q t ω≤k) (i:J):0≤d k P Q t ω i ∧ d k P Q t ω i≤72*size (P i) t ω:=
  ActualCaps.cap_bounds hk Q (P i) _ t ω hs
lemma inactive_d {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hs:size Q t ω≤k) {i:J} (hi:i∉ActualStar.active P t ω):d k P Q t ω i=0:=
  ActualCaps.inactive_cap (by norm_num [ds]) (by norm_num [ds]) hk Q (P i) _ t ω hs (inactive P t ω hi)

lemma regular_caps {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J) (hi:i∈ActualStar.active P t ω) (ho:mark P Q t ω≠some i):
    fc k P t ω i≤flexcap k P Q t ω i ∧ flexcap k P Q t ω i≤f k P Q t ω i:=by
  have hg:=parameter_gap hk P Q hs t ω i hi
  have hh:=h_one P Q t ω i ho
  have hcg:0 ≤ cg/ActualCaps.ell k:=div_nonneg positive.2.1.le (ActualCaps.ell_pos hk).le
  have hmul:=mul_le_mul_of_nonneg_left hh hcg
  have hgap:cg/ActualCaps.ell k≤ActualCaps.z k (P i) t ω-ActualCaps.z k Q t ω:=by
    dsimp only [β] at hg
    simp only [div_eq_mul_inv] at hg hmul ⊢
    nlinarith only [hg,hmul]
  simpa only [fc,flexcap,f,decide_eq_false ho] using ActualCaps.regular_bounds hk Q (P i) t ω hq hgap
lemma dominant_caps {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k) {o:J} (ho:mark P Q t ω=some o):
    f k P Q t ω o≤flexcap k P Q t ω o ∧
      flexcap k P Q t ω o≤(1+eb/ActualCaps.ell k)*f k P Q t ω o:=by
  simpa only [f,flexcap,ho,decide_true] using ActualCaps.dominant_bounds hk Q (P o) t ω hq
lemma T_nonneg {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):0≤T k P Q t ω:=by
  unfold T
  split
  · rfl
  · exact TrackedCaps.flex_nonneg _ (ActualCaps.ranges hk Q t ω hq).1 t ω
lemma e_bounds {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):0≤e k P Q t ω ∧ e k P Q t ω≤eb/ActualCaps.ell k*T k P Q t ω:=by
  cases ho:mark P Q t ω with
  | none=>simp only [e,T,ho,mul_zero,le_refl,and_self]
  | some o=>
    have hh:=dominant_caps hk P Q t ω hq ho
    simp only [e,T,ho]
    constructor <;> nlinarith [hh.1,hh.2]
lemma DT_compare {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):T k P Q t ω/2≤D P Q t ω ∧ D P Q t ω≤2*T k P Q t ω:=by
  have hmark:StarSide.mark ds P (key Q) t ω=mark P Q t ω:=rfl
  cases ho:mark P Q t ω with
  | none=>simp only [D,StarSide.scale,hmark,ho,T,zero_div,mul_zero,le_refl,and_self]
  | some o=>
    have hh:=CoarseFineBridge.compare (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
      (ActualCaps.ranges hk Q t ω hq).1 (P o) t ω
    simp only [D,StarSide.scale,hmark,ho,T,f]
    constructor <;> linarith [hh.1,hh.2]
end KServer.ActualOutput

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_OutputRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma inactive_flexcap {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k) {i:J} (hi:i∉ActualStar.active P t ω):flexcap k P Q t ω i=0:=by
  have hd:=inactive_d hk P Q t ω hq hi
  have hn:=TrackedCaps.count_nonneg (P i) t ω
  have hb:=ActualCaps.flexCap_nonneg hk Q (P i) (decide (mark P Q t ω=some i)) t ω hq
  change 0≤flexcap k P Q t ω i at hb
  change n P t ω i+flexcap k P Q t ω i=0 at hd
  change 0≤n P t ω i at hn
  linarith
lemma regular_upper {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J) (ho:mark P Q t ω≠some i):flexcap k P Q t ω i≤f k P Q t ω i:=by
  by_cases hi:i∈ActualStar.active P t ω
  · exact (regular_caps hk P Q hs t ω hq i hi ho).2
  · rw [inactive_flexcap hk P Q t ω hq hi,inactive_f k P Q t ω hi]
lemma own_flex_le {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (i:J)
    (hi:i∈ActualStar.active P t ω):fc k P t ω i≤f k P Q t ω i:=by
  have hg:=parameter_gap hk P Q hs t ω i hi
  have hn:0 ≤ cg*h P Q t ω i/ActualCaps.ell k:=
    div_nonneg (mul_nonneg positive.2.1.le (h_nonneg P Q t ω i)) (ActualCaps.ell_pos hk).le
  apply TrackedCaps.flex_antitone (P i) t ω
  dsimp only [β] at hg
  linarith
lemma cap_lower {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J):fc k P t ω i≤flexcap k P Q t ω i:=by
  by_cases hi:i∈ActualStar.active P t ω
  · by_cases ho:mark P Q t ω=some i
    · exact (own_flex_le hk P Q hs t ω i hi).trans (dominant_caps hk P Q t ω hq ho).1
    · exact (regular_caps hk P Q hs t ω hq i hi ho).1
  · have hh:=inactive_f k P (P i) t ω hi
    change fc k P t ω i=0 at hh
    rw [hh,inactive_flexcap hk P Q t ω hq hi]
lemma error_sum {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k):
    (∑ i,(flexcap k P Q t ω i-f k P Q t ω i))≤e k P Q t ω:=by
  cases ho:mark P Q t ω with
  | none=>
    simp only [e,ho]
    exact sum_nonpos fun i _=>sub_nonpos.mpr (regular_upper hk P Q hs t ω hq i (by simp [ho]))
  | some o=>
    calc
      _≤∑ i,(if i=o then flexcap k P Q t ω o-f k P Q t ω o else 0):=by
        apply sum_le_sum
        intro i _
        by_cases hi:i=o
        · subst i; simp only [ite_true,le_refl]
        · rw [ite_eq_right hi]
          exact sub_nonpos.mpr (regular_upper hk P Q hs t ω hq i (by simpa [ho,eq_comm] using hi))
      _=e k P Q t ω:=by simp only [sum_ite_eq',mem_univ,ite_true,e,ho]
lemma dominant_slack {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (i:J) (hi:i∈ActualStar.active P t ω):
    (cg*h P Q t ω i/ActualCaps.ell k)/96*f k P Q t ω i≤
      (n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i)-lower k (P i) t ω:=by
  have hg:=parameter_gap hk P Q hs t ω i hi
  have hn:0 ≤ cg*h P Q t ω i/ActualCaps.ell k:=
    div_nonneg (mul_nonneg positive.2.1.le (h_nonneg P Q t ω i)) (ActualCaps.ell_pos hk).le
  have hzz:ActualCaps.z k Q t ω≤ActualCaps.z k (P i) t ω:=by dsimp only [β] at hg; linarith
  have hf:=TrackedCaps.flex_slack (P i) (ActualCaps.ranges hk Q t ω hq).1 hzz t ω
  have hb:=mul_nonneg (sub_nonneg.mpr hzz) (TrackedCaps.core_nonneg (P i) t ω)
  have hfn:=TrackedCaps.flex_nonneg (P i) (ActualCaps.ranges hk Q t ω hq).1 t ω
  have hmul:=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hg (by norm_num : (0:ℝ)≤96)) hfn
  rw [lower_decomposition]
  dsimp only [f,fc,B,β] at *
  linarith only [hf,hb,hmul]
end KServer.ActualOutput

end


/-! Rule I applied to the actual scheduled proportions and caps. Its only
external numeric input is a parent allocation covering the sum of the child
lower envelopes at the parent's parameter (the rank superadditivity premise). -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def outI (k:ℝ) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (q:ℝ):J→ℝ:=
  OutputDynamics.outputI (d k P Q t ω) q (α k P Q t ω)

lemma ruleI_T {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    (hr:∀ o,mark P Q t ω=some o→D P Q t ω/2≤S P t ω):T k P Q t ω≤4*S P t ω:=by
  cases ho:mark P Q t ω with
  | none=>simp only [T,ho]; linarith [S_nonneg P t ω]
  | some o=>linarith [(DT_compare hk P Q t ω hq).1,hr o ho]

lemma outI_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q)
    (hr:∀ o,mark P Q t ω=some o→D P Q t ω/2≤S P t ω) :
    (∀ i,lower k (P i) t ω≤outI k P Q t ω q i ∧ outI k P Q t ω q i≤d k P Q t ω i) ∧
      (∑ i,outI k P Q t ω q i)≤q := by
  have hps:∀ s z,(∑ i,size (P i) s z)≤k:=fun s z=>(hs s z).trans (hq s z)
  have ha:=α_mem k P Q t ω
  have hprop:=α_feasible hk P Q hps t ω
  have hb:=beta_range hk Q t ω (hq t ω)
  have he:=e_bounds hk P Q t ω (hq t ω)
  have hT:=ruleI_T hk P Q t ω (hq t ω) hr
  have hS:=S_nonneg P t ω
  have hTn:=T_nonneg hk P Q t ω (hq t ω)
  have hzero:S P t ω=0→e k P Q t ω=0:=by
    intro hz
    have ht:T k P Q t ω=0:=by linarith
    rw [ht,mul_zero] at he
    exact le_antisymm he.2 he.1
  have hcaps:=error_sum hk P Q hs t ω (hq t ω)
  have hout (i:J):lower k (P i) t ω≤outI k P Q t ω q i ∧ outI k P Q t ω q i≤d k P Q t ω i:=by
    by_cases hi:i∈ActualStar.active P t ω
    · have hbi:=beta_range hk (P i) t ω ((child_size P t ω i).trans (hps t ω))
      have hg:=parameter_gap hk P Q hs t ω i hi
      by_cases hm:mark P Q t ω=some i
      · have hsum:∑ j,α k P Q t ω j=1:=by
          simpa only [ite_eq_left (show (ActualStar.active P t ω).Nonempty from ⟨i,hi⟩)] using ha.2.1
        have hroom:=OutputConstants.dominant_room hb.2 (h_nonneg P Q t ω i) (ActualCaps.ell_pos hk) hg
        have hfc:fc k P t ω i≤flexcap k P Q t ω i-e k P Q t ω:=by
          have hf:=own_flex_le hk P Q hs t ω i hi
          simp only [e,hm]
          linarith
        have hh:=OutputDynamics.outputI_dominant (βi:=fun j=>β k (P j) t ω) hp hcaps (by linarith : 0≤β k Q t ω) he.1
          (fun j=>TrackedCaps.core_nonneg (P j) t ω) ha.1 hsum hprop i hroom (fc k P t ω i) hfc
        rw [lower_decomposition]
        exact hh
      · have hroom:=OutputConstants.regular_room hS he.1 hT (h_one P Q t ω i hm)
          (h_upper hk P Q hps t ω i) (ActualCaps.ell_pos hk) hb.2 he.2 hg
        have hh:=OutputDynamics.outputI_regular (βi:=fun j=>β k (P j) t ω) hp hcaps (by linarith : 0≤β k Q t ω) he.1
          (fun j=>TrackedCaps.core_nonneg (P j) t ω) ha.1 hprop hzero i (by linarith : 0≤β k (P i) t ω)
          (by linarith [OutputConstants.eta_nonneg (h_nonneg P Q t ω i) (ActualCaps.ell_pos hk)]:0≤1+ct*h P Q t ω i/ActualCaps.ell k)
          hroom (fc k P t ω i) (cap_lower hk P Q hs t ω (hq t ω) i)
        rw [lower_decomposition]
        exact hh
    · have hd:=inactive_d hk P Q t ω (hq t ω) hi
      have hl:=inactive_lower k P t ω hi
      have haz:=ha.2.2 i hi
      simp only [outI,OutputDynamics.outputI,OutputDynamics.holesI,hd,haz,hl,mul_zero,sub_zero,le_refl,and_self]
  refine ⟨hout,?_⟩
  by_cases hn:(ActualStar.active P t ω).Nonempty
  · have hsum:∑ j,α k P Q t ω j=1:=by simpa only [ite_eq_left hn] using ha.2.1
    exact (OutputDynamics.outputI_budget hsum (d k P Q t ω) q).le.trans (min_le_right _ _)
  · have hz:∀ i,d k P Q t ω i=0:=fun i=>inactive_d hk P Q t ω (hq t ω) (fun hi=>hn ⟨i,hi⟩)
    have houtz:∀ i,outI k P Q t ω q i=0:=by
      intro i
      have hl:0≤lower k (P i) t ω:=lower_nonneg hk (P i) t ω ((child_size P t ω i).trans (hps t ω))
      have h:=hout i
      rw [hz i] at h
      linarith
    have hparentzero:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))=0:=by
      apply sum_eq_zero
      intro i _
      have hh:=inactive_lower_zero (by norm_num [ds]) (by norm_num [ds]) (P i)
        (inactive P t ω (fun hi=>hn ⟨i,hi⟩)) (ActualCaps.z k Q t ω)
      rw [TrackedCaps.decomposition] at hh
      exact hh
    simp only [houtz,sum_const_zero]
    rwa [hparentzero] at hp
end KServer.ActualOutput

end


/-! Literal side minimizer bounds at the fixed absolute constants. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def sides (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):ℕ→Ω→Finset J:=StarSide.sides ds P (key Q)
def sideData {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) : ℕ→Ω→CausalSide.Input J R:=
  StarSide.input positive.2.2.2.1 (ActualCaps.ell_pos hk) ds P (key Q) (ActualStar.b k Q)
def side {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):ℕ→Ω→J→ℝ:=
  StarSide.proportion positive.2.2.2.1 (ActualCaps.ell_pos hk) ds P (key Q) (ActualStar.b k Q)
def slack {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):J→ℝ:=
  fun i=>if i∈sides P Q t ω then (sideData hk P Q t ω).data.θ i*(sideData hk P Q t ω).data.z i else 0

lemma sides_eq (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    {o:J} (ho:mark P Q t ω=some o):sides P Q t ω=(ActualStar.active P t ω).erase o:=by
  change (match mark P Q t ω with | none=>∅ | some o=>(ActualStar.active P t ω).erase o)=_
  rw [ho]
lemma side_mem {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    side hk P Q t ω∈ChangingDomains.sideDomain (sides P Q t ω) 16:=
  StarSide.proportion_mem _ _ _ _ _ _ _ _
lemma side_core {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (i:J):
    SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i=
      if i∈sides P Q t ω then B P t ω i else 0:=by
  change (∑ r,if (if i∈sides P Q t ω then CoreFlags.flag (P i r) t ω else false) then (P i r).p t ω else 0)=_
  by_cases hi:i∈sides P Q t ω
  · rw [ite_eq_left hi]
    simp only [ite_eq_left hi]
    rfl
  · rw [ite_eq_right hi]
    simp only [ite_eq_right hi,Bool.false_eq_true,ite_false,sum_const_zero]
lemma side_core_total {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
    (∑ i,SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i)≤S P t ω:=by
  apply sum_le_sum
  intro i _
  rw [side_core]
  split_ifs
  · rfl
  · exact TrackedCaps.core_nonneg (P i) t ω
lemma side_logs (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω)
    {o i:J} (ho:mark P Q t ω=some o) (hi:i≠o):StarSide.logs ds P (key Q) t ω i=h P Q t ω i:=by
  apply max_eq_right
  exact h_one P Q t ω i (by simpa [ho,eq_comm] using hi)
lemma side_upper {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i∈sides P Q t ω):
    D P Q t ω*side hk P Q t ω i≤β k (P i) t ω*B P t ω i:=by
  have hr:=mem_erase.mp ((sides_eq P Q t ω ho) ▸ hi)
  have hb:=b_range hk Q t ω (hq t ω)
  have hf:=StarSide.feasible (δ:=ds) (cw:=cw) (by norm_num [ds]) (by norm_num [ds]) hk
    positive.2.2.2.1 small.2.1 P (key Q) (ActualStar.b k Q) (fun s z=>(hs s z).trans (hq s z)) t ω
    (by linarith : 1≤ActualStar.b k Q t ω) hb.2
  dsimp only at hf
  have hf0:=hf.1 i
  change D P Q t ω*side hk P Q t ω i≤(ActualStar.b k Q t ω+cw*StarSide.logs ds P (key Q) t ω i/ActualCaps.ell k)*
    SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i at hf0
  rw [side_core,ite_eq_left hi,side_logs P Q t ω ho hr.1] at hf0
  have hroom:=OutputConstants.side_room (h_one P Q t ω i (by simpa [ho,eq_comm] using hr.1))
    (ActualCaps.ell_pos hk) (b_error hk Q t ω).2 (parameter_gap hk P Q hs t ω i hr.2)
  exact hf0.trans (mul_le_mul_of_nonneg_right hroom (TrackedCaps.core_nonneg (P i) t ω))
lemma side_lower {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (hS:S P t ω≤2*D P Q t ω) {i:J} (hi:i∈sides P Q t ω):
    β k Q t ω*B P t ω i-D P Q t ω*slack hk P Q t ω i≤D P Q t ω*side hk P Q t ω i:=by
  have hb:=b_range hk Q t ω (hq t ω)
  have hf:=StarSide.feasible (δ:=ds) (cw:=cw) (by norm_num [ds]) (by norm_num [ds]) hk
    positive.2.2.2.1 small.2.1 P (key Q) (ActualStar.b k Q) (fun s z=>(hs s z).trans (hq s z)) t ω
    (by linarith : 1≤ActualStar.b k Q t ω) hb.2
  dsimp only at hf
  have ht:(∑ j,SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks j)≤2*(sideData hk P Q t ω).data.D:=
    (side_core_total hk P Q t ω).trans hS
  have hf0:=hf.2 ht i
  change ActualStar.b k Q t ω*SideFamilies.core (sideData hk P Q t ω).data (sideData hk P Q t ω).ranks i-
    (sideData hk P Q t ω).data.θ i*(sideData hk P Q t ω).data.z i*D P Q t ω≤D P Q t ω*side hk P Q t ω i at hf0
  rw [side_core,ite_eq_left hi] at hf0
  have hm:=mul_le_mul_of_nonneg_right (b_error hk Q t ω).1 (TrackedCaps.core_nonneg (P i) t ω)
  change β k Q t ω*B P t ω i≤ActualStar.b k Q t ω*B P t ω i at hm
  simp only [slack,ite_eq_left hi]
  nlinarith only [hf0,hm]
end KServer.ActualOutput

end


/-! Side slack for the actual held logarithms, including zero and empty side
mass. This is a proved inequality, not an assumed output feasibility interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

lemma slack_nonneg {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (i:J):0 ≤ slack hk P Q t ω i:=by
  unfold slack
  split_ifs
  · exact mul_nonneg ((sideData hk P Q t ω).data.θ_pos i).le ((sideData hk P Q t ω).data.z_pos i).le
  · rfl
lemma slack_exp {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i∈sides P Q t ω):
    slack hk P Q t ω i=(cw/ActualCaps.ell k*Real.exp 1)*Real.exp (-h P Q t ω i):=by
  have hio:=(mem_erase.mp ((sides_eq P Q t ω ho) ▸ hi)).1
  have hh:=h_one P Q t ω i (by simpa [ho,eq_comm] using hio)
  have hh0:h P Q t ω i≠0:=ne_of_gt (by linarith)
  rw [slack,ite_eq_left hi]
  change cw*StarSide.logs ds P (key Q) t ω i/ActualCaps.ell k*
    (Real.exp (1-StarSide.logs ds P (key Q) t ω i)/StarSide.logs ds P (key Q) t ω i)=_
  rw [side_logs P Q t ω ho hio,sub_eq_add_neg,Real.exp_add]
  field_simp
lemma slack_sum {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) {o:J} (ho:mark P Q t ω=some o):
    (∑ i,slack hk P Q t ω i)≤128*cw*h P Q t ω o/ActualCaps.ell k:=by
  have hsum:=side_exp_sum (δ:=ds) (by norm_num [ds]) (by norm_num [ds])
    (vector cutoff ds P ω) (fun s=>key Q s ω) (vector_nonneg cutoff ds P ω) t ho
  have hu:h P Q t ω o=sideRatio ds (vector cutoff ds P ω) (fun s=>key Q s ω) t:=
    marked_weight ds _ _ t o ho
  have hn:=h_nonneg P Q t ω o
  have hc:0 ≤ cw/ActualCaps.ell k:=div_nonneg positive.2.2.2.1.le (ActualCaps.ell_pos hk).le
  have he:(∑ i,slack hk P Q t ω i)=(cw/ActualCaps.ell k*Real.exp 1)*
      ∑ i∈sides P Q t ω,Real.exp (-h P Q t ω i):=by
    calc
      _=∑ i∈sides P Q t ω,slack hk P Q t ω i:=by
        symm
        apply sum_subset (subset_univ _)
        intro i _ hi
        simp only [slack,ite_eq_right hi]
      _=_:=by rw [mul_sum]; exact sum_congr rfl fun i hi=>slack_exp hk P Q t ω ho hi
  have hbound:(∑ i∈sides P Q t ω,Real.exp (-h P Q t ω i))≤2*h P Q t ω o:=by
    rw [hu]
    simpa only [sides_eq P Q t ω ho,h,ActualStar.active] using hsum
  have hm:=mul_le_mul_of_nonneg_left hbound (mul_nonneg hc (Real.exp_pos 1).le)
  have h2:=mul_le_mul_of_nonneg_right (le_of_lt Real.exp_one_lt_three) (mul_nonneg hc hn)
  rw [he]
  simp only [div_eq_mul_inv] at hm h2 hc ⊢
  nlinarith only [hm,h2,mul_nonneg hc hn]
lemma side_slack_paid {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (t:ℕ) (ω:Ω) (hq:size Q t ω≤k)
    {o:J} (ho:mark P Q t ω=some o):
    D P Q t ω*(∑ i,slack hk P Q t ω i)≤
      (n P t ω o-β k Q t ω*B P t ω o+f k P Q t ω o)-lower k (P o) t ω:=by
  have hm:=mul_le_mul_of_nonneg_left (slack_sum hk P Q t ω ho) (D_nonneg P Q t ω)
  have hroom:=OutputConstants.residual_room (h_nonneg P Q t ω o) (T_nonneg hk P Q t ω hq)
    (DT_compare hk P Q t ω hq).2 (ActualCaps.ell_pos hk)
  simp only [T,ho] at hroom
  exact (hm.trans hroom).trans (dominant_slack hk P Q hs t ω hq o (mark_active P Q t ω ho))
end KServer.ActualOutput

end


/-! The residual Rule II formula and its feasibility for the actual side
minimizer and marked flex scale. Empty side sets require no separate assumption. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def sideOut {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):J→ℝ:=
  fun i=>d k P Q t ω i-D P Q t ω*side hk P Q t ω i
def outII {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω) (o:J) (q:ℝ):J→ℝ:=
  fun i=>if i=o then min (d k P Q t ω o) (q-∑ j∈univ.erase o,sideOut hk P Q t ω j) else sideOut hk P Q t ω i

lemma sideOut_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i≠o):
    lower k (P i) t ω≤ sideOut hk P Q t ω i ∧ sideOut hk P Q t ω i≤d k P Q t ω i:=by
  have hmem:=side_mem hk P Q t ω
  have hn:=mul_nonneg (D_nonneg P Q t ω) (hmem.1 i)
  by_cases ha:i∈ActualStar.active P t ω
  · have his:i∈sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact mem_erase.mpr ⟨hi,ha⟩
    have hu:=side_upper hk P Q hs hq t ω ho his
    have hf:=cap_lower hk P Q hs t ω (hq t ω) i
    rw [lower_decomposition]
    dsimp only [sideOut,d]
    constructor <;> linarith
  · have his:i∉sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact fun h=>ha (mem_erase.mp h).2
    have hw:=hmem.2.2 i his
    simp only [sideOut,inactive_d hk P Q t ω (hq t ω) ha,inactive_lower k P t ω ha,hw,mul_zero,sub_zero,le_refl,and_self]
lemma sideOut_parent {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (hS:S P t ω≤2*D P Q t ω) {o i:J} (ho:mark P Q t ω=some o) (hi:i≠o):
    sideOut hk P Q t ω i≤n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i+D P Q t ω*slack hk P Q t ω i:=by
  by_cases ha:i∈ActualStar.active P t ω
  · have his:i∈sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact mem_erase.mpr ⟨hi,ha⟩
    have hl:=side_lower hk P Q hs hq t ω hS his
    have hf:=regular_upper hk P Q hs t ω (hq t ω) i (by simpa [ho,eq_comm] using hi)
    dsimp only [sideOut,d]
    linarith
  · have his:i∉sides P Q t ω:=by rw [sides_eq P Q t ω ho]; exact fun h=>ha (mem_erase.mp h).2
    have hw:=(side_mem hk P Q t ω).2.2 i his
    have hp:=inactive_lower_zero (by norm_num [ds]) (by norm_num [ds]) (P i)
      (inactive P t ω ha) (ActualCaps.z k Q t ω)
    rw [TrackedCaps.decomposition] at hp
    change n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i=0 at hp
    simp only [sideOut,inactive_d hk P Q t ω (hq t ω) ha,hw,mul_zero,sub_zero,hp,zero_add]
    exact mul_nonneg (D_nonneg P Q t ω) (slack_nonneg hk P Q t ω i)

lemma outII_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) {o:J} (ho:mark P Q t ω=some o) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q)
    (hS:S P t ω≤2*D P Q t ω) :
    (∀ i,lower k (P i) t ω≤outII hk P Q t ω o q i ∧ outII hk P Q t ω o q i≤d k P Q t ω i) ∧
      (∑ i,outII hk P Q t ω o q i)≤q := by
  let L:J→ℝ:=fun i=>n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i
  have hpaid:=side_slack_paid hk P Q hs t ω (hq t ω) ho
  change D P Q t ω*(∑ i,slack hk P Q t ω i)≤L o-lower k (P o) t ω at hpaid
  have he: (∑ i∈univ.erase o,L i)+L o=∑ i,L i:=sum_erase_add univ L (mem_univ o)
  have hsides:(∑ i∈univ.erase o,sideOut hk P Q t ω i)≤
      (∑ i∈univ.erase o,L i)+D P Q t ω*(∑ i,slack hk P Q t ω i):=by
    calc
      _≤∑ i∈univ.erase o,(L i+D P Q t ω*slack hk P Q t ω i):=
        sum_le_sum fun i hi=>sideOut_parent hk P Q hs hq t ω hS ho (mem_erase.mp hi).1
      _=(∑ i∈univ.erase o,L i)+D P Q t ω*(∑ i∈univ.erase o,slack hk P Q t ω i):=by rw [sum_add_distrib,mul_sum]
      _≤_:=add_le_add_right (mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _=>slack_nonneg hk P Q t ω i))
        (D_nonneg P Q t ω)) _
  have hrem:lower k (P o) t ω≤q-∑ i∈univ.erase o,sideOut hk P Q t ω i:=by
    change (∑ i,L i)≤q at hp
    linarith
  have hcap:lower k (P o) t ω≤d k P Q t ω o:=by
    have hc:=cap_lower hk P Q hs t ω (hq t ω) o
    have hb:=beta_range hk (P o) t ω ((child_size P t ω o).trans ((hs t ω).trans (hq t ω)))
    have hm:=mul_nonneg (show 0≤β k (P o) t ω by linarith) (TrackedCaps.core_nonneg (P o) t ω)
    change 0≤β k (P o) t ω*B P t ω o at hm
    rw [lower_decomposition]
    dsimp only [d]
    linarith
  refine ⟨?_,?_⟩
  · intro i
    by_cases hi:i=o
    · subst i
      simp only [outII,ite_true]
      exact ⟨le_min hcap hrem,min_le_left _ _⟩
    · simpa only [outII,ite_eq_right hi] using sideOut_feasible hk P Q hs hq t ω ho hi
  · have hout:(∑ i∈univ.erase o,outII hk P Q t ω o q i)=(∑ i∈univ.erase o,sideOut hk P Q t ω i):=by
      apply sum_congr rfl
      intro i hi
      exact ite_eq_right (mem_erase.mp hi).1
    rw [←sum_erase_add univ _ (mem_univ o),hout]
    have hm:=min_le_right (d k P Q t ω o) (q-∑ i∈univ.erase o,sideOut hk P Q t ω i)
    simp only [outII,ite_true]
    linarith
end KServer.ActualOutput

end


/-! Literal two-regime rule schedule of §05. The rule is decided without
using the parent allocation. Ordinary switches earn potential drops; the
filtering increment is retained on every history, before the tests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RuleSchedule
attribute [local instance] Classical.propDecidable

/-- `true` is rule II. Ties select I at a restart. -/
def choose (S D : ℝ) : Bool := decide (S < D/2)
def update (S D : ℝ) (old : Bool) : Bool :=
  if old then decide (S ≤ 2*D) else choose S D
def step (marked reset : Bool) (S D : ℝ) (old : Bool) : Bool :=
  if marked then if reset then choose S D else update S D old else false

def run {Ω : Type*} (marked reset : ℕ → Ω → Bool) (S D : ℕ → Ω → ℝ) : ℕ → Ω → Bool
  | 0, ω => step (marked 0 ω) true (S 0 ω) (D 0 ω) false
  | t+1, ω => step (marked (t+1) ω) (reset (t+1) ω) (S (t+1) ω) (D (t+1) ω)
      (run marked reset S D t ω)

def allowed (marked rule : Bool) (S D : ℝ) : Prop :=
  (marked=false → rule=false) ∧
  (marked=true → if rule then S≤2*D else D/2≤S)

lemma choose_allowed {S D : ℝ} (hD : 0≤D) :
    if choose S D then S≤2*D else D/2≤S := by
  unfold choose
  split_ifs with h
  · simp only [decide_eq_true_eq] at h
    linarith
  · simp only [decide_eq_true_eq,not_lt] at h
    exact h

lemma step_allowed {S D : ℝ} (hD : 0≤D) (marked reset old : Bool) :
    allowed marked (step marked reset S D old) S D := by
  cases marked with
  | false => simp [allowed,step]
  | true =>
    refine ⟨(by intro h; cases h), ?_⟩
    intro _
    change (if (if reset then choose S D else update S D old) then S≤2*D else D/2≤S)
    cases reset with
    | true => simpa using choose_allowed hD
    | false =>
      cases old with
      | false => simpa [update] using choose_allowed hD
      | true =>
        simp only [update,Bool.false_eq_true,ite_false,ite_true]
        split_ifs with h
        · exact of_decide_eq_true h
        · have h' : 2*D<S := by simpa only [decide_eq_true_eq,not_le] using h
          linarith

lemma run_allowed {Ω : Type*} (marked reset : ℕ → Ω → Bool) (S D : ℕ → Ω → ℝ)
    (hD : ∀ t ω,0≤D t ω) (t : ℕ) (ω : Ω) :
    allowed (marked t ω) (run marked reset S D t ω) (S t ω) (D t ω) := by
  cases t <;> exact step_allowed (hD _ _) _ _ _

def value (marked rule : Bool) (S D : ℝ) : ℝ :=
  if marked then if rule then S else D else 0

def charge (marked reset old : Bool) (S D : ℝ) : ℝ :=
  if reset then 0 else if marked then
    if update S D old=old then 0 else if update S D old then D else S
  else 0

variable {Ω R : Type*} [Fintype Ω] [Fintype R]
open RankTracking

def core (f : R → Bool) (p : R → ℝ) : ℝ := ∑ r,if f r then p r else 0

def coefficient (marked rule : Bool) (f : R → Bool) (r : R) : ℝ :=
  if marked && rule && f r then 1 else 0

end KServer.RuleSchedule

end


/-! The literal causal-regime output of a star: true hysteresis, both formulas,
and feasibility, uniformly in empty and vanishing-core cases. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def marked (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):Bool:=
  (mark P Q t ω).isSome
def reset (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):Bool:=
  decide (EpochSchedule.reset (vector cutoff ds P ω (t-1)) (vector cutoff ds P ω t)
    (key Q (t-1) ω) (key Q t ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=>key Q s ω) (t-1)))
def rule (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w):ℕ→Ω→Bool:=
  RuleSchedule.run (marked P Q) (reset P Q) (S P) (D P Q)
def out {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (t:ℕ) (ω:Ω) (q:ℝ):J→ℝ:=
  match mark P Q t ω with
  | none=>outI k P Q t ω q
  | some o=>if rule P Q t ω then outII hk P Q t ω o q else outI k P Q t ω q

lemma rule_allowed (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w) (t:ℕ) (ω:Ω):
  RuleSchedule.allowed (marked P Q t ω) (rule P Q t ω) (S P t ω) (D P Q t ω):=
  RuleSchedule.run_allowed _ _ _ _ (D_nonneg P Q) t ω
lemma out_feasible {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q):
    (∀ i,lower k (P i) t ω≤out hk P Q t ω q i ∧ out hk P Q t ω q i≤d k P Q t ω i) ∧
      (∑ i,out hk P Q t ω q i)≤q:=by
  have hr:=rule_allowed P Q t ω
  cases ho:mark P Q t ω with
  | none=>
    simp only [out,ho]
    exact outI_feasible hk P Q hs hq t ω q hp (fun o h=>by rw [ho] at h; cases h)
  | some o=>
    have hm:marked P Q t ω=true:=by simp [marked,ho]
    have hreg:=hr.2 hm
    cases hb:rule P Q t ω with
    | false=>
      simp only [out,ho,hb,Bool.false_eq_true,ite_false]
      simp only [hb,Bool.false_eq_true,ite_false] at hreg
      exact outI_feasible hk P Q hs hq t ω q hp (fun _ _=>hreg)
    | true=>
      simp only [out,ho,hb,ite_true]
      simp only [hb,ite_true] at hreg
      exact outII_feasible hk P Q hs hq t ω ho q hp hreg

lemma output_domination {k:ℝ} (hk:1≤k) (P:J→R→FilteredRanks w) (Q:R→FilteredRanks w)
    (hs:∀ t ω,(∑ i,size (P i) t ω)≤ size Q t ω) (hq:∀ t ω,size Q t ω≤k)
    (t:ℕ) (ω:Ω) (q:ℝ)
    (hp:(∑ i,(n P t ω i-β k Q t ω*B P t ω i+f k P Q t ω i))≤q) (i:J):
    0≤out hk P Q t ω q i ∧ out hk P Q t ω q i≤72*size (P i) t ω:=by
  have h:=out_feasible hk P Q hs hq t ω q hp
  exact ⟨(lower_nonneg hk (P i) t ω ((child_size P t ω i).trans ((hs t ω).trans (hq t ω)))).trans (h.1 i).1,
    (h.1 i).2.trans (d_bounds hk P Q t ω (hq t ω) i).2⟩
end KServer.ActualOutput

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationMovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree-independent movement algebra, allowing a zero simplex on an empty
active set and using the original fixed universe of star coordinates. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OutputDynamics
variable {J:Type*} [Fintype J]
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The same residual formula as Rule II on a fixed star universe. -/
def residual (o:J) (d:J→ℝ) (q D:ℝ) (w:J→ℝ):J→ℝ:=
  fun i=>if i=o then min (d o) (q-∑ j∈univ.erase o,(d j-D*w j)) else d i-D*w i

end KServer.OutputDynamics

end


/-! Literal residual-hole mass and switch estimates on the fixed star universe.
These bounds also cover empty side sets and zero active masses. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OutputDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {J:Type*} [Fintype J]

def residualHoles (o:J) (d:J→ℝ) (q D:ℝ) (w:J→ℝ):J→ℝ:=
  fun i=>d i-residual o d q D w i

end KServer.OutputDynamics

end


/-! Same-rule and full crossing movement bounds for the actual output,
with one unit of parent variation. -/


/-! Frozen-history affine payment with bounds on the actual held parameters.
No bound on fictitious off-schedule parameters is needed; the signed edit term
still has to be paid by the concrete coarse schedule. -/


/-! Dimension-free affine input slope on the actual held simplex parameters. -/


/-! Selective parameter charges on the actual size schedule.  In particular a
regular-component edit is charged only to its changed coordinate, and the
marked component is charged to side mass, never to the dominant child. -/


/-! Literal all-case pointwise movement, preserving the coefficient one of
parent movement. No probabilistic movement endpoint is assumed here. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def switchCharge (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  RuleSchedule.charge (marked P Q (t+1) ω) (reset P Q (t+1) ω)
    (rule P Q t ω) (S P (t+1) ω) (D P Q (t+1) ω)

end KServer.ActualOutput

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Rounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Prescribed correlated-total rounding and minimization over finite joint laws, without an independence requirement. -/


noncomputable section
open Finset
open scoped BigOperators
namespace KServer.Rounding

variable {J : Type*} [Fintype J] [DecidableEq J]

def move (p : J → ℝ) (x y : J) (ε : ℝ) : J → ℝ :=
  fun z => p z + ε * ((if z = y then 1 else 0) - (if z = x then 1 else 0))

omit [Fintype J] in
lemma move_nonneg {p : J → ℝ} (hp : ∀ z, 0 ≤ p z) {x y : J} {ε : ℝ}
    (hε : 0 ≤ ε) (hx : ε ≤ p x) : ∀ z, 0 ≤ move p x y ε z := by
  intro z
  by_cases hz : z = x
  · subst z
    by_cases hy : x = y
    · simp [move, hy, hp]
    · simp only [move, ite_eq_right hy, ite_true]
      linarith
  · by_cases hy : z = y
    · simp only [move, ite_eq_left hy, ite_eq_right hz]
      linarith [hp z]
    · simpa only [move, ite_eq_right hy, ite_eq_right hz, sub_self, mul_zero, add_zero] using hp z

lemma move_sum (p : J → ℝ) (x y : J) (ε : ℝ) (f : J → ℝ) :
    (∑ z, move p x y ε z * f z) = (∑ z, p z * f z) + ε * (f y - f x) := by
  calc (∑ z, move p x y ε z * f z) =
      ∑ z, (p z * f z + (if z = y then ε * f z else 0) -
        (if z = x then ε * f z else 0)) := by
          apply sum_congr rfl
          intro z _
          simp only [move]
          split_ifs <;> ring
    _ = _ := by rw [sum_sub_distrib, sum_add_distrib]; simp; ring

omit [Fintype J] in
lemma move_coordinate (p : J → ℝ) {x y z : J} {ε : ℝ} (hε : 0 ≤ ε)
    (hz : z ≠ x) : p z ≤ move p x y ε z := by
  by_cases hy : z = y
  · simp only [move, ite_eq_left hy, ite_eq_right hz]; linarith
  · simp [move, hy, hz]

variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq S] [DecidableEq I]

/-- Each fiber records the actual observed total, not a conditional mean. -/
abbrev Outcome (r : S → ℕ) := {x : S × Finset I // x.2.card = r x.1}

def subset {r : S → ℕ} (x : Outcome (I := I) r) : Finset I := x.val.2
def state {r : S → ℕ} (x : Outcome (I := I) r) : S := x.val.1

def Marginal {r : S → ℕ} (p : Outcome (I := I) r → ℝ) (i : I) : ℝ :=
  ∑ x, p x * (if i ∈ subset x then 1 else 0)

def Mass {r : S → ℕ} (p : Outcome (I := I) r → ℝ) (ω : S) : ℝ :=
  ∑ x, p x * (if state x = ω then 1 else 0)

def Feasible {r : S → ℕ} (p₀ p : Outcome (I := I) r → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∀ ω, Mass p ω = Mass p₀ ω

omit [DecidableEq I] in
lemma mass_total {r : S → ℕ} (p : Outcome (I := I) r → ℝ) :
    (∑ ω, Mass p ω) = ∑ x, p x := by
  simp only [Mass]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp

lemma marginal_total {r : S → ℕ} (p : Outcome (I := I) r → ℝ) :
    (∑ i, Marginal p i) = ∑ ω, Mass p ω * r ω := by
  simp only [Marginal, Mass]
  rw [sum_comm]
  simp_rw [sum_mul]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro x _
  have hx : (subset x).card = r (state x) := x.property
  simp only [← mul_sum]
  have h : (∑ i : I, if i ∈ subset x then (1 : ℝ) else 0) = (subset x).card := by simp
  rw [h, hx]
  simp

omit [DecidableEq I] in
lemma feasible_mass {r : S → ℕ} {p₀ p : Outcome (I := I) r → ℝ}
    (hp : Feasible p₀ p) : (∑ x, p x) = ∑ x, p₀ x := by
  rw [← mass_total p, ← mass_total p₀]
  exact sum_congr rfl fun ω _ => hp.2 ω

lemma move_feasible {r : S → ℕ} {p₀ p : Outcome (I := I) r → ℝ} (hp : Feasible p₀ p)
    {x y : Outcome (I := I) r} (hxy : state x = state y)
    {ε : ℝ} (hε : 0 ≤ ε) (hx : ε ≤ p x) : Feasible p₀ (move p x y ε) := by
  refine ⟨move_nonneg hp.1 hε hx, ?_⟩
  intro ω
  rw [Mass, move_sum, hxy]
  simpa [Mass] using hp.2 ω

omit [DecidableEq I] in
lemma continuous_mass {r : S → ℕ} (ω : S) : Continuous (fun p : Outcome (I := I) r → ℝ => Mass p ω) := by
  unfold Mass
  fun_prop

omit [DecidableEq S] in
lemma continuous_marginal {r : S → ℕ} (i : I) : Continuous (fun p : Outcome (I := I) r → ℝ => Marginal p i) := by
  unfold Marginal
  fun_prop

omit [DecidableEq I] in
lemma feasible_compact {r : S → ℕ} (p₀ : Outcome (I := I) r → ℝ)
    (h₀ : ∑ x, p₀ x = 1) : IsCompact {p | Feasible p₀ p} := by
  have hc : IsClosed {p | Feasible p₀ p} := by
    change IsClosed ({p : Outcome (I := I) r → ℝ | ∀ x, 0 ≤ p x} ∩
      {p | ∀ ω, Mass p ω = Mass p₀ ω})
    apply IsClosed.inter
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun ω => isClosed_eq (continuous_mass ω) continuous_const
  apply (isCompact_pi_infinite fun _ : Outcome (I := I) r =>
    isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset hc
  intro p hp x
  refine ⟨hp.1 x, ?_⟩
  have he : ∑ z, p z = 1 := (feasible_mass hp).trans h₀
  rw [← he]
  exact single_le_sum (fun z _ => hp.1 z) (mem_univ x)

def Objective {r : S → ℕ} (c : Outcome (I := I) r → ℝ) (f : I → ℝ)
    (p : Outcome (I := I) r → ℝ) : ℝ :=
  (∑ x, p x * c x) + 10 * ∑ i, |Marginal p i - f i|

omit [DecidableEq S] in
lemma objective_continuous {r : S → ℕ} (c : Outcome (I := I) r → ℝ) (f : I → ℝ) :
    Continuous (Objective c f) := by
  apply Continuous.add
  · fun_prop
  · apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    exact ((continuous_marginal i).sub continuous_const).abs

lemma exists_minimizer {r : S → ℕ} (p₀ c : Outcome (I := I) r → ℝ) (f : I → ℝ)
    (hp₀ : ∀ x, 0 ≤ p₀ x) (h₀ : ∑ x, p₀ x = 1) :
    ∃ p, Feasible p₀ p ∧ IsMinOn (Objective c f) {p | Feasible p₀ p} p := by
  exact (feasible_compact p₀ h₀).exists_isMinOn ⟨p₀, hp₀, fun _ => rfl⟩
    (objective_continuous c f).continuousOn

def exchange (A : Finset I) (i j : I) : Finset I := insert j (A.erase i)

omit [Fintype I] in
lemma exchange_card {A : Finset I} {i j : I} (hi : i ∈ A) (hj : j ∉ A) :
    (exchange A i j).card = A.card := by
  rw [exchange, card_insert_of_notMem (fun h => hj (mem_of_mem_erase h)), card_erase_of_mem hi]
  have := card_pos.mpr ⟨i, hi⟩
  omega

omit [Fintype I] in
lemma exchange_indicator {A : Finset I} {i j : I} (hi : i ∈ A) (hj : j ∉ A) (a : I) :
    (if a ∈ exchange A i j then (1 : ℝ) else 0) = (if a ∈ A then 1 else 0) +
       (if a = j then 1 else 0) - (if a = i then 1 else 0) := by
  have hij : i ≠ j := by intro h; subst j; contradiction
  by_cases ha : a = i
  · subst a; simp [exchange, hij, hi]
  · by_cases hb : a = j
    · subst a; simp [exchange, Ne.symm hij, hj]
    · simp [exchange, ha, hb]

def afterExchange {r : S → ℕ} (x : Outcome (I := I) r) (i j : I)
    (hi : i ∈ subset x) (hj : j ∉ subset x) : Outcome (I := I) r :=
  ⟨(state x, exchange (subset x) i j), (exchange_card hi hj).trans x.property⟩

lemma move_exchange_marginal {r : S → ℕ} (p : Outcome (I := I) r → ℝ)
    (x : Outcome (I := I) r) (i j : I) (hi : i ∈ subset x) (hj : j ∉ subset x)
    (ε : ℝ) (a : I) :
    Marginal (move p x (afterExchange x i j hi hj) ε) a = Marginal p a +
      ε * ((if a = j then 1 else 0) - (if a = i then 1 else 0)) := by
  rw [Marginal, move_sum]
  change _ + ε * ((if a ∈ exchange (subset x) i j then 1 else 0) - _) = _
  rw [exchange_indicator hi hj]
  unfold Marginal
  ring

lemma deviation_descent (a f : I → ℝ) {i j : I} (hij : i ≠ j) {ε : ℝ}
    (hε : 0 ≤ ε) (hi : ε ≤ a i - f i) (hj : ε ≤ f j - a j) :
    (∑ x, |a x + ε * ((if x = j then 1 else 0) - (if x = i then 1 else 0)) - f x|) =
    (∑ x, |a x - f x|) - 2 * ε := by
  have he (x : I) :
      |a x + ε * ((if x = j then 1 else 0) - (if x = i then 1 else 0)) - f x| =
      |a x - f x| - (if x = i then ε else 0) - (if x = j then ε else 0) := by
    by_cases hx : x = i
    · subst x
      simp only [ite_eq_right hij, ite_true]
      rw [abs_of_nonneg (by linarith : 0 ≤ a i + ε * (0 - 1) - f i),
        abs_of_nonneg (by linarith : 0 ≤ a i - f i)]
      ring
    · by_cases hy : x = j
      · subst x
        simp only [ite_true, ite_eq_right (Ne.symm hij)]
        rw [abs_of_nonpos (by linarith : a j + ε * (1 - 0) - f j ≤ 0),
          abs_of_nonpos (by linarith : a j - f j ≤ 0)]
        ring
      · simp [hx, hy]
  simp_rw [he]
  rw [sum_sub_distrib, sum_sub_distrib]
  simp
  ring

omit [DecidableEq I] in
lemma discrepancy_pair (a f : I → ℝ) (hs : ∑ i, a i = ∑ i, f i)
    (hne : ¬∀ i, a i = f i) : ∃ i j, a i > f i ∧ a j < f j := by
  have hi : ∃ i, f i < a i := by
    by_contra! h
    apply hne
    intro i
    exact (sum_eq_sum_iff_of_le (fun i _ => h i)).mp hs i (mem_univ _)
  have hj : ∃ j, a j < f j := by
    by_contra! h
    apply hne
    have he := (sum_eq_sum_iff_of_le (fun i _ => h i)).mp hs.symm
    intro i
    exact (he i (mem_univ i)).symm
  obtain ⟨i, hi⟩ := hi
  obtain ⟨j, hj⟩ := hj
  exact ⟨i, j, hi, hj⟩

omit [DecidableEq S] in
lemma support_mem {r : S → ℕ} {p : Outcome (I := I) r → ℝ} (hp : ∀x, 0 ≤ p x)
    {i : I} (hi : 0 < Marginal p i) : ∃ x, 0 < p x ∧ i ∈ subset x := by
  by_contra! h
  have he : Marginal p i = 0 := by
    apply sum_eq_zero
    intro x _
    by_cases hh : 0 < p x
    · simp [h x hh]
    · have hz := le_antisymm (le_of_not_gt hh) (hp x)
      simp [hz]
  linarith

omit [DecidableEq S] in
lemma support_notMem {r : S → ℕ} {p : Outcome (I := I) r → ℝ} (hp : ∀x, 0 ≤ p x)
    (h₁ : ∑ x, p x = 1) {i : I} (hi : Marginal p i < 1) :
    ∃ x, 0 < p x ∧ i ∉ subset x := by
  by_contra! h
  have he : Marginal p i = ∑ x, p x := by
    apply sum_congr rfl
    intro x _
    by_cases hh : 0 < p x
    · simp [h x hh]
    · have hz := le_antisymm (le_of_not_gt hh) (hp x)
      simp [hz]
  linarith

omit [Fintype I] in
lemma exists_bridge {A B : Finset I} {i j : I} (hij : i ≠ j)
    (hiA : i ∈ A) (hjA : j ∈ A) (hiB : i ∉ B) (hjB : j ∉ B)
    (hc : A.card ≤ B.card + 1) : ∃ h, h ∈ B ∧ h ∉ A := by
  by_contra! hh
  have hBA : B ⊆ A := hh
  have hsub : insert i (insert j B) ⊆ A := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hiA
    rcases mem_insert.mp ha with rfl | ha
    · exact hjA
    exact hBA ha
  have hcard := card_le_card hsub
  have hn : i ∉ insert j B := by simp [hij, hiB]
  rw [card_insert_of_notMem hn, card_insert_of_notMem hjB] at hcard
  omega

/-- The local Lipschitz property needed by the repair objective. It will be
instantiated by Hamming distance from the state's preliminary rounding. -/
def ExchangeCost {r : S → ℕ} (c : Outcome (I := I) r → ℝ) : Prop :=
  ∀ (x : Outcome (I := I) r) (i j : I) (hi : i ∈ subset x) (hj : j ∉ subset x),
    c (afterExchange x i j hi hj) - c x ≤ 2

lemma one_exchange_improves {r : S → ℕ} {p₀ p c : Outcome (I := I) r → ℝ} {f : I → ℝ}
    (hp : Feasible p₀ p) (hc : ExchangeCost c)
    {i j : I} (hi : f i < Marginal p i) (hj : Marginal p j < f j)
    (x : Outcome (I := I) r) (hx : 0 < p x) (hxi : i ∈ subset x) (hxj : j ∉ subset x) :
    ∃ q, Feasible p₀ q ∧ Objective c f q < Objective c f p := by
  have hij : i ≠ j := by intro he; subst j; linarith
  let ε := min (p x) (min (Marginal p i - f i) (f j - Marginal p j))
  have hε : 0 < ε := lt_min hx (lt_min (sub_pos.mpr hi) (sub_pos.mpr hj))
  have hεx : ε ≤ p x := min_le_left _ _
  have hεi : ε ≤ Marginal p i - f i := (min_le_right _ _).trans (min_le_left _ _)
  have hεj : ε ≤ f j - Marginal p j := (min_le_right _ _).trans (min_le_right _ _)
  let y := afterExchange x i j hxi hxj
  let q := move p x y ε
  refine ⟨q, move_feasible (x := x) (y := y) hp rfl hε.le hεx, ?_⟩
  have hd : (∑ a, |Marginal q a - f a|) = (∑ a, |Marginal p a - f a|) - 2 * ε := by
    simp only [q, y, move_exchange_marginal]
    exact deviation_descent _ _ hij hε.le hεi hεj
  have hcost : (∑ z, q z * c z) ≤ (∑ z, p z * c z) + 2 * ε := by
    dsimp only [q]
    rw [move_sum]
    have hh := mul_le_mul_of_nonneg_left (hc x i j hxi hxj) hε.le
    dsimp [y]
    linarith
  unfold Objective
  rw [hd]
  linarith

lemma two_exchanges_improve {r : S → ℕ} {p₀ p c : Outcome (I := I) r → ℝ} {f : I → ℝ}
    (hp : Feasible p₀ p) (hc : ExchangeCost c)
    {i j : I} (hi : f i < Marginal p i) (hj : Marginal p j < f j)
    (x y : Outcome (I := I) r) (hx : 0 < p x) (hy : 0 < p y)
    (hxi : i ∈ subset x) (hxj : j ∈ subset x)
    (hyi : i ∉ subset y) (hyj : j ∉ subset y)
    (h : I) (hyh : h ∈ subset y) (hxh : h ∉ subset x) :
    ∃ q, Feasible p₀ q ∧ Objective c f q < Objective c f p := by
  have hij : i ≠ j := by intro he; subst j; linarith
  have hyx : y ≠ x := by intro he; subst y; contradiction
  let ε := min (min (p x) (p y)) (min (Marginal p i - f i) (f j - Marginal p j))
  have hε : 0 < ε := lt_min (lt_min hx hy) (lt_min (sub_pos.mpr hi) (sub_pos.mpr hj))
  have hεx : ε ≤ p x := (min_le_left _ _).trans (min_le_left _ _)
  have hεy : ε ≤ p y := (min_le_left _ _).trans (min_le_right _ _)
  have hεi : ε ≤ Marginal p i - f i := (min_le_right _ _).trans (min_le_left _ _)
  have hεj : ε ≤ f j - Marginal p j := (min_le_right _ _).trans (min_le_right _ _)
  let x' := afterExchange x i h hxi hxh
  let y' := afterExchange y h j hyh hyj
  let mid := move p x x' ε
  let q := move mid y y' ε
  have hmid : Feasible p₀ mid := move_feasible (x := x) (y := x') hp rfl hε.le hεx
  have hq : Feasible p₀ q := move_feasible (x := y) (y := y') hmid rfl hε.le
    (hεy.trans (move_coordinate p hε.le hyx))
  refine ⟨q, hq, ?_⟩
  have hm (a : I) : Marginal q a = Marginal p a +
      ε * ((if a = j then 1 else 0) - (if a = i then 1 else 0)) := by
    dsimp only [q, mid, x', y']
    rw [move_exchange_marginal, move_exchange_marginal]
    ring
  have hd : (∑ a, |Marginal q a - f a|) = (∑ a, |Marginal p a - f a|) - 2 * ε := by
    simp only [hm]
    exact deviation_descent _ _ hij hε.le hεi hεj
  have hcost : (∑ z, q z * c z) ≤ (∑ z, p z * c z) + 4 * ε := by
    dsimp only [q, mid]
    rw [move_sum, move_sum]
    have hhx := mul_le_mul_of_nonneg_left (hc x i h hxi hxh) hε.le
    have hhy := mul_le_mul_of_nonneg_left (hc y h j hyh hyj) hε.le
    dsimp only [x', y']
    linarith
  unfold Objective
  rw [hd]
  linarith

/-- A minimizer has the prescribed unconditional marginals, even when different
fibers have different adjacent totals. This is the source's essential
correlation-tolerant two-state exchange argument. -/
lemma minimizer_marginals {r : S → ℕ} {p₀ p c : Outcome (I := I) r → ℝ} {f : I → ℝ}
    (hr : ∀ ω ν, r ω ≤ r ν + 1) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hfSum : ∑ i, f i = ∑ ω, Mass p₀ ω * r ω)
    (hp : Feasible p₀ p) (h₀ : ∑ x, p₀ x = 1) (hc : ExchangeCost c)
    (hmin : IsMinOn (Objective c f) {p | Feasible p₀ p} p) :
    ∀ i, Marginal p i = f i := by
  by_contra hne
  have hsum : ∑ i, Marginal p i = ∑ i, f i := by
    rw [marginal_total, hfSum]
    exact sum_congr rfl fun ω _ => by rw [hp.2 ω]
  obtain ⟨i, j, hi, hj⟩ := discrepancy_pair (Marginal p) f hsum hne
  have hij : i ≠ j := by intro he; subst j; linarith
  by_cases hex : ∃ x, 0 < p x ∧ i ∈ subset x ∧ j ∉ subset x
  · obtain ⟨x, hx, hxi, hxj⟩ := hex
    obtain ⟨q, hq, hqCost⟩ := one_exchange_improves hp hc hi hj x hx hxi hxj
    exact (not_lt_of_ge (hmin hq)) hqCost
  · obtain ⟨x, hx, hxi⟩ := support_mem hp.1 ((hf i).1.trans_lt hi)
    have hxj : j ∈ subset x := by
      by_contra hh
      exact hex ⟨x, hx, hxi, hh⟩
    obtain ⟨y, hy, hyj⟩ := support_notMem hp.1 ((feasible_mass hp).trans h₀) (hj.trans_le (hf j).2)
    have hyi : i ∉ subset y := fun hh => hex ⟨y, hy, hh, hyj⟩
    have hcard : (subset x).card ≤ (subset y).card + 1 := by
      rw [show (subset x).card = r (state x) from x.property,
          show (subset y).card = r (state y) from y.property]
      exact hr _ _
    obtain ⟨h, hyh, hxh⟩ := exists_bridge hij hxi hxj hyi hyj hcard
    obtain ⟨q, hq, hqCost⟩ := two_exchanges_improve hp hc hi hj x y hx hy hxi hxj hyi hyj h hyh hxh
    exact (not_lt_of_ge (hmin hq)) hqCost

/-- The compact finite-law repair step, including its quantitative cost bound. -/
theorem finite_repair {r : S → ℕ} (p₀ c : Outcome (I := I) r → ℝ) (f : I → ℝ)
    (hr : ∀ ω ν, r ω ≤ r ν + 1) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hfSum : ∑ i, f i = ∑ ω, Mass p₀ ω * r ω)
    (hp₀ : ∀ x, 0 ≤ p₀ x) (h₀ : ∑ x, p₀ x = 1) (hc : ExchangeCost c) :
    ∃ p, Feasible p₀ p ∧ (∀ i, Marginal p i = f i) ∧
      (∑ x, p x * c x) ≤ (∑ x, p₀ x * c x) + 10 * ∑ i, |Marginal p₀ i - f i| := by
  obtain ⟨p, hp, hm⟩ := exists_minimizer p₀ c f hp₀ h₀
  have hmar := minimizer_marginals hr hf hfSum hp h₀ hc hm
  refine ⟨p, hp, hmar, ?_⟩
  have hh := hm (show Feasible p₀ p₀ from ⟨hp₀, fun _ => rfl⟩)
  simpa [Objective, hmar] using hh

def hamming (A B : Finset I) : ℝ :=
  ∑ i, |(if i ∈ A then (1 : ℝ) else 0) - (if i ∈ B then 1 else 0)|

lemma hamming_self (A : Finset I) : hamming A A = 0 := by simp [hamming]

lemma hamming_triangle (A B C : Finset I) : hamming A C ≤ hamming A B + hamming B C := by
  rw [hamming, hamming, hamming, ← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

lemma hamming_exchange {A : Finset I} {i j : I} (hi : i ∈ A) (hj : j ∉ A) :
    hamming (exchange A i j) A = 2 := by
  have hij : i ≠ j := by intro he; subst j; contradiction
  have he (a : I) :
      |(if a ∈ exchange A i j then (1 : ℝ) else 0) - (if a ∈ A then 1 else 0)| =
      (if a = j then 1 else 0) + (if a = i then 1 else 0) := by
    rw [exchange_indicator hi hj]
    by_cases ha : a = i
    · subst a; simp [hij]
    · by_cases hb : a = j
      · subst a; simp [Ne.symm hij]
      · simp [ha, hb]
  simp only [hamming, he, sum_add_distrib]
  norm_num

def HammingCost {r : S → ℕ} (A₀ : S → Finset I) (x : Outcome (I := I) r) : ℝ :=
  hamming (subset x) (A₀ (state x))

omit [Fintype S] [DecidableEq S] in
lemma hamming_exchangeCost {r : S → ℕ} (A₀ : S → Finset I) :
    ExchangeCost (HammingCost (r := r) A₀) := by
  intro x i j hi hj
  have hh := hamming_triangle (exchange (subset x) i j) (subset x) (A₀ (state x))
  rw [hamming_exchange hi hj] at hh
  change hamming (exchange (subset x) i j) (A₀ (state x)) - _ ≤ 2
  unfold HammingCost
  linarith

def seed {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r) : Outcome (I := I) r → ℝ :=
  fun x => ∑ ω, if x = e ω then w ω else 0

omit [Fintype I] in
lemma seed_nonneg {r : S → ℕ} {w : S → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (e : S → Outcome (I := I) r) : ∀ x, 0 ≤ seed w e x := by
  intro x
  exact sum_nonneg fun ω _ => by split_ifs; exact hw ω; rfl

lemma seed_sum {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r)
    (g : Outcome (I := I) r → ℝ) :
    (∑ x, seed w e x * g x) = ∑ ω, w ω * g (e ω) := by
  simp only [seed, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp [ite_mul]

lemma seed_total {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r) :
    (∑ x, seed w e x) = ∑ ω, w ω := by
  simpa using seed_sum w e (fun _ => 1)

lemma seed_mass {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r)
    (he : ∀ ω, state (e ω) = ω) (ω : S) : Mass (seed w e) ω = w ω := by
  rw [Mass, seed_sum]
  simp [he]

lemma seed_marginal {r : S → ℕ} (w : S → ℝ) (e : S → Outcome (I := I) r) (i : I) :
    Marginal (seed w e) i = ∑ ω, w ω * (if i ∈ subset (e ω) then 1 else 0) := by
  exact seed_sum _ _ _

/-- Joint-law repair in the exact Hamming metric of the manuscript. All
correlation is retained by preserving every original state probability. -/
theorem hamming_repair (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (r : S → ℕ) (hr : ∀ ω ν, r ω ≤ r ν + 1) (A₀ : S → Finset I)
    (hA : ∀ ω, (A₀ ω).card = r ω) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hs : ∑ i, f i = ∑ ω, w ω * r ω) :
    ∃ p : Outcome (I := I) r → ℝ, (∀ x, 0 ≤ p x) ∧ (∀ ω, Mass p ω = w ω) ∧
      (∀ i, Marginal p i = f i) ∧
      (∑ x, p x * HammingCost A₀ x) ≤
        10 * ∑ i, |(∑ ω, w ω * (if i ∈ A₀ ω then 1 else 0)) - f i| := by
  let e : S → Outcome (I := I) r := fun ω => ⟨(ω, A₀ ω), hA ω⟩
  have he (ω : S) : state (e ω) = ω := rfl
  have hsubset (ω : S) : subset (e ω) = A₀ ω := rfl
  have hmass := seed_mass w e he
  have hfs : ∑ i, f i = ∑ ω, Mass (seed w e) ω * r ω := by simpa [hmass] using hs
  obtain ⟨p, hp, hmar, hcost⟩ := finite_repair (seed w e) (HammingCost A₀) f hr hf hfs
    (seed_nonneg hw e) ((seed_total w e).trans h₁) (hamming_exchangeCost A₀)
  refine ⟨p, hp.1, fun ω => (hp.2 ω).trans (hmass ω), hmar, ?_⟩
  have hzero : (∑ x, seed w e x * HammingCost A₀ x) = 0 := by
    rw [seed_sum]
    simp [HammingCost, he, hsubset, hamming_self]
  simpa [hzero, seed_marginal, hsubset] using hcost

lemma hamming_comm (A B : Finset I) : hamming A B = hamming B A := by
  apply sum_congr rfl
  intro i _
  exact abs_sub_comm _ _

lemma hamming_subset {A B : Finset I} (h : B ⊆ A) :
    hamming A B = (A.card : ℝ) - B.card := by
  have hn (i : I) : (0 : ℝ) ≤ (if i ∈ A then 1 else 0) - (if i ∈ B then 1 else 0) := by
    by_cases hi : i ∈ B
    · simp [hi, h hi]
    · simp [hi]; split_ifs <;> norm_num
  simp only [hamming, abs_of_nonneg (hn _)]
  rw [sum_sub_distrib]
  simp

/-- Deterministic adjustment to any attainable integer total, with optimal
Hamming cost. The permitted coordinates H may omit all integral targets. -/
lemma adjust_subset (H A : Finset I) (hAH : A ⊆ H) {r : ℕ} (hr : r ≤ H.card) :
    ∃ B : Finset I, B ⊆ H ∧ B.card = r ∧ hamming B A = |(r : ℝ) - A.card| := by
  by_cases hsmall : r ≤ A.card
  · obtain ⟨B, hBA, hBr⟩ := exists_subset_card_eq hsmall
    refine ⟨B, hBA.trans hAH, hBr, ?_⟩
    rw [hamming_comm, hamming_subset hBA, hBr, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hsmall : (r : ℝ) ≤ A.card))]
    ring
  · have hbig : A.card ≤ r := le_of_not_ge hsmall
    have hc : r - A.card ≤ (H \ A).card := by
      rw [card_sdiff, inter_eq_left.mpr hAH]
      omega
    obtain ⟨C, hCH, hCr⟩ := exists_subset_card_eq hc
    have hdis : Disjoint A C := by
      apply disjoint_left.mpr
      intro a ha hca
      exact (mem_sdiff.mp (hCH hca)).2 ha
    let B := A ∪ C
    have hAB : A ⊆ B := subset_union_left
    have hBH : B ⊆ H := union_subset hAH (hCH.trans sdiff_subset)
    have hBr : B.card = r := by
      dsimp [B]
      rw [card_union_of_disjoint hdis, hCr]
      omega
    refine ⟨B, hBH, hBr, ?_⟩
    rw [hamming_subset hAB, hBr, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hbig : (A.card : ℝ) ≤ r))]

/-- The literal scalar interval used by the source's preliminary clipping. -/
def clip (b : ℝ) (x : ℤ) : ℤ := max ⌊b⌋ (min ⌈b⌉ x)

def Balanced (b : ℝ) (x : ℤ) : Prop := x = ⌊b⌋ ∨ x = ⌈b⌉

lemma balanced_iff_bounds (b : ℝ) (x : ℤ) :
    Balanced b x ↔ ⌊b⌋ ≤ x ∧ x ≤ ⌈b⌉ := by
  have hl := Int.floor_le_ceil b
  have hu := Int.ceil_le_floor_add_one b
  unfold Balanced
  omega

lemma clip_balanced (b : ℝ) (x : ℤ) : Balanced b (clip b x) := by
  rw [balanced_iff_bounds]
  exact ⟨le_max_left _ _, max_le (Int.floor_le_ceil b) (min_le_left _ _)⟩

lemma balanced_bounds {b : ℝ} {x : ℤ} (h : Balanced b x) :
    ⌊b⌋ ≤ x ∧ x ≤ ⌈b⌉ := (balanced_iff_bounds b x).mp h

lemma clip_up {a b : ℝ} (hab : a ≤ b) {x : ℤ} (hx : Balanced a x) :
    clip b x = max ⌊b⌋ x := by
  unfold clip
  rw [min_eq_right ((balanced_bounds hx).2.trans (Int.ceil_mono hab))]

lemma clip_down {a b : ℝ} (hab : b ≤ a) {x : ℤ} (hx : Balanced a x) :
    clip b x = min ⌈b⌉ x := by
  unfold clip
  rw [max_eq_right (le_min (Int.floor_le_ceil b) ((Int.floor_mono hab).trans (balanced_bounds hx).1))]

omit [DecidableEq S] in
/-- Exact source clipping estimate, with arbitrary finite weights and no
independence assumptions. -/
lemma clipping_bound (w : S → ℝ) (_hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    {a b : ℝ} (X : S → ℤ) (hX : ∀ ω, Balanced a (X ω))
    (hmean : ∑ ω, w ω * (X ω : ℝ) = a) :
    (∑ ω, w ω * |(clip b (X ω) : ℝ) - X ω|) ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · simp_rw [clip_up hab (hX _)]
    by_cases hf : ⌊b⌋ ≤ ⌊a⌋
    · have hh (ω : S) : max ⌊b⌋ (X ω) = X ω := max_eq_right (hf.trans (balanced_bounds (hX ω)).1)
      simp [hh]
    · have hl : ⌈a⌉ ≤ ⌊b⌋ := by have := Int.ceil_le_floor_add_one a; omega
      have hh (ω : S) : max ⌊b⌋ (X ω) = ⌊b⌋ := max_eq_left ((balanced_bounds (hX ω)).2.trans hl)
      have hn (ω : S) : (0 : ℝ) ≤ (⌊b⌋ : ℝ) - X ω := by
        exact_mod_cast sub_nonneg.mpr ((balanced_bounds (hX ω)).2.trans hl)
      simp_rw [hh, abs_of_nonneg (hn _), mul_sub]
      rw [sum_sub_distrib, ← sum_mul, h₁, one_mul, hmean, abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith [Int.floor_le b]
  · simp_rw [clip_down hba (hX _)]
    by_cases hc : ⌈a⌉ ≤ ⌈b⌉
    · have hh (ω : S) : min ⌈b⌉ (X ω) = X ω := min_eq_right ((balanced_bounds (hX ω)).2.trans hc)
      simp [hh]
    · have hu : ⌈b⌉ ≤ ⌊a⌋ := by have := Int.ceil_le_floor_add_one a; omega
      have hh (ω : S) : min ⌈b⌉ (X ω) = ⌈b⌉ := min_eq_left (hu.trans (balanced_bounds (hX ω)).1)
      have hn (ω : S) : (⌈b⌉ : ℝ) - X ω ≤ 0 := by
        exact_mod_cast sub_nonpos.mpr (hu.trans (balanced_bounds (hX ω)).1)
      simp_rw [hh, abs_of_nonpos (hn _), mul_neg, mul_sub]
      rw [sum_neg_distrib, sum_sub_distrib, ← sum_mul, h₁, one_mul, hmean, abs_of_nonneg (sub_nonneg.mpr hba)]
      linarith [Int.le_ceil b]

def fraction (b : ℝ) : ℝ := b - ⌊b⌋

def fractionalSet (b : I → ℝ) : Finset I := univ.filter fun i => ⌊b i⌋ < ⌈b i⌉

def liftSet (b : I → ℝ) (A : Finset I) (i : I) : ℤ :=
  ⌊b i⌋ + if i ∈ A then 1 else 0

lemma fraction_range (b : ℝ) : 0 ≤ fraction b ∧ fraction b < 1 := by
  unfold fraction
  constructor <;> linarith [Int.floor_le b, Int.lt_floor_add_one b]

lemma ceil_formula (b : ℝ) : ⌈b⌉ = ⌊b⌋ + if ⌊b⌋ < ⌈b⌉ then 1 else 0 := by
  have := Int.ceil_le_floor_add_one b
  have := Int.floor_le_ceil b
  split_ifs <;> omega

lemma not_fractional {b : ℝ} (h : ¬⌊b⌋ < ⌈b⌉) : (⌊b⌋ : ℝ) = b := by
  have he : ⌊b⌋ = ⌈b⌉ := by have := Int.floor_le_ceil b; omega
  apply le_antisymm (Int.floor_le b)
  rw [he]
  exact Int.le_ceil b

lemma fraction_zero_iff (b : ℝ) : fraction b = 0 ↔ ¬⌊b⌋ < ⌈b⌉ := by
  constructor
  · intro h
    have he : b = (⌊b⌋ : ℝ) := by unfold fraction at h; linarith
    have hc := Int.ceil_le.mpr he.le
    omega
  · intro h
    simp [fraction, not_fractional h]

lemma liftSet_sum (b : I → ℝ) (A : Finset I) :
    (∑ i, liftSet b A i) = (∑ i, ⌊b i⌋) + A.card := by
  simp [liftSet, sum_add_distrib]

lemma liftSet_balanced (b : I → ℝ) {A : Finset I} (hA : A ⊆ fractionalSet b) (i : I) :
    Balanced (b i) (liftSet b A i) := by
  unfold liftSet
  by_cases hi : i ∈ A
  · simp only [ite_eq_left hi]
    right
    have hbi : ⌊b i⌋ < ⌈b i⌉ := (mem_filter.mp (hA hi)).2
    rw [ceil_formula, ite_eq_left hbi]
  · left
    simp [hi]

lemma balanced_liftSet (b : I → ℝ) (Y : I → ℤ) (hY : ∀ i, Balanced (b i) (Y i)) :
    ∃ A : Finset I, A ⊆ fractionalSet b ∧ ∀ i, Y i = liftSet b A i := by
  let A := univ.filter fun i => ⌊b i⌋ < Y i
  have hA : A ⊆ fractionalSet b := by
    intro i hi
    have hi' : ⌊b i⌋ < Y i := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _, hi'.trans_le (balanced_bounds (hY i)).2⟩
  refine ⟨A, hA, ?_⟩
  intro i
  have hu := Int.ceil_le_floor_add_one (b i)
  have := balanced_bounds (hY i)
  by_cases hi : i ∈ A
  · unfold liftSet
    rw [ite_eq_left hi]
    have hh : ⌊b i⌋ < Y i := (mem_filter.mp hi).2
    omega
  · unfold liftSet
    rw [ite_eq_right hi]
    have hh : ¬⌊b i⌋ < Y i := by simpa [A] using hi
    omega

lemma liftSet_distance (b : I → ℝ) (A B : Finset I) :
    (∑ i, |(liftSet b A i : ℝ) - liftSet b B i|) = hamming A B := by
  apply sum_congr rfl
  intro i _
  unfold liftSet
  push_cast
  congr 1
  ring

omit [DecidableEq I] in
lemma total_endpoints (b : I → ℝ) :
    (∑ i, ⌊b i⌋) ≤ ⌊∑ i, b i⌋ ∧ ⌈∑ i, b i⌉ ≤ (∑ i, ⌊b i⌋) + (fractionalSet b).card := by
  constructor
  · apply Int.le_floor.mpr
    push_cast
    exact sum_le_sum fun i _ => Int.floor_le _
  · apply Int.ceil_le.mpr
    have he : (∑ i, ⌈b i⌉) = (∑ i, ⌊b i⌋) + (fractionalSet b).card := by
      calc
        (∑ i, ⌈b i⌉) = ∑ i, (⌊b i⌋ + if ⌊b i⌋ < ⌈b i⌉ then (1 : ℤ) else 0) :=
          sum_congr rfl (fun i _ => ceil_formula (b i))
        _ = _ := ?_
      rw [sum_add_distrib]
      congr 1
      simp [fractionalSet]
    rw [← he]
    push_cast
    exact sum_le_sum fun i _ => Int.le_ceil _

def residual (b : I → ℝ) (N : ℤ) : ℕ := (N - ∑ i, ⌊b i⌋).toNat

omit [DecidableEq I] in
lemma residual_cast (b : I → ℝ) {N : ℤ} (hN : Balanced (∑ i, b i) N) :
    (residual b N : ℤ) = N - ∑ i, ⌊b i⌋ := by
  unfold residual
  apply Int.toNat_of_nonneg
  exact sub_nonneg.mpr ((total_endpoints b).1.trans (balanced_bounds hN).1)

omit [DecidableEq I] in
lemma residual_bound (b : I → ℝ) {N : ℤ} (hN : Balanced (∑ i, b i) N) :
    residual b N ≤ (fractionalSet b).card := by
  have hcast := residual_cast b hN
  have hu := (balanced_bounds hN).2.trans (total_endpoints b).2
  omega

omit [DecidableEq I] in
lemma residual_adjacent (b : I → ℝ) {N M : ℤ}
    (hN : Balanced (∑ i, b i) N) (hM : Balanced (∑ i, b i) M) :
    residual b N ≤ residual b M + 1 := by
  have hcastN := residual_cast b hN
  have hcastM := residual_cast b hM
  have hN' := balanced_bounds hN
  have hM' := balanced_bounds hM
  have := Int.ceil_le_floor_add_one (∑ i, b i)
  omega

omit [DecidableEq I] in
lemma residual_cast_real (b : I → ℝ) {N : ℤ} (hN : Balanced (∑ i, b i) N) :
    (residual b N : ℝ) = N - ∑ i, (⌊b i⌋ : ℝ) := by
  have he := congrArg (fun z : ℤ => (z : ℝ)) (residual_cast b hN)
  simpa using he

omit [DecidableEq I] [DecidableEq S] in
lemma residual_mean (w : S → ℝ) (h₁ : ∑ ω, w ω = 1) (b : I → ℝ) (N : S → ℤ)
    (hN : ∀ ω, Balanced (∑ i, b i) (N ω)) (hm : ∑ ω, w ω * (N ω : ℝ) = ∑ i, b i) :
    (∑ i, fraction (b i)) = ∑ ω, w ω * residual b (N ω) := by
  simp_rw [residual_cast_real b (hN _), mul_sub, fraction]
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, h₁, one_mul, hm]

/-- The statewise preliminary adjustment has exactly the source's cost. -/
lemma preliminary_state (b : I → ℝ) (X : I → ℤ) {N : ℤ}
    (hN : Balanced (∑ i, b i) N) :
    ∃ A : Finset I, A ⊆ fractionalSet b ∧ A.card = residual b N ∧
      (∑ i, |(liftSet b A i : ℝ) - clip (b i) (X i)|) =
        |(N : ℝ) - ∑ i, (clip (b i) (X i) : ℝ)| := by
  obtain ⟨Y, hY, he⟩ := balanced_liftSet b (fun i => clip (b i) (X i))
    (fun i => clip_balanced _ _)
  obtain ⟨A, hA, hcard, hcost⟩ := adjust_subset (fractionalSet b) Y hY (residual_bound b hN)
  refine ⟨A, hA, hcard, ?_⟩
  simp_rw [he]
  rw [liftSet_distance, hcost, residual_cast_real b hN]
  congr 1
  have hy := congrArg (fun z : ℤ => (z : ℝ)) (liftSet_sum b Y)
  push_cast at hy
  rw [hy]
  ring

def mean (w : S → ℝ) (X : S → ℝ) : ℝ := ∑ ω, w ω * X ω

def dist₁ (X Y : I → ℝ) : ℝ := ∑ i, |X i - Y i|

omit [DecidableEq I] in
lemma dist₁_triangle (X Y Z : I → ℝ) : dist₁ X Z ≤ dist₁ X Y + dist₁ Y Z := by
  unfold dist₁
  rw [← sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

omit [DecidableEq I] in
lemma abs_total_le (X Y : I → ℝ) : |(∑ i, X i) - ∑ i, Y i| ≤ dist₁ X Y := by
  rw [← sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _

omit [DecidableEq S] in
lemma mean_mono (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) {X Y : S → ℝ}
    (h : ∀ ω, X ω ≤ Y ω) : mean w X ≤ mean w Y :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)

omit [DecidableEq S] in
lemma mean_add (w : S → ℝ) (X Y : S → ℝ) :
    mean w (fun ω => X ω + Y ω) = mean w X + mean w Y := by
  simp [mean, mul_add, sum_add_distrib]

omit [DecidableEq S] in
lemma mean_abs_sub (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (X Y : S → ℝ) :
    |mean w X - mean w Y| ≤ mean w (fun ω => |X ω - Y ω|) := by
  calc
    |mean w X - mean w Y| = |∑ ω, w ω * (X ω - Y ω)| := by
      simp [mean, mul_sub, sum_sub_distrib]
    _ ≤ ∑ ω, |w ω * (X ω - Y ω)| := abs_sum_le_sum_abs _ _
    _ = _ := by simp [mean, abs_mul, abs_of_nonneg (hw _)]

omit [DecidableEq I] [DecidableEq S] in
lemma dist₁_mean (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (X Y : S → I → ℝ) :
    dist₁ (fun i => mean w (fun ω => X ω i)) (fun i => mean w (fun ω => Y ω i)) ≤
      mean w (fun ω => dist₁ (X ω) (Y ω)) := by
  calc
    _ ≤ ∑ i, mean w (fun ω => |X ω i - Y ω i|) :=
      sum_le_sum fun i _ => mean_abs_sub w hw _ _
    _ = _ := by unfold mean dist₁; rw [sum_comm]; simp_rw [mul_sum]

omit [DecidableEq S] in
lemma preliminary_bounds (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (a b : I → ℝ) (X : S → I → ℤ) (N : S → ℤ)
    (hX : ∀ ω i, Balanced (a i) (X ω i))
    (hm : ∀ i, mean w (fun ω => (X ω i : ℝ)) = a i)
    (A : S → Finset I)
    (hadj : ∀ ω, (∑ i, |(liftSet b (A ω) i : ℝ) - clip (b i) (X ω i)|) =
      |(N ω : ℝ) - ∑ i, (clip (b i) (X ω i) : ℝ)|) :
    let L := mean w (fun ω => dist₁ (fun i => (liftSet b (A ω) i : ℝ)) (fun i => (X ω i : ℝ)))
    let T := dist₁ a b
    let U := mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|)
    let D := dist₁ (fun i => mean w (fun ω => (liftSet b (A ω) i : ℝ))) b
    L ≤ 2*T + U ∧ D ≤ 3*T + U := by
  dsimp only
  let Y : S → I → ℝ := fun ω i => clip (b i) (X ω i)
  let Z : S → I → ℝ := fun ω i => liftSet b (A ω) i
  let V : S → I → ℝ := fun ω i => X ω i
  have hclip : mean w (fun ω => dist₁ (Y ω) (V ω)) ≤ dist₁ a b := by
    unfold mean dist₁
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_le_sum fun i _ => clipping_bound w hw h₁ (fun ω => X ω i) (fun ω => hX ω i) (hm i)
  have hadjust : mean w (fun ω => dist₁ (Z ω) (Y ω)) ≤
      mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) + mean w (fun ω => dist₁ (Y ω) (V ω)) := by
    rw [← mean_add]
    apply mean_mono w hw
    intro ω
    change (∑ i, |(liftSet b (A ω) i : ℝ) - clip (b i) (X ω i)|) ≤ _
    rw [hadj ω]
    have hsum : |(∑ i, (X ω i : ℝ)) - ∑ i, (clip (b i) (X ω i) : ℝ)| ≤ dist₁ (Y ω) (V ω) := by
      change |(∑ i, V ω i) - ∑ i, Y ω i| ≤ dist₁ (Y ω) (V ω)
      rw [abs_sub_comm (∑ i, V ω i) (∑ i, Y ω i)]
      exact abs_total_le (Y ω) (V ω)
    calc
      _ ≤ |(N ω : ℝ) - ∑ i, (X ω i : ℝ)| + |(∑ i, (X ω i : ℝ)) - ∑ i, (clip (b i) (X ω i) : ℝ)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add le_rfl hsum
  have hL : mean w (fun ω => dist₁ (Z ω) (V ω)) ≤ 2 * dist₁ a b +
      mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) := by
    have htri := mean_mono w hw (fun ω => dist₁_triangle (Z ω) (Y ω) (V ω))
    rw [mean_add] at htri
    linarith
  refine ⟨hL, ?_⟩
  have htri := dist₁_triangle (fun i => mean w (fun ω => Z ω i)) a b
  have hmean := dist₁_mean w hw Z V
  have hmeans : (fun i => mean w (fun ω => V ω i)) = a := funext hm
  rw [hmeans] at hmean
  linarith
omit [DecidableEq I] in
lemma weighted_state {r : S → ℕ} (p : Outcome (I := I) r → ℝ) (f : S → ℝ) :
    (∑ x, p x * f (state x)) = ∑ ω, Mass p ω * f ω := by
  simp only [Mass, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [mul_assoc, ← mul_sum]
  simp

omit [Fintype I] [DecidableEq S] in
lemma liftSet_mean (w : S → ℝ) (h₁ : ∑ ω, w ω = 1) (b : I → ℝ)
    (A : S → Finset I) (i : I) :
    mean w (fun ω => (liftSet b (A ω) i : ℝ)) =
      (⌊b i⌋ : ℝ) + ∑ ω, w ω * (if i ∈ A ω then 1 else 0) := by
  unfold mean liftSet
  push_cast
  simp_rw [mul_add]
  rw [sum_add_distrib, ← sum_mul, h₁, one_mul]

omit [DecidableEq S] in
lemma marginal_support {r : S → ℕ} {p : Outcome (I := I) r → ℝ}
    (hp : ∀ x, 0 ≤ p x) (b : I → ℝ) (hm : ∀ i, Marginal p i = fraction (b i))
    {x : Outcome (I := I) r} (hx : 0 < p x) : subset x ⊆ fractionalSet b := by
  intro i hi
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  by_contra h
  have he : Marginal p i = 0 := (hm i).trans ((fraction_zero_iff _).mpr h)
  have hpos : p x ≤ Marginal p i := by
    calc
      p x = p x * (if i ∈ subset x then 1 else 0) := by simp [hi]
      _ ≤ _ := single_le_sum (f := fun y => p y * (if i ∈ subset y then 1 else 0))
        (fun y _ => mul_nonneg (hp y) (by split_ifs <;> norm_num)) (mem_univ x)
  linarith

/-- Full finite joint-law formulation of Section 09's star lemma. The first
coordinate retains the original state and hence all its correlations. A kernel
is obtained by finite disintegration below. Nonnegativity of a,b is needed only
to deduce nonnegative integer output, not for this stronger signed statement. -/
theorem rounding_star_joint (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (a b : I → ℝ) (X : S → I → ℤ) (N : S → ℤ)
    (hX : ∀ ω i, Balanced (a i) (X ω i))
    (hmX : ∀ i, mean w (fun ω => (X ω i : ℝ)) = a i)
    (hN : ∀ ω, Balanced (∑ i, b i) (N ω))
    (hmN : mean w (fun ω => (N ω : ℝ)) = ∑ i, b i) :
    ∃ (p : Outcome (I := I) (fun ω => residual b (N ω)) → ℝ)
      (X' : Outcome (I := I) (fun ω => residual b (N ω)) → I → ℤ),
      (∀ x, 0 ≤ p x) ∧ (∀ ω, Mass p ω = w ω) ∧
      (∀ x i, Balanced (b i) (X' x i)) ∧
      (∀ x, (∑ i, X' x i) = N (state x)) ∧
      (∀ i, (∑ x, p x * (X' x i : ℝ)) = b i) ∧
      (∑ x, p x * dist₁ (fun i => (X' x i : ℝ)) (fun i => (X (state x) i : ℝ))) ≤
        32 * dist₁ a b + 11 * mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) := by
  choose A hAH hAr hcost using fun ω => preliminary_state b (X ω) (hN ω)
  let r : S → ℕ := fun ω => residual b (N ω)
  have hr : ∀ ω ν, r ω ≤ r ν + 1 := fun ω ν => residual_adjacent b (hN ω) (hN ν)
  have hf (i : I) : 0 ≤ fraction (b i) ∧ fraction (b i) ≤ 1 :=
    ⟨(fraction_range _).1, (fraction_range _).2.le⟩
  obtain ⟨p, hp, hmass, hmar, hrepair⟩ := hamming_repair w hw h₁ r hr A hAr
    (fun i => fraction (b i)) hf (residual_mean w h₁ b N hN hmN)
  let A' : Outcome (I := I) r → Finset I :=
    fun x => if subset x ⊆ fractionalSet b then subset x else A (state x)
  have hA'H (x : Outcome (I := I) r) : A' x ⊆ fractionalSet b := by
    dsimp [A']; split_ifs with h
    · exact h
    · exact hAH _
  have hA'r (x : Outcome (I := I) r) : (A' x).card = r (state x) := by
    dsimp [A']; split_ifs
    · exact x.property
    · exact hAr _
  let X' : Outcome (I := I) r → I → ℤ := fun x => liftSet b (A' x)
  have hpos (x : Outcome (I := I) r) (hx : 0 < p x) : A' x = subset x :=
    ite_eq_left (marginal_support hp b hmar hx)
  have htotal : ∑ x, p x = 1 := by rw [← mass_total, show (fun ω => Mass p ω) = w from funext hmass]; exact h₁
  have hmean (i : I) : (∑ x, p x * (X' x i : ℝ)) = b i := by
    have he : (∑ x, p x * (X' x i : ℝ)) =
        mean p (fun x => (liftSet b (subset x) i : ℝ)) := by
      apply sum_congr rfl
      intro x _
      by_cases hx : 0 < p x
      · simp only [X', hpos x hx]
      · simp [le_antisymm (le_of_not_gt hx) (hp x)]
    rw [he, liftSet_mean p htotal b subset i]
    change (⌊b i⌋ : ℝ) + Marginal p i = b i
    rw [hmar]
    unfold fraction
    ring
  refine ⟨p, X', hp, hmass, fun x i => liftSet_balanced b (hA'H x) i, ?_, hmean, ?_⟩
  · intro x
    rw [show (∑ i, X' x i) = (∑ i, ⌊b i⌋) + (A' x).card from liftSet_sum b (A' x), hA'r]
    rw [show r (state x) = residual b (N (state x)) from rfl, residual_cast b (hN _)]
    ring
  · let L := mean w (fun ω => dist₁ (fun i => (liftSet b (A ω) i : ℝ)) (fun i => (X ω i : ℝ)))
    let D := dist₁ (fun i => mean w (fun ω => (liftSet b (A ω) i : ℝ))) b
    have hD : (∑ i, |(∑ ω, w ω * (if i ∈ A ω then 1 else 0)) - fraction (b i)|) = D := by
      apply sum_congr rfl
      intro i _
      dsimp only
      rw [liftSet_mean w h₁ b A i]
      unfold fraction
      congr 1
      ring
    rw [hD] at hrepair
    have hbound : (∑ x, p x * dist₁ (fun i => (X' x i : ℝ)) (fun i => (X (state x) i : ℝ))) ≤
        (∑ x, p x * HammingCost A x) + L := by
      calc
        _ ≤ ∑ x, p x * (HammingCost A x +
            dist₁ (fun i => (liftSet b (A (state x)) i : ℝ)) (fun i => (X (state x) i : ℝ))) := by
          apply sum_le_sum
          intro x _
          by_cases hx : 0 < p x
          · apply mul_le_mul_of_nonneg_left _ (hp x)
            have ht := dist₁_triangle (fun i => (X' x i : ℝ))
              (fun i => (liftSet b (A (state x)) i : ℝ)) (fun i => (X (state x) i : ℝ))
            simpa only [X', hpos x hx, dist₁, liftSet_distance, HammingCost] using ht
          · simp [le_antisymm (le_of_not_gt hx) (hp x)]
        _ = _ := by
          simp_rw [mul_add]
          rw [sum_add_distrib, weighted_state p (fun ω =>
            dist₁ (fun i => (liftSet b (A ω) i : ℝ)) (fun i => (X ω i : ℝ)))]
          simp only [hmass]
          rfl
    have hb := preliminary_bounds w hw h₁ a b X N hX hmX A hcost
    change L ≤ _ ∧ D ≤ _ at hb
    linarith
/-- Finite disintegration, including genuinely zero-probability input states. -/
def conditionalKernel (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (ω : S) (j : J) : ℝ :=
  if w ω = 0 then (if j = e ω then 1 else 0)
  else p j * (if st j = ω then 1 else 0) / w ω

omit [Fintype J] [Fintype S] in
lemma conditionalKernel_nonneg (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hw : ∀ ω, 0 ≤ w ω) (hp : ∀ j, 0 ≤ p j) (ω : S) (j : J) :
    0 ≤ conditionalKernel w p st e ω j := by
  unfold conditionalKernel
  split_ifs
  · norm_num
  · norm_num
  · exact div_nonneg (mul_nonneg (hp j) zero_le_one) (hw ω)
  · simp

omit [Fintype S] in
lemma conditionalKernel_sum (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hm : ∀ ω, (∑ j, p j * (if st j = ω then 1 else 0)) = w ω) (ω : S) :
    (∑ j, conditionalKernel w p st e ω j) = 1 := by
  by_cases hw : w ω = 0
  · simp [conditionalKernel, hw]
  · simp only [conditionalKernel, ite_eq_right hw, ← sum_div, hm ω, div_self hw]

omit [Fintype S] in
lemma conditionalKernel_identity (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hp : ∀ j, 0 ≤ p j)
    (hm : ∀ ω, (∑ j, p j * (if st j = ω then 1 else 0)) = w ω) (ω : S) (j : J) :
    w ω * conditionalKernel w p st e ω j = p j * (if st j = ω then 1 else 0) := by
  by_cases hw : w ω = 0
  · have hsmall : p j * (if st j = ω then 1 else 0) ≤ 0 := by
      calc
        _ ≤ ∑ j, p j * (if st j = ω then 1 else 0) :=
          single_le_sum (fun j _ => mul_nonneg (hp j) (by split_ifs <;> norm_num)) (mem_univ j)
        _ = 0 := (hm ω).trans hw
    have hz : p j * (if st j = ω then 1 else 0) = 0 :=
      le_antisymm hsmall (mul_nonneg (hp j) (by split_ifs <;> norm_num))
    simp [hw, hz]
  · simp only [conditionalKernel, ite_eq_right hw]
    field_simp

lemma conditionalKernel_average (w : S → ℝ) (p : J → ℝ) (st : J → S) (e : S → J)
    (hp : ∀ j, 0 ≤ p j)
    (hm : ∀ ω, (∑ j, p j * (if st j = ω then 1 else 0)) = w ω) (F : S → J → ℝ) :
    (∑ ω, w ω * ∑ j, conditionalKernel w p st e ω j * F ω j) =
      ∑ j, p j * F (st j) j := by
  simp_rw [mul_sum, ← mul_assoc, conditionalKernel_identity w p st e hp hm]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [mul_assoc, ← mul_sum]
  simp [eq_comm]

/-- The source's exact finite randomized kernel, with the constants 32 and 11,
all correlations preserved, and valid outputs even at null input states. -/
theorem rounding_star (w : S → ℝ) (hw : ∀ ω, 0 ≤ w ω) (h₁ : ∑ ω, w ω = 1)
    (a b : I → ℝ) (_ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (X : S → I → ℤ) (N : S → ℤ)
    (hX : ∀ ω i, Balanced (a i) (X ω i))
    (hmX : ∀ i, mean w (fun ω => (X ω i : ℝ)) = a i)
    (hN : ∀ ω, Balanced (∑ i, b i) (N ω))
    (hmN : mean w (fun ω => (N ω : ℝ)) = ∑ i, b i) :
    ∃ (κ : S → Outcome (I := I) (fun ω => residual b (N ω)) → ℝ)
      (X' : S → Outcome (I := I) (fun ω => residual b (N ω)) → I → ℤ),
      (∀ ω x, 0 ≤ κ ω x) ∧ (∀ ω, (∑ x, κ ω x) = 1) ∧
      (∀ ω x i, 0 ≤ X' ω x i ∧ Balanced (b i) (X' ω x i)) ∧
      (∀ ω x, (∑ i, X' ω x i) = N ω) ∧
      (∀ i, (∑ ω, w ω * ∑ x, κ ω x * (X' ω x i : ℝ)) = b i) ∧
      (∑ ω, w ω * ∑ x, κ ω x * dist₁ (fun i => (X' ω x i : ℝ)) (fun i => (X ω i : ℝ))) ≤
        32 * dist₁ a b + 11 * mean w (fun ω => |(N ω : ℝ) - ∑ i, (X ω i : ℝ)|) := by
  obtain ⟨p, Z, hp, hmass, hZ, htotal, hmean, hcost⟩ :=
    rounding_star_joint w hw h₁ a b X N hX hmX hN hmN
  choose A hAH hAr hAcost using fun ω => preliminary_state b (X ω) (hN ω)
  let r : S → ℕ := fun ω => residual b (N ω)
  let e : S → Outcome (I := I) r := fun ω => ⟨(ω, A ω), hAr ω⟩
  let κ := conditionalKernel w p state e
  let Z' : S → Outcome (I := I) r → I → ℤ :=
    fun ω x => if state x = ω then Z x else liftSet b (A ω)
  have hZ' (ω : S) (x : Outcome (I := I) r) (i : I) : Balanced (b i) (Z' ω x i) := by
    dsimp [Z']; split_ifs
    · exact hZ x i
    · exact liftSet_balanced b (hAH ω) i
  refine ⟨κ, Z', conditionalKernel_nonneg w p state e hw hp,
    conditionalKernel_sum w p state e hmass, ?_, ?_, ?_, ?_⟩
  · intro ω x i
    exact ⟨(Int.floor_nonneg.mpr (hb i)).trans (balanced_bounds (hZ' ω x i)).1, hZ' ω x i⟩
  · intro ω x
    dsimp [Z']
    split_ifs with hx
    · exact (htotal x).trans (congrArg N hx)
    · rw [liftSet_sum, hAr, residual_cast b (hN ω)]
      ring
  · intro i
    rw [conditionalKernel_average w p state e hp hmass]
    simp only [Z', ite_true]
    exact hmean i
  · rw [conditionalKernel_average w p state e hp hmass]
    simpa only [Z', ite_true] using hcost

end KServer.Rounding

/-! Continuation of Section09: finite top-down tree coupling.  The sampled
ancestors are retained as part of the joint state; no conditional means given
those ancestors are assumed. -/
namespace KServer.TreeRounding
open KServer.Rounding

structure Law (α : Type) where
  Ω : Type
  finite : Fintype Ω
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω=1
  point : Ω → α
attribute [instance] Law.finite

def Law.avg {α : Type} (L : Law α) (f : α → ℝ) : ℝ :=
  ∑ ω, L.weight ω*f (L.point ω)

lemma Law.avg_const {α : Type} (L : Law α) (c : ℝ) : L.avg (fun _ => c)=c := by
  simp [Law.avg, ← sum_mul, L.total]

lemma Law.avg_sum {α I : Type} [Fintype I] (L : Law α) (f : I → α → ℝ) :
    L.avg (fun x => ∑ i, f i x)=∑ i, L.avg (f i) := by
  simp only [Law.avg, mul_sum]; rw [sum_comm]

lemma Law.avg_mono {α : Type} (L : Law α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    L.avg f ≤ L.avg g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h _) (L.nonneg ω)

lemma Law.avg_nonneg {α : Type} (L : Law α) {f : α → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ L.avg f := sum_nonneg fun ω _ => mul_nonneg (L.nonneg ω) (h _)

lemma Law.avg_congr {α : Type} (L : Law α) {f g : α → ℝ}
    (h : ∀ ω, f (L.point ω)=g (L.point ω)) : L.avg f=L.avg g :=
  sum_congr rfl fun ω _ => congrArg (L.weight ω * ·) (h ω)

/-- A finite extension with a normalized kernel retains the entire old state. -/
def Law.extend {α β J : Type} [Fintype J] (L : Law α) (κ : L.Ω → J → ℝ)
    (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → β) : Law (α × β) where
  Ω := L.Ω × J
  finite := inferInstance
  weight p := L.weight p.1*κ p.1 p.2
  nonneg p := mul_nonneg (L.nonneg p.1) (hκ p.1 p.2)
  total := by simp [Fintype.sum_prod_type, ← mul_sum, hκ1, L.total]
  point p := (L.point p.1, z p.1 p.2)

lemma Law.extend_avg {α β J : Type} [Fintype J] (L : Law α) (κ : L.Ω → J → ℝ)
    (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → β) (f : α × β → ℝ) :
    (L.extend κ hκ hκ1 z).avg f =
      ∑ ω, L.weight ω*∑ j, κ ω j*f (L.point ω, z ω j) := by
  change (∑ p : L.Ω × J, (L.weight p.1*κ p.1 p.2)*f (L.point p.1,z p.1 p.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [mul_sum, mul_assoc]

def Law.map {α β : Type} (L : Law α) (f : α → β) : Law β :=
  { L with point := f ∘ L.point }

@[simp] lemma Law.map_avg {α β : Type} (L : Law α) (f : α → β) (g : β → ℝ) :
    (L.map f).avg g=L.avg (g ∘ f) := rfl

structure Tree (n : ℕ) [NeZero n] where
  parent : Fin n → Fin n
  root : parent 0=0
  lower : ∀ v : Fin n, v≠0 → (parent v).val<v.val

variable {n : ℕ} [NeZero n]

abbrev Tree.Child (T : Tree n) (v : Fin n) := {u : Fin n // u≠0 ∧ T.parent u=v}
instance instFintypeChild (T : Tree n) (v : Fin n) : Fintype (T.Child v) := by
  classical
  unfold Tree.Child
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance instDecidableEqChild (T : Tree n) (v : Fin n) : DecidableEq (T.Child v) := Classical.decEq _

def Tree.park (T : Tree n) (q : Fin n → ℝ) (v : Fin n) : ℝ :=
  q v-∑ u : T.Child v, q u.val

def Tree.star (T : Tree n) (q : Fin n → ℝ) (v : Fin n) : Option (T.Child v) → ℝ
  | none => T.park q v
  | some u => q u.val

lemma Tree.star_sum (T : Tree n) (q : Fin n → ℝ) (v : Fin n) :
    ∑ i, T.star q v i=q v := by
  simp [Fintype.sum_option, Tree.star, Tree.park]

structure Counts (n : ℕ) where
  subtree : Fin n → ℤ
  park : Fin n → ℤ

structure PairState (n : ℕ) where
  old : Counts n
  new : Counts n

def Tree.intStar (T : Tree n) (c : Counts n) (v : Fin n) : Option (T.Child v) → ℤ
  | none => c.park v
  | some u => c.subtree u.val

def Tree.Consistent (T : Tree n) (c : Counts n) : Prop :=
  ∀ v, c.park v+∑ u : T.Child v, c.subtree u.val=c.subtree v

lemma Tree.intStar_sum (T : Tree n) {c : Counts n} (hc : T.Consistent c) (v : Fin n) :
    ∑ i, T.intStar c v i=c.subtree v := by
  simpa [Fintype.sum_option, Tree.intStar] using hc v

def Tree.Valid (T : Tree n) (q : Fin n → ℝ) (c : Counts n) : Prop :=
  (∀ v, 0 ≤ c.subtree v ∧ Balanced (q v) (c.subtree v)) ∧
  (∀ v, 0 ≤ c.park v ∧ Balanced (T.park q v) (c.park v)) ∧ T.Consistent c

def Tree.Means (T : Tree n) (q : Fin n → ℝ) (L : Law (Counts n)) : Prop :=
  (∀ v, L.avg (fun c => (c.subtree v:ℝ))=q v) ∧
  (∀ v, L.avg (fun c => (c.park v:ℝ))=T.park q v)

/-- Set just the new children and the new park of one star. -/
def Tree.setStar (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : Counts n where
  subtree u := if h : u≠0 ∧ T.parent u=v then z (some ⟨u,h⟩) else c.subtree u
  park u := if u=v then z none else c.park u

lemma Tree.setStar_old (T : Tree n) (c : Counts n) (v u : Fin n)
    (z : Option (T.Child v) → ℤ) (h : ¬(u≠0 ∧ T.parent u=v)) :
    (T.setStar c v z).subtree u=c.subtree u := by simp [Tree.setStar, h]

lemma Tree.setStar_child (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) (u : T.Child v) :
    (T.setStar c v z).subtree u.val=z (some u) := by
  simp only [Tree.setStar, dite_eq_left u.property]

lemma Tree.setStar_root (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : (T.setStar c v z).subtree 0=c.subtree 0 := by
  simp [Tree.setStar]

lemma Tree.setStar_self (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : (T.setStar c v z).subtree v=c.subtree v := by
  apply T.setStar_old
  rintro ⟨hv,hp⟩
  have h := T.lower v hv
  rw [hp] at h
  exact (lt_irrefl _) h

lemma Tree.setStar_intStar (T : Tree n) (c : Counts n) (v : Fin n)
    (z : Option (T.Child v) → ℤ) : T.intStar (T.setStar c v z) v=z := by
  funext i
  cases i with
  | none => simp [Tree.intStar, Tree.setStar]
  | some u => exact T.setStar_child c v z u


lemma Tree.setStar_other (T : Tree n) (c : Counts n) (v w : Fin n)
    (z : Option (T.Child v) → ℤ) (hw : w≠v) :
    T.intStar (T.setStar c v z) w=T.intStar c w := by
  funext i
  cases i with
  | none => simp [Tree.intStar, Tree.setStar, hw]
  | some u =>
    apply T.setStar_old
    rintro ⟨_,hp⟩
    exact hw (u.property.2.symm.trans hp)

lemma Tree.setStar_before (T : Tree n) (c : Counts n) (v w : Fin n)
    (z : Option (T.Child v) → ℤ) (hw : w.val ≤ v.val) :
    (T.setStar c v z).subtree w=c.subtree w := by
  apply T.setStar_old
  rintro ⟨h0,hp⟩
  have h := T.lower w h0
  rw [hp] at h
  omega

def Tree.Assigned (T : Tree n) (m : ℕ) (v : Fin n) : Prop :=
  v=0 ∨ (T.parent v).val < m

lemma Tree.assigned_self (T : Tree n) (v : Fin n) : T.Assigned v.val v := by
  by_cases h : v=0
  · exact Or.inl h
  · exact Or.inr (T.lower v h)

lemma Tree.assigned_next (T : Tree n) (v u : Fin n) (h : T.Assigned (v.val+1) u) :
    T.Assigned v.val u ∨ (u≠0 ∧ T.parent u=v) := by
  by_cases h0 : u=0
  · exact Or.inl (Or.inl h0)
  rcases h with h | h
  · exact (h0 h).elim
  by_cases hp : (T.parent u).val<v.val
  · exact Or.inl (Or.inr hp)
  · right
    exact ⟨h0, Fin.ext (by omega)⟩

lemma Tree.assigned_not_child (T : Tree n) (v u : Fin n) (h : T.Assigned v.val u) :
    ¬(u≠0 ∧ T.parent u=v) := by
  rintro ⟨h0,hp⟩
  rcases h with h | h
  · exact h0 h
  · rw [hp] at h; exact lt_irrefl _ h

/-- The induction stores the original joint law and every already rounded
ancestor, so all conditional correlations are retained. -/
structure Stage (T : Tree n) (a b : Fin n → ℝ) (k : ℤ)
    (L₀ : Law (Counts n)) (m : ℕ) where
  law : Law (PairState n)
  oldLaw : ∀ f : Counts n → ℝ, law.avg (fun s => f s.old)=L₀.avg f
  oldValid : ∀ ω, T.Valid a (law.point ω).old
  root : ∀ ω, (law.point ω).new.subtree 0=k
  balanced : ∀ u, T.Assigned m u → ∀ ω,
    0 ≤ (law.point ω).new.subtree u ∧ Balanced (b u) ((law.point ω).new.subtree u)
  means : ∀ u, T.Assigned m u → law.avg (fun s => (s.new.subtree u:ℝ))=b u
  parkBalanced : ∀ u, u.val < m → ∀ ω,
    0 ≤ (law.point ω).new.park u ∧ Balanced (T.park b u) ((law.point ω).new.park u)
  parkMeans : ∀ u, u.val < m → law.avg (fun s => (s.new.park u:ℝ))=T.park b u
  consistent : ∀ u, u.val < m → ∀ ω,
    (law.point ω).new.park u+∑ c : T.Child u, (law.point ω).new.subtree c.val=
      (law.point ω).new.subtree u
  cost : ∀ u, u.val < m →
    law.avg (fun s => dist₁ (fun i => (T.intStar s.new u i:ℝ))
                              (fun i => (T.intStar s.old u i:ℝ))) ≤
      32*dist₁ (T.star a u) (T.star b u)+
        11*law.avg (fun s => |(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|)

/-- The saved old law's means are valid at every intermediate refinement. -/
lemma Stage.oldMean {T : Tree n} {a b : Fin n → ℝ} {k : ℤ} {L₀ : Law (Counts n)}
    {m : ℕ} (S : Stage T a b k L₀ m) (hmean : T.Means a L₀) (v : Fin n)
    (i : Option (T.Child v)) :
    mean S.law.weight (fun ω => (T.intStar (S.law.point ω).old v i:ℝ))=T.star a v i := by
  change S.law.avg (fun s => (T.intStar s.old v i:ℝ)) = _
  rw [S.oldLaw (fun c => (T.intStar c v i:ℝ))]
  cases i with
  | none => exact hmean.2 v
  | some u => exact hmean.1 u.val

/-- A finite kernel is extended and its output written into one star. -/
def stepLaw {T : Tree n} (L : Law (PairState n)) (v : Fin n) {J : Type} [Fintype J]
    (κ : L.Ω → J → ℝ) (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → Option (T.Child v) → ℤ) : Law (PairState n) :=
  (L.extend κ hκ hκ1 z).map fun p => ⟨p.1.old,T.setStar p.1.new v p.2⟩

lemma stepLaw_avg {T : Tree n} (L : Law (PairState n)) (v : Fin n) {J : Type} [Fintype J]
    (κ : L.Ω → J → ℝ) (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → Option (T.Child v) → ℤ) (f : PairState n → ℝ) :
    (stepLaw L v κ hκ hκ1 z).avg f=
      ∑ ω, L.weight ω*∑ j, κ ω j*f ⟨(L.point ω).old,T.setStar (L.point ω).new v (z ω j)⟩ := by
  unfold stepLaw
  rw [Law.map_avg, Law.extend_avg]
  rfl

lemma stepLaw_preserve {T : Tree n} (L : Law (PairState n)) (v : Fin n) {J : Type} [Fintype J]
    (κ : L.Ω → J → ℝ) (hκ : ∀ ω j, 0 ≤ κ ω j) (hκ1 : ∀ ω, ∑ j, κ ω j=1)
    (z : L.Ω → J → Option (T.Child v) → ℤ) (f : PairState n → ℝ)
    (hf : ∀ s Z, f ⟨s.old,T.setStar s.new v Z⟩=f s) :
    (stepLaw L v κ hκ hκ1 z).avg f=L.avg f := by
  rw [stepLaw_avg]
  simp only [hf, ← sum_mul, hκ1, one_mul]
  rfl


/-- One complete top-down update. The only existence input is the proved
finite star kernel, not a policy or a tree-rounding interface. -/
theorem Stage.next {T : Tree n} {a b : Fin n → ℝ} {k : ℤ} {L₀ : Law (Counts n)}
    (ha : ∀ v, 0 ≤ a v) (hpa : ∀ v, 0 ≤ T.park a v)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v)
    (hmean : T.Means a L₀) (v : Fin n) (S : Stage T a b k L₀ v.val) :
    Nonempty (Stage T a b k L₀ (v.val+1)) := by
  classical
  let L := S.law
  let old : L.Ω → Option (T.Child v) → ℤ := fun ω => T.intStar (L.point ω).old v
  let N : L.Ω → ℤ := fun ω => (L.point ω).new.subtree v
  have hsa : ∀ i, 0 ≤ T.star a v i := by
    intro i; cases i with
    | none => exact hpa v
    | some u => exact ha u.val
  have hsb : ∀ i, 0 ≤ T.star b v i := by
    intro i; cases i with
    | none => exact hpb v
    | some u => exact hb u.val
  have hX : ∀ ω i, Balanced (T.star a v i) (old ω i) := by
    intro ω i; cases i with
    | none => exact (S.oldValid ω).2.1 v |>.2
    | some u => exact (S.oldValid ω).1 u.val |>.2
  have hmX : ∀ i, mean L.weight (fun ω => (old ω i:ℝ))=T.star a v i := S.oldMean hmean v
  have hN : ∀ ω, Balanced (∑ i, T.star b v i) (N ω) := by
    rw [T.star_sum]
    exact fun ω => (S.balanced v (T.assigned_self v) ω).2
  have hmN : mean L.weight (fun ω => (N ω:ℝ))=∑ i, T.star b v i := by
    rw [T.star_sum]
    exact S.means v (T.assigned_self v)
  obtain ⟨κ,z,hκ,hκ1,hz,hztot,hzmean,hcost⟩ :=
    rounding_star L.weight L.nonneg L.total (T.star a v) (T.star b v)
      hsa hsb old N hX hmX hN hmN
  let R := stepLaw L v κ hκ hκ1 z
  have hpres (f : PairState n → ℝ)
      (hf : ∀ s Z, f ⟨s.old,T.setStar s.new v Z⟩=f s) : R.avg f=L.avg f :=
    stepLaw_preserve L v κ hκ hκ1 z f hf
  have hcount (u : Fin n) (hu : ¬(u≠0 ∧ T.parent u=v)) :
      R.avg (fun s => (s.new.subtree u:ℝ))=L.avg (fun s => (s.new.subtree u:ℝ)) := by
    apply hpres
    intro s Z
    rw [T.setStar_old _ _ _ _ hu]
  have hchild (u : T.Child v) : R.avg (fun s => (s.new.subtree u.val:ℝ))=b u.val := by
    rw [stepLaw_avg]
    simpa only [Tree.setStar_child, Tree.star] using hzmean (some u)
  have hpark : R.avg (fun s => (s.new.park v:ℝ))=T.park b v := by
    rw [stepLaw_avg]
    simpa only [Tree.setStar, ite_true, Tree.star] using hzmean none
  refine ⟨{
    law := R
    oldLaw := ?_
    oldValid := ?_
    root := ?_
    balanced := ?_
    means := ?_
    parkBalanced := ?_
    parkMeans := ?_
    consistent := ?_
    cost := ?_ }⟩
  · intro f
    exact (hpres _ (fun _ _ => rfl)).trans (S.oldLaw f)
  · intro ω
    exact S.oldValid ω.1
  · intro ω
    change (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree 0=k
    rw [T.setStar_root]
    exact S.root ω.1
  · intro u hu ω
    rcases T.assigned_next v u hu with hu | hu
    · change 0 ≤ (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u ∧
        Balanced (b u) ((T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u)
      rw [T.setStar_old _ _ _ _ (T.assigned_not_child v u hu)]
      exact S.balanced u hu ω.1
    · change 0 ≤ (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u ∧
        Balanced (b u) ((T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u)
      have he := T.setStar_child (L.point ω.1).new v (z ω.1 ω.2) ⟨u,hu⟩
      change (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u=z ω.1 ω.2 (some ⟨u,hu⟩) at he
      rw [he]
      exact hz ω.1 ω.2 (some ⟨u,hu⟩)
  · intro u hu
    rcases T.assigned_next v u hu with hu | hu
    · exact (hcount u (T.assigned_not_child v u hu)).trans (S.means u hu)
    · exact hchild ⟨u,hu⟩
  · intro u hu ω
    change 0 ≤ (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).park u ∧
      Balanced (T.park b u) ((T.setStar (L.point ω.1).new v (z ω.1 ω.2)).park u)
    by_cases huv : u=v
    · subst u
      simpa only [Tree.setStar, ite_true, Tree.star] using hz ω.1 ω.2 none
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      simpa only [Tree.setStar, ite_eq_right huv] using S.parkBalanced u hul ω.1
  · intro u hu
    by_cases huv : u=v
    · subst u; exact hpark
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      have he : R.avg (fun s => (s.new.park u:ℝ))=L.avg (fun s => (s.new.park u:ℝ)) := by
        apply hpres
        intro s Z
        simp only [Tree.setStar, ite_eq_right huv]
      exact he.trans (S.parkMeans u hul)
  · intro u hu ω
    change (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).park u+
      ∑ c : T.Child u, (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree c.val=
      (T.setStar (L.point ω.1).new v (z ω.1 ω.2)).subtree u
    by_cases huv : u=v
    · subst u
      rw [T.setStar_self]
      have he := hztot ω.1 ω.2
      rw [Fintype.sum_option] at he
      simp only [Tree.setStar_child]
      simpa only [Tree.setStar, ite_true] using he
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      rw [T.setStar_before _ _ _ _ hul.le]
      have he := congrArg (fun f => ∑ i, f i) (T.setStar_other (L.point ω.1).new v u (z ω.1 ω.2) huv)
      simp only [Fintype.sum_option, Tree.intStar] at he
      rw [he]
      exact S.consistent u hul ω.1
  · intro u hu
    by_cases huv : u=v
    · subst u
      have hleft : R.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
            (fun i => (T.intStar s.old v i:ℝ)))=
          ∑ ω, L.weight ω*∑ j, κ ω j*dist₁ (fun i => (z ω j i:ℝ)) (fun i => (old ω i:ℝ)) := by
        rw [stepLaw_avg]
        simp only [Tree.setStar_intStar]
        rfl
      rw [hleft]
      have hright : R.avg (fun s => |(s.new.subtree v:ℝ)-(s.old.subtree v:ℝ)|)=
          mean L.weight (fun ω => |(N ω:ℝ)-∑ i, (old ω i:ℝ)|) := by
        rw [hpres _ (by intro s Z; rw [T.setStar_self])]
        unfold Law.avg mean
        apply sum_congr rfl
        intro ω _
        congr 1
        change |((L.point ω).new.subtree v:ℝ)-((L.point ω).old.subtree v:ℝ)| =
          |((L.point ω).new.subtree v:ℝ)-∑ i, (T.intStar (L.point ω).old v i:ℝ)|
        rw [← Int.cast_sum, T.intStar_sum (S.oldValid ω).2.2]
      rw [hright]
      exact hcost
    · have hul : u.val<v.val := by have hne := Fin.val_ne_of_ne huv; omega
      rw [hpres _ (by intro s Z; rw [T.setStar_other _ _ _ _ huv])]
      rw [hpres _ (by intro s Z; rw [T.setStar_before _ _ _ _ hul.le])]
      exact S.cost u hul


def initialCounts (k : ℤ) : Counts n where
  subtree v := if v=0 then k else 0
  park _ := 0

lemma stage_zero {T : Tree n} {a b : Fin n → ℝ} {k : ℤ} (hk : 0 ≤ k) (hb0 : b 0=(k:ℝ))
    (L₀ : Law (Counts n)) (hvalid : ∀ ω, T.Valid a (L₀.point ω)) :
    Nonempty (Stage T a b k L₀ 0) := by
  classical
  let L := L₀.map fun c => (⟨c,initialCounts k⟩ : PairState n)
  have hroot : ∀ ω, (L.point ω).new.subtree 0=k := by
    intro ω
    change (if (0 : Fin n)=0 then k else 0)=k
    simp
  refine ⟨{
    law := L
    oldLaw := fun _ => rfl
    oldValid := hvalid
    root := hroot
    balanced := ?_
    means := ?_
    parkBalanced := by intro u hu; omega
    parkMeans := by intro u hu; omega
    consistent := by intro u hu; omega
    cost := by intro u hu; omega }⟩
  · intro u hu ω
    have hu0 : u=0 := hu.resolve_right (by omega)
    subst u
    rw [hroot ω, hb0]
    exact ⟨hk, Or.inl (by simp)⟩
  · intro u hu
    have hu0 : u=0 := hu.resolve_right (by omega)
    subst u
    rw [hb0]
    calc _ = L.avg (fun _ => (k:ℝ)) := L.avg_congr fun ω => by rw [hroot ω]
         _ = _ := L.avg_const _

/-- All vertices are processed in increasing order; the parent order is the
only tree-shape assumption used by the constructive correlated coupling. -/
theorem tree_coupling {T : Tree n} {a b : Fin n → ℝ} {k : ℤ}
    (ha : ∀ v, 0 ≤ a v) (hpa : ∀ v, 0 ≤ T.park a v)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v)
    (hk : 0 ≤ k) (hb0 : b 0=(k:ℝ)) (L₀ : Law (Counts n))
    (hvalid : ∀ ω, T.Valid a (L₀.point ω)) (hmean : T.Means a L₀) :
    ∃ L : Law (PairState n),
      (∀ f : Counts n → ℝ, L.avg (fun s => f s.old)=L₀.avg f) ∧
      (∀ ω, T.Valid a (L.point ω).old ∧ T.Valid b (L.point ω).new ∧ (L.point ω).new.subtree 0=k) ∧
      (∀ v, L.avg (fun s => (s.new.subtree v:ℝ))=b v) ∧
      (∀ v, L.avg (fun s => (s.new.park v:ℝ))=T.park b v) ∧
      (∀ v, L.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
                                  (fun i => (T.intStar s.old v i:ℝ))) ≤
        32*dist₁ (T.star a v) (T.star b v)+
          11*L.avg (fun s => |(s.new.subtree v:ℝ)-(s.old.subtree v:ℝ)|)) := by
  have hstage : ∀ m, m ≤ n → Nonempty (Stage T a b k L₀ m) := by
    intro m
    induction m with
    | zero => intro _; exact stage_zero hk hb0 L₀ hvalid
    | succ m ih =>
      intro hm
      obtain ⟨S⟩ := ih (by omega)
      exact S.next ha hpa hb hpb hmean ⟨m,by omega⟩
  obtain ⟨S⟩ := hstage n le_rfl
  have hassigned (v : Fin n) : T.Assigned n v := Or.inr (T.parent v).isLt
  refine ⟨S.law,S.oldLaw,?_,?_,?_,?_⟩
  · intro ω
    exact ⟨S.oldValid ω, ⟨fun v => S.balanced v (hassigned v) ω,
      fun v => S.parkBalanced v v.isLt ω, fun v => S.consistent v v.isLt ω⟩,S.root ω⟩
  · intro v; exact S.means v (hassigned v)
  · intro v; exact S.parkMeans v v.isLt
  · intro v; exact S.cost v v.isLt


lemma Law.avg_mul {α : Type} (L : Law α) (c : ℝ) (f : α → ℝ) :
    L.avg (fun x => c*f x)=c*L.avg f := by
  simp only [Law.avg, mul_sum, mul_left_comm (L.weight _) c]

/-- Every nonroot vertex occurs in exactly one child list. -/
def Tree.childEquiv (T : Tree n) : (Σ v : Fin n, T.Child v) ≃ {v : Fin n // v≠0} where
  toFun p := ⟨p.2.val,p.2.property.1⟩
  invFun u := ⟨T.parent u.val,⟨u.val,u.property,rfl⟩⟩
  left_inv := by
    rintro ⟨v,u,hu,hp⟩
    dsimp
    subst v
    rfl
  right_inv := by intro u; rfl

lemma Tree.weighted_children (T : Tree n) (w f : Fin n → ℝ) (h0 : f 0=0) :
    (∑ v, w v*∑ u : T.Child v, f u.val)=∑ u, w (T.parent u)*f u := by
  classical
  simp_rw [mul_sum]
  rw [← Fintype.sum_sigma (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)]
  have he := Fintype.sum_equiv (T.childEquiv)
    (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)
    (fun u : {v : Fin n // v≠0} => w (T.parent u.val)*f u.val)
    (by intro p; change w p.1*f p.2.val=w (T.parent p.2.val)*f p.2.val
        rw [p.2.property.2])
  rw [he]
  have hsub := Fintype.sum_subtype_add_sum_subtype (fun v : Fin n => v≠0)
    (fun u => w (T.parent u)*f u)
  have hz : (∑ u : {v : Fin n // ¬v≠0}, w (T.parent u.val)*f u.val)=0 := by
    apply sum_eq_zero
    intro u _
    have hu : u.val=0 := not_ne_iff.mp u.property
    simp [hu,h0]
  simpa only [hz, add_zero] using hsub

lemma Tree.star_distance (T : Tree n) (a b : Fin n → ℝ) (v : Fin n) :
    dist₁ (T.star a v) (T.star b v) ≤
      |a v-b v|+2*∑ u : T.Child v, |a u.val-b u.val| := by
  have hp : |T.park a v-T.park b v| ≤
      |a v-b v|+∑ u : T.Child v, |a u.val-b u.val| := by
    calc _ = |(a v-b v)-∑ u : T.Child v, (a u.val-b u.val)| := by
          unfold Tree.park
          rw [sum_sub_distrib]
          congr 1; ring
         _ ≤ |a v-b v|+|∑ u : T.Child v, (a u.val-b u.val)| := abs_sub _ _
         _ ≤ _ := add_le_add_right (abs_sum_le_sum_abs (fun u : T.Child v => a u.val-b u.val) Finset.univ) _
  simpa only [dist₁, Fintype.sum_option, Tree.star] using
    (show |T.park a v-T.park b v|+(∑ u : T.Child v, |a u.val-b u.val|) ≤
      |a v-b v|+2*∑ u : T.Child v, |a u.val-b u.val| by linarith)

lemma Tree.children_distance_le (T : Tree n) (c d : Counts n) (v : Fin n) :
    (∑ u : T.Child v, |(c.subtree u.val:ℝ)-(d.subtree u.val:ℝ)|) ≤
      dist₁ (fun i => (T.intStar c v i:ℝ)) (fun i => (T.intStar d v i:ℝ)) := by
  simp only [dist₁, Fintype.sum_option, Tree.intStar]
  linarith [abs_nonneg ((c.park v:ℝ)-(d.park v:ℝ))]

/-- The radius at a nonroot node is one tau-th of its parent radius. -/
lemma Tree.parent_weight (T : Tree n) {τ : ℝ} (hτ : 0 < τ) (w f : Fin n → ℝ)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) (h0 : f 0=0) :
    (∑ u, w u*f u)=(1/τ)*(∑ u, w (T.parent u)*f u) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  by_cases hu : u=0
  · simp [hu,h0]
  · rw [hscale u hu]
    field_simp

lemma Tree.star_weight_bound (T : Tree n) {τ : ℝ} (hτ : 0 < τ)
    (w a b : Fin n → ℝ) (hw : ∀ u, 0 ≤ w u)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) (h0 : a 0=b 0) :
    (∑ v, w v*dist₁ (T.star a v) (T.star b v)) ≤
      (2+1/τ)*(∑ u, w (T.parent u)*|a u-b u|) := by
  calc _ ≤ ∑ v, w v*(|a v-b v|+2*∑ u : T.Child v, |a u.val-b u.val|) :=
        sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (T.star_distance a b v) (hw v)
       _ = (∑ v, w v*|a v-b v|)+2*(∑ v, w v*∑ u : T.Child v, |a u.val-b u.val|) := by
        simp only [mul_add,mul_left_comm (w _) (2:ℝ),sum_add_distrib,mul_sum]
       _ = _ := by
        rw [T.weighted_children w (fun u => |a u-b u|) (by simp [h0]), T.parent_weight hτ w _ hscale (by simp [h0])]
        ring

/-- Finite, exact absorption of the local 32/11 bounds. No tree depth or
initialization cost enters the coefficient. -/
theorem Tree.rounding_absorption (T : Tree n) {τ : ℝ} (hτ : 22 ≤ τ)
    (w a b : Fin n → ℝ) (hw : ∀ u, 0 ≤ w u)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) (h0 : a 0=b 0)
    (L : Law (PairState n)) (hroot : ∀ ω, (L.point ω).new.subtree 0=(L.point ω).old.subtree 0)
    (hcost : ∀ v, L.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
                                  (fun i => (T.intStar s.old v i:ℝ))) ≤
      32*dist₁ (T.star a v) (T.star b v)+
        11*L.avg (fun s => |(s.new.subtree v:ℝ)-(s.old.subtree v:ℝ)|)) :
    L.avg (fun s => ∑ u, w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|) ≤
      132*(∑ u, w (T.parent u)*|a u-b u|) := by
  have ht : 0 < τ := by linarith
  let F : Fin n → PairState n → ℝ := fun u s => |(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|
  let V := ∑ u, w (T.parent u)*|a u-b u|
  let N := L.avg (fun s => ∑ u, w (T.parent u)*F u s)
  have hV : 0 ≤ V := sum_nonneg fun u _ => mul_nonneg (hw _) (abs_nonneg _)
  have hN : 0 ≤ N := L.avg_nonneg fun s => sum_nonneg fun u _ => mul_nonneg (hw _) (abs_nonneg _)
  have hF0 : ∀ ω, F 0 (L.point ω)=0 := by intro ω; simp [F,hroot ω]
  have havg0 : L.avg (F 0)=0 := by
    calc _ = L.avg (fun _ => 0) := L.avg_congr hF0
         _ = 0 := L.avg_const _
  have hNavg : N=∑ u, w (T.parent u)*L.avg (F u) := by
    dsimp [N]
    rw [L.avg_sum]
    simp_rw [L.avg_mul]
  have hparent : (∑ v, w v*L.avg (F v))=(1/τ)*N := by
    rw [T.parent_weight ht w _ hscale havg0, hNavg]
  have hchildren : (∑ v, w v*L.avg (fun s => ∑ u : T.Child v, F u.val s))=N := by
    simp_rw [L.avg_sum]
    rw [T.weighted_children w (fun u => L.avg (F u)) havg0, hNavg]
  have hrec : N ≤ (64+32/τ)*V+(11/τ)*N := by
    calc N = ∑ v, w v*L.avg (fun s => ∑ u : T.Child v, F u.val s) := hchildren.symm
         _ ≤ ∑ v, w v*L.avg (fun s => dist₁ (fun i => (T.intStar s.new v i:ℝ))
              (fun i => (T.intStar s.old v i:ℝ))) := by
          apply sum_le_sum
          intro v _
          exact mul_le_mul_of_nonneg_left (L.avg_mono (fun s => T.children_distance_le s.new s.old v)) (hw v)
         _ ≤ ∑ v, w v*(32*dist₁ (T.star a v) (T.star b v)+11*L.avg (F v)) :=
          sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hcost v) (hw v)
         _ = 32*(∑ v, w v*dist₁ (T.star a v) (T.star b v))+11*(∑ v, w v*L.avg (F v)) := by
          simp only [mul_add,mul_left_comm (w _) (32:ℝ),mul_left_comm (w _) (11:ℝ),sum_add_distrib,mul_sum]
         _ ≤ 32*((2+1/τ)*V)+11*((1/τ)*N) := by
          rw [hparent]
          exact add_le_add_left (mul_le_mul_of_nonneg_left (T.star_weight_bound ht w a b hw hscale h0) (by norm_num : (0:ℝ) ≤32)) _
         _ = _ := by ring
  have h11 : 11/τ ≤ 1/2 := (div_le_iff₀ ht).mpr (by linarith)
  have h32 : 32/τ ≤ 2 := (div_le_iff₀ ht).mpr (by linarith)
  have hrec' : N ≤ 66*V+(1/2)*N := hrec.trans (add_le_add
    (mul_le_mul_of_nonneg_right (by linarith : 64+32/τ ≤66) hV)
    (mul_le_mul_of_nonneg_right h11 hN))
  change N ≤ 132*V
  linarith


def Law.pure {α : Type} (x : α) : Law α where
  Ω := Unit
  finite := inferInstance
  weight _ := 1
  nonneg _ := by norm_num
  total := by simp
  point _ := x

@[simp] lemma Law.avg_pure {α : Type} (x : α) (f : α → ℝ) : (Law.pure x).avg f=f x := by
  change (∑ ω : Unit, (1:ℝ)*f x)=f x
  simp

lemma balanced_integer {r : ℝ} {j k : ℤ} (hr : r=(k:ℝ)) (hj : Balanced r j) : j=k := by
  simpa [hr,KServer.Rounding.Balanced] using hj

/-- Deterministic park of all k units at the root, solely for initialization. -/
def stock (k : ℤ) : Counts n where
  subtree v := if v=0 then k else 0
  park v := if v=0 then k else 0

def stockMass (k : ℤ) (v : Fin n) : ℝ := if v=0 then (k:ℝ) else 0

lemma stockMass_park (T : Tree n) (k : ℤ) (v : Fin n) :
    T.park (stockMass k) v=stockMass k v := by
  have hs : (∑ u : T.Child v, stockMass k u.val)=0 :=
    sum_eq_zero fun u _ => by simp [stockMass,u.property.1]
  simp [Tree.park,hs]

lemma stock_valid (T : Tree n) {k : ℤ} (hk : 0 ≤ k) : T.Valid (stockMass k) (stock k) := by
  have hb (v : Fin n) : 0 ≤ (stock k : Counts n).subtree v ∧
      KServer.Rounding.Balanced (stockMass k v) ((stock k : Counts n).subtree v) := by
    by_cases hv : v=0
    · simp [stock,stockMass,hv,KServer.Rounding.Balanced,hk]
    · simp [stock,stockMass,hv,KServer.Rounding.Balanced]
  refine ⟨hb,?_,?_⟩
  · intro v
    rw [stockMass_park]
    exact hb v
  · intro v
    have hs : (∑ u : T.Child v, (stock k : Counts n).subtree u.val)=0 :=
      sum_eq_zero fun u _ => by simp [stock,u.property.1]
    change (stock k : Counts n).subtree v+_=(stock k).subtree v
    rw [hs,add_zero]

lemma stock_means (T : Tree n) (k : ℤ) : T.Means (stockMass k) (Law.pure (stock k)) := by
  constructor <;> intro v <;> simp [Law.avg_pure,stock,stockMass,stockMass_park]

/-- Actual balanced law at the initial fractional configuration. This is not
an assumed rounding interface: it is obtained by the finite star construction. -/
theorem tree_initialization (T : Tree n) (b : Fin n → ℝ) {k : ℤ} (hk : 0 ≤ k)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v) (hb0 : b 0=(k:ℝ)) :
    ∃ L : Law (Counts n), (∀ ω, T.Valid b (L.point ω) ∧ (L.point ω).subtree 0=k) ∧
      T.Means b L := by
  have ha (v : Fin n) : 0 ≤ stockMass k v := by
    dsimp [stockMass]; split_ifs <;> positivity
  obtain ⟨R,hRold,hRv,hRs,hRp,hRc⟩ := tree_coupling ha
    (fun v => by rw [stockMass_park]; exact ha v) hb hpb hk hb0
      (Law.pure (stock k)) (fun _ => stock_valid T hk) (stock_means T k)
  refine ⟨R.map PairState.new,?_,?_,?_⟩
  · intro ω; exact (hRv ω).2
  · intro v; exact hRs v
  · intro v; exact hRp v

/-- Section09's one-step top-down rounding, including the uniform constant132.
The old marginal is kept exactly, and the new root and all parks are balanced. -/
theorem rounded_step (T : Tree n) {τ : ℝ} (hτ : 22 ≤ τ)
    (w a b : Fin n → ℝ) (hw : ∀ u, 0 ≤ w u)
    (hscale : ∀ u, u≠0 → w (T.parent u)=τ*w u) {k : ℤ} (hk : 0 ≤ k)
    (ha0 : a 0=(k:ℝ)) (hb0 : b 0=(k:ℝ))
    (ha : ∀ v, 0 ≤ a v) (hpa : ∀ v, 0 ≤ T.park a v)
    (hb : ∀ v, 0 ≤ b v) (hpb : ∀ v, 0 ≤ T.park b v)
    (L₀ : Law (Counts n)) (hvalid : ∀ ω, T.Valid a (L₀.point ω)) (hmean : T.Means a L₀) :
    ∃ L : Law (PairState n),
      (∀ f : Counts n → ℝ, L.avg (fun s => f s.old)=L₀.avg f) ∧
      (∀ ω, T.Valid a (L.point ω).old ∧ T.Valid b (L.point ω).new ∧ (L.point ω).new.subtree 0=k) ∧
      T.Means b (L.map PairState.new) ∧
      L.avg (fun s => ∑ u, w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|) ≤
        132*(∑ u, w (T.parent u)*|a u-b u|) := by
  obtain ⟨L,hLold,hLv,hLs,hLp,hLc⟩ := tree_coupling ha hpa hb hpb hk hb0 L₀ hvalid hmean
  refine ⟨L,hLold,hLv,⟨hLs,hLp⟩,?_⟩
  apply T.rounding_absorption hτ w a b hw hscale (ha0.trans hb0.symm) L _ hLc
  intro ω
  rw [(hLv ω).2.2, balanced_integer ha0 ((hLv ω).1.1 0).2]

end KServer.TreeRounding

end

/- Finite-tree park conservation and geometric subcapacity. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding

structure Tree (n : ℕ) [NeZero n] where
  parent : Fin n → Fin n
  root : parent 0=0
  lower : ∀ v : Fin n, v≠0 → (parent v).val<v.val

variable {n : ℕ} [NeZero n]

abbrev Tree.Child (T : Tree n) (v : Fin n) := {u : Fin n // u≠0 ∧ T.parent u=v}
instance instFintypeChild (T : Tree n) (v : Fin n) : Fintype (T.Child v) := by
  classical
  unfold Tree.Child
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)
instance instDecidableEqChild (T : Tree n) (v : Fin n) : DecidableEq (T.Child v) := Classical.decEq _

def Tree.park (T : Tree n) (q : Fin n → ℝ) (v : Fin n) : ℝ :=
  q v-∑ u : T.Child v, q u.val

def Tree.childEquiv (T : Tree n) : (Σ v : Fin n, T.Child v) ≃ {v : Fin n // v≠0} where
  toFun p := ⟨p.2.val,p.2.property.1⟩
  invFun u := ⟨T.parent u.val,⟨u.val,u.property,rfl⟩⟩
  left_inv := by
    rintro ⟨v,u,hu,hp⟩
    dsimp
    subst v
    rfl
  right_inv := by intro u; rfl

lemma Tree.weighted_children (T : Tree n) (w f : Fin n → ℝ) (h0 : f 0=0) :
    (∑ v, w v*∑ u : T.Child v, f u.val)=∑ u, w (T.parent u)*f u := by
  classical
  simp_rw [mul_sum]
  rw [← Fintype.sum_sigma (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)]
  have he := Fintype.sum_equiv (T.childEquiv)
    (fun p : Σ v : Fin n, T.Child v => w p.1*f p.2.val)
    (fun u : {v : Fin n // v≠0} => w (T.parent u.val)*f u.val)
    (by intro p; change w p.1*f p.2.val=w (T.parent p.2.val)*f p.2.val
        rw [p.2.property.2])
  rw [he]
  have hsub := Fintype.sum_subtype_add_sum_subtype (fun v : Fin n => v≠0)
    (fun u => w (T.parent u)*f u)
  have hz : (∑ u : {v : Fin n // ¬v≠0}, w (T.parent u.val)*f u.val)=0 := by
    apply sum_eq_zero
    intro u _
    have hu : u.val=0 := not_ne_iff.mp u.property
    simp [hu,h0]
  simpa only [hz, add_zero] using hsub

/-- True precisely on a vertex's descendants (including the vertex itself). -/
def Tree.under (T : Tree n) (v w : Fin n) : Bool :=
  if w=v then true else if _hw : w=0 then false else T.under v (T.parent w)
termination_by w.val
decreasing_by exact T.lower w _hw

lemma Tree.under_self (T : Tree n) (v : Fin n) : T.under v v=true := by
  rw [Tree.under,ite_eq_left rfl]

lemma Tree.under_le (T : Tree n) (v w : Fin n) (h : T.under v w=true) : v.val ≤ w.val := by
  by_cases hwv : w=v
  · subst w; exact le_rfl
  · by_cases hw0 : w=0
    · rw [Tree.under,ite_eq_right hwv,dite_eq_left hw0] at h
      contradiction
    · have hp : T.under v (T.parent w)=true := by
        rw [Tree.under,ite_eq_right hwv,dite_eq_right hw0] at h
        exact h
      exact (T.under_le v (T.parent w) hp).trans (T.lower w hw0).le
termination_by w.val
decreasing_by exact T.lower w hw0

lemma Tree.under_parent_self (T : Tree n) (v : Fin n) (hv : v≠0) :
    T.under v (T.parent v)=false := by
  cases hh : T.under v (T.parent v)
  · rfl
  · have h := T.under_le v (T.parent v) hh
    have := T.lower v hv
    omega

lemma Tree.under_zero (T : Tree n) (v : Fin n) : T.under v 0=(v==0) := by
  rw [Tree.under]
  by_cases h : v=0
  · subst v; simp
  · simp [h,Ne.symm h]

def Tree.indicator (T : Tree n) (v w : Fin n) : ℝ := if T.under v w then 1 else 0

lemma Tree.indicator_parent (T : Tree n) (v w : Fin n) (hw : w≠0) :
    T.indicator v w-T.indicator v (T.parent w) = if w=v then 1 else 0 := by
  by_cases h : w=v
  · subst w
    simp [Tree.indicator,T.under_self,T.under_parent_self v hw]
  · have he : T.under v w=T.under v (T.parent w) := by
      rw [Tree.under,ite_eq_right h,dite_eq_right hw]
    simp [Tree.indicator,he,h]

/-- Literal telescoping over one subtree of the concrete parent tree. -/
theorem Tree.park_subtree_total (T : Tree n) (q : Fin n → ℝ) (v : Fin n) :
    (∑ w, T.indicator v w*T.park q w)=q v := by
  classical
  let q0 : Fin n → ℝ := fun w => if w=0 then 0 else q w
  have hq0 : q0 0=0 := by simp [q0]
  have he : ∀ w, (∑ u : T.Child w, q u.val) = ∑ u : T.Child w, q0 u.val := by
    intro w
    apply sum_congr rfl
    intro u _
    simp [q0,u.property.1]
  have hs := T.weighted_children (T.indicator v) q0 hq0
  simp_rw [Tree.park,mul_sub,he]
  rw [sum_sub_distrib,hs,←sum_sub_distrib]
  have hpoint : ∀ w : Fin n,
      T.indicator v w*q w-T.indicator v (T.parent w)*q0 w = if w=v then q w else 0 := by
    intro w
    by_cases hw : w=0
    · subst w
      by_cases hv : v=0
      · subst v; simp [q0,Tree.indicator,T.under_zero]
      · simp [q0,Tree.indicator,T.under_zero,hv,Ne.symm hv]
    · simp only [q0,ite_eq_right hw]
      rw [←sub_mul,T.indicator_parent v w hw]
      split_ifs <;> simp
  simp_rw [hpoint]
  simp

section Geometry
variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]

/-- Finite posterior counting mass; repeated hidden locations contribute their
full weight and do not require an injective posterior support. -/
def countingMass (μ : Y → ℝ) (R : Finset Y) : ℝ := ∑ y ∈ R, μ y

end Geometry

end KServer.Rounding

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Trees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal finite complete-prefix tree, numbered parent-before-child. The
unused words are retained, as required for an unconditioned finite key tape. -/
noncomputable section
open scoped BigOperators
namespace KServer.PrefixTree
variable (A:Type) [Fintype A] (L:ℕ)

abbrev Vertex := (j:Fin (L+1)) × (Fin j.val→A)

def root : Vertex A L := ⟨0,Fin.elim0⟩
instance instNonemptyVertex : Nonempty (Vertex A L) := ⟨root A L⟩

def code (v:Vertex A L) : Lex (ℕ×ℕ) :=
  toLex (v.1.val,(Fintype.equivFin (Fin v.1.val→A) v.2).val)

lemma code_injective : Function.Injective (code A L) := by
  rintro ⟨j,f⟩ ⟨j',g⟩ h
  have hj:j=j':=Fin.ext (congrArg (fun p:Lex (ℕ×ℕ)=>(ofLex p).1) h)
  subst j'
  have hf:(Fintype.equivFin (Fin j.val→A) f).val=(Fintype.equivFin (Fin j.val→A) g).val :=
    congrArg (fun p:Lex (ℕ×ℕ)=>(ofLex p).2) h
  have he:f=g:=(Fintype.equivFin _).injective (Fin.ext hf)
  subst g
  rfl

instance instLinearOrderVertex : LinearOrder (Vertex A L) := LinearOrder.lift' (code A L) (code_injective A L)

lemma root_le (v:Vertex A L) : root A L≤v := by
  by_cases hj:v.1.val=0
  · have he:v=root A L:=by
      rcases v with ⟨j,f⟩
      have hj':j=0:=Fin.ext hj
      subst j
      congr
      exact funext (fun i=>Fin.elim0 i)
    rw [he]
  · change code A L (root A L) ≤ code A L v
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (Nat.pos_of_ne_zero hj))

instance instNeZeroNatCardVertex : NeZero (Fintype.card (Vertex A L)) := ⟨Nat.ne_of_gt Fintype.card_pos⟩

def numbering : Fin (Fintype.card (Vertex A L)) ≃o Vertex A L :=
  Fintype.orderIsoFinOfCardEq _ rfl

lemma numbering_zero : numbering A L 0=root A L := by
  apply le_antisymm
  · rw [←(numbering A L).apply_symm_apply (root A L)]
    apply (numbering A L).monotone
    exact Fin.zero_le _
  · exact root_le A L _

def parent (v:Vertex A L) : Vertex A L :=
  if h:v.1.val=0 then root A L
  else ⟨⟨v.1.val-1,by omega⟩,fun i=>v.2 ⟨i.val,by have hi : i.val<v.1.val-1 := i.isLt; omega⟩⟩

omit [Fintype A] in
lemma parent_root : parent A L (root A L)=root A L := by simp [parent,root]

lemma parent_lt {v:Vertex A L} (hv:v≠root A L) : parent A L v<v := by
  have hj:v.1.val≠0:=by
    intro h
    apply hv
    rcases v with ⟨j,f⟩
    have hj:j=0:=Fin.ext h
    subst j
    congr
    exact funext (fun i=>Fin.elim0 i)
  change code A L (parent A L v) < code A L v
  rw [parent,dite_eq_right hj]
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  dsimp only [code]
  omega

def tree : TreeRounding.Tree (Fintype.card (Vertex A L)) where
  parent v := (numbering A L).symm (parent A L (numbering A L v))
  root := by rw [numbering_zero,parent_root,←numbering_zero]; exact (numbering A L).symm_apply_apply 0
  lower v hv := by
    have h:(numbering A L v)≠root A L:=by
      intro he
      apply hv
      apply (numbering A L).injective
      rw [he,numbering_zero]
    have hp:=parent_lt A L h
    have he: (numbering A L).symm (parent A L (numbering A L v))<v :=by
      simpa only [(numbering A L).symm_apply_apply] using (numbering A L).symm.strictMono hp
    exact he

end KServer.PrefixTree

end


/-! Literal cells and hidden labeled counts in the retained complete-prefix
hierarchy.  Empty words/nodes are not removed. Child counts partition the
parent exactly, including repeated physical server locations. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchyCounts
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A Y Ω : Type} [Fintype A] [Fintype Ω] {k d : ℕ}

def hit (maps : ℕ → Y → A) (word : Fin d → A) (y : Y) : Prop :=
  ∀ i, maps i.val y=word i

def count (maps : ℕ → Y → A) (word : Fin d → A) (q : Fin k → Y) : ℕ :=
  (univ.filter fun l => hit maps word (q l)).card

omit [Fintype A] in
lemma count_le (maps : ℕ → Y → A) (word : Fin d → A) (q : Fin k → Y) :
    count maps word q ≤ k := by
  exact (card_filter_le _ _).trans_eq (card_univ.trans (Fintype.card_fin k))

omit [Fintype A] in
lemma hit_zero (maps : ℕ → Y → A) (word : Fin 0 → A) (y : Y) : hit maps word y :=
  fun i => Fin.elim0 i

omit [Fintype A] in
lemma count_zero (maps : ℕ → Y → A) (word : Fin 0 → A) (q : Fin k → Y) :
    count maps word q=k := by simp [count,hit_zero]

omit [Fintype A] in
lemma hit_snoc (maps : ℕ → Y → A) (word : Fin d → A) (a : A) (y : Y) :
    hit maps (Fin.snoc word a) y ↔ hit maps word y ∧ maps d y=a := by
  constructor
  · intro h
    exact ⟨fun i=>by simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using h i.castSucc,
      by simpa only [Fin.snoc_last,Fin.val_last] using h (Fin.last d)⟩
  · rintro ⟨h,ha⟩ i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa using ha
    · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using h j

lemma count_sum (maps : ℕ → Y → A) (word : Fin d → A) (q : Fin k → Y) :
    (∑ a : A, count maps (Fin.snoc word a) q)=count maps word q := by
  simp only [count,card_filter,hit_snoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  by_cases h : hit maps word (q l)
  · simp [h]
  · simp [h]

open RankTracking PosteriorRanks

lemma positive_mass {w : Ω → ℝ} (hw : ∀ ρ,0≤w ρ) (H : Ω → ℕ) (ω : Ω)
    (hω : 0<w ω) : 0<PosteriorRanks.mass w H (H ω) := by
  exact hω.trans_le (single_le_sum (fun ρ _=>hw ρ) (by simp [fiber]))

/-- The actual conditional distribution on the true prefix fiber. -/
def conditional (w : Ω → ℝ) (H : Ω → ℕ) (ω ρ : Ω) : ℝ :=
  if H ρ=H ω then w ρ/PosteriorRanks.mass w H (H ω) else 0

lemma conditional_nonneg {w : Ω → ℝ} (hw : ∀ ω,0≤w ω) (H : Ω → ℕ) (ω ρ : Ω) :
    0 ≤ conditional w H ω ρ := by
  unfold conditional
  split_ifs
  · exact div_nonneg (hw ρ) (mass_nonneg hw H (H ω))
  · rfl

lemma conditional_sum (w : Ω → ℝ) (H : Ω → ℕ) (ω : Ω)
    (hm : PosteriorRanks.mass w H (H ω)≠0) : (∑ ρ,conditional w H ω ρ)=1 := by
  unfold conditional
  rw [←sum_filter,←sum_div]
  exact div_self hm

lemma conditional_rank (w : Ω → ℝ) (H : Ω → ℕ) (ω : Ω) (N : Ω → ℕ) (a : ℕ) :
    RankOrder.countRank (conditional w H ω) N a=posterior w H (PosteriorRanks.rank N a) ω := by
  unfold RankOrder.countRank conditional posterior numerator PosteriorRanks.rank
  simp only [ite_mul,zero_mul,div_mul_eq_mul_div]
  rw [←sum_filter,←sum_div]
  rfl

/-- The actual posterior lower bounds simultaneously satisfy both source
superadditivities, even though the labeled counts are arbitrarily dependent. -/
theorem compatible (w : Ω → ℝ) (hw : ∀ ω,0≤w ω) (H : Ω → ℕ) (ω : Ω)
    (hω : 0<w ω) (maps : Ω → ℕ → Y → A) (word : Fin d → A) (q : Ω → Fin k → Y)
    {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ)) :
    (∑ a : A, CompatibleBounds.L k (conditional w H ω)
      (fun ρ=>count (maps ρ) (Fin.snoc word a) (q ρ)) z) ≤
      CompatibleBounds.L k (conditional w H ω) (fun ρ=>count (maps ρ) word (q ρ)) z ∧
    (∑ a : A, CompatibleBounds.M k (conditional w H ω)
      (fun ρ=>count (maps ρ) (Fin.snoc word a) (q ρ))) ≤
      CompatibleBounds.M k (conditional w H ω) (fun ρ=>count (maps ρ) word (q ρ)) ∧
    CompatibleBounds.M k (conditional w H ω) (fun ρ=>count (maps ρ) word (q ρ)) ≤
      ∑ ρ,conditional w H ω ρ*count (maps ρ) word (q ρ) := by
  have hb:=CompatibleBounds.compatible_bounds (conditional w H ω) (conditional_nonneg hw H ω)
    (conditional_sum w H ω (positive_mass hw H ω hω).ne')
    (fun ρ a=>count (maps ρ) (Fin.snoc word a) (q ρ))
    (fun ρ=>by rw [count_sum]; exact count_le _ _ _) hz
  simpa only [count_sum] using hb

end KServer.HierarchyCounts

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conditional ranks of literal complete-prefix cells, connected to the
allocation's filtered process and compatible lower envelopes. No local
allocation or competitiveness assertion is an input. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalRanks
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking PosteriorRanks HierarchyCounts
variable {Ω A Y : Type} [Fintype Ω] [Fintype A] {k d : ℕ}
variable {w : Ω → ℝ} (hw : ∀ ω,0≤w ω)
variable (H : ℕ → Ω → ℕ)
variable (hr : ∀ t ω ρ,H (t+1) ω=H (t+1) ρ → H t ω=H t ρ)
variable (maps : ℕ → Ω → ℕ → Y → A) (q : ℕ → Ω → Fin k → Y)

def family (word : Fin d → A) (a : Fin k) : FilteredRanks w :=
  rankProcess hw H hr (fun t ω=>count (maps t ω) word (q t ω)) a.val

def lower (word : Fin d → A) (z : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k, RankFunctions.rank z ((family hw H hr maps q word a).p t ω)

def size (word : Fin d → A) (t : ℕ) (ω : Ω) : ℝ :=
  CoarseProcess.size (family hw H hr maps q word) t ω

omit [Fintype A] in
lemma family_value (word : Fin d → A) (a : Fin k) (t : ℕ) (ω : Ω) :
    (family hw H hr maps q word a).p t ω=
      RankOrder.countRank (conditional w (H t) ω)
        (fun ρ=>count (maps t ρ) word (q t ρ)) a.val :=
  (conditional_rank w (H t) ω _ _).symm

omit [Fintype A] in
lemma lower_eq (word : Fin d → A) (z : ℝ) (t : ℕ) (ω : Ω) :
    lower hw H hr maps q word z t ω=CompatibleBounds.L k (conditional w (H t) ω)
      (fun ρ=>count (maps t ρ) word (q t ρ)) z := by
  simp only [lower,CompatibleBounds.L,family_value]

omit [Fintype A] in
lemma size_eq (word : Fin d → A) (t : ℕ) (ω : Ω) :
    size hw H hr maps q word t ω=CompatibleBounds.M k (conditional w (H t) ω)
      (fun ρ=>count (maps t ρ) word (q t ρ)) := by
  simp only [size,CoarseProcess.size,CompatibleBounds.M,family_value]

lemma lower_superadditive (word : Fin d → A) {z : ℝ}
    (hz : z∈Set.Icc 0 (1/100:ℝ)) (t : ℕ) (ω : Ω) (hω : 0<w ω) :
    (∑ a : A,lower hw H hr maps q (Fin.snoc word a) z t ω) ≤ lower hw H hr maps q word z t ω := by
  simp_rw [lower_eq]
  exact (HierarchyCounts.compatible w hw (H t) ω hω (maps t) word (q t) hz).1

lemma size_superadditive (word : Fin d → A) (t : ℕ) (ω : Ω) (hω : 0<w ω) :
    (∑ a : A,size hw H hr maps q (Fin.snoc word a) t ω) ≤ size hw H hr maps q word t ω := by
  simp_rw [size_eq]
  exact (HierarchyCounts.compatible w hw (H t) ω hω (maps t) word (q t)
    (z:=0) (by norm_num)).2.1

omit [Fintype A] in
lemma family_root (word : Fin 0 → A) (a : Fin k) (t : ℕ) (ω : Ω) :
    (family hw H hr maps q word a).p t ω=0 := by
  change posterior w (H t) (PosteriorRanks.rank _ a.val) ω=0
  have he : PosteriorRanks.rank (fun ρ=>count (maps t ρ) word (q t ρ)) a.val=fun _=>0 := by
    funext ρ
    simp only [PosteriorRanks.rank,count_zero]
    exact ite_eq_right (by omega)
  rw [he]
  simp [posterior,numerator]

omit [Fintype A] in
lemma lower_root (word : Fin 0 → A) (z : ℝ) (t : ℕ) (ω : Ω) :
    lower hw H hr maps q word z t ω=k := by
  simp only [lower,family_root,RankFunctions.rank_zero]
  simp

omit [Fintype A] in
lemma size_root (word : Fin 0 → A) (t : ℕ) (ω : Ω) :
    size hw H hr maps q word t ω=k := by
  simp only [size,CoarseProcess.size,family_root]
  norm_num [RankFunctions.sizeRank]

omit [Fintype A] in
lemma size_bound (word : Fin d → A) (t : ℕ) (ω : Ω) : size hw H hr maps q word t ω ≤ k := by
  calc _ ≤ ∑ _a : Fin k,(1:ℝ) := by
        unfold size CoarseProcess.size
        apply sum_le_sum
        intro a _
        have h:=(family hw H hr maps q word a).range t ω
        exact (RankFunctions.sizeRank_le_complement h).trans (by linarith [h.1])
       _ = _ := by simp

end KServer.HierarchicalRanks

end


/-! Actual top-down fractional quotas on all complete-prefix labels. The
parent budget is obtained from conditional count superadditivity, not posited
as an allocation oracle. Fixed unused labels remain present. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualStar
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def children {d:ℕ} (word:Fin d→A):A→Fin k→FilteredRanks w:=
  fun a=>HierarchicalRanks.family hw H hr maps q (Fin.snoc word a)
def parent {d:ℕ} (word:Fin d→A):Fin k→FilteredRanks w:=
  HierarchicalRanks.family hw H hr maps q word

def quota (hk:1≤(k:ℝ)): (d:ℕ)→(Fin d→A)→ℕ→Ω→ℝ
  | 0,_ ,_,_ => k
  | d+1,word,t,ω=>ActualOutput.out hk (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) t ω
      (quota hk d (Fin.init word) t ω) (word (Fin.last d))

lemma quota_snoc (hk:1≤(k:ℝ)) {d:ℕ} (word:Fin d→A) (a:A) (t:ℕ) (ω:Ω):
    quota hw H hr maps q hk (d+1) (Fin.snoc word a) t ω=
      ActualOutput.out hk (children hw H hr maps q word) (parent hw H hr maps q word)
        t ω (quota hw H hr maps q hk d word t ω) a:=by
  simp only [quota,Fin.init_snoc,Fin.snoc_last]

lemma sizes {d:ℕ} (word:Fin d→A) (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω):
    (∑ a,CoarseProcess.size (children hw H hr maps q word a) t ω)≤
      CoarseProcess.size (parent hw H hr maps q word) t ω:=
  HierarchicalRanks.size_superadditive hw H hr maps q word t ω (hwpos ω)
omit [Fintype A] in
lemma size_bound {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    CoarseProcess.size (parent hw H hr maps q word) t ω≤k:=
  HierarchicalRanks.size_bound hw H hr maps q word t ω

lemma parent_budget (hk:1≤(k:ℝ)) {d:ℕ} (word:Fin d→A) (hwpos:∀ ω,0<w ω)
    (t:ℕ) (ω:Ω) (x:ℝ) (hx:ActualOutput.lower k (parent hw H hr maps q word) t ω≤x):
    (∑ a,(ActualOutput.n (children hw H hr maps q word) t ω a-
      β k (parent hw H hr maps q word) t ω*ActualOutput.B (children hw H hr maps q word) t ω a+
      ActualOutput.f k (children hw H hr maps q word) (parent hw H hr maps q word) t ω a))≤x:=by
  have hz:=(ActualCaps.ranges hk (parent hw H hr maps q word) t ω (size_bound hw H hr maps q word t ω)).1
  have hs:=HierarchicalRanks.lower_superadditive hw H hr maps q word hz t ω (hwpos ω)
  have heq : (∑ a,(ActualOutput.n (children hw H hr maps q word) t ω a-
      β k (parent hw H hr maps q word) t ω*ActualOutput.B (children hw H hr maps q word) t ω a+
      ActualOutput.f k (children hw H hr maps q word) (parent hw H hr maps q word) t ω a))=
      ∑ a,HierarchicalRanks.lower hw H hr maps q (Fin.snoc word a)
        (ActualCaps.z k (parent hw H hr maps q word) t ω) t ω := by
    apply sum_congr rfl
    intro a _
    exact (TrackedCaps.decomposition (children hw H hr maps q word a)
      (ActualCaps.z k (parent hw H hr maps q word) t ω) t ω).symm
  rw [heq]
  exact hs.trans hx

lemma quota_bounds (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) (d:ℕ) (word:Fin d→A) (t:ℕ) (ω:Ω):
    ActualOutput.lower k (parent hw H hr maps q word) t ω≤quota hw H hr maps q hk d word t ω ∧
      quota hw H hr maps q hk d word t ω≤72*CoarseProcess.size (parent hw H hr maps q word) t ω:=by
  induction d with
  | zero=>
    have hl:=HierarchicalRanks.lower_root hw H hr maps q word (ActualCaps.z k (parent hw H hr maps q word) t ω) t ω
    have hs:=HierarchicalRanks.size_root hw H hr maps q word t ω
    change ActualOutput.lower k (parent hw H hr maps q word) t ω=(k:ℝ) at hl
    change CoarseProcess.size (parent hw H hr maps q word) t ω=(k:ℝ) at hs
    simp only [quota,hl,hs]
    constructor
    · rfl
    · linarith
  | succ d ih=>
    have hp:=parent_budget hw H hr maps q hk (Fin.init word) hwpos t ω _ (ih (Fin.init word)).1
    have hf:=ActualOutput.out_feasible hk (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) (sizes hw H hr maps q (Fin.init word) hwpos)
      (size_bound hw H hr maps q (Fin.init word)) t ω _ hp
    have hd:=ActualOutput.output_domination hk (children hw H hr maps q (Fin.init word))
      (parent hw H hr maps q (Fin.init word)) (sizes hw H hr maps q (Fin.init word) hwpos)
      (size_bound hw H hr maps q (Fin.init word)) t ω _ hp (word (Fin.last d))
    have he:Fin.snoc (Fin.init word) (word (Fin.last d))=word:=Fin.snoc_init_self word
    have hl := (hf.1 (word (Fin.last d))).1
    have hu := hd.2
    simp only [children,he] at hl hu
    exact ⟨hl,hu⟩

lemma children_budget (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    (∑ a,quota hw H hr maps q hk (d+1) (Fin.snoc word a) t ω)≤quota hw H hr maps q hk d word t ω:=by
  simp_rw [quota_snoc]
  exact (ActualOutput.out_feasible hk _ _ (sizes hw H hr maps q word hwpos)
    (size_bound hw H hr maps q word) t ω _ (parent_budget hw H hr maps q hk word hwpos t ω _
      (quota_bounds hw H hr maps q hk hwpos d word t ω).1)).2

lemma quota_nonneg (hk:1≤(k:ℝ)) (hwpos:∀ ω,0<w ω) {d:ℕ} (word:Fin d→A) (t:ℕ) (ω:Ω):
    0≤quota hw H hr maps q hk d word t ω:=
  (ActualOutput.lower_nonneg hk _ t ω (size_bound hw H hr maps q word t ω)).trans
    (quota_bounds hw H hr maps q hk hwpos d word t ω).1

end KServer.HierarchicalQuota

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationCausality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hysteresis switch budget with signed filtering before every reset test.
The only costs are actual rank drifts, actual flag changes, held-scale
variation, and the new potential at literal wholesale resets. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RuleSchedule
attribute [local instance] Classical.propDecidable
open RankTracking
variable {Ω R : Type} [Fintype Ω] [Fintype R] {w : Ω→ℝ}

def S (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool) (t : ℕ) (ω : Ω) : ℝ :=
  core (flags t ω) (fun r=>(P r).p t ω)

def potential (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  value (marked t ω) (run marked reset (S P flags) D t ω) (S P flags t ω) (D t ω)

def J (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (marked reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  charge (marked (t+1) ω) (reset (t+1) ω) (run marked reset (S P flags) D t ω)
    (S P flags (t+1) ω) (D (t+1) ω)

def expense (P : R→FilteredRanks w) (flags : ℕ→Ω→R→Bool)
    (reset : ℕ→Ω→Bool) (D : ℕ→Ω→ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ r,if flags t ω r=flags (t+1) ω r then (0:ℝ) else 1)+|D (t+1) ω-D t ω|+
    if reset (t+1) ω then S P flags (t+1) ω+D (t+1) ω else 0

end KServer.RuleSchedule

end


/-! Predictability of the *actual* star schedule and regime, for the common
observation history. In particular none of the filtering coefficients uses
the new reset event. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def ruleFlags (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω) (ir:J×R):Bool:=CoreFlags.flag (P ir.1 ir.2) t ω
end KServer.ActualOutput

end


/-! Uniform affine slope and endpoint bounds for the literal marked-side
family; logarithmic cancellation removes dependence on the number of children. -/


/-! Literal synthetic-flag preparation and selective held-log parameter edits
for the marked-side minimizers of the constructed star. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SideEdits
attribute [local instance] Classical.propDecidable
open SideTracker SideFamilies
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

def L (cw ell:ℝ):ℝ:=640*(1/cw+1)*ell
def Q (cw ell:ℝ):ℝ:=200*(Real.log 17+2)/cw*ell
def K (cw ell:ℝ):ℝ:=2*(200*(1/cw+1)+200*(Real.log 17+2)/cw)*ell

end KServer.SideEdits

end


/-! Every side edit is charged to the literal rank-flag and coarse-coordinate
schedule. No cardinality factor or charge to an unchanged dominant child. -/


/-! The non-wholesale cap variation of the literal output. All endpoint
trackers are charged over all times before selecting the ordinary steps. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualOutput
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar OutputDynamics
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def capScale (k:ℝ) (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w)
    (t:ℕ) (ω:Ω) (i:J):ℝ:=if mark P Q t ω=some i then 1+lb/ActualCaps.ell k else 1-lb/ActualCaps.ell k

end KServer.ActualOutput

end


/-! Every coordinate of the actual feasible star output depends only on
observed history and on the supplied parent quota. -/


/-! The literal recursive allocation is adapted to the request filtration.
No adaptedness of the hidden offline configurations is asserted or required. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace KServer

universe u

/-- Literal main objective, with arbitrary universes, arbitrary metric spaces,
repeated initial positions, and one policy and additive constant for all finite
inputs. Real constants are finite; an embedding witnesses at least k+1 points.
The final implication encodes availability of B=0 for distinct starts. -/
def ReductionStatement : Prop :=
  ∃ C : ℝ, ∀ (k : ℕ), 2  ≤  k →
    ∀ (X : Type u) (_ : MetricSpace X),
      (∃ e : Fin (k + 1) → X, Function.Injective e) →
      ∀ s : Configuration k X,
        ∃ A : Policy k X, ∃ B : ℝ,
          0  ≤  B ∧ (Function.Injective s → B = 0) ∧
          ∀ σ : List X,
            expectedCost A s σ  ≤  C * (Real.log (k + 1)) ^ 2 * optimalCost s σ + B


/- Finite behavioral experiments and product compactness. -/


instance instTopologicalSpaceLabelDistribution (k : ℕ) : TopologicalSpace (LabelDistribution k) :=
  inferInstanceAs (TopologicalSpace
    {probability : Fin k → ℝ // (∀ label, 0 ≤ probability label) ∧ ∑ label, probability label = 1})

instance instCompactSpaceLabelDistribution (k : ℕ) : CompactSpace (LabelDistribution k) := by
  apply isCompact_iff_compactSpace.mp
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc : IsCompact (Set.Icc (0 : Fin k → ℝ) 1))
  · change IsClosed
      ({probability : Fin k → ℝ | ∀ label, 0 ≤ probability label} ∩
        {probability : Fin k → ℝ | ∑ label, probability label = 1})
    apply IsClosed.inter
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun label => isClosed_le continuous_const (continuous_apply label)
    · exact isClosed_eq (by fun_prop) continuous_const
  · rintro probability ⟨nonnegative, total⟩
    refine ⟨nonnegative, ?_⟩
    intro label
    calc
      probability label ≤ ∑ other, probability other :=
        Finset.single_le_sum (fun other _ => nonnegative other) (Finset.mem_univ label)
      _ = 1 := total

/-- A pure choice, also used to fill unreachable decision histories. -/
def pureDistribution {k : ℕ} (i : Fin k) : LabelDistribution k :=
  ⟨fun j => if j = i then 1 else 0, by
    constructor
    · intro j; dsimp only; split_ifs <;> norm_num
    · simp⟩

instance instNonemptyLabelDistributionOfNeZeroNat (k : ℕ) [NeZero k] : Nonempty (LabelDistribution k) :=
  ⟨pureDistribution 0⟩

lemma serviceCost_nonneg {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (σ : List X) (j : Fin σ.length → Fin k) :
    0  ≤  serviceCost s σ j := by
  induction σ generalizing s with
  | nil => simp [serviceCost]
  | cons r rs ih => exact add_nonneg dist_nonneg (ih _ _)

/-! Section02's matching and strongly lazy simulation, including repeated
positions and arbitrary metric spaces. -/

def configurationAfter {k : ℕ} {X : Type u} (s : Configuration k X)
    (h : List (X × Fin k)) : Configuration k X :=
  h.foldl (fun c ri => serve c ri.2 ri.1) s

def StronglyLazy {k : ℕ} {X : Type u} (s : Configuration k X) (A : Policy k X) : Prop :=
  ∀ h r, (∃ i, configurationAfter s h i = r) →
    ∀ j, configurationAfter s h j ≠ r → (A h r).val j = 0

lemma configurationAfter_append {k : ℕ} {X : Type u} (s : Configuration k X)
    (h : List (X × Fin k)) (r : X) (i : Fin k) :
    configurationAfter s (h ++ [(r,i)]) = serve (configurationAfter s h) i r := by
  simp [configurationAfter, List.foldl_append]

end KServer
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Behavior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace KServer
universe u

section Matching
variable {k : ℕ} {X : Type u} [MetricSpace X]

def matchSum (A C : Configuration k X) (π : Equiv.Perm (Fin k)) : ℝ :=
  ∑ i, dist (A i) (C (π i))

lemma exists_minimum_matching (A C : Configuration k X) :
    ∃ π : Equiv.Perm (Fin k), ∀ τ, matchSum A C π  ≤  matchSum A C τ := by
  obtain ⟨π, _, hπ⟩ := Finset.exists_min_image Finset.univ (matchSum A C)
    Finset.univ_nonempty
  exact ⟨π, fun τ => hπ τ (Finset.mem_univ τ)⟩

def matchingPerm (A C : Configuration k X) : Equiv.Perm (Fin k) :=
  (exists_minimum_matching A C).choose

def matching (A C : Configuration k X) : ℝ := matchSum A C (matchingPerm A C)

/-- A causal minimum-matching choice. Repeated actual and virtual positions are
retained: only the permutation of occurrence labels is used. -/
def lazyChoice (A C : Configuration k X) (r : X) (hc : ∃ i, C i = r) : Fin k := by
  classical
  exact if ha : ∃ i, A i = r then ha.choose else (matchingPerm A C).symm hc.choose

end Matching


/-- Expected continuation from a specified (possibly null) history. -/
def continuationCost {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (h : List (X × Fin k)) (σ : List X) : ℝ :=
  ∑ j : Fin σ.length → Fin k, pathProbability A h σ j * serviceCost s σ j

section CausalSimulation
variable {k : ℕ} {X : Type u} [MetricSpace X]
variable (start : Configuration k X) (C : List X → Configuration k X)
variable (hcover : ∀ h r, ∃ i, C (h ++ [r]) i = r)

/-- Simulated movement measured by occurrence matching, exactly Section02. -/
def simulatedMovement (C : List X → Configuration k X) (pre : List X) : List X → ℝ
  | [] => 0
  | r :: σ => matching (C pre) (C (pre ++ [r])) + simulatedMovement C (pre ++ [r]) σ

end CausalSimulation

section OfflineComparison
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

omit [NeZero k] in
lemma optimalCost_le_service (s : Configuration k X) (σ : List X)
    (j : Fin σ.length → Fin k) : optimalCost s σ  ≤  serviceCost s σ j := by
  exact csInf_le ⟨0, by rintro _ ⟨w,rfl⟩; exact serviceCost_nonneg _ _ _⟩ ⟨j,rfl⟩

lemma optimalCost_attained (s : Configuration k X) (σ : List X) :
    ∃ j : Fin σ.length → Fin k, serviceCost s σ j = optimalCost s σ := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ (serviceCost s σ)
    Finset.univ_nonempty
  refine ⟨j, le_antisymm ?_ (optimalCost_le_service s σ j)⟩
  exact le_csInf (Set.range_nonempty _) (by
    rintro _ ⟨w,rfl⟩
    exact hj w (Finset.mem_univ w))

end OfflineComparison
def historyProbability {k : ℕ} {X : Type u} (A : Policy k X)
    (pre : List (X × Fin k)) : List (X × Fin k) → ℝ
  | [] => 1
  | (r,i) :: h => (A pre r).val i * historyProbability A (pre ++ [(r,i)]) h

lemma historyProbability_nonneg {k : ℕ} {X : Type u} (A : Policy k X)
    (pre h : List (X × Fin k)) : 0  ≤  historyProbability A pre h := by
  induction h generalizing pre with
  | nil => simp [historyProbability]
  | cons ri h ih => exact mul_nonneg ((A pre ri.1).property.1 _) (ih _)


/-! ## Explicit causal realization of finite hidden-state algorithms.
This discharges a policy-existence interface needed both by correlated rounding
and by the fictitious-prefix episode extraction. It is not a competitiveness
premise: the machine below is arbitrary and its behavioral policy is constructed. -/
namespace HiddenMachine
open Finset
variable {k : ℕ} {X : Type u} {S : Type*} [Fintype S]

structure Data (k : ℕ) (X : Type u) (S : Type*) [Fintype S] where
  initial : S → ℝ
  initial_nonneg : ∀ s, 0  ≤  initial s
  initial_sum : ∑ s, initial s = 1
  transition : List (X × Fin k) → X → S → S → ℝ
  transition_nonneg : ∀ h r s s', 0  ≤  transition h r s s'
  transition_sum : ∀ h r s, ∑ s', transition h r s s' = 1
  output : List (X × Fin k) → X → S → S → Fin k
  nullOutput : List (X × Fin k) → X → Fin k

variable (M : Data k X S)

def step (h : List (X × Fin k)) (r : X) (i : Fin k) (w : S → ℝ) : S → ℝ :=
  fun s' => ∑ s, if M.output h r s s'=i then w s*M.transition h r s s' else 0

def evolve (w : S → ℝ) (pre : List (X × Fin k)) : List (X × Fin k) → S → ℝ
  | [] => w
  | (r,i)::h => evolve (step M pre r i w) (pre++[(r,i)]) h

def weights (h : List (X × Fin k)) : S → ℝ := evolve M M.initial [] h

def mass (h : List (X × Fin k)) : ℝ := ∑ s, weights M h s

def outMass (h : List (X × Fin k)) (r : X) (i : Fin k) : ℝ :=
  ∑ s', step M h r i (weights M h) s'

lemma step_nonneg (h : List (X × Fin k)) (r : X) (i : Fin k) (w : S → ℝ)
    (hw : ∀ s, 0  ≤  w s) (s' : S) : 0  ≤  step M h r i w s' := by
  exact sum_nonneg fun s _ => by
    split_ifs
    · exact mul_nonneg (hw s) (M.transition_nonneg _ _ _ _)
    · exact le_rfl

lemma evolve_nonneg (w : S → ℝ) (hw : ∀ s, 0  ≤  w s)
    (pre h : List (X × Fin k)) (s : S) : 0  ≤  evolve M w pre h s := by
  induction h generalizing w pre with
  | nil => exact hw s
  | cons ri h ih => exact ih _ (step_nonneg M pre ri.1 ri.2 w hw) _

lemma weights_nonneg (h : List (X × Fin k)) (s : S) : 0  ≤  weights M h s :=
  evolve_nonneg M M.initial M.initial_nonneg [] h s

lemma outMass_nonneg (h : List (X × Fin k)) (r : X) (i : Fin k) : 0  ≤  outMass M h r i :=
  sum_nonneg fun s _ => step_nonneg M h r i _ (weights_nonneg M h) s

lemma step_sum (h : List (X × Fin k)) (r : X) (w : S → ℝ) :
    (∑ i : Fin k, ∑ s', step M h r i w s') = ∑ s, w s := by
  simp only [step]
  calc
    _ = ∑ s', ∑ s, ∑ i : Fin k,
        if M.output h r s s'=i then w s*M.transition h r s s' else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro s' _
      rw [sum_comm]
    _ = ∑ s', ∑ s, w s*M.transition h r s s' := by simp
    _ = ∑ s, w s * ∑ s', M.transition h r s s' := by
      rw [sum_comm]; simp only [mul_sum]
    _ = ∑ s, w s := by simp only [M.transition_sum,mul_one]

lemma outMass_sum (h : List (X × Fin k)) (r : X) : ∑ i, outMass M h r i=mass M h :=
  step_sum M h r _

/-- Null histories are filled by a fixed legal label, not by any future input. -/
def policy : Policy k X := fun h r =>
  if hp : 0 < mass M h then
    ⟨fun i => outMass M h r i / mass M h, by
      constructor
      · intro i; exact div_nonneg (outMass_nonneg M h r i) hp.le
      · rw [←sum_div,outMass_sum,div_self (ne_of_gt hp)]⟩
  else pureDistribution (M.nullOutput h r)

variable [MetricSpace X]

/-- The machine's literal finite expected movement, prior to forgetting its
private state. Physical configurations are determined by visible histories. -/
def machineCost (start : Configuration k X) (h : List (X × Fin k)) (s : S) :
    List X → ℝ
  | [] => 0
  | r::σ => ∑ s', M.transition h r s s' *
      (dist (configurationAfter start h (M.output h r s s')) r +
        machineCost start (h++[(r,M.output h r s s')]) s' σ)

variable [NeZero k]

/-- A null-history fallback that satisfies strong laziness at every history. -/
def lazyFallback (start : Configuration k X) (h : List (X × Fin k)) (r : X) : Fin k := by
  classical
  exact if hc : ∃ i, configurationAfter start h i=r then Classical.choose hc else 0

variable (start : Configuration k X) (V : List X → S → Configuration k X)
variable (hcover : ∀ h r s, ∃ i, V (h++[r]) s i=r)

/-- Source's matching simulation, with the entire virtual private state kept.
There is no illegal conditioning of a marginal coupling on realized ancestors. -/
def lazyMachine : Data k X S where
  initial := M.initial
  initial_nonneg := M.initial_nonneg
  initial_sum := M.initial_sum
  transition := M.transition
  transition_nonneg := M.transition_nonneg
  transition_sum := M.transition_sum
  output h r _s s' := lazyChoice (configurationAfter start h) (V (h.map Prod.fst++[r]) s') r
    (hcover (h.map Prod.fst) r s')
  nullOutput := lazyFallback start

/-- Virtual movement under exactly the same finite hidden-state experiment. -/
def virtualCost (h : List (X × Fin k)) (s : S) : List X → ℝ
  | [] => 0
  | r::σ => ∑ s', M.transition h r s s' *
      (matching (V (h.map Prod.fst) s) (V (h.map Prod.fst++[r]) s')+
        virtualCost (h++[(r,(lazyMachine M start V hcover).output h r s s')]) s' σ)

end HiddenMachine
end KServer

namespace KServer
namespace BoundedSimulation
noncomputable section
open Finset
universe u
variable {k : ℕ} [NeZero k] {X : Type u}

/-- Finite private memory, sufficient for a fixed local experiment. The final
policy is extended to all requests; compactness below removes this bound. -/
abbrev Memory (H k : ℕ) := Fin H → Fin k

def labelAt {H : ℕ} (s : Memory H k) (n : ℕ) : Fin k :=
  if h : n<H then s ⟨n,h⟩ else 0

def history {H : ℕ} (h : List X) (s : Memory H k) : List (X × Fin k) :=
  h.mapIdx (fun n r => (r,labelAt s n))

lemma history_append {H : ℕ} (h : List X) (r : X) (s : Memory H k) :
    history (h++[r]) s=history h s++[(r,labelAt s h.length)] := by
  exact List.mapIdx_concat

def update {H : ℕ} (s : Memory H k) (n : ℕ) (i : Fin k) : Memory H k := by
  classical
  exact if hn : n<H then Function.update s ⟨n,hn⟩ i else s

variable (H : ℕ) (A : Policy k X) (pre : List (X × Fin k))

def transition (h : List (X × Fin k)) (r : X) (s s' : Memory H k) : ℝ :=
  ∑ i : Fin k, if s'=update s h.length i then (A (pre++history (h.map Prod.fst) s) r).val i else 0

lemma transition_sum (h : List (X × Fin k)) (r : X) (s : Memory H k) :
    ∑ s', transition H A pre h r s s'=1 := by
  classical
  simp only [transition]
  rw [Finset.sum_comm]
  simpa using (A (pre++history (h.map Prod.fst) s) r).property.2

def machine : HiddenMachine.Data k X (Memory H k) where
  initial s := if s=(fun _=>0) then 1 else 0
  initial_nonneg _ := by split_ifs <;> norm_num
  initial_sum := by classical simp
  transition := transition H A pre
  transition_nonneg h r s s' := by
    classical
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact (A (pre++history (h.map Prod.fst) s) r).property.1 i
    · exact le_rfl
  transition_sum := transition_sum H A pre
  output _ _ _ _ := 0
  nullOutput _ _ := 0

variable (start virtualStart : Configuration k X)

def virtual (h : List X) (s : Memory H k) : Configuration k X :=
  configurationAfter virtualStart (history h s)

lemma virtual_covers (h : List X) (r : X) (s : Memory H k) :
    ∃ i, virtual H virtualStart (h++[r]) s i=r := by
  refine ⟨labelAt s h.length,?_⟩
  simp [virtual,history_append,configurationAfter_append,serve]

end
end BoundedSimulation
end KServer

namespace KServer
universe u
section Mixture
variable {k : ℕ} {X : Type u} {Ω : Type*} [Fintype Ω]
variable (w : Ω → ℝ) (hw : ∀ ω, 0  ≤  w ω) (hs : ∑ ω, w ω = 1)
variable (A : Ω → Policy k X)

def mixtureLikelihood (h : List (X × Fin k)) : ℝ :=
  ∑ ω, w ω * historyProbability (A ω) [] h

variable [NeZero k]

/-- The posterior distribution over the private mixture index is normalized
only at reached histories; all null histories receive the same fixed pure rule. -/
def mixturePolicy : Policy k X := fun h r =>
  if hpos : 0 < mixtureLikelihood w A h then
    ⟨fun i => (∑ ω, w ω * historyProbability (A ω) [] h * (A ω h r).val i) /
      mixtureLikelihood w A h, by
      constructor
      · intro i
        exact div_nonneg (Finset.sum_nonneg fun ω _ =>
          mul_nonneg (mul_nonneg (hw ω) (historyProbability_nonneg _ _ _))
            ((A ω h r).property.1 i)) hpos.le
      · rw [← Finset.sum_div, Finset.sum_comm]
        simp_rw [← Finset.mul_sum, (A _ h r).property.2, mul_one]
        exact div_self hpos.ne'⟩
  else pureDistribution 0

end Mixture

end KServer


namespace KServer
noncomputable section
open scoped BigOperators
universe u v

/-- Relabeling requests, leaving server labels unchanged. -/
def mapHistory {k : ℕ} {X : Type u} {Y : Type v} (f : X → Y)
    (h : List (X × Fin k)) : List (Y × Fin k) := h.map (fun p => (f p.1,p.2))

/-- Ambient extension by a retraction. The extension is deliberately arbitrary
on requests outside the finite submetric, while agreeing exactly on all its
histories. It is one policy, not a collection indexed by horizons. -/
def retractPolicy {k : ℕ} {X : Type u} {Y : Type v}
    (f : X → Y) (A : Policy k Y) : Policy k X :=
  fun h r => A (mapHistory f h) (f r)

/-- The exact conclusion needed from source §10's episode amplification, on
finite metrics only. This definition is an open obligation, not an assumption
asserted by the development, and is not the main theorem. -/
def FiniteDistinctLawBound (k : ℕ) (α : ℝ) : Prop :=
  ∀ (Y : Type u) (_ : MetricSpace Y) (_ : Fintype Y),
    ∀ s : Configuration k Y, Function.Injective s →
    ∀ (ι : Type) (_ : Fintype ι), ∀ σ : ι → List Y, ∀ w : ι → ℝ,
      (∀ i, 0  ≤  w i) → (∑ i, w i=1) →
      ∃ A : Policy k Y, (∑ i, w i*expectedCost A s (σ i))  ≤ 
        ∑ i, w i*(α*optimalCost s (σ i))

end
end KServer

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace KServer
universe u
namespace Episode
open Finset
variable {k : ℕ} {X : Type u} [MetricSpace X]

def traceCost (s : Configuration k X) : List (X × Fin k) → ℝ
  | [] => 0
  | (r,i)::h => dist (s i) r + traceCost (serve s i r) h

def reverseTrace (s : Configuration k X) : List (X × Fin k) → List (X × Fin k)
  | [] => []
  | (r,i)::h => reverseTrace (serve s i r) h ++ [(s i,i)]

def serviceTrace : (σ : List X) → (Fin σ.length → Fin k) → List (X × Fin k)
  | [], _ => []
  | r::σ,j => (r,j 0)::serviceTrace σ (fun i => j i.succ)

omit [MetricSpace X] in
lemma serviceTrace_requests (σ : List X) (j : Fin σ.length → Fin k) :
    (serviceTrace σ j).map Prod.fst = σ := by
  induction σ with
  | nil => rfl
  | cons r σ ih => simp only [serviceTrace,List.map_cons,ih]

/-- Pathwise strong laziness, imposed only on the trace actually selected. -/
def LazyTrace (s : Configuration k X) : List (X × Fin k) → Prop
  | [] => True
  | (r,i)::h => ((∃ j, s j=r) → s i=r) ∧ LazyTrace (serve s i r) h

def cycleTrace (s : Configuration k X) (j : Fin k → Fin k) : List (X × Fin k) :=
  List.ofFn (fun i => (s i,j i))

def resetTrace (s : Configuration k X) (ls : List (Fin k → Fin k)) :
    List (X × Fin k) := ls.flatMap (cycleTrace s)

def resetCount (k : ℕ) (Δ δ : ℝ) : ℕ := ⌊(k : ℝ)*Δ/δ⌋₊+1

end Episode
end KServer

namespace KServer
namespace Amplification
noncomputable section
open Finset
universe u
variable {k : ℕ} [NeZero k] {X : Type u} [MetricSpace X]

/-- Exact finite-input Bellman expectation of an arbitrary terminal observable.
The private action history, not only the current configuration, is retained. -/
def after (A : Policy k X) (h : List (X × Fin k)) : List X →
    (List (X × Fin k) → ℝ) → ℝ
  | [],f => f h
  | r::σ,f => ∑ i, (A h r).val i * after A (h++[(r,i)]) σ f

def cost (A : Policy k X) (s : Configuration k X)
    (h : List (X × Fin k)) (σ : List X) :=
  continuationCost A (configurationAfter s h) h σ

variable {Ω : Type} [Fintype Ω]

def lawAfter (A : Policy k X) (w : Ω → ℝ) (σ : Ω → List X)
    (h : List (X × Fin k)) (f : List (X × Fin k) → ℝ) :=
  ∑ ω, w ω * after A h (σ ω) f

def lawCost (A : Policy k X) (s : Configuration k X) (w : Ω → ℝ)
    (σ : Ω → List X) (h : List (X × Fin k)) := ∑ ω, w ω*cost A s h (σ ω)

def runCost (A : Policy k X) (s : Configuration k X) (w : Ω → ℝ)
    (ep : Ω → List X) : ℕ → List (X × Fin k) → ℝ
  | 0,_ => 0
  | N+1,h => lawCost A s w ep h+lawAfter A w ep h (runCost A s w ep N)

def iidWord (ep : Ω → List X) : (N : ℕ) → (Fin N → Ω) → List X
  | 0,_ => []
  | N+1,v => ep (v 0)++iidWord ep N (fun i=>v i.succ)

def iidWeight (w : Ω → ℝ) : (N : ℕ) → (Fin N → Ω) → ℝ
  | 0,_ => 1
  | N+1,v => w (v 0)*iidWeight w N (fun i=>v i.succ)

def iidTrace (t : Ω → List (X × Fin k)) : (N : ℕ) → (Fin N → Ω) → List (X × Fin k)
  | 0,_ => []
  | N+1,v => t (v 0)++iidTrace t N (fun i=>v i.succ)

def iidSum (q : Ω → ℝ) : (N : ℕ) → (Fin N → Ω) → ℝ
  | 0,_ => 0
  | N+1,v => q (v 0)+iidSum q N (fun i=>v i.succ)

universe v
variable {Λ : Type v} [Fintype Λ]

def pushWeights (f : Ω → Λ) (w : Ω → ℝ) : Λ → ℝ :=
  by classical exact fun y=>∑ ω, if f ω=y then w ω else 0

end
end Amplification
end KServer

namespace KServer
noncomputable section
open Finset
universe u

def FiniteDistribution (Ω : Type*) [Fintype Ω] :=
  {w : Ω → ℝ // (∀ ω, 0 ≤ w ω) ∧ ∑ ω, w ω = 1}

def FiniteLawStatement : Prop :=
  ∃ a : ℝ, ∀ (Y : Type u) (_ : MetricSpace Y) (_ : Fintype Y),
    (∃ x y : Y, x ≠ y) → ∀ k : ℕ, 2 ≤ k → ∀ s : Configuration k Y,
      ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∀ H : ℕ, ∀ law : FiniteDistribution (Fin H → Y),
        ∃ A : Policy k Y, StronglyLazy s A ∧
          (∑ σ, law.val σ * expectedCost A s (List.ofFn σ)) ≤
            a * (1 + Real.log (k + 1)) ^ 2 *
              (∑ σ, law.val σ * optimalCost s (List.ofFn σ)) + D₀


end
end KServer

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Experiments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.FiniteExperiment
attribute [local instance] Classical.propDecidable
open Finset Episode PosteriorRanks
universe u v
variable {Y : Type u} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

/-- A fixed minimizing labeled trajectory for each complete input. -/
def optimalTrace (s : Configuration k Y) (σ : Fin H → Y) : List (Y × Fin k) :=
  serviceTrace (List.ofFn σ) (optimalCost_attained s (List.ofFn σ)).choose

omit [Fintype Y] in
lemma optimalTrace_requests (s : Configuration k Y) (σ : Fin H → Y) :
    (optimalTrace s σ).map Prod.fst=List.ofFn σ :=
  serviceTrace_requests _ _

omit [Fintype Y] in
lemma optimalTrace_length (s : Configuration k Y) (σ : Fin H → Y) :
    (optimalTrace s σ).length=H := by
  simpa only [List.length_map,List.length_ofFn] using
    congrArg List.length (optimalTrace_requests s σ)

/-- The genuine hidden configuration, frozen when the finite input ends. -/
def hidden (s : Configuration k Y) (σ : Fin H → Y) (t : ℕ) : Configuration k Y :=
  configurationAfter s ((optimalTrace s σ).take t)

/-- Current designated occurrence in the selected optimum; it is not observed. -/
def mover (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) : Fin k :=
  ((optimalTrace s σ)[t.val]'(by rw [optimalTrace_length]; exact t.isLt)).2

/-- A finite observation sufficient for exactly the request requestPrefix. -/
def requestPrefix (σ : Fin H → Y) (t : ℕ) : Fin H → Option Y :=
  fun i => if i.val<t then some (σ i) else none

omit [MetricSpace Y] [Fintype Y] in
lemma prefix_refines (σ ρ : Fin H → Y) (t : ℕ)
    (h : requestPrefix σ (t+1)=requestPrefix ρ (t+1)) : requestPrefix σ t=requestPrefix ρ t := by
  funext i
  by_cases hi : i.val<t
  · have he := congrFun h i
    simpa [requestPrefix,hi,show i.val<t+1 by omega] using he
  · simp [requestPrefix,hi]

variable {T : Type v} [Fintype T]

/-- Histories include the independent partition tape from time zero. Coding a
finite observation by a natural number is injective, not a loss of information. -/
def history (t : ℕ) (ω : (Fin H → Y) × T) : ℕ :=
  (Fintype.equivFin (T × (Fin H → Option Y)) (ω.2,requestPrefix ω.1 t)).val

omit [MetricSpace Y] in
lemma history_eq_iff (t : ℕ) (ω z : (Fin H → Y) × T) :
    history t ω=history t z ↔ ω.2=z.2 ∧ requestPrefix ω.1 t=requestPrefix z.1 t := by
  unfold history
  rw [Fin.val_inj,(Fintype.equivFin _).injective.eq_iff,Prod.mk.injEq]

omit [MetricSpace Y] in
lemma history_refines (t : ℕ) (ω z : (Fin H → Y) × T)
    (h : history (t+1) ω=history (t+1) z) : history t ω=history t z := by
  rw [history_eq_iff] at h ⊢
  exact ⟨h.1,prefix_refines _ _ _ h.2⟩

/-- Literal independent product weights, before any requestPrefix is revealed. -/
def weight (law : FiniteDistribution (Fin H → Y)) (tape : FiniteDistribution T)
    (ω : (Fin H → Y) × T) : ℝ := law.val ω.1*tape.val ω.2

/-- True request history alone, for computing the metric posterior independently
of the partition tape. -/
def requestHistory (t : ℕ) (σ : Fin H → Y) : ℕ :=
  (Fintype.equivFin (Fin H → Option Y) (requestPrefix σ t)).val

/-- Counting measure of a labeled configuration; repetitions contribute separately. -/
def metricCount (c : Configuration k Y) (y : Y) : ℝ := by
  classical
  exact ∑ i : Fin k, if c i=y then 1 else 0

/-- The true-metric posterior after t requests, independent of algorithmic tapes. -/
def mu (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : ℕ) (σ : Fin H → Y) (y : Y) : ℝ :=
  posterior law.val (requestHistory t) (fun ρ => metricCount (hidden s ρ t) y) σ

/-- Old counting measure filtered through the new true request. -/
def muBefore (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : ℝ :=
  posterior law.val (requestHistory (t.val+1)) (fun ρ => metricCount (hidden s ρ t.val) y) σ

/-- The conditional old-location law of the single designated optimum mover. -/
def nu (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (y : Y) : ℝ := by
  classical
  exact posterior law.val (requestHistory (t.val+1))
    (fun ρ => if hidden s ρ t.val (mover s ρ t)=y then 1 else 0) σ

end KServer.FiniteExperiment

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Deterministic heavy-center schedule and its clipped distance profile.
Random heavy radii do not affect this schedule. -/
noncomputable section
open scoped BigOperators Classical
open Finset Set
namespace KServer.HeavyCenters

/-- The heavy profile is zero up to radius 3 and one from radius 4. -/
def ramp (u : ℝ) : ℝ := min 1 (max 0 (u-3))

variable {Y : Type*} [MetricSpace Y]

/-- Finite minimum with a default value 1, also for the empty center set. -/
def profile (r : ℝ) (C : Finset Y) (y : Y) : ℝ :=
  (insert 1 (C.image (fun a => ramp (dist a y/r)))).min' ⟨1,mem_insert_self _ _⟩

/-- Delete centers at distance at most 100r, then insert the heavy request. -/
def replace (r : ℝ) (C : Finset Y) (x : Y) : Finset Y :=
  insert x (C.filter (fun a => 100*r<dist a x))

end KServer.HeavyCenters

end


/- The finite variational pilot potential. -/

noncomputable section
open scoped BigOperators Classical
open Finset Set
namespace KServer.Pilot

structure Template where
  σ : ℝ
  R : ℝ
  L : ℝ
  σ_pos : 0 < σ
  σ_le : σ ≤ 1
  R_ge : 256 ≤ R
  L_nonneg : 0 ≤ L

def b (T : Template) (v : ℝ) : ℝ := max 0 (min 1 (2 - v / T.σ))
def a (T : Template) (v : ℝ) : ℝ :=
  if v ≤ T.R then min (v ^ 2 / T.σ ^ 2) 1
  else if v ≤ 2 * T.R then 2 - v / T.R else 0
def G (T : Template) (v : ℝ) : ℝ := max 0 (min 1 (v / (10 * T.R) - 1))

lemma G_nonneg (T : Template) (v : ℝ) : 0 ≤ G T v := le_max_left _ _
lemma G_eq_zero {T : Template} {v : ℝ} (hv : v ≤ 10 * T.R) : G T v = 0 := by
  have : v / (10 * T.R) ≤ 1 := (div_le_one (by linarith [T.R_ge])).mpr hv
  exact max_eq_left (le_trans (min_le_right _ _) (by linarith))

variable {Y : Type*} [Fintype Y] [MetricSpace Y]

def Feasible (T : Template) (r : ℝ) (z : Y → ℝ) : Prop :=
  (∀ s, 0 ≤ z s) ∧
  (∀ p, ∑ s, max (z s - G T (dist s p / r)) 0 ≤ 1) ∧
  ∀ s t, s ≠ t → dist s t < 5 * T.σ * r → z s * z t = 0

def integrand (T : Template) (r : ℝ) (g z : Y → ℝ) (p : Y) : ℝ :=
  (1 + g p) * (1 - ∑ s, z s * b T (dist s p / r)) +
    256 * ∑ s, z s * (1 + g s) * a T (dist s p / r)

def objective (T : Template) (r : ℝ) (μ g z : Y → ℝ) : ℝ :=
  r * ∑ p, μ p * integrand T r g z p

lemma feasible_zero (T : Template) (r : ℝ) : Feasible (Y := Y) T r 0 := by
  refine ⟨fun _ => le_rfl, fun p => ?_, fun _ _ _ _ => by simp⟩
  have : ∀ s : Y, max (0 - G T (dist s p / r)) 0 = 0 :=
    fun s => max_eq_right (by linarith [G_nonneg T (dist s p / r)])
  simp only [Pi.zero_apply, this, sum_const_zero, zero_le_one]

lemma coordinate_le_one {T : Template} {r : ℝ} {z : Y → ℝ}
    (hz : Feasible T r z) (s : Y) : z s ≤ 1 := by
  have hG : G T (dist s s / r) = 0 := G_eq_zero (by simp; linarith [T.R_ge])
  have hs := single_le_sum (s := (univ : Finset Y))
    (fun t _ => le_max_right (z t - G T (dist t s / r)) 0) (mem_univ s)
  rw [hG, sub_zero, max_eq_left (hz.1 s)] at hs
  exact hs.trans (hz.2.1 s)

lemma feasible_closed (T : Template) (r : ℝ) : IsClosed {z : Y → ℝ | Feasible T r z} := by
  unfold Feasible
  simp only [ofPred_and, ofPred_forall]
  refine (isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter ?_
  refine (isClosed_iInter fun p => isClosed_le ?_ continuous_const).inter ?_
  · fun_prop
  · exact isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq ((continuous_apply s).mul (continuous_apply t)) continuous_const

lemma feasible_compact (T : Template) (r : ℝ) : IsCompact {z : Y → ℝ | Feasible T r z} := by
  apply (isCompact_pi_infinite fun _ : Y => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    (feasible_closed T r)
  intro z hz s
  exact ⟨hz.1 s, coordinate_le_one hz s⟩

lemma objective_continuous (T : Template) (r : ℝ) (μ g : Y → ℝ) :
    Continuous (objective T r μ g) := by
  unfold objective integrand
  fun_prop

lemma exists_minimizer (T : Template) (r : ℝ) (μ g : Y → ℝ) :
    ∃ z, Feasible T r z ∧ IsMinOn (objective T r μ g) {z | Feasible T r z} z := by
  exact (feasible_compact T r).exists_isMinOn ⟨0, feasible_zero T r⟩
    (objective_continuous T r μ g).continuousOn

/-- A canonical tie-break using choice is legitimate on the finite input tree. -/
def minimizer (T : Template) (r : ℝ) (μ g : Y → ℝ) : Y → ℝ :=
  (exists_minimizer T r μ g).choose

def potential (T : Template) (r : ℝ) (μ g : Y → ℝ) : ℝ :=
  objective T r μ g (minimizer T r μ g)

def coefficient (T : Template) (r : ℝ) (μ g : Y → ℝ) (s : Y) : ℝ :=
  ∑ p, μ p * (256 * (1 + g s) * a T (dist s p / r) - (1 + g p) * b T (dist s p / r))

/-- Closed metric balls. -/
def ball (x : Y) (r : ℝ) : Finset Y := univ.filter fun p => dist x p ≤ r

/-- Only the near-site region in pilot-local(2) uses a strict inequality. -/
def nearBall (x : Y) (r : ℝ) : Finset Y := univ.filter fun p => dist x p < r

def mass (μ : Y → ℝ) (S : Finset Y) : ℝ := ∑ p ∈ S, μ p

/-- The clear-and-insert competitor; the clearing radius is 5D*. -/
def insertUnit (T : Template) (r : ℝ) (z : Y → ℝ) (x : Y) : Y → ℝ :=
  fun s => if s = x then 1 else if dist x s < 50 * T.R * r then 0 else z s

def nearWeight (T : Template) (r : ℝ) (z : Y → ℝ) (x : Y) : ℝ :=
  ∑ s ∈ nearBall x (T.σ * r / 4), z s

def innerMoment (μ : Y → ℝ) (x : Y) (γ r : ℝ) : ℝ :=
  ∑ p ∈ ball x (γ * r), μ p * (dist x p / r)

/-! Relocation at a concentrated request and local optimality,
including the dimension-free capacity repair competitor. -/

def relocate (T : Template) (r : ℝ) (z : Y → ℝ) (s x : Y) : Y → ℝ := fun i =>
  if i = x then z s else if i = s then 0 else
    if dist x i < 50 * T.R * r then max (z i - (dist s x / r) / (10*T.R)) 0 else z i

/-- Exact constant displayed in (6.10), with no dependence on the metric size. -/
def localConstant (T : Template) : ℝ :=
  (T.L+1024/T.σ)*(514+8/T.σ)+1024*(5+T.L)/T.σ^2

def globalConstant (T : Template) : ℝ := T.L+1026/T.σ

end KServer.Pilot


/-! Exact scale summations for pilot drift and the partition budget.
No policy or drift estimate is assumed. -/
noncomputable section
open scoped BigOperators Classical
open Finset
namespace KServer.ScaleMass


def convolution (q : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range (j+1), q^(j-i)*a i

/-- The first relative increment includes the entire first ball. -/
def increment (m : ℕ → ℝ) (i : ℕ) : ℝ := if i=0 then m 0 else m i-m (i-1)

end KServer.ScaleMass

namespace KServer.Pilot
open Finset
variable {Y : Type*} [Fintype Y] [MetricSpace Y]

/-- The coarse consecutive range, written in increasing order for moment summation. -/
def radius (r₀ τ : ℝ) (j : ℕ) : ℝ := r₀*τ^j

lemma radius_pos {r₀ τ : ℝ} (hr : 0 < r₀) (hτ : 0 < τ) (j : ℕ) :
    0 < radius r₀ τ j := mul_pos hr (pow_pos hτ j)

def innerMass (μ : Y → ℝ) (x : Y) (γ r₀ τ : ℝ) (j : ℕ) : ℝ :=
  mass μ (ball x (γ*radius r₀ τ j))


def moveMeasure (μ ν : Y → ℝ) (x : Y) (y : Y) : ℝ := μ y-ν y+if y=x then 1 else 0

def moveCost (ν : Y → ℝ) (x : Y) : ℝ := ∑ y, ν y*dist x y

def shellRatio (μ : Y → ℝ) (x : Y) (γ D r : ℝ) : ℝ :=
  mass μ (ball x (D*r)\ball x (γ*r))/mass μ (ball x (γ*r))

def momentRatio (μ : Y → ℝ) (x : Y) (γ r : ℝ) : ℝ :=
  innerMoment μ x γ r/mass μ (ball x (γ*r))

def slopeBudget (T : Template) (δ h t : ℝ) : ℝ :=
  (globalConstant T/δ+localConstant T)*min 1 h+localConstant T*t


def coarseBudget (T : Template) (γ δ k : ℝ) (p : ℕ) : ℝ :=
  (globalConstant T/δ+localConstant T)*((p:ℝ)/Real.log 2*Real.log (2*k))+
    localConstant T*(2*γ*(1+Real.log (2*k)))+8224/T.σ


def driftConstant (T : Template) (γ δ : ℝ) (p : ℕ) : ℝ :=
  2056/γ + 8224/T.σ + 2*globalConstant T*p/(δ*Real.log 2)+
    2*localConstant T*((p:ℝ)/Real.log 2+2*γ)

end KServer.Pilot

end
end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Partitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyCenters
open Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

def template : Pilot.Template where
  σ := 1
  R := 512
  L := 1
  σ_pos := by norm_num
  σ_le := le_rfl
  R_ge := by norm_num
  L_nonneg := by norm_num

/-- The exact annulus charged at a heavy update. -/
def annulus (x : Y) (r : ℝ) : Finset Y :=
  univ.filter (fun p => 3*r<dist x p ∧ dist x p ≤ 120*r)

end KServer.HeavyCenters

end


/-! The actual true-prefix heavy-center recursion of §07. All physical and
filtering steps are included in its potential budget, not only edit steps. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyCenters
open Pilot FiniteExperiment RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

def Active (r γ δ : ℝ) (C : Finset Y) (μ : Y → ℝ) (x : Y) : Prop :=
  Pilot.mass μ (Pilot.ball x (51200*r)) ≤ (1+δ)*Pilot.mass μ (Pilot.ball x (γ*r)) ∧
    ∀ a∈C,8*r<dist a x

def step (r γ δ : ℝ) (C : Finset Y) (μ : Y → ℝ) (x : Y) : Finset Y :=
  if Active r γ δ C μ x then replace r C x else C

/-- Initially empty. End-of-input states are frozen; requests before then
use the genuine posterior at the new true prefix. -/
def centers (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) : ℕ → Finset Y
  | 0 => ∅
  | t+1 => if ht : t<H then
      step r γ δ (centers s law r γ δ σ t) (mu s law (t+1) σ) (σ ⟨t,ht⟩)
    else centers s law r γ δ σ t

/-- Exact annular charge made by a real center edit, zero on non-edit steps. -/
def charge (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (t : Fin H) (σ : Fin H → Y) : ℝ :=
  if Active r γ δ (centers s law r γ δ σ t.val) (mu s law (t.val+1) σ) (σ t)
  then r*Pilot.mass (mu s law (t.val+1) σ) (annulus (σ t) r) else 0

end KServer.HeavyCenters

end


/-! Fixed labels with a cooldown are constructed by finite online coloring.
A conflict set is a deterministic collection of previously reserved records;
labels are never used as random-tape indices. This is the finite pool mechanism
of §07, not a growing historical alphabet. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OnlineLabels

variable {M : ℕ}

lemma unused_exists (s : Finset ℕ) (f : ℕ → Fin M) (hs : s.card<M) :
    ∃ c : Fin M, ∀ j ∈ s, f j≠c := by
  classical
  have hi : (s.image f).card < (univ : Finset (Fin M)).card := by
    simpa using (card_image_le.trans_lt hs)
  obtain ⟨c,_,hc⟩ := exists_mem_notMem_of_card_lt_card hi
  refine ⟨c,?_⟩
  intro j hj h
  exact hc (mem_image.mpr ⟨j,hj,h⟩)

/-- A finite coloring chosen at each insertion using only earlier colors. -/
def stage (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) : ℕ → ℕ → Fin M
  | 0 => fun _ => ⟨0,hM⟩
  | t+1 => fun j => if j=t then
      (unused_exists (conflict t) (stage hM conflict hcard t) (hcard t)).choose
      else stage hM conflict hcard t j

/-- Permanent color of a chronological record; later stages never modify it. -/
def color (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) (i : ℕ) : Fin M :=
  stage hM conflict hcard (i+1) i

end KServer.OnlineLabels

end


/-! Actual finite heavy-ball label update. Intersections in the finite metric
force reuse; otherwise the new label avoids both current and previous labels.
No region, anchor or label lifetime is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyLabels
open HeavyCenters
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

abbrev Pool (Y : Type*) [Fintype Y] := Fin (4*Fintype.card Y+4)
def overlap (C : Finset Y) (rad : Y → ℝ) (x : Y) (R : ℝ) : Finset Y :=
  C.filter (fun a => ∃ p : Y, dist a p ≤ rad a ∧ dist x p≤R)

omit [MetricSpace Y] in
lemma unused (C D : Finset Y) (label prev : Y → Pool Y) :
    ∃ i : Pool Y, i∉C.image label ∧ i∉D.image prev := by
  have hC : (C.image label).card≤Fintype.card Y := card_image_le.trans C.card_le_univ
  have hD : (D.image prev).card≤Fintype.card Y := card_image_le.trans D.card_le_univ
  have hh : (C.image label∪D.image prev).card<(univ:Finset (Pool Y)).card := by
    have hu:=card_union_le (C.image label) (D.image prev)
    simp only [card_univ,Fintype.card_fin]
    omega
  obtain ⟨i,_,hi⟩:=exists_mem_notMem_of_card_lt_card hh
  exact ⟨i,fun h=>hi (mem_union_left _ h),fun h=>hi (mem_union_right _ h)⟩

def fresh (C D : Finset Y) (label prev : Y → Pool Y) : Pool Y := (unused C D label prev).choose

def insertedLabel (C D : Finset Y) (rad : Y → ℝ) (label prev : Y → Pool Y) (x : Y) (R : ℝ) : Pool Y :=
  if h:(overlap C rad x R).Nonempty then label h.choose else fresh C D label prev

def updatedLabel (C D : Finset Y) (rad : Y → ℝ) (label prev : Y → Pool Y) (x : Y) (R : ℝ) : Y → Pool Y :=
  Function.update label x (insertedLabel C D rad label prev x R)

end KServer.HeavyLabels

end


/-! Exact truncated exponential tails and first-hit cancellation used by the
chronological finite-law partition construction, manuscript §07.  The radius
law is not replaced by a uniform/padded law: `tail` is its exact tail. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PartitionProbabilities

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Normalized clipped position in the source radius interval `[r,2*r]`. -/
def position (r a : ℝ) : ℝ := min (max (a/r-1) 0) 1

lemma position_range (r a : ℝ) : position r a ∈ Set.Icc (0:ℝ) 1 := by
  dsimp [position]
  exact ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

lemma position_mono {r : ℝ} (hr : 0 < r) : Monotone (position r) := by
  intro a b hab
  exact min_le_min_right _ (max_le_max_right _ (sub_le_sub_right (div_le_div_of_nonneg_right hab hr.le) _))

/-- The exact tail of the density in eq. tier-radius-density.  The clipped
formula includes both support endpoints (which have zero atom). -/
def tail (lam r a : ℝ) : ℝ :=
  (Real.exp (lam*(1-position r a))-1)/(Real.exp lam-1)

lemma tail_range {lam : ℝ} (hlam : 0 < lam) (r a : ℝ) :
    tail lam r a ∈ Set.Icc (0:ℝ) 1 := by
  have he : 0 < Real.exp lam-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam)
  have hu := position_range r a
  have hlow : 1 ≤ Real.exp (lam*(1-position r a)) := Real.one_le_exp (by nlinarith [hu.2])
  have hup : Real.exp (lam*(1-position r a)) ≤ Real.exp lam :=
    Real.exp_le_exp.mpr (by nlinarith [hu.1])
  exact ⟨div_nonneg (by linarith) he.le, (div_le_one he).mpr (by linarith)⟩

lemma tail_antitone {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) : Antitone (tail lam r) := by
  intro a b hab
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr (Real.one_le_exp hlam.le))
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (position_mono hr hab) _) hlam.le

lemma position_of_le {r a : ℝ} (hr : 0 < r) (ha : a ≤ r) : position r a=0 := by
  have h : a/r-1 ≤ 0 := by have := (div_le_one hr).mpr ha; linarith
  simp [position,max_eq_right h]

lemma tail_of_le {lam r a : ℝ} (hlam : 0 < lam) (hr : 0 < r) (ha : a ≤ r) :
    tail lam r a=1 := by
  simp [tail,position_of_le hr ha,ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam))]

section FiniteProduct
variable {I : Type*} [Fintype I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]

/-- Literal independent product tape; independence is proved by multiplication,
not postulated as an assumption about adaptive states. -/
def productWeight (w : ∀ i, Ω i → ℝ) (o : ∀ i, Ω i) : ℝ := ∏ i, w i (o i)

def probability (w : ∀ i, Ω i → ℝ) (event : (∀ i, Ω i) → Prop) : ℝ := by
  classical
  exact ∑ o, if event o then productWeight w o else 0

omit [∀ i, Fintype (Ω i)] in
lemma productWeight_nonneg {w : ∀ i, Ω i → ℝ} (hw : ∀ i a, 0 ≤ w i a)
    (o : ∀ i, Ω i) : 0 ≤ productWeight w o := prod_nonneg fun i _ => hw i (o i)

lemma productWeight_sum (w : ∀ i, Ω i → ℝ) (hw : ∀ i, ∑ a, w i a=1) :
    ∑ o, productWeight w o=1 := by
  classical
  simp only [productWeight, ← Fintype.prod_sum]
  simp [hw]

end FiniteProduct

section FirstSeparation
variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)]

/-- Exactly the source separating-first-hit event in chronological order. -/
def firstSeparation (hit sep : ∀ i, Ω i → Prop) (o : ∀ i, Ω i) : Prop :=
  ∃ i, sep i (o i) ∧ ∀ j, j < i → ¬hit j (o j)

def firstAt (hit sep : ∀ i, Ω i → Prop) (i : Fin n) (o : ∀ i, Ω i) : Prop :=
  sep i (o i) ∧ ∀ j, j < i → ¬hit j (o j)

end FirstSeparation

end KServer.PartitionProbabilities

end


/-! Finite inverse-tail sampling for the chronological tape. It applies both
to retirement ages and to the finitely many observable radius thresholds. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteSurvival

/-- A finite lifetime `d` is alive at ages `0,...,d`. -/
def weight (s : ℕ → ℝ) {N : ℕ} (d : Fin N) : ℝ := s d-s (d+1)

def probability {N : ℕ} (s : ℕ → ℝ) (E : Fin N → Prop) : ℝ := by
  classical
  exact ∑ d, if E d then weight s d else 0

lemma weight_nonneg {s : ℕ → ℝ} (hs : Antitone s) {N : ℕ} (d : Fin N) :
    0 ≤ weight s d := sub_nonneg.mpr (hs (Nat.le_succ _))

lemma weight_sum (s : ℕ → ℝ) (N : ℕ) : ∑ d : Fin N, weight s d=s 0-s N := by
  unfold weight
  rw [Fin.sum_univ_eq_sum_range (fun i => s i-s (i+1)), sum_range_sub']

end KServer.FiniteSurvival

end


/-! Finite discretization of the manuscript's truncated exponential radius.
All pairwise-distance decisions are included in a finite ordered grid; its
literal tail law yields a finite tape, without invoking assumed independence. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteRadius
open PartitionProbabilities FiniteSurvival
attribute [local instance] Classical.propDecidable Classical.decEq

def grid (D : Finset ℝ) (r : ℝ) : Finset ℝ := insert r (insert (2*r) (D.filter (fun a=>r≤a ∧ a≤2*r)))

lemma grid_pos (D : Finset ℝ) (r : ℝ) : 0<(grid D r).card :=
  card_pos.mpr ⟨r,mem_insert_self _ _⟩

def point (D : Finset ℝ) (r : ℝ) (i : Fin (grid D r).card) : ℝ :=
  ((grid D r).orderIsoOfFin rfl i).val

lemma point_mono (D : Finset ℝ) (r : ℝ) : StrictMono (point D r) :=
  ((grid D r).orderEmbOfFin rfl).strictMono

lemma point_range (D : Finset ℝ) {r : ℝ} (hr : 0 < r) (i : Fin (grid D r).card) :
    point D r i∈Set.Icc r (2*r) := by
  have hi : point D r i∈grid D r := ((grid D r).orderIsoOfFin rfl i).property
  change point D r i∈insert r (insert (2*r) (D.filter (fun a=>r≤a ∧ a≤2*r))) at hi
  simp only [mem_insert,mem_filter] at hi
  rcases hi with he|he|⟨_,he⟩
  · rw [he]; exact ⟨le_rfl,by linarith⟩
  · rw [he]; exact ⟨by linarith,le_rfl⟩
  · exact he

lemma point_zero (D : Finset ℝ) {r : ℝ} (hr : 0 < r) :
    point D r ⟨0,grid_pos D r⟩=r := by
  let i:=((grid D r).orderIsoOfFin rfl).symm ⟨r,mem_insert_self _ _⟩
  have he : point D r i=r := congrArg Subtype.val (((grid D r).orderIsoOfFin rfl).apply_symm_apply _)
  have hm:point D r ⟨0,grid_pos D r⟩≤point D r i := (point_mono D r).monotone (Nat.zero_le _)
  exact le_antisymm (hm.trans_eq he) (point_range D hr _).1

def survival (D : Finset ℝ) (lam r : ℝ) (a : ℕ) : ℝ :=
  if ha:a<(grid D r).card then tail lam r (point D r ⟨a,ha⟩) else 0

lemma survival_zero (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0 < r) :
    survival D lam r 0=1 := by
  rw [survival, dite_eq_left (grid_pos D r),point_zero D hr]
  exact tail_of_le hlam hr le_rfl

lemma survival_last (D : Finset ℝ) (lam r : ℝ) :
    survival D lam r (grid D r).card=0 := by simp [survival]

lemma survival_nonneg (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (a : ℕ) :
    0 ≤ survival D lam r a := by
  unfold survival; split_ifs
  · exact (tail_range hlam _ _).1
  · rfl

lemma survival_antitone (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0 < r) :
    Antitone (survival D lam r) := by
  intro a b hab
  by_cases hb:b<(grid D r).card
  · have ha:a<(grid D r).card := lt_of_le_of_lt hab hb
    rw [survival,dite_eq_left hb,survival,dite_eq_left ha]
    exact tail_antitone hlam hr ((point_mono D r).monotone hab)
  · rw [survival,dite_eq_right hb]
    exact survival_nonneg D hlam a

/-- Weights of the actual finite radius outcome. -/
def weights (D : Finset ℝ) (lam r : ℝ) (i : Fin (grid D r).card) : ℝ :=
  weight (survival D lam r) i

lemma weights_nonneg (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0 < r)
    (i : Fin (grid D r).card) : 0≤weights D lam r i :=
  weight_nonneg (survival_antitone D hlam hr) i

lemma weights_sum (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0 < r) :
    ∑ i,weights D lam r i=1 := by
  change (∑ i : Fin (grid D r).card,weight (survival D lam r) i)=1
  rw [weight_sum,survival_zero D hlam hr,survival_last]
  norm_num

end KServer.FiniteRadius

end


/-! Finite realization of the uniform heavy-ball radii. The finite grid
preserves every relevant metric threshold, hence its law is exact for balls. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteUniform
open FiniteRadius FiniteSurvival
attribute [local instance] Classical.propDecidable Classical.decEq

def tail (r a : ℝ) : ℝ := max 0 (min 1 ((2*r-a)/r))

lemma tail_nonneg (r a : ℝ) : 0 ≤ tail r a := le_max_left _ _
lemma tail_of_le {r a : ℝ} (hr : 0 < r) (ha : a ≤ r) : tail r a=1 := by
  have hh : 1≤(2*r-a)/r := (le_div_iff₀ hr).mpr (by linarith)
  simp [tail,min_eq_left hh]
lemma tail_antitone {r : ℝ} (hr : 0 < r) : Antitone (tail r) := by
  intro a b hab
  exact max_le_max_left _ (min_le_min_left _ (div_le_div_of_nonneg_right (by linarith) hr.le))

def survival (D : Finset ℝ) (r : ℝ) (a : ℕ) : ℝ :=
  if ha:a<(grid D r).card then tail r (point D r ⟨a,ha⟩) else 0
lemma survival_zero (D : Finset ℝ) {r : ℝ} (hr : 0 < r) : survival D r 0=1 := by
  rw [survival,dite_eq_left (grid_pos D r),point_zero D hr]
  exact tail_of_le hr le_rfl
lemma survival_last (D : Finset ℝ) (r : ℝ) : survival D r (grid D r).card=0 := by simp [survival]
lemma survival_nonneg (D : Finset ℝ) (r : ℝ) (a : ℕ) : 0 ≤ survival D r a := by
  unfold survival; split_ifs
  · exact tail_nonneg _ _
  · rfl
lemma survival_antitone (D : Finset ℝ) {r : ℝ} (hr : 0 < r) : Antitone (survival D r) := by
  intro a b hab
  by_cases hb:b<(grid D r).card
  · have ha:a<(grid D r).card := lt_of_le_of_lt hab hb
    rw [survival,dite_eq_left hb,survival,dite_eq_left ha]
    exact tail_antitone hr ((point_mono D r).monotone hab)
  · rw [survival,dite_eq_right hb]
    exact survival_nonneg D r a

def weights (D : Finset ℝ) (r : ℝ) (i : Fin (grid D r).card) : ℝ := weight (survival D r) i
lemma weights_nonneg (D : Finset ℝ) {r : ℝ} (hr : 0 < r) (i : Fin (grid D r).card) :
    0≤weights D r i := weight_nonneg (survival_antitone D hr) i
lemma weights_sum (D : Finset ℝ) {r : ℝ} (hr : 0 < r) : ∑ i,weights D r i=1 := by
  change (∑ i : Fin (grid D r).card,weight (survival D r) i)=1
  rw [weight_sum,survival_zero D hr,survival_last]
  norm_num

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]
def thresholds (r : ℝ) : Finset ℝ := univ.image (fun p : Y×Y=>(dist p.1 p.2-12*r)/4)
abbrev Outcome (Y : Type*) [Fintype Y] [PseudoMetricSpace Y] (r : ℝ) := Fin (grid (thresholds (Y:=Y) r) r).card
def radius (r : ℝ) (i : Outcome Y r) : ℝ := 4*point (thresholds (Y:=Y) r) r i+12*r
def law (r : ℝ) (i : Outcome Y r) : ℝ := weights (thresholds (Y:=Y) r) r i
lemma law_nonneg {r : ℝ} (hr : 0 < r) (i : Outcome Y r) : 0≤law r i := weights_nonneg _ hr i
lemma law_sum {r : ℝ} (hr : 0 < r) : (∑ i : Outcome Y r,law r i)=1 := weights_sum _ hr

def separates (r : ℝ) (c x y : Y) (i : Outcome Y r) : Prop :=
  (dist c x ≤ radius r i ∧ radius r i<dist c y) ∨
  (dist c y ≤ radius r i ∧ radius r i<dist c x)
end KServer.FiniteUniform

end


/-! The literal causal heavy-ball radii/labels recursion on the constructed
finite tape. The center schedule is the actual true-prefix pilot schedule. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavySchedule
open HeavyCenters HeavyLabels FiniteExperiment
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

structure Data (Y : Type*) [Fintype Y] where
  rad : Y → ℝ
  label : Y → Pool Y
  previous : Y → Pool Y

def initial (Y : Type*) [Fintype Y] (r : ℝ) : Data Y :=
  ⟨fun _=>16*r,fun _=>⟨0,by omega⟩,fun _=>⟨0,by omega⟩⟩

def run (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) (r γ δ : ℝ)
    (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r) : ℕ → Data Y
  | 0 => initial Y r
  | t+1 =>
    let old:=run s law r γ δ σ tape t
    if ht:t<H then
      let x:=σ ⟨t,ht⟩
      let C:=centers s law r γ δ σ t
      if Active r γ δ C (mu s law (t+1) σ) x then
        let R:=FiniteUniform.radius r (tape ⟨t,ht⟩)
        ⟨Function.update old.rad x R,
          updatedLabel C (centers s law r γ δ σ (t-1)) old.rad old.label old.previous x R,
          old.label⟩
      else ⟨old.rad,old.label,old.label⟩
    else ⟨old.rad,old.label,old.label⟩

def birth (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) (r γ δ : ℝ)
    (σ : Fin H → Y) : ℕ → Y → Option (Fin H)
  | 0 => fun _=>none
  | t+1 => if ht:t<H then
      if Active r γ δ (centers s law r γ δ σ t) (mu s law (t+1) σ) (σ ⟨t,ht⟩)
      then Function.update (birth s law r γ δ σ t) (σ ⟨t,ht⟩) (some ⟨t,ht⟩)
      else birth s law r γ δ σ t
    else birth s law r γ δ σ t

end KServer.HeavySchedule

end


/-! Exact finite ball laws for the metric thresholds used in §07.  Their
chronological first-hit estimate uses the constructed product law, not an
independence premise about a posterior filtration. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteBallLaw
open PartitionProbabilities FiniteRadius
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]

def thresholds : Finset ℝ := univ.image (fun p : Y×Y => dist p.1 p.2)

abbrev Outcome (Y : Type*) [Fintype Y] [PseudoMetricSpace Y] (r : ℝ) :=
  Fin (grid (thresholds (Y:=Y)) r).card

def radius (r : ℝ) (i : Outcome Y r) : ℝ := point (thresholds (Y:=Y)) r i

def law (lam r : ℝ) (i : Outcome Y r) : ℝ := weights (thresholds (Y:=Y)) lam r i

lemma law_nonneg {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (i : Outcome Y r) :
    0 ≤ law lam r i := weights_nonneg _ hlam hr i

lemma law_sum {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) :
    (∑ i : Outcome Y r, law lam r i)=1 := weights_sum _ hlam hr

def hit (r : ℝ) (c x y : Y) (i : Outcome Y r) : Prop :=
  dist c x ≤ radius r i ∨ dist c y ≤ radius r i

def separates (r : ℝ) (c x y : Y) (i : Outcome Y r) : Prop :=
  (dist c x ≤ radius r i ∧ radius r i < dist c y) ∨
  (dist c y ≤ radius r i ∧ radius r i < dist c x)

end KServer.FiniteBallLaw

end


/- Chronological rosters retain insertion times rather than surviving random balls. The tests are independent of the partition tape, and young records reserve slots. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological

variable {Y : Type*} [MetricSpace Y]

/-- Number of later insertions in the fixed-radius neighbourhood of an entry. -/
def age (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (i : ℕ) : ℕ := by
  classical
  exact (I.filter fun j => i < j ∧ dist (center i) (center j) ≤ R).card

/-- Chronological, not surviving, entries below an age cutoff. -/
def young (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (A : ℕ) : Finset ℕ := by
  classical
  exact I.filter fun i => age center I R i < A

lemma mem_young (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (A i : ℕ) :
    i ∈ young center I R A ↔ i ∈ I ∧ age center I R i < A := by
  classical
  simp [young]

/-- Actual age-count lemma. No independence or surviving-record assumption is
used, and repeated centers are allowed. -/
theorem local_age_count (center : ℕ → Y) (I S : Finset ℕ) (R : ℝ) (A : ℕ)
    (hSI : S ⊆ I) (hyoung : ∀ i ∈ S, age center I R i < A)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, dist (center i) (center j) ≤ R) :
    S.card ≤ A := by
  classical
  by_cases hS : S.Nonempty
  · let i := S.min' hS
    have hi : i ∈ S := min'_mem _ _
    have hcover : S.erase i ⊆ I.filter (fun j => i < j ∧ dist (center i) (center j) ≤ R) := by
      intro j hj
      obtain ⟨hji,hj⟩ := mem_erase.mp hj
      refine mem_filter.mpr ⟨hSI hj,?_,hdiam i hi j hj⟩
      have hij := min'_le S j hj
      change i ≤ j at hij
      omega
    have hb := card_le_card hcover
    change (S.erase i).card ≤ age center I R i at hb
    have he := card_erase_add_one hi
    have ha := hyoung i hi
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/-- The exact test in the manuscript. Its input is a qualifying request,
not a condition involving lifetimes, radii, allocation, or rounding. -/
def insertTest (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (K t : ℕ)
    (qualifies : Prop) : Prop :=
  qualifies ∧ ¬ ∃ i ∈ I, age center I (20*r) i < K ∧ dist (center i) (center t) ≤ r/2

/-- Chronological insertion history after `t` requests. `qualifies` will be
computed from the actual true-prefix posterior and the fixed tier parameter. -/
def schedule (request : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) : ℕ → Finset ℕ
  | 0 => ∅
  | t+1 => by
      classical
      let I := schedule request r K qualifies t
      exact if insertTest request I r K t (qualifies t) then insert t I else I

/-- Reservation count for the complete chronological roster, by applying the
local bound separately to each center in the finite metric. -/
theorem reserved_count [Fintype Y] (center : ℕ → Y) (I : Finset ℕ) {R : ℝ}
    (hR : 0 ≤ R) (A : ℕ) : (young center I R A).card ≤ Fintype.card Y * A := by
  classical
  let S := young center I R A
  have hlocal (y : Y) : (S.filter fun i => center i = y).card ≤ A := by
    apply local_age_count center I _ R A
    · intro i hi
      exact ((mem_young center I R A i).mp (mem_filter.mp hi).1).1
    · intro i hi
      exact ((mem_young center I R A i).mp (mem_filter.mp hi).1).2
    · intro i hi j hj
      have hi' := (mem_filter.mp hi).2
      have hj' := (mem_filter.mp hj).2
      rw [hi',hj',dist_self]
      exact hR
  calc S.card = ∑ y : Y, (S.filter fun i => center i = y).card := by
        symm
        simpa using sum_card_fiberwise_eq_card_filter S univ center
       _ ≤ ∑ _y : Y, A := sum_le_sum fun y _ => hlocal y
       _ = Fintype.card Y * A := by simp

end KServer.Chronological

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SparseFirstHit
open PartitionProbabilities FiniteBallLaw Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [Fintype Y] [MetricSpace Y] {H : ℕ}

def candidates (r : ℝ) (center : Fin H → Y) (present : Fin H → Prop) (x y : Y) : Finset (Fin H) :=
  univ.filter fun i => present i ∧ min (dist (center i) x) (dist (center i) y) ≤ 2*r

end KServer.SparseFirstHit

end


/-! The distinct actual and auxiliary lifetimes of §07.  These estimates are
uniform in the horizon and in every fixed chronological insertion schedule.
Compulsory-retirement tails are unconditional, as required by the source. -/
noncomputable section
open scoped BigOperators
namespace KServer.RosterLifetimes

/-- Survival through `N` independent retirement trials of rate `q`. -/
def survive (q : ℝ) (N : ℕ) : ℝ := (1-q)^N

lemma survive_range {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) (N : ℕ) :
    survive q N ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨pow_nonneg (by linarith [hq.2]) _, ?_⟩
  exact pow_le_one₀ (by linarith [hq.2]) (by linarith [hq.1])

lemma survive_mono {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) : Antitone (survive q) := by
  intro M N hMN
  exact pow_le_pow_of_le_one (by linarith [hq.2]) (by linarith [hq.1]) hMN

/-- Actual lifetime: ages 0,...,K-1 certain, trials K,...,K²-1,
compulsory retirement at K². -/
def actualPresence (K a : ℕ) : ℝ :=
  if a<K then 1 else if a<K^2 then survive (1/K) (a-K+1) else 0

/-- Auxiliary short lifetime: a trial on each positive age increment,
compulsory retirement at K.  It does not define the actual partition. -/
def shortPresence (K a : ℕ) : ℝ :=
  if a<K then survive (1/Real.sqrt K) a else 0

lemma actual_guaranteed {K a : ℕ} (ha : a<K) : actualPresence K a=1 := by
  simp [actualPresence,ha]

lemma actual_cutoff {K a : ℕ} (ha : K^2 ≤ a) : actualPresence K a=0 := by
  have hK : K ≤ K^2 := by nlinarith [Nat.zero_le K]
  simp [actualPresence,not_lt.mpr (hK.trans ha),not_lt.mpr ha]

end KServer.RosterLifetimes

end


/-! Literal actual roster lifetime tape, separate from the auxiliary short
roster.  Every construction below is finite at the prescribed horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open RosterLifetimes FiniteSurvival Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

lemma rate_range {K : ℕ} (hK : 1 ≤ K) : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  exact ⟨by positivity,(div_le_one (by linarith)).mpr hk⟩

lemma survival_range {K : ℕ} (hK : 1 ≤ K) (a : ℕ) : actualPresence K a ∈ Set.Icc (0:ℝ) 1 := by
  unfold actualPresence
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact survive_range (rate_range hK) _
  · exact ⟨le_rfl,zero_le_one⟩

lemma survival_antitone {K : ℕ} (hK : 1 ≤ K) : Antitone (actualPresence K) := by
  intro a b hab
  by_cases hb : b < K
  · rw [actual_guaranteed hb,actual_guaranteed (lt_of_le_of_lt hab hb)]
  · by_cases hcut : K^2 ≤ b
    · rw [actual_cutoff hcut]
      exact (survival_range hK a).1
    · by_cases ha : a < K
      · rw [actual_guaranteed ha]
        exact (survival_range hK b).2
      · have hac : a < K^2 := lt_of_le_of_lt hab (lt_of_not_ge hcut)
        simp only [actualPresence,ite_eq_right hb,ite_eq_left (lt_of_not_ge hcut),ite_eq_right ha,ite_eq_left hac]
        exact survive_mono (rate_range hK) (by omega)

abbrev Lifetime (K : ℕ) := Fin (K^2)

def lifetimeLaw (K : ℕ) (d : Lifetime K) : ℝ := weight (actualPresence K) d

lemma lifetime_nonneg {K : ℕ} (hK : 1 ≤ K) (d : Lifetime K) : 0 ≤ lifetimeLaw K d :=
  weight_nonneg (survival_antitone hK) d

lemma lifetime_sum {K : ℕ} (hK : 1 ≤ K) : ∑ d : Lifetime K, lifetimeLaw K d=1 := by
  change (∑ d : Fin (K^2), weight (actualPresence K) d)=1
  rw [weight_sum,actual_guaranteed (lt_of_lt_of_le Nat.zero_lt_one hK),actual_cutoff le_rfl]
  norm_num

/-- Certain initial ages are included even on zero-weight tape outcomes; this
makes deterministic coverage a pathwise property, not just an almost-sure one. -/
def alive (K a : ℕ) (d : Lifetime K) : Prop := a<K ∨ a≤(d:ℕ)

variable {Y : Type*} [MetricSpace Y] {H K : ℕ}

def present (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (tape : Fin H → Lifetime K) (i : Fin H) : Prop :=
  (i:ℕ)∈I ∧ alive K (age center I (20*r) i) (tape i)

section Radius
variable [Fintype Y]

def covered (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) (i : Fin H) : Prop :=
  present center I r life i ∧ dist (center i) x ≤ radius r (radii i)

def first (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) : Option (Fin H) :=
  let C:=univ.filter (covered center I r life radii x)
  if h:C.Nonempty then some (C.min' h) else none

end Radius
end KServer.ActualRoster

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Rosters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Heavy keys of the constructed finite schedule and their exact full-input
spatial estimate; label reuse does not impose or assume a probability law. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyKeys
open HeavyCenters HeavySchedule HeavyLabels FiniteExperiment PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

def hits (C : Finset Y) (rad : Y → ℝ) (x : Y) : Finset Y :=
  C.filter (fun a=>dist a x ≤ rad a)

def centerKey (C : Finset Y) (rad : Y → ℝ) (x : Y) : Option Y :=
  if h:(hits C rad x).Nonempty then some h.choose else none

def candidates (C : Finset Y) (r : ℝ) (x y : Y) : Finset Y :=
  C.filter (fun a=>dist a x≤20*r ∨ dist a y≤20*r)

variable [Fintype Y] {k H : ℕ} [NeZero k]

def key (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r) (t : ℕ) (x : Y) :
    Option (Pool Y) :=
  (centerKey (centers s law r γ δ σ t) (run s law r γ δ σ tape t).rad x).map
    (run s law r γ δ σ tape t).label

end KServer.HeavyKeys

end


/-! Finite independent short-lifetime expectations used only for the pilot
profile in §07. No adaptive independence is postulated: all equalities below
are identities of finite product sums. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RosterExpectation
open PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]

/-- Bernoulli weights, with `true` denoting that the record survives. -/
def bernoulli (q : ℝ) (b : Bool) : ℝ := if b then q else 1-q

/-- Finite minimum of the clipped ramps, with value 1 for an empty roster. -/
def minimum (v : I → ℝ) (a : I → Bool) : ℝ :=
  (insert 1 ((univ.filter (fun i=>a i=true)).image v)).min' ⟨1,mem_insert_self _ _⟩

/-- Expected ramp under independent survival probabilities. -/
def profile (q v : I → ℝ) : ℝ := ∑ a,productWeight (fun i=>bernoulli (q i)) a*minimum v a

end KServer.RosterExpectation

end


/-! The genuine deterministic expected short-roster profile in §07, on the
finite preallocated set of insertion ordinals. The auxiliary lifetimes are
not the actual partition lifetimes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ShortRoster
open Chronological RosterLifetimes
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Exact increasing clipped ramp on [1/8,1/4]. -/
def ramp (u : ℝ) : ℝ := min 1 (max 0 (8*u-1))

variable {Y : Type*} [MetricSpace Y] {H : ℕ}

def probability (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (i : Fin H) : ℝ :=
  if (i:ℕ)∈S then shortPresence K (age request S (20*r) i) else 0

def values (request : ℕ → Y) (r : ℝ) (p : Y) (i : Fin H) : ℝ := ramp (dist (request i) p/r)

def profile (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (p : Y) : ℝ :=
  RosterExpectation.profile (probability (H := H) request r K S) (values request r p)

/-- Death trials for one actual age increment, including the compulsory
cutoff. Already absent records are assigned probability zero. -/
def death (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (t : Fin H) (i : Fin H) : ℝ :=
  if (i:ℕ)∈S ∧ age request S (20*r) i<K ∧ dist (request i) (request t) ≤ 20*r
  then if age request S (20*r) i+1<K then 1/Real.sqrt K else 1 else 0

/-- Compulsory candidates that can actually affect the ramp at a test point. -/
def compulsory (request : ℕ → Y) (r : ℝ) (K : ℕ) (S : Finset ℕ) (p : Y) : Finset (Fin H) :=
  univ.filter (fun i=>(i:ℕ)∈S ∧ age request S (20*r) i=K-1 ∧ dist (request i) p < r/4)

end KServer.ShortRoster

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Tiers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Analytic insertion gain for the second compact pilot under the profile hypotheses. -/


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [Fintype Y] [MetricSpace Y] [DecidableEq Y]

/-- The finite region whose mass is charged by one real tier insertion. -/
def tierRegion (T : Template) (r γ δ : ℝ) (μ : Y → ℝ) (x : Y) : Finset Y :=
  if mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γ*r)) then
    ball x (51200*r) \ ball x (γ*r)
  else ball x (100*T.R*r)

end KServer.Pilot

end


/-! The actual adapted chronological tier process and its all-step compact
pilot payment. No conditional drift or unconstructed roster is postulated. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.TierProcess
open FiniteExperiment RankTracking PosteriorRanks Pilot Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]
variable {k H : ℕ} [NeZero k]

def request (s : Configuration k Y) (σ : Fin H → Y) (t : ℕ) : Y :=
  if ht : t<H then σ ⟨t,ht⟩ else s 0

def qualifies (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (σ : Fin H → Y) (t : ℕ) : Prop :=
  t<H ∧ mass (mu s law (t+1) σ) (ball (request s σ t) (100*T.R*r))≤
    Real.exp h*mass (mu s law (t+1) σ) (ball (request s σ t) (γ*r))

def roster (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) : Finset ℕ :=
  schedule (request s σ) r K (qualifies s law T r γ h σ) t

def profile (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) (p : Y) : ℝ :=
  ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γ h K σ t) p

/-- The genuine insertion mass W of the manuscript, zero on noninsertions. -/
def charge (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γH γL δ h : ℝ) (K : ℕ) (t : Fin H) (σ : Fin H → Y) : ℝ :=
  if insertTest (request s σ) (roster s law T r γL h K σ t) r K t
    (qualifies s law T r γL h σ t)
  then r*mass (mu s law (t.val+1) σ) (tierRegion T r γH δ (mu s law (t.val+1) σ) (σ t)) else 0

end KServer.TierProcess

end


/-! Fixed absolute tier parameters and the weighted insertion estimate.
The roster remains the chronological finite-law
roster, not a family satisfying a hypothetical insertion bound. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.TierProcess
open FiniteExperiment RankTracking PosteriorRanks Pilot Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

def tierTemplate : Template where
  σ := 1/1048576
  R := 204800
  L := 8
  σ_pos := by norm_num
  σ_le := by norm_num
  R_ge := by norm_num
  L_nonneg := by norm_num

def heavyGamma : ℝ := 1/1024
def heavyDelta : ℝ := 1/8192
def tierGamma : ℝ := 1/1073741824
def tierDelta : ℝ := 1/8192

def tierK (h : ℝ) : ℕ := ⌈Real.exp (64*h)⌉₊

lemma tierK_exp (h : ℝ) : Real.exp (64*h)≤(tierK h:ℝ) := Nat.le_ceil _

lemma exp_one_ge_two : (2:ℝ)≤Real.exp 1 := by
  have hh:=Real.add_one_le_exp (1:ℝ)
  linarith

lemma tierK_ge_two {h : ℝ} (hh : 1≤h) : 2≤tierK h := by
  have he : (2:ℝ)≤Real.exp (64*h) := exp_one_ge_two.trans (Real.exp_le_exp.mpr (by linarith))
  exact_mod_cast he.trans (tierK_exp h)

variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]
variable {k H : ℕ} [NeZero k]

/-- The constant is shared by all tiers; the overlap integer is fixed. -/
def tierDrift : ℝ := driftConstant tierTemplate tierGamma tierDelta 60

end KServer.TierProcess

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

variable [Fintype Y]

def reserved (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) : Finset ℕ :=
  young center (schedule center r K qualifies t) (20*r) (K^2)

lemma reserved_card (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) :
    (reserved center r K qualifies t).card ≤ Fintype.card Y*K^2 :=
  reserved_count center _ (by positivity) _

/-- Reservation is deterministic and persists even after a random retirement.
The previous prefix is also excluded, giving the stipulated one-step cooldown. -/
def conflicts (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) : Finset ℕ :=
  reserved center r K qualifies t ∪ reserved center r K qualifies (t-1)

def pool (Y : Type*) [Fintype Y] (K : ℕ) : ℕ := 4*(Fintype.card Y*K^2)+4

omit [MetricSpace Y] in
lemma pool_pos (K : ℕ) : 0<pool Y K := by dsimp [pool]; omega

lemma conflicts_card (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) :
    (conflicts center r K qualifies t).card<pool Y K := by
  have h := card_union_le (reserved center r K qualifies t) (reserved center r K qualifies (t-1))
  have h1 := reserved_card center hr K qualifies t
  have h2 := reserved_card center hr K qualifies (t-1)
  dsimp [conflicts,pool]
  omega

/-- Actual permanent record labels in the finite source pool. -/
def label (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (K : ℕ) (qualifies : ℕ → Prop) (i : ℕ) : Fin (pool Y K) :=
  OnlineLabels.color (pool_pos K) (conflicts center r K qualifies) (conflicts_card center hr K qualifies) i

end KServer.Chronological

end


/-! Present chronological balls, permanent finite-pool labels and actual
anchors. These are literal constructed keys, not assumed partitions. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierKeys
open Chronological ActualRoster FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

def key (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (K : ℕ) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y) :
    Option (Fin (pool Y K)) :=
  (first center (schedule center r K q t) r life rad x).map
    (fun i : Fin H=>Chronological.label center hr K q i)

variable [Nonempty Y]

def anchor (center : ℕ → Y) {r : ℝ} (hr : 0 ≤ r) (K : ℕ) (q : ℕ → Prop)
    (t : ℕ) (a : Fin (pool Y K)) : Y :=
  if he : ∃ i∈reserved center r K q t,Chronological.label center hr K q i=a
  then center he.choose else Classical.arbitrary Y

end KServer.TierKeys

end


/-! Fixed finite precedence alphabets: literal selection of the first covering
structure, with singleton fallback. This is the coordinate map in §07. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I Y : Type*} [Fintype I] [LinearOrder I] {A : I → Type*}

def covered (key : (i:I) → Y → Option (A i)) (x : Y) : Finset I :=
  univ.filter (fun i=>key i x≠none)

def selected (key : (i:I) → Y → Option (A i)) (x : Y) : Option (Sigma A) :=
  if h:(covered key x).Nonempty then
    let i:=(covered key x).min' h
    (key i x).map (fun a=>⟨i,a⟩)
  else none

def key (keys : (i:I) → Y → Option (A i)) (x : Y) : Sigma A ⊕ Y :=
  match selected keys x with
  | some z=>Sum.inl z
  | none=>Sum.inr x

variable [MetricSpace Y]

def anchor (anchors : (i:I) → A i → Y) : Sigma A ⊕ Y → Y
  | Sum.inl z=>anchors z.1 z.2
  | Sum.inr x=>x

end KServer.PriorityKeys

end


/-! Literal dyadic tier parameters and their logarithmic expense, §07. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierDyadic
open TierProcess

lemma exists_power (L:ℝ) : ∃ n:ℕ,L≤(2:ℝ)^n := by
  obtain ⟨n,hn⟩:=exists_nat_gt L
  refine ⟨n,hn.le.trans ?_⟩
  exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le

def index (L:ℝ) : ℕ := Nat.find (exists_power L)

end KServer.TierDyadic

end


/-! Coverage and exact tier selection for the actual posterior-driven map.
The logarithmic ratio is computed from the new true-prefix metric posterior. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelCoverage
open FiniteExperiment Pilot TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

def logratio (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) (r:ℝ) : ℝ :=
  Real.log (mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r)) /
    mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)))

def firstTier (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) (r:ℝ) : ℕ := TierDyadic.index (logratio s law σ t r)

end KServer.LevelCoverage

end


/-! The actual finite complete level alphabet and map of §07: chronological
heavy balls precede the dyadic tiers, and singleton keys are the fallback. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelKeys
open FiniteExperiment Pilot TierProcess LevelCoverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

abbrev Tier (k:ℕ) := Fin (TierDyadic.index (Real.log k)+1)
abbrev Structure (k:ℕ) := WithBot (Tier k)

def height (i:Tier k) : ℝ := (2:ℝ)^i.val
omit [NeZero k] in
lemma height_ge (i:Tier k) : 1 ≤ height i := one_le_pow₀ (by norm_num)

abbrev Alphabet (Y:Type*) [Fintype Y] (k:ℕ) : Structure k → Type _
  | none => HeavyLabels.Pool Y
  | some i => Fin (Chronological.pool Y (tierK (height i)))

abbrev Key (Y:Type*) [Fintype Y] (k:ℕ) := (Sigma (Alphabet Y k)) ⊕ Y

abbrev Tape (Y:Type*) [MetricSpace Y] [Fintype Y] (k H:ℕ) (r:ℝ) :=
  (Fin H → FiniteUniform.Outcome Y r) ×
    ((i:Tier k) → (Fin H → ActualRoster.Lifetime (tierK (height i))) ×
      (Fin H → FiniteBallLaw.Outcome Y r))

def tierQualifies (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (i:Tier k) : ℕ → Prop :=
  qualifies s law tierTemplate r tierGamma (height i) σ

def keys (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) :
    (i:Structure k) → Y → Option (Alphabet Y k i)
  | none => HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t
  | some i => TierKeys.key (request s σ) hr (tierK (height i))
      (tierQualifies s law r σ i) (tape.2 i).1 (tape.2 i).2 t

def map (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x:Y) : Key Y k :=
  PriorityKeys.key (keys s law hr σ tape t) x

def heavyAnchor (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (a:HeavyLabels.Pool Y) : Y :=
  if h:∃ c∈HeavyCenters.centers s law r heavyGamma heavyDelta σ t,
    (HeavySchedule.run s law r heavyGamma heavyDelta σ tape t).label c=a
  then h.choose else s 0

omit [MetricSpace Y] [Fintype Y] in
theorem nonemptyY (s:Configuration k Y) : Nonempty Y := ⟨s 0⟩

def anchors (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) :
    (i:Structure k) → Alphabet Y k i → Y
  | none => heavyAnchor s law r σ tape.1 t
  | some i => @TierKeys.anchor Y _ _ (nonemptyY s) (request s σ) r hr
      (tierK (height i)) (tierQualifies s law r σ i) t

def anchor (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) : Key Y k → Y :=
  PriorityKeys.anchor (anchors s law hr σ tape t)

end KServer.LevelKeys

end


/-! Explicit finite independent tapes and their exact marginal laws. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteTape
open PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I:Type*} [Fintype I] {Ω:I→Type*} [∀ i,Fintype (Ω i)]

variable {A B:Type*} [Fintype A] [Fintype B]

def pair (u:A→ℝ) (v:B→ℝ) (p:A×B) : ℝ := u p.1*v p.2

lemma pair_sum (u:A→ℝ) (v:B→ℝ) (hu:∑ a,u a=1) (hv:∑ b,v b=1) :
    ∑ p,pair u v p=1 := by simp only [pair,Fintype.sum_prod_type,←mul_sum,hv,mul_one,hu]

end KServer.FiniteTape

end


/-! A single genuine finite independent tape for the complete level map. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelLaw
open LevelKeys FiniteTape PartitionProbabilities FiniteExperiment TierProcess
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
abbrev RequestLaw (Y:Type*) [Fintype Y] (H:ℕ) := FiniteDistribution (Fin H→Y)
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ}

def heavyWeight (r:ℝ) (a:Fin H→FiniteUniform.Outcome Y r) : ℝ :=
  productWeight (fun _ : Fin H=>FiniteUniform.law r) a

def lifetimeWeight (i:Tier k) (a:Fin H→ActualRoster.Lifetime (tierK (height i))) : ℝ :=
  productWeight (fun _ : Fin H=>ActualRoster.lifetimeLaw (tierK (height i))) a

def radiusWeight (r:ℝ) (i:Tier k) (a:Fin H→FiniteBallLaw.Outcome Y r) : ℝ :=
  productWeight (fun _ : Fin H=>FiniteBallLaw.law (Real.log (1+(tierK (height i):ℝ)^2)) r) a

def tierWeight (r:ℝ) (i:Tier k) :
    (Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r)→ℝ :=
  pair (lifetimeWeight i) (radiusWeight r i)

def weight (r:ℝ) : Tape Y k H r→ℝ :=
  pair (heavyWeight r) (productWeight (tierWeight r))

lemma heavy_sum {r:ℝ} (hr:0 < r) : (∑ a:Fin H→FiniteUniform.Outcome Y r,heavyWeight r a)=1 :=
  productWeight_sum (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r) (fun _=>FiniteUniform.law_sum hr)

lemma lifetime_sum (i:Tier k) : (∑ a:Fin H→ActualRoster.Lifetime (tierK (height i)),lifetimeWeight i a)=1 :=
  productWeight_sum (fun _ : Fin H=>ActualRoster.lifetimeLaw (tierK (height i)))
    (fun _=>ActualRoster.lifetime_sum (by have hh:=tierK_ge_two (height_ge i); omega))

lemma log_pos (i:Tier k) : 0 < Real.log (1+(tierK (height i):ℝ)^2) := by
  have hn:=tierK_ge_two (height_ge i)
  have hr : (2:ℝ) ≤ tierK (height i) := by exact_mod_cast hn
  apply Real.log_pos
  nlinarith

lemma radius_sum {r:ℝ} (hr:0 < r) (i:Tier k) :
    (∑ a:Fin H→FiniteBallLaw.Outcome Y r,radiusWeight r i a)=1 :=
  productWeight_sum (fun _ : Fin H=>FiniteBallLaw.law (Y:=Y) (Real.log (1+(tierK (height i):ℝ)^2)) r)
    (fun _=>FiniteBallLaw.law_sum (log_pos i) hr)

lemma tier_sum {r:ℝ} (hr:0 < r) (i:Tier k) : ∑ a,tierWeight (Y:=Y) (H:=H) r i a=1 :=
  pair_sum (lifetimeWeight (H:=H) i) (radiusWeight (Y:=Y) (H:=H) r i) (lifetime_sum i) (radius_sum hr i)

lemma weight_sum {r:ℝ} (hr:0 < r) : ∑ a: Tape Y k H r,weight r a=1 :=
  pair_sum (heavyWeight (Y:=Y) (H:=H) r) (productWeight (tierWeight (Y:=Y) (H:=H) (k:=k) r))
    (heavy_sum hr) (productWeight_sum _ (tier_sum hr))

lemma heavy_nonneg {r:ℝ} (hr:0 < r) (a:Fin H→FiniteUniform.Outcome Y r) : 0 ≤ heavyWeight r a :=
  productWeight_nonneg (fun (_:Fin H) b=>FiniteUniform.law_nonneg hr b) a

lemma lifetime_nonneg (i:Tier k) (a:Fin H→ActualRoster.Lifetime (tierK (height i))) :
    0 ≤ lifetimeWeight i a :=
  productWeight_nonneg (fun (_:Fin H) b=>ActualRoster.lifetime_nonneg
    (by have hh:=tierK_ge_two (height_ge i); omega) b) a

lemma radius_nonneg {r:ℝ} (hr:0 < r) (i:Tier k) (a:Fin H→FiniteBallLaw.Outcome Y r) :
    0 ≤ radiusWeight r i a :=
  productWeight_nonneg (fun (_:Fin H) b=>FiniteBallLaw.law_nonneg (log_pos i) hr b) a

lemma tier_nonneg {r:ℝ} (hr:0 < r) (i:Tier k) (a:(Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r)) :
    0 ≤ tierWeight r i a := mul_nonneg (lifetime_nonneg i a.1) (radius_nonneg hr i a.2)

lemma weight_nonneg {r:ℝ} (hr:0 < r) (a:Tape Y k H r) : 0 ≤ weight r a :=
  mul_nonneg (heavy_nonneg hr a.1) (productWeight_nonneg (tier_nonneg hr) a.2)

end KServer.LevelLaw

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_RosterEdits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

def retired (center : ℕ → Y) (I J : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) : Prop :=
  ∃ i, first center I r life rad p=some i ∧ ¬present center J r life i

def indicator (P : Prop) : ℝ := if P then 1 else 0

end KServer.ActualRoster

end


/-! One-structure edits of the actual priority map. These lemmas keep earlier
structures fixed; in particular a covered heavy key suppresses all tier edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I Y:Type*} [Fintype I] [LinearOrder I] {A:I→Type*}

/-- Before and after the elementary edit at structure j. -/
def stageBefore (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) : (i:I)→Y→Option (A i) :=
  fun i=>if i<j then q₁ i else q₀ i

def stageAfter (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) : (i:I)→Y→Option (A i) :=
  fun i=>if i≤j then q₁ i else q₀ i

end KServer.PriorityKeys

end


/-! Literal finite-label tier edit tables. The old/new difference is bounded
through permanent chronological labels; no resampling or independence is
assumed at an observed surviving roster. -/


/-! The literal chronological tier edits inside a complete level, including
heavy-priority shadowing. Noncoverage deliberately ignores earlier structures. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelTierEdits
open LevelKeys LevelCoverage LevelLaw FiniteExperiment TierProcess Pilot
open ActualRoster Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : ℝ :=
  indicator (PriorityKeys.key (PriorityKeys.stageBefore (keys s law hr σ a t)
    (keys s law hr σ a (t+1)) (i:Structure k)) p ≠
    PriorityKeys.key (PriorityKeys.stageAfter (keys s law hr σ a t)
    (keys s law hr σ a (t+1)) (i:Structure k)) p)

def uncovered (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : ℝ :=
  indicator (keys s law hr σ a t (i:Structure k) p=none)

def inserted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (t:ℕ) (i:Tier k) : Prop :=
  insertTest (request s σ) (schedule (request s σ) r (tierK (height i))
    (tierQualifies s law r σ i) t) r (tierK (height i)) t (tierQualifies s law r σ i t)

def retirement (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : Prop :=
  retired (request s σ) (schedule (request s σ) r (tierK (height i))
    (tierQualifies s law r σ i) t) (schedule (request s σ) r (tierK (height i))
    (tierQualifies s law r σ i) (t+1)) r (a.2 i).1 (a.2 i).2 p

end KServer.LevelTierEdits

end


/-! Average actual tier retirements over the full finite partition tape, not
conditionally on surviving entries. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelRetirement
open LevelKeys LevelCoverage LevelLaw LevelTierEdits FiniteExperiment TierProcess Pilot
open ActualRoster Chronological FiniteTape PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ}

variable [NeZero k]

def mean (r:ℝ) (f:Tape Y k H r→ℝ) : ℝ := ∑ a,weight r a*f a

end KServer.LevelRetirement

end


/-! Exact scale-log sums for the true post-request metric posterior. The same
absolute shift works for the heavy test and all dyadic tier tests. -/


/-! The complete-level first-covering probability bound, with its individual
local log ratio (not the largest tier times the number of scales). -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelSpatial
open LevelKeys LevelCoverage LevelLaw FiniteExperiment TierProcess Pilot
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def separation (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (t:ℕ) (x y:Y) : ℝ :=
  ∑ a:Tape Y k H r,if map s law hr σ a t x≠map s law hr σ a t y then weight r a else 0

end KServer.LevelSpatial

end


/-! Physical movement of the tier noncoverage potential on steps without an
insertion.  Unqualified dyadic heights sum against the local log ratio. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelNoInsert
open ActualRoster LevelKeys LevelCoverage LevelLaw LevelTierEdits LevelRetirement FiniteExperiment TierProcess Pilot
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

/-- Positive error is zero on insertion steps here; those steps are separately
charged to the actual retirement and pilot budgets. -/
def error (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) : ℝ :=
  if inserted s law r σ t i then 0 else mean r (fun a=>
    LevelTierEdits.charge s law hr σ a t i p+uncovered s law hr σ a (t.val+1) i (σ t)-
      uncovered s law hr σ a t i p)

end KServer.LevelNoInsert

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_PartitionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal conditional averaging for the hidden optimum's stationary members.
Only conditioning on the true request prefix is used; tape averages may be
performed first without conditioning on a surviving random roster. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HiddenAverages
open FiniteExperiment PosteriorRanks RankTracking
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def stationary (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (t:Fin H) (σ:Fin H→Y) (y:Y) : ℝ := muBefore s law t σ y-nu s law t σ y

end KServer.HiddenAverages

end


/-! Literal tier edit potentials along the selected hidden optimum.
Retirement averages are over the complete independent tape, before request
prefix conditioning.  All quantities below refer to constructed keys. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierTemporal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def potential (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) : ℝ :=
  ∑ l:Fin k,uncovered s law hr σ a t i (hidden s σ t l)

def editCost (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) : ℝ :=
  ∑ l:Fin k,LevelTierEdits.charge s law hr σ a t i (hidden s σ t l)

end KServer.TierTemporal

end


/-! True-prefix payment of literal tier retirement errors by the posterior
insertion mass.  No conditioning on the realized random tape is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierAverages
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def region (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) : Finset Y :=
  tierRegion tierTemplate r heavyGamma heavyDelta (mu s law (t.val+1) σ) (σ t)

def test (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) : ℝ :=
  if inserted s law r σ t i then indicator (p∈region s law r σ t) else 0

end KServer.TierAverages

end


/-! Literal one-step tier cost + potential accounting at the true observation
filtration. The insertion term is the existing geometric pilot charge. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelTierEdits
open LevelRetirement HiddenAverages RankTracking PosteriorRanks TierTemporal TierAverages ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def paidMass (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (i:Tier k) : ℝ :=
  if inserted s law r σ t i then mass (mu s law (t.val+1) σ) (region s law r σ t) else 0

end KServer.TierBudget

end


/-! Horizon-independent endpoint bound for the actual dyadic-tier edits. -/


/-! Literal deterministic heavy-center schedule and its clipped distance profile,
§07 of the current manuscript. Random heavy radii do not affect this schedule. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyEdit

/-- The heavy profile is zero up to radius 9 and one from radius 10. -/
def ramp (u : ℝ) : ℝ := min 1 (max 0 (u-9))

attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

/-- Finite minimum with a default value 1, also for the empty center set. -/
def profile (r : ℝ) (C : Finset Y) (y : Y) : ℝ :=
  (insert 1 (C.image (fun a => ramp (dist a y/r)))).min' ⟨1,mem_insert_self _ _⟩


open HeavyCenters HeavyLabels HeavyKeys

variable [Fintype Y]

def oldKey (C:Finset Y) (rad:Y→ℝ) (lab:Y→Pool Y) (p:Y) : Option (Pool Y) :=
  (centerKey C rad p).map lab

def newKey (C D:Finset Y) (rad:Y→ℝ) (lab prev:Y→Pool Y) (r:ℝ) (x:Y) (R:ℝ)
    (p:Y) : Option (Pool Y) :=
  (centerKey (replace r C x) (Function.update rad x R) p).map
    (updatedLabel C D rad lab prev x R)

end KServer.HeavyEdit

end


/-! The actual heavy-priority stage, including its deterministic clipped-ramp
potential and the true hidden trajectory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyTemporal
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw PriorityKeys ActualRoster
open HeavyCenters HeavySchedule HeavyLabels LevelRetirement RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def active (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) : Prop :=
  Active r heavyGamma heavyDelta (centers s law r heavyGamma heavyDelta σ t)
    (mu s law (t.val+1) σ) (σ t)

def charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (p:Y) : ℝ :=
  indicator (PriorityKeys.key (stageBefore (keys s law hr σ a t) (keys s law hr σ a (t+1)) none) p≠
    PriorityKeys.key (stageAfter (keys s law hr σ a t) (keys s law hr σ a (t+1)) none) p)

def profile (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:ℕ) (p:Y) : ℝ :=
  HeavyEdit.profile r (centers s law r heavyGamma heavyDelta σ t) p


def heavy (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) : Prop :=
  mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r))≤
    (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*r))

end KServer.HeavyTemporal

end


/-! True-prefix causality of the literal fixed-label complete level map.
The finite permanent colors and cooldown reservations do not read the future. -/


/-! True-prefix heavy edit accounting. The deterministic profile is telescoped
on the hidden labeled optimum; no surviving-radius conditioning is used. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyBudget
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw PriorityKeys ActualRoster
open HeavyCenters HeavySchedule HeavyLabels LevelRetirement RankTracking PosteriorRanks
open HiddenAverages HeavyTemporal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def test (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:Fin H) (p:Y) : ℝ :=
  if active s law r σ t then indicator (3*r<dist (σ t) p ∧ dist (σ t) p≤120*r) else 0

def potential (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ) (σ:Fin H→Y) (t:ℕ) : ℝ :=
  ∑ l,HeavyTemporal.profile s law r σ t (hidden s σ t l)

def editCost (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) : ℝ :=
  ∑ l,HeavyTemporal.charge s law hr σ a t (hidden s σ t l)

end KServer.HeavyBudget

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointExperiment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The posterior counting measure is built from labeled hidden positions.
Integrating adapted metric tests is exactly conditional expectation, and
prefix quota domination is relative to this measure, not an extra premise. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PosteriorCounting
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking PosteriorRanks HierarchyCounts
variable {Ω Y A:Type} [Fintype Ω] [Fintype Y] [Fintype A]
variable {w:Ω→ℝ} (hw:∀ ω,0≤w ω) {k:ℕ}

def atoms (q:Fin k→Y) (y:Y):ℝ:=∑ l:Fin k,if q l=y then 1 else 0

def measure (H:Ω→ℕ) (q:Ω→Fin k→Y) (ω:Ω) (y:Y):ℝ:=
  posterior w H (fun ρ=>atoms (q ρ) y) ω

end KServer.PosteriorCounting

end


/-! Removing null atoms preserves the literal conditional experiment. This
allows quota feasibility to be used only on positive posterior fibers. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PositiveExperiment
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω:Type} [Fintype Ω]

abbrev Support (w:Ω→ℝ):= {ω:Ω // 0<w ω}

def weight (w:Ω→ℝ):Support w→ℝ:=fun ω=>w ω.val

end KServer.PositiveExperiment

end


/-! The single positive finite joint request/tape experiment for every scale.
All maps use precisely the request history and the independent finite tapes. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointExperiment
open FiniteExperiment PartitionProbabilities RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ}

instance (priority := 2000) levelTapeFintype (r:ℝ):Fintype (LevelKeys.Tape Y k H r):=by
  letI (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
  infer_instance

abbrev Tape (Y:Type) [MetricSpace Y] [Fintype Y] (k H L:ℕ) (r:Fin L→ℝ):=
  (d:Fin L)→LevelKeys.Tape Y k H (r d)

def tapeWeight (r:Fin L→ℝ):Tape Y k H L r→ℝ:=
  productWeight (fun d=>LevelLaw.weight (Y:=Y) (k:=k) (H:=H) (r d))

lemma tapeWeight_sum {r:Fin L→ℝ} (hr:∀ d,0 < r d):
    (∑ a:Tape Y k H L r,tapeWeight r a)=1:=by
  unfold tapeWeight
  convert productWeight_sum (fun d=>LevelLaw.weight (Y:=Y) (k:=k) (H:=H) (r d))
    (fun d=>LevelLaw.weight_sum (Y:=Y) (k:=k) (H:=H) (hr d)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [mem_univ]

lemma tapeWeight_nonneg {r:Fin L→ℝ} (hr:∀ d,0 < r d) (a:Tape Y k H L r):
    0≤tapeWeight r a:=
  productWeight_nonneg (fun d b=>LevelLaw.weight_nonneg (Y:=Y) (k:=k) (H:=H) (hr d) b) a

def tapeLaw {r:Fin L→ℝ} (hr:∀ d,0 < r d):FiniteDistribution (Tape Y k H L r):=
  ⟨tapeWeight r,tapeWeight_nonneg hr,tapeWeight_sum hr⟩

abbrev Raw (Y:Type) [MetricSpace Y] [Fintype Y] (k H L:ℕ) (r:Fin L→ℝ):=
  (Fin H→Y)×Tape Y k H L r

variable (law:FiniteDistribution (Fin H→Y)) {r:Fin L→ℝ} (hr:∀ d,0 < r d)

def rawWeight:Raw Y k H L r→ℝ:=FiniteExperiment.weight law (tapeLaw (Y:=Y) (k:=k) (H:=H) hr)
abbrev Atom:=PositiveExperiment.Support (rawWeight (k:=k) law hr)
def weight:Atom (k:=k) law hr→ℝ:=PositiveExperiment.weight (rawWeight law hr)

lemma weight_pos (ω:Atom (k:=k) law hr):0<weight law hr ω:=ω.property
lemma weight_nonneg (ω:Atom (k:=k) law hr):0≤weight law hr ω:=(weight_pos law hr ω).le

def history (t:ℕ) (ω:Atom (k:=k) law hr):ℕ:=FiniteExperiment.history t ω.val

lemma history_refines (t:ℕ) (ω ρ:Atom (k:=k) law hr)
    (h:history law hr (t+1) ω=history law hr (t+1) ρ):
    history law hr t ω=history law hr t ρ:=FiniteExperiment.history_refines t ω.val ρ.val h

variable [NeZero k] (s:Configuration k Y)

def hidden (t:ℕ) (ω:Atom (k:=k) law hr):Fin k→Y:=FiniteExperiment.hidden s ω.val.1 t

def maps (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (y:Y):LevelKeys.Key Y k:=
  if hd:d<L then LevelKeys.map s law (hr ⟨d,hd⟩).le ω.val.1 (ω.val.2 ⟨d,hd⟩) t y
  else Sum.inr y

end KServer.JointExperiment

end


/-! The dependent permanent key alphabet is genuinely finite. -/
noncomputable section
namespace KServer.LevelKeys
instance alphabetFintype {Y:Type*} [Fintype Y] (k:ℕ) (i:Structure k):Fintype (Alphabet Y k i):=by
  cases i <;> dsimp only [Alphabet] <;> infer_instance
end KServer.LevelKeys

end


/-! Endpoint costs on the actual schedule are charged to active size, rather
than to all inactive fixed labels. This is needed for wholesale edits. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_ScheduleBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact structural identifications of the scheduled integral family and
bounds on the actual slack coefficients. -/


/-! Actual singleton/side-free transitions: their cost is paid by changed
flags, not by a fresh charge to the persistent dominant mass. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SingletonPayment
attribute [local instance] Classical.propDecidable
open SimplexFamilies AdaptiveAllocation
variable {J R : Type} [Fintype J] [DecidableEq J] [Fintype R]

def point (o:J) : J→ℝ := fun i=>if i=o then 1 else 0

end KServer.SingletonPayment

end


/-! The complete ordinary/wholesale simplex payment for the literal schedule.
All charges below are computed by the actual switches, never supplied by a
finite-law hypothesis. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ScheduledPayment
attribute [local instance] Classical.propDecidable
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule
open SimplexFamilies AdaptiveAllocation SingletonPayment
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [DecidableEq J] [Fintype R]
variable {w : Ω→ℝ}

def expense (C ell δ:ℝ) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) : ℝ :=
  let x:=vector cutoff δ P ω
  let ky:=fun s=>key s ω
  (26*C*ell+4)*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
  320*C*ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))+
  2976*C*ell*CoarseSide.charge δ (CoarseSide.sideInput x ky) (CoarseSide.epochReset x ky) t+
  (520*C*ell+80)*EpochSchedule.wholesale (x t) (x (t+1)) (ky t) (ky (t+1)) (EpochSchedule.run x ky t)

end KServer.ScheduledPayment

end


/-! Literal coarse schedule bills and their finite-experiment budgets. The
right sides use drift after conditioning, never raw posterior variation. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def drift (P:R→ FilteredRanks w) (N:ℕ):ℝ:=
  ∑ t∈range N,avg w (fun ω=>∑ r,|(P r).p (t+1) ω-(P r).before (t+1) ω|)
def inventory (P:R→ FilteredRanks w) (N:ℕ):ℝ:=drift P N+Fintype.card R
def flat (P:J→ R→ FilteredRanks w):J×R→ FilteredRanks w:=fun ir=> P ir.1 ir.2

def flags (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))
def active (P:J→ R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  ∑ i,CoarseSchedule.charge (CoarseProcess.active cutoff ds (P i) ω t)
    (CoarseProcess.active cutoff ds (P i) ω (t+1))
def parentCharge (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  CoarseProcess.relativeCharge dp (clipped cutoff dp Q) t ω
def wholesale (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  EpochSchedule.wholesale (vector cutoff ds P ω t) (vector cutoff ds P ω (t+1))
    (key Q t ω) (key Q (t+1) ω) (EpochSchedule.run (vector cutoff ds P ω) (fun s=> key Q s ω) t)
def sideRefresh (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (t:ℕ) (ω:Ω):ℝ:=
  CoarseSide.charge ds (CoarseSide.sideInput (vector cutoff ds P ω) (fun s=> key Q s ω))
    (CoarseSide.epochReset (vector cutoff ds P ω) (fun s=> key Q s ω)) t

def activeConstant:ℝ:=CoarseSchedule.factor ds*(5*(4/3:ℝ)^2/ds+1)
def parentConstant:ℝ:=CoarseSchedule.factor dp*(5*(4/3:ℝ)^2/dp)
def flagConstant:ℝ:=(CoreFlags.tolerance^2)⁻¹

end KServer.ActualCharges

end


/-! Uniform coarse accounting for the actual local star. The only variable
right-hand side is the sum of true drift and one fixed rank inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def total (w:Ω→ℝ) (N:ℕ) (f:ℕ→Ω→ℝ):ℝ:=∑ t∈range N,avg w (f t)
def stock (P:J→ R→ FilteredRanks w) (Q:R→ FilteredRanks w) (N:ℕ):ℝ:=
  inventory (flat P) N+inventory Q N

def wholesaleConstant:ℝ:=203*activeConstant+2*parentConstant
def scaleConstant:ℝ:=80/ds+flagConstant+41*wholesaleConstant
def sideRefreshConstant:ℝ:=CoarseSide.C ds*activeConstant

end KServer.ActualCharges

end


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/


/-! Deterministic payment for the literal side state, with only actual edits
on the right hand side. Parent parameters are held through an ordinary epoch. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SidePayment
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseEpoch CoarseProcess StarProfile AllocationSchedule StarSide SideFamilies
variable {Ω J R K : Type} [Fintype Ω] [Fintype J]  [Fintype R]
variable {w:Ω→ℝ}

def expense (cw ell δ:ℝ) (P:J→R→FilteredRanks w) (key:ℕ→Ω→K) (t:ℕ) (ω:Ω) : ℝ :=
  if epoch (vector cutoff δ P ω) (fun s=>key s ω) t=
      epoch (vector cutoff δ P ω) (fun s=>key s ω) (t+1) then
    SideEdits.L cw ell*|scale δ P key (t+1) ω-scale δ P key t ω|+
      SideEdits.Q cw ell*ChangingDomains.changedFlags (StarSimplex.flags P ω t) (StarSimplex.flags P ω (t+1))+
      40*SideEdits.K cw ell*(∑ i,CoarseSchedule.charge (active cutoff δ (P i) ω t) (active cutoff δ (P i) ω (t+1)))
  else 300000*(1/cw+1)*ell*(EpochSchedule.total (vector cutoff δ P ω t)+EpochSchedule.total (vector cutoff δ P ω (t+1)))

end KServer.SidePayment

end


/-! Fixed absolute coefficients for actual simplex/side edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def simplexConstant:ℝ:=(26*C+4)*flagConstant+320*C*activeConstant+
  2976*C*sideRefreshConstant+(520*C+80)*wholesaleConstant
def sideConstant:ℝ:=SideEdits.L cw 1*scaleConstant+SideEdits.Q cw 1*flagConstant+
  40*SideEdits.K cw 1*activeConstant+300000*(1/cw+1)*wholesaleConstant
end KServer.ActualCharges

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AllocationBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! True-prefix filtering followed by paid literal profile edits.  In particular
no event chosen at the new history is allowed to select a filtering term. -/


/-! Expected movement of the literal minimizers, with uniform endpoint bills. -/


/-! Switch charges from the actual regime recursion, including uniform
initialization and literal wholesale bills. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def ruleConstant:ℝ:=flagConstant+scaleConstant+81*wholesaleConstant

end KServer.ActualCharges
end


/-! All-step output charging, including wholesale jumps without a charge per
child or per epoch. The parent variation retains coefficient exactly one. -/


/-! The unconditional local allocation movement theorem for the
literal output already constructed. Its parent coefficient is exactly one;
all other costs are true drift and a fixed, law/horizon-independent inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking RankFunctions CoarseProcess CoarseEpoch StarProfile AllocationSchedule LocalConstants ActualStar ActualOutput
variable {Ω J R:Type} [Fintype Ω] [Fintype J] [Fintype R] {w:Ω→ℝ}

def fineConstant:ℝ:=2*(160/rho+flagConstant)
def movementConstant:ℝ:=2*fineConstant+40*(13*C+simplexConstant+3600/cw+sideConstant+
  scaleConstant+2*(1+ruleConstant))+80*wholesaleConstant
def endpointConstant:ℝ:=40*(1144*C+440000*(1/cw+1)+180)
def localConstant:ℝ:=movementConstant+endpointConstant+1
end KServer.ActualCharges

end


/-! The actual top-down allocation, summed over the fixed complete-prefix
hierarchy. All initialization costs depend only on the fixed label inventory. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualCharges
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}

variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def nodeMove (hk:1 ≤ (k:ℝ)) {d:ℕ} (word:Fin d→A) (N:ℕ):ℝ:=
  total w N (fun t ω=>|quota hw H hr maps q hk d word (t+1) ω-quota hw H hr maps q hk d word t ω|)
def levelMove (hk:1 ≤ (k:ℝ)) (d N:ℕ):ℝ:=∑ word:Fin d→A,nodeMove hw H hr maps q hk word N
def levelDrift (d N:ℕ):ℝ:=∑ word:Fin d→A,drift (parent hw H hr maps q word) N

def levelInventory (A:Type) [Fintype A] (k d:ℕ):ℝ:=
  Fintype.card (Fin d→A)*((Fintype.card (A×Fin k):ℝ)+Fintype.card (Fin k)+(k:ℝ))

end KServer.HierarchicalQuota

end


/-! Geometric absorption with the literal parent coefficient one. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota

variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

open ActualCharges

def treeMove (hk:1 ≤ (k:ℝ)) (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*levelMove hw H hr maps q hk (d+1) N
def treeDrift (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*(levelDrift hw H hr maps q d N+levelDrift hw H hr maps q (d+1) N)
def treeInventory (A:Type) [Fintype A] (k:ℕ) (r:ℕ→ℝ) (L:ℕ):ℝ:=
  ∑ d∈range L,r d*levelInventory A k d
end KServer.HierarchicalQuota

end


/-! Conditional-drift coupling for literal fixed-prefix occupancies. The
right side is movement of the hidden labeled configurations, not observation
noise or a hypothesized allocation cost. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open RankTracking ActualCharges HierarchyCounts

variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def address (d:ℕ) (t:ℕ) (ω:Ω) (l:Fin k):Fin d→A:=fun i=>maps t ω i.val (q t ω l)
def prefixCross (d:ℕ) (t:ℕ) (ω:Ω):ℝ:=
  ∑ l:Fin k,if address maps q d (t+1) ω l=address maps q d t ω l then 0 else 1

def levelHidden (d N:ℕ):ℝ:=total w N (fun t ω=>∑ word:Fin d→A,
  |(count (maps (t+1) ω) word (q (t+1) ω):ℝ)-count (maps t ω) word (q t ω)|)

end KServer.HierarchicalQuota

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_PrefixAllocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Persistent heavy-slot size tracking filters tangents before adaptive refresh. -/


noncomputable section
open scoped BigOperators
open Set Finset
namespace KServer.KeySizeTracking

def tangent (u s : ℝ) : ℝ := u - (1 + Real.log u) * s

def entropy (u s : ℝ) : ℝ := s * Real.log (s / u) - s + u


variable {Ω : Type} [Fintype Ω]

def avg (w : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ ω, w ω*f ω

def Adapted (H : Ω → ℕ) (f : Ω → ℝ) : Prop := ∀ ω ω', H ω=H ω' → f ω=f ω'

/-- Old and new membership counts shifted by one, with literal finite-fiber
conditioning. There is no policy-existence or budget assumption in this data. -/
structure FilteredSizes (w : Ω → ℝ) (K : ℝ) where
  history : ℕ → Ω → ℕ
  refines : ∀ t ω ω', history (t+1) ω=history (t+1) ω' → history t ω=history t ω'
  s : ℕ → Ω → ℝ
  before : ℕ → Ω → ℝ
  range : ∀ t ω, s t ω ∈ Set.Icc 1 K
  before_range : ∀ t ω, before t ω ∈ Set.Icc 1 K
  adapted : ∀ t, Adapted (history t) (s t)
  filtering : ∀ t h, ∑ ω ∈ Finset.univ.filter (fun ω => history t ω=h),
    w ω*(before (t+1) ω-s t ω)=0

def refresh (s u : ℝ) : Prop := s < (5/6:ℝ)*u ∨ (6/5:ℝ)*u < s
instance instDecidableRelRealRefresh : DecidableRel refresh := Classical.decRel _

def held (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, ω => s 0 ω
  | t+1, ω => if refresh (s (t+1) ω) (held s t ω) then s (t+1) ω else held s t ω

def refreshCost (s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if refresh (s (t+1) ω) (held s t ω) then held s t ω+held s (t+1) ω else 0

end KServer.KeySizeTracking

end


/-! Persistent heavy-slot size tracking on the actual finite observation
experiment. Raw counts can change with both the hidden trajectory and the
adapted partition. No martingale identity is postulated. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PosteriorSizes
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω:Type} [Fintype Ω] {w:Ω→ℝ}

lemma bounded (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) (H:Ω→ℕ)
    {f:Ω→ℝ} {K:ℝ} (hf:∀ ω,f ω∈Set.Icc 0 K) (ω:Ω):
    posterior w H f ω∈Set.Icc 0 K:=by
  refine ⟨posterior_nonneg hw H (fun ρ=>(hf ρ).1) ω,?_⟩
  have h:=posterior_mono_fiber hw (H:=H) (g:=fun _=>K) ω (fun ρ _=>(hf ρ).2)
  rw [posterior_fiber_const ω (fun _ _=>rfl) (HierarchyCounts.positive_mass hw H ω (hwpos ω)).ne'] at h
  exact h

def process (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω) {K:ℝ}
    (H:ℕ→Ω→ℕ) (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
    (N:ℕ→Ω→ℝ) (hN:∀ t ω,N t ω∈Set.Icc 0 K):KeySizeTracking.FilteredSizes w (K+1) where
  history:=H
  refines:=hr
  s t ω:=1+posterior w (H t) (N t) ω
  before t ω:=1+posterior w (H t) (N (t-1)) ω
  range:=by intro t ω; have h:=bounded hw hwpos (H t) (hN t) ω; constructor <;> linarith [h.1,h.2]
  before_range:=by intro t ω; have h:=bounded hw hwpos (H t) (hN (t-1)) ω; constructor <;> linarith [h.1,h.2]
  adapted:=by
    intro t ω ρ he
    exact congrArg (1+·) (posterior_adapted w (H t) (N t) ω ρ he)
  filtering:=by
    intro t h
    simp only [Nat.add_sub_cancel,add_sub_add_left_eq_sub]
    exact filtered_fiber hw (H t) (H (t+1)) (hr t) (N t) h

end KServer.PosteriorSizes

end


/-! Literal children and geometric edge weights of the retained complete
prefix tree. These identify the numbered rounding tree without deleting empty
words or changing its allocated coordinates. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

abbrev Child (v:Vertex A L):= {u:Vertex A L // u≠root A L ∧ parent A L u=v}

omit [Fintype A] in
lemma depth_zero_iff (v:Vertex A L):v.1.val=0 ↔ v=root A L:=by
  constructor
  · rintro h
    rcases v with ⟨j,f⟩
    have hj:j=0:=Fin.ext h
    subst j
    congr
    exact funext (fun i=>Fin.elim0 i)
  · rintro rfl; rfl

omit [Fintype A] in
lemma parent_succ {d:ℕ} (hd:d+1<L+1) (f:Fin (d+1)→A):
    parent A L ⟨⟨d+1,hd⟩,f⟩=⟨⟨d,by omega⟩,Fin.init f⟩:=by
  simp only [parent,Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceDIte]
  rfl

omit [Fintype A] in
lemma child_depth {v:Vertex A L} (u:Child A L v):u.val.1.val=v.1.val+1:=by
  have hp:0<u.val.1.val:=Nat.pos_of_ne_zero ((depth_zero_iff A L _).not.mpr u.property.1)
  have he:=congrArg (fun x:Vertex A L=>x.1.val) u.property.2
  simp only [parent,dite_eq_right (by omega : u.val.1.val≠0)] at he
  omega

omit [Fintype A] in
lemma child_last_lt {v:Vertex A L} (u:Child A L v):u.val.1.val-1<u.val.1.val:=by
  have :=child_depth A L u
  omega

def extend (v:Vertex A L) (h:v.1.val<L) (a:A):Vertex A L:=
  ⟨⟨v.1.val+1,by omega⟩,Fin.snoc v.2 a⟩

omit [Fintype A] in
lemma parent_extend (v:Vertex A L) (h:v.1.val<L) (a:A):
    parent A L (extend A L v h a)=v:=by
  rw [extend,parent_succ]
  simp only [Fin.init_snoc]

omit [Fintype A] in
lemma extend_ne_root (v:Vertex A L) (h:v.1.val<L) (a:A):
    extend A L v h a≠root A L:=by
  intro he
  have he':=(depth_zero_iff A L _).mpr he
  dsimp [extend] at he'
  omega

def childEquiv (v:Vertex A L) (h:v.1.val<L):A≃Child A L v where
  toFun a:=⟨extend A L v h a,extend_ne_root A L v h a,parent_extend A L v h a⟩
  invFun u:=u.val.2 ⟨u.val.1.val-1,child_last_lt A L u⟩
  left_inv a:=by
    simp only [extend,Nat.add_sub_cancel]
    exact Fin.snoc_last _ _
  right_inv u:=by
    apply Subtype.ext
    rcases v with ⟨⟨d,hd⟩,f⟩
    rcases u with ⟨⟨⟨e,he⟩,g⟩,hn,hp⟩
    have hdeg:e=d+1:=child_depth A L ⟨_,hn,hp⟩
    subst e
    rw [parent_succ] at hp
    have hf:Fin.init g=f:=by cases hp; rfl
    dsimp only [extend,Nat.add_sub_cancel]
    change (⟨⟨d+1,he⟩,Fin.snoc f (g (Fin.last d))⟩:Vertex A L) = _
    rw [←hf]
    have hg:Fin.snoc (Fin.init g) (g (Fin.last d))=g:=Fin.snoc_init_self g
    exact congrArg (fun f:Fin (d+1)→A=>(⟨⟨d+1,he⟩,f⟩:Vertex A L)) hg

omit [Fintype A] in
lemma no_child (v:Vertex A L) (h:v.1.val=L):IsEmpty (Child A L v):=by
  refine ⟨fun u=>?_⟩
  have hd:=child_depth A L u
  have hu:=u.val.1.isLt
  omega

def numberedChildEquiv (v:Fin (Fintype.card (Vertex A L))):
    (tree A L).Child v ≃ Child A L (numbering A L v) where
  toFun u:=⟨numbering A L u.val,by
    constructor
    · intro he
      apply u.property.1
      apply (numbering A L).injective
      rw [he,numbering_zero]
    · have he:=congrArg (numbering A L) u.property.2
      simpa only [tree,OrderIso.apply_symm_apply] using he⟩
  invFun u:=⟨(numbering A L).symm u.val,by
    constructor
    · intro he
      apply u.property.1
      have hh:=congrArg (numbering A L) he
      simpa only [OrderIso.apply_symm_apply,numbering_zero] using hh
    · change (numbering A L).symm (parent A L (numbering A L ((numbering A L).symm u.val)))=v
      rw [OrderIso.apply_symm_apply,u.property.2,OrderIso.symm_apply_apply]⟩
  left_inv u:=by apply Subtype.ext; exact OrderIso.symm_apply_apply _ _
  right_inv u:=by apply Subtype.ext; exact OrderIso.apply_symm_apply _ _

lemma children_sum (v:Fin (Fintype.card (Vertex A L))) (f:Vertex A L→ℝ)
    (h:(numbering A L v).1.val<L):
    (∑ u:(tree A L).Child v,f (numbering A L u.val))=
      ∑ a:A,f (extend A L (numbering A L v) h a):=by
  let e: A ≃ (tree A L).Child v :=
    (childEquiv A L (numbering A L v) h).trans (numberedChildEquiv A L v).symm
  symm
  exact Fintype.sum_equiv e _ _ (fun a=>by
    change f (extend A L (numbering A L v) h a) =
      f (numbering A L ((numbering A L).symm (extend A L (numbering A L v) h a)))
    rw [OrderIso.apply_symm_apply])

lemma children_sum_leaf (v:Fin (Fintype.card (Vertex A L))) (f:Vertex A L→ℝ)
    (h:(numbering A L v).1.val=L):
    (∑ u:(tree A L).Child v,f (numbering A L u.val))=0:=by
  let: IsEmpty (Child A L (numbering A L v)):=no_child A L _ h
  let:IsEmpty ((tree A L).Child v):=Function.isEmpty (numberedChildEquiv A L v)
  exact sum_of_isEmpty _

def weight (R τ:ℝ) (v:Fin (Fintype.card (Vertex A L))):ℝ:=
  R/τ^(numbering A L v).1.val

lemma weight_nonneg {R τ:ℝ} (hR:0≤R) (hτ:0≤τ) (v:Fin (Fintype.card (Vertex A L))):
    0≤weight A L R τ v:=div_nonneg hR (pow_nonneg hτ _)

lemma parent_weight {R τ:ℝ} (hτ:τ≠0) (v:Fin (Fintype.card (Vertex A L))) (hv:v≠0):
    weight A L R τ ((tree A L).parent v)=τ*weight A L R τ v:=by
  let hu:Child A L (numbering A L ((tree A L).parent v)):=
    numberedChildEquiv A L _ ⟨v,hv,rfl⟩
  have he: (numbering A L v).1.val=(numbering A L ((tree A L).parent v)).1.val+1:=
    by simpa only [hu,numberedChildEquiv,Equiv.coe_fn_mk] using child_depth A L hu
  unfold weight
  rw [he,pow_succ]
  field_simp

end KServer.PrefixTree

end


/-! Quotas and parks on the actual numbered complete-prefix tree, with their
posterior support witnesses. Rounding.Tree and TreeRounding.Tree have the same
parent data; the conversion below changes no vertex or quantity. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

def travelTree:Rounding.Tree (Fintype.card (Vertex A L)) where
  parent:=(tree A L).parent
  root:=(tree A L).root
  lower:=(tree A L).lower

variable {Ω Y:Type} [Fintype Ω] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

def Q (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):ℝ:=
  HierarchicalQuota.quota hw H hr maps q hk (numbering A L v).1 (numbering A L v).2 t ω

def region (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):Finset Y:=
  univ.filter (HierarchyCounts.hit (maps t ω) (numbering A L v).2)

omit [Fintype Y] in
lemma Q_root (t:ℕ) (ω:Ω):Q A L hw H hr maps q hk t ω 0=k:=by
  exact congrArg (fun u:Vertex A L=>HierarchicalQuota.quota hw H hr maps q hk u.1.val u.2 t ω)
    (numbering_zero A L)

omit [Fintype Y] in
lemma Q_nonneg (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    0≤Q A L hw H hr maps q hk t ω v:=
  HierarchicalQuota.quota_nonneg hw H hr maps q hk hwpos _ t ω

omit [Fintype Y] in
lemma Q_children (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    (∑ u:(tree A L).Child v,Q A L hw H hr maps q hk t ω u.val)≤Q A L hw H hr maps q hk t ω v:=by
  by_cases hv:(numbering A L v).1.val<L
  · unfold Q
    rw [children_sum A L v (fun u:Vertex A L=>HierarchicalQuota.quota hw H hr maps q hk u.1.val u.2 t ω) hv]
    exact HierarchicalQuota.children_budget hw H hr maps q hk hwpos (numbering A L v).2 t ω
  · have he:(numbering A L v).1.val=L:=by have :=(numbering A L v).1.isLt; omega
    unfold Q
    rw [children_sum_leaf A L v (fun u:Vertex A L=>HierarchicalQuota.quota hw H hr maps q hk u.1.val u.2 t ω) he]
    exact Q_nonneg A L hw H hr maps q hk hwpos t ω v

omit [Fintype Y] in
lemma park_nonneg (hwpos:∀ ω,0<w ω) (t:ℕ) (ω:Ω) (v:Fin (Fintype.card (Vertex A L))):
    0≤(travelTree A L).park (Q A L hw H hr maps q hk t ω) v:=by
  apply sub_nonneg.mpr
  exact Q_children A L hw H hr maps q hk hwpos t ω v

end KServer.PrefixTree

namespace KServer.Rounding
variable {n:ℕ} [NeZero n]
lemma Tree.under_root (T:Tree n) (v:Fin n):T.under 0 v=true:=by
  by_cases hv:v=0
  · subst v; exact T.under_self 0
  · rw [Tree.under,ite_eq_right hv,dite_eq_right hv]
    exact T.under_root (T.parent v)
termination_by v.val
decreasing_by exact T.lower v hv

end KServer.Rounding

end


/-! Actual truncation ancestors of complete-prefix words, with the retained
numbering used by the finite rounding tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

def take (v:Vertex A L) (d:ℕ) (hd:d≤v.1.val):Vertex A L:=
  ⟨⟨d,lt_of_le_of_lt hd v.1.isLt⟩,fun i=>v.2 ⟨i.val,lt_of_lt_of_le i.isLt hd⟩⟩

omit [Fintype A] in
lemma parent_depth (v:Vertex A L) (hv:0<v.1.val):
    (parent A L v).1.val=v.1.val-1:=by
  simp only [parent,dite_eq_right (by omega:v.1.val≠0)]

end KServer.PrefixTree

end


/-! Cumulative parked mass in the actual prefix cut is bounded by posterior
mass of the 67-radius ball. Selection can depend on the completed state. -/


/-! Literal variation of all parks, including the root park, with the exact
parent-edge factor. No metric or rounding movement estimate is assumed. -/


/-! Fixed last-key bands in the complete prefix tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

abbrev Node:=Fin (Fintype.card (Vertex A L))
def depth (v:Node A L):ℕ:=(numbering A L v).1.val
def lastKey (v:Node A L):Option A:=
  if h:0<depth A L v then some ((numbering A L v).2 ⟨depth A L v-1,by change depth A L v-1<depth A L v; omega⟩) else none

def band (d:ℕ) (a:A):Finset (Node A L):=
  univ.filter (fun v=>depth A L v=d+1 ∧ lastKey A L v=some a)

def bandMass (p:Node A L→ℝ) (d:ℕ) (a:A):ℝ:=∑ v∈band A L d a,p v

end KServer.PrefixTree

end


/-! Literal all-key persistent size references on the adapted complete map. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.KeyReferences
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] [Fintype Y] {k:ℕ} {w:Ω→ℝ}
variable (H:ℕ→Ω→ℕ) (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def count (d:ℕ) (a:A) (t:ℕ) (ω:Ω):ℝ:=∑ i:Fin k,if maps t ω d (q t ω i)=a then 1 else 0

omit [Fintype Ω] [Fintype A] [Fintype Y] in
lemma count_range (d:ℕ) (a:A) (t:ℕ) (ω:Ω):count maps q d a t ω∈Set.Icc 0 (k:ℝ):=by
  constructor
  · exact sum_nonneg fun i _=>by split_ifs <;> norm_num
  · have hh:=sum_le_sum (s:=(univ:Finset (Fin k))) (f:=fun i=>if maps t ω d (q t ω i)=a then (1:ℝ) else 0)
      (g:=fun _=>(1:ℝ)) (fun i _=>by split_ifs <;> norm_num)
    simpa [count] using hh

def size (d:ℕ) (a:A) (t:ℕ) (ω:Ω):ℝ:=1+posterior w (H t) (count maps q d a t) ω

def reference (d:ℕ) (a:A):ℕ→Ω→ℝ:=KeySizeTracking.held (size (w:=w) H maps q d a)

variable (hw:∀ ω,0≤w ω) (hwpos:∀ ω,0<w ω)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)

def process (d:ℕ) (a:A):KeySizeTracking.FilteredSizes w ((k:ℝ)+1):=
  PosteriorSizes.process hw hwpos H hr (count maps q d a) (count_range maps q d a)

end KServer.KeyReferences

end


/- Height-independent scale-capacity estimates use summation by parts rather than dyadic grouping. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ParkedCoefficients

def tail (b : ℕ → ℝ) (n i : ℕ) : ℝ := ∑ j ∈ Ico i n, b j

end KServer.ParkedCoefficients

namespace KServer.ParkedCoefficients
section MetricScales
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

/-- The manuscript's posterior measure of a closed metric ball, as a finite
counting sum. We do not restrict to distinct hidden locations. -/
def ballMass (μ : Y → ℝ) (y : Y) (r : ℝ) : ℝ :=
  ∑ z, if dist y z ≤ r then μ z else 0

def radius (r₀ τ : ℝ) (i : ℕ) := r₀/τ^i

end MetricScales
end KServer.ParkedCoefficients

end


/-! All finer selected last-key bands form a literal prefix cut. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)

def selectedBand (sel:ℕ→Option A) (d:ℕ):Finset (Node A L):=
  match sel d with | none =>∅ | some a =>band A L d a

def selectedMass (p:Node A L→ℝ) (sel:ℕ→Option A) (d:ℕ):ℝ:=
  ∑ v∈selectedBand A L sel d,p v

end KServer.PrefixTree

end


/-! The actual prefix parks satisfy the logarithmic coefficient estimate.
The denominator is the held persistent slot size; empty selected levels vanish. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Ω Y:Type} [Fintype Ω] [Fintype Y] [MetricSpace Y] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0≤w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y) (hk:1≤(k:ℝ))

def selectedDenominator (μ:Y→ℝ) (y:Y) (r:ℕ→ℝ) (sel:ℕ→Option A) (u:ℕ→A→ℝ) (i:ℕ):ℝ:=
  match sel i with | none =>1+ParkedCoefficients.ballMass μ y (r i) | some a =>u i a

end KServer.PrefixTree

end


/-! Literal allocation and persistent bands on the single positive experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointAllocation
open JointExperiment RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

abbrev Ω:=JointExperiment.Atom (k:=k) law hr
abbrev A:=LevelKeys.Key Y k
local instance keyDecEq : DecidableEq (A (Y:=Y) (k:=k)) := Classical.decEq _

def quota (t:ℕ) (ω:Ω (k:=k) law hr):PrefixTree.Node (A (Y:=Y) (k:=k)) L→ℝ:=
  PrefixTree.Q _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk t ω

def park (t:ℕ) (ω:Ω (k:=k) law hr):PrefixTree.Node (A (Y:=Y) (k:=k)) L→ℝ:=
  (PrefixTree.travelTree _ L).park (quota s law hr hk t ω)

def band (t:ℕ) (ω:Ω (k:=k) law hr) (d:ℕ) (a:A (Y:=Y) (k:=k)):ℝ:=
  PrefixTree.bandMass _ L (park s law hr hk t ω) d a

def size (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):ℝ:=
  KeyReferences.size (w:=weight law hr) (history law hr) (maps law hr s) (hidden law hr s) d a t ω

def reference (d:ℕ) (a:A (Y:=Y) (k:=k)) (t:ℕ) (ω:Ω (k:=k) law hr):ℝ:=
  KeySizeTracking.held (size s law hr d a) t ω

lemma quota_nonneg (t:ℕ) (ω:Ω (k:=k) law hr) (v:PrefixTree.Node (A (Y:=Y) (k:=k)) L):
    0≤quota s law hr hk t ω v:=
  PrefixTree.Q_nonneg _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω v

lemma park_nonneg (t:ℕ) (ω:Ω (k:=k) law hr) (v:PrefixTree.Node (A (Y:=Y) (k:=k)) L):
    0≤park s law hr hk t ω v:=
  PrefixTree.park_nonneg _ L (weight_nonneg law hr) (history law hr) (history_refines law hr)
    (maps law hr s) (hidden law hr s) hk (weight_pos law hr) t ω v

end KServer.JointAllocation

end


/-! From the exact conditional allocation construction to levelwise hidden-key
changes. This counts both true hidden movement and changing online maps. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchicalQuota
attribute [local instance] Classical.propDecidable Classical.decEq
open ActualCharges
variable {Ω A Y:Type} [Fintype Ω] [Fintype A] {k:ℕ} {w:Ω→ℝ}
variable (hw:∀ ω,0 ≤ w ω) (H:ℕ→Ω→ℕ)
variable (hr:∀ t ω ρ,H (t+1) ω=H (t+1) ρ→H t ω=H t ρ)
variable (maps:ℕ→Ω→ℕ→Y→A) (q:ℕ→Ω→Fin k→Y)

def keyCross (d t:ℕ) (ω:Ω):ℝ:=∑ l:Fin k,
  if maps (t+1) ω d (q (t+1) ω l)=maps t ω d (q t ω l) then 0 else 1

def keyTransport (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*total w N (keyCross maps q d)

def prefixTransport (r:ℕ→ℝ) (L N:ℕ):ℝ:=
  ∑ d∈range L,r d*total w N (prefixCross maps q (d+1))

end KServer.HierarchicalQuota

end


end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_AnchorTravel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual retained heavy label, not an assumed anchor motion rule. -/


/-! The first-priority heavy region is its full ball, including boundaries. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def slot (a:Pool Y):Key Y k:=Sum.inl ⟨none,a⟩

end KServer.HeavyAnchorDynamics

end


/-! The metric and heavy-ball payment portions of §08's anchor travel proof.
These are required by the open finite-law construction, not a new main result.
The clipped ramp and rho=6/5 are the exact source choices. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel

def ramp (u : ℝ) : ℝ := min 1 (max 0 ((u-4)/3))

variable {Y : Type*} [MetricSpace Y]

variable [DecidableEq Y]

def integral (w : Y → ℝ) (C : Finset Y) (a : Y) (r : ℝ) : ℝ :=
  ∑ z ∈ C, w z*ramp (dist a z/r)

def mass (w : Y → ℝ) (C : Finset Y) : ℝ := ∑ z ∈ C, w z

end KServer.AnchorTravel

end


/-! The actual retained label releases the ramp credit. All geometry and the
one-unit inner mass are obtained from the actual embedding and served hidden
trajectory, not postulated as an anchor-payment interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def present (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (a:Pool Y):Prop:=
  ∃ c∈centers s law r heavyGamma heavyDelta σ t,
    (run s law r heavyGamma heavyDelta σ tape t).label c=a

def cell (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (a:Pool Y):Finset Y:=
  univ.filter (fun x=>map s law hr σ tape t x=slot (k:=k) a)

end KServer.HeavyAnchorDynamics

end


/-! The old ramp cutoff selects a heavy ball containing the unit-radius ball
about the old point and lying inside its twenty-seven-radius neighborhood. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyAnchorDynamics
open FiniteExperiment Pilot HeavyCenters HeavyLabels HeavySchedule LevelKeys TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def selected (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (y:Y):Option (Key Y k):=
  match HeavyKeys.key s law r heavyGamma heavyDelta σ tape t y with
  | none=>none
  | some a=>if dist (heavyAnchor s law r σ tape t a) y<7*r then some (slot (k:=k) a) else none

end KServer.HeavyAnchorDynamics

end


/-! The pointwise drift comparison for the old heavy-slot ramp coefficients.
It applies to an arbitrary coupled old/new member, without independence. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y J D:Type*} [MetricSpace Y]

def term (r:ℝ) (c:J→ℝ) (a:J→Y) (key:Option J) (y:Y):ℝ:=
  match key with
  | none=>0
  | some j=>r*c j*ramp (dist (a j) y/r)

def cutoff (r:ℝ) (c:J→ℝ) (a:J→Y) (key:Option J) (y:Y):ℝ:=
  match key with
  | none=>0
  | some j=>if dist (a j) y<7*r then c j else 0

end KServer.AnchorTravel

end


/-! Exact finite conditional integration for the chronological ramp. These
identities do not discard a filtering term after an adaptive choice. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω Y D J:Type} [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J]
variable [MetricSpace Y] {w:Ω→ℝ} {k:ℕ}

def slotIntegral (μ:Y→ℝ) (key:Y→Option J) (a:Y) (r:ℝ) (j:J):ℝ:=
  ∑ y∈univ.filter (fun y=>key y=some j),μ y*ramp (dist a y/r)

end KServer.AnchorTravel

end


/-! Scalar chronological accounting in the source order: membership, reference,
park, anchor. The normalization comparison is used only after its refresh. -/


/-! Signed chronological potential, with old coefficients throughout the
membership comparison. The final telescope keeps a single finite endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.AnchorTravel
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω Y D J:Type} [Fintype Ω] [Fintype Y] [Fintype D] [Fintype J]
variable [MetricSpace Y] {w:Ω→ℝ} {k:ℕ}

def familyTest (r:D→ℝ) (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J) (y:Y):ℝ:=
  ∑ d,term (r d) (c d) (a d) (key d y) y

def familyIntegral (μ:Y→ℝ) (r:D→ℝ) (c:D→J→ℝ) (a:D→J→Y) (key:D→Y→Option J):ℝ:=
  ∑ d,∑ j,r d*c d j*slotIntegral μ (key d) (a d j) (r d) j

end KServer.AnchorTravel

end


/-! A literal single-slot ordered update: held reference, park, retained anchor. -/


/-! True prefix measurability of the literal permanent anchors, including
unused labels. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric absorption on the same numbered tree used for metric rounding. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointBudget
open JointExperiment JointAllocation HierarchicalQuota ActualCharges RankTracking
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

abbrev Node:=PrefixTree.Node (LevelKeys.Key Y k) L

def stepQuota (R τ:ℝ) (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ v:Node (Y:=Y) (k:=k) (L:=L),PrefixTree.weight (LevelKeys.Key Y k) L R τ ((PrefixTree.tree _ L).parent v)*
    |quota s law hr hk (t+1) ω v-quota s law hr hk t ω v|

def stepKey (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ d:Fin L,r d*keyCross (maps law hr s) (hidden law hr s) d.val t ω

end KServer.JointBudget

end


/-! All-scale, law/horizon-independent roster endpoint, aggregating the actual
chronological edit charges rather than assuming metric distortion. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def opt (s:Configuration k Y) (law:RequestLaw Y H):ℝ:=
  ∑ σ,law.val σ*optimalCost s (List.ofFn σ)
def inventory (k:ℕ) (r₀ τ:ℝ) (n:ℕ):ℝ:=∑ j∈range n,radius r₀ τ j*(k:ℝ)
def tierMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):ℝ:=
  ∑ i:Tier k,∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    mean (radius r₀ τ j) (fun a=>TierTemporal.editCost s law
      (radius_pos hr (by linarith) j).le σ a t i)))

def tierCoefficient (k:ℕ):ℝ:=147*tierDrift*(1+Real.log ((k:ℝ)+1))+
  98/heavyGamma+32*(1+Real.log k)+31440*Real.log k

end KServer.EmbeddedCost

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open HeavyTemporal ActualRoster
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def heavyDrift:ℝ:=driftConstant HeavyCenters.template heavyGamma heavyDelta 26

def heavyMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ):ℝ:=
  ∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    mean (radius r₀ τ j) (fun a=>HeavyBudget.editCost s law
      (radius_pos hr (by linarith) j).le σ a t)))

def heavyCoefficient (k:ℕ):ℝ:=2*heavyDrift*(1+Real.log ((k:ℝ)+1))+
  2/3+(60/Real.log (1+heavyDelta))*Real.log k

end KServer.EmbeddedCost

end


/-! The chronological triangle inequality for the literal priority stages. -/


/-! The all-step embedded motion of the selected hidden labeled optimum. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open ActualRoster RankTracking TierTemporal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def mappedCross (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H):ℝ:=
  ∑ l:Fin k,indicator (map s law hr σ a t (hidden s σ t l)≠
    map s law hr σ a (t.val+1) (hidden s σ (t.val+1) l))

end KServer.EmbeddedCost

end


/-! The finite all-scale offline embedding endpoint. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EmbeddedCost
open FiniteExperiment TierProcess Pilot LevelKeys LevelLaw LevelRetirement RankTracking
open ActualRoster RankTracking TierTemporal
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def spatialCoefficient (k:ℕ):ℝ:=8+1050*(60/Real.log (1+heavyDelta)+60)*Real.log k

def spatialMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ):ℝ:=
  ∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    LevelSpatial.separation s law (radius_pos hr (by linarith) j).le σ (t.val+1)
      (σ t) (hidden s σ t (mover s σ t))))

def keyMove (s:Configuration k Y) (law:RequestLaw Y H)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2≤τ) (n:ℕ):ℝ:=
  ∑ j∈range n,radius r₀ τ j*(∑ t:Fin H,avg law.val (fun σ=>
    mean (radius r₀ τ j) (fun a=>mappedCross s law
      (radius_pos hr (by linarith) j).le σ a t)))

end KServer.EmbeddedCost

end


/-! The finite all-scale embedding is used with the reversed geometric list
of radii in the top-down prefix construction, not with a moved quantifier. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointEmbedding
open JointExperiment RankTracking ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d)

def scaleCost (a:ℝ):ℝ:=if ha:0<a then
  ∑ t:Fin H,avg law.val (fun σ=>LevelRetirement.mean a (fun tape=>
    EmbeddedCost.mappedCross s law ha.le σ tape t)) else 0

end KServer.JointEmbedding

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_JointTravel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal retained-heavy anchor data and chronological payment on the one
joint request/tape experiment. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))
local instance keyDecEq : DecidableEq (LevelKeys.Key Y k) := Classical.decEq _
abbrev J:=HeavyLabels.Pool Y
local instance poolDecEq : DecidableEq (J (Y:=Y)) := Classical.decEq _

def key (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L):Y→Option (J (Y:=Y)):=
  HeavyKeys.key s law (r d) heavyGamma heavyDelta ω.val.1 (ω.val.2 d).1 t

def anchor (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L):J (Y:=Y)→Y:=
  heavyAnchor s law (r d) ω.val.1 (ω.val.2 d).1 t

def b (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):ℝ:=
  band s law hr hk t ω d.val (slot (k:=k) a)

def u (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):ℝ:=
  reference s law hr d.val (slot (k:=k) a) t ω

def c (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):ℝ:=
  b s law hr hk t ω d a/u s law hr t ω d a

def present (t:ℕ) (ω:Atom (k:=k) law hr) (d:Fin L) (a:J (Y:=Y)):Prop:=
  HeavyAnchorDynamics.present s law (r d) ω.val.1 (ω.val.2 d).1 t a

end KServer.JointHeavy

end


/-! Adapted chronological stage aggregation, retaining signed filtering. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
open RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))
attribute [local instance] keyDecEq poolDecEq

def travel (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ d:Fin L,∑ a:J (Y:=Y),if present s law hr t ω d a ∧ present s law hr (t+1) ω d a ∧
    anchor s law hr t ω d a≠anchor s law hr (t+1) ω d a then r d*b s law hr hk (t+1) ω d a else 0

def charge (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ d:Fin L,∑ a:J (Y:=Y),((6/5:ℝ)*72*r d*KeySizeTracking.refreshCost (size s law hr d.val (slot (k:=k) a)) t ω+
    2*(6/5:ℝ)*r d*|b s law hr hk (t+1) ω d a-b s law hr hk t ω d a|)

def potential (t:ℕ) (ω:Atom (k:=k) law hr):ℝ:=
  ∑ i:Fin k,familyTest r (c s law hr hk t ω) (anchor s law hr t ω) (key s law hr t ω) (hidden law hr s t ω i)

end KServer.JointHeavy

end


/-! The actual old heavy-slot coefficients have logarithmic all-scale sum. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHeavy
open JointExperiment JointAllocation LevelKeys TierProcess AnchorTravel HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq keyDecEq poolDecEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

def selected (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y) (d:ℕ):Option (LevelKeys.Key Y k):=
  if hd:d<L then HeavyAnchorDynamics.selected s law (r ⟨d,hd⟩) ω.val.1 (ω.val.2 ⟨d,hd⟩).1 t y else none

end KServer.JointHeavy

end


/-! Literal size-reference refresh budget summed over the fixed key inventory. -/


/-! Fixed bands are disjoint inventories, so grouping never enlarges variation. -/


/-! Full signed heavy-travel telescope for the actual joint experiment. -/


/-! Actual heavy references and fixed-band changes, charged to full-key
transport and the variation of the complete park inventory. -/


/-! Completion of the genuine observed prefix to an atom is used only on
positive fibers. Impossible histories receive the fixed root stock. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointHistory
open JointExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

def Observed (a:Tape Y k H L r) (h:List Y) (ω:Atom (k:=k) law hr):Prop:=
  ω.val.2=a ∧ h.length≤H ∧ (List.ofFn ω.val.1).take h.length=h

def q (a:Tape Y k H L r) (h:List Y):PrefixTree.Node (LevelKeys.Key Y k) L→ℝ:=
  if hp:∃ ω,Observed law hr a h ω then
    JointAllocation.quota s law hr hk h.length hp.choose
  else TreeRounding.stockMass (k:ℤ)

lemma q_nonneg (a:Tape Y k H L r) (h:List Y) (v:PrefixTree.Node (LevelKeys.Key Y k) L):
    0≤q s law hr hk a h v:=by
  unfold q
  split_ifs with hp
  · exact JointAllocation.quota_nonneg s law hr hk _ _ v
  · unfold TreeRounding.stockMass; split_ifs <;> positivity

lemma q_park_nonneg (a:Tape Y k H L r) (h:List Y) (v:PrefixTree.Node (LevelKeys.Key Y k) L):
    0≤(PrefixTree.tree (LevelKeys.Key Y k) L).park (q s law hr hk a h) v:=by
  unfold q
  split_ifs with hp
  · exact JointAllocation.park_nonneg s law hr hk _ _ v
  · rw [TreeRounding.stockMass_park]
    unfold TreeRounding.stockMass; split_ifs <;> positivity

lemma q_root (a:Tape Y k H L r) (h:List Y):q s law hr hk a h 0=(k:ℝ):=by
  unfold q
  split_ifs with hp
  · exact PrefixTree.Q_root _ L _ _ _ _ _ hk _ _
  · simp only [TreeRounding.stockMass,ite_true,Int.cast_natCast]

def anchors (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (key:LevelKeys.Key Y k):Y:=
  if hd:d<L then LevelKeys.anchor s law (hr ⟨d,hd⟩).le ω.val.1 (ω.val.2 ⟨d,hd⟩) t key else s 0

def a (tape:Tape Y k H L r) (h:List Y):ℕ→LevelKeys.Key Y k→Y:=
  if hp:∃ ω,Observed law hr tape h ω then anchors s law hr h.length hp.choose else fun _ _=>s 0

end KServer.JointHistory

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_MetricMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! In a finite laminar tree, one matching simultaneously has the optimal
crossing count at every cut. This is proved by the uncrossing minimizer, rather
than assuming a transport/matching interface. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LaminarMatching
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V Z I:Type*} [Fintype V] [Fintype I]

def Laminar (c:V→Z→Bool):Prop:=∀ v w,
  (∀ z,c v z=true→c w z=true) ∨ (∀ z,c w z=true→c v z=true) ∨
    (∀ z,c v z=true→c w z=false)

def bit (b:Bool):ℝ:=if b then 1 else 0

def cross (c:V→Z→Bool) (f g:I→Z) (π:Equiv.Perm I) (v:V) (i:I):ℝ:=
  |bit (c v (f i))-bit (c v (g (π i)))|

def cost (c:V→Z→Bool) (f g:I→Z) (π:Equiv.Perm I):ℝ:=∑ v,∑ i,cross c f g π v i

end KServer.LaminarMatching

end


/-! The concrete parent-ordered tree's descendant cuts form a laminar family. -/


/-! Metric movement of the simultaneous laminar matching. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Rounding
variable {n:ℕ} [NeZero n]
attribute [local instance] Classical.propDecidable Classical.decEq

def Tree.cutDistance (T:Tree n) (w:Fin n→ℝ) (u v:Fin n):ℝ:=
  ∑ z,w z*|T.indicator z u-T.indicator z v|

end KServer.Rounding

end


/-! A deepest common ancestor exposes a discrepant cut. This permits bounds
using witnesses only at occupied endpoints; no empty-prefix anchor edge is
assumed short. -/


/-! Every ancestor of an occupied word is witnessed by the same point. -/


/-! Geometric comparisons only at witnessed occupied words. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} [MetricSpace Y]

def nodeAnchor (z:Y) (a:ℕ→A→Y) (v:Node A L):Y:=
  match lastKey A L v with
  | none=>z
  | some key=>a (depth A L v-1) key

def nodeMotion (m:ℕ→A→ℝ) (v:Node A L):ℝ:=
  match lastKey A L v with
  | none=>0
  | some key=>m (depth A L v-1) key

end KServer.PrefixTree

end


/-! An actual labeled list of k occupied vertices for every consistent
nonnegative integral count state. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
open Rounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

def Tree.toTravel (T:Tree n):Rounding.Tree n where
  parent:=T.parent
  root:=T.root
  lower:=T.lower

lemma Tree.consistent_park (T:Tree n) (c:Counts n) (hc:T.Consistent c) (v:Fin n):
    (c.park v:ℝ)=T.park (fun u=>(c.subtree u:ℝ)) v:=by
  have hh:((c.park v:ℝ)+(∑ u:T.Child v,(c.subtree u.val:ℝ)))=(c.subtree v:ℝ):=by
    exact_mod_cast hc v
  unfold Tree.park
  linarith

lemma Tree.park_nats_sum (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0 ≤ c.park v) (hr:c.subtree 0=(k:ℤ)):
    (∑ v,(c.park v).toNat)=k:=by
  apply Nat.cast_injective (R:=ℝ)
  rw [Nat.cast_sum]
  have hh:=T.toTravel.park_subtree_total (fun u=>(c.subtree u:ℝ)) 0
  have hi:∀ v,T.toTravel.indicator 0 v=1:=by
    intro v
    simp only [Rounding.Tree.indicator,Rounding.Tree.under_root,ite_true]
  simp only [hi,one_mul] at hh
  calc
    (∑ v,((c.park v).toNat:ℝ))=∑ v,(c.park v:ℝ):=by
      apply sum_congr rfl; intro v _
      exact_mod_cast Int.toNat_of_nonneg (hp v)
    _ = ∑ v,T.toTravel.park (fun u=>(c.subtree u:ℝ)) v:=by
      apply sum_congr rfl; intro v _; exact T.consistent_park c hc v
    _ = (k:ℝ):=by rw [hh,hr]; rfl

def countEquiv (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0 ≤ c.park v) (hr:c.subtree 0=(k:ℤ)):
    (Σ v:Fin n,Fin (c.park v).toNat)≃Fin k:=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_sigma,Fintype.card_fin] using T.park_nats_sum c hc hp hr)

def slots (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0 ≤ c.park v) (hr:c.subtree 0=(k:ℤ)) (i:Fin k):Fin n:=
  ((countEquiv T c hc hp hr).symm i).1

lemma slots_sum (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0 ≤ c.park v) (hr:c.subtree 0=(k:ℤ)) (f:Fin n→ℝ):
    (∑ i:Fin k,f (slots T c hc hp hr i))=∑ v,(c.park v:ℝ)*f v:=by
  unfold slots
  rw [Equiv.sum_comp (countEquiv T c hc hp hr).symm (fun p=>f p.1)]
  simp only [Fintype.sum_sigma,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply sum_congr rfl
  intro v _
  have he : ((c.park v).toNat:ℝ)=(c.park v:ℝ):=by
    exact_mod_cast Int.toNat_of_nonneg (hp v)
  rw [he]

lemma slots_subtree (T:Tree n) (c:Counts n) (hc:T.Consistent c)
    (hp:∀ v,0 ≤ c.park v) (hr:c.subtree 0=(k:ℤ)) (u:Fin n):
    (∑ i:Fin k,T.toTravel.indicator u (slots T c hc hp hr i))=(c.subtree u:ℝ):=by
  rw [slots_sum]
  simp_rw [T.consistent_park c hc,mul_comm (T.park _ _) (T.toTravel.indicator _ _)]
  exact T.toTravel.park_subtree_total _ u

end KServer.TreeRounding

end


/-! Cross-time occupied-endpoint matching, without any edge hypothesis on
empty words. New endpoint anchor drift is paid only for coincident vertices. -/


/-! The fixed finite inventory of integral count states with total mass k.
The encoding is an actual k-slot list, not a bound on future randomness. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n k:ℕ} [NeZero n]

def Good (T:Tree n) (k:ℕ) (c:Counts n):Prop:=
  T.Consistent c ∧ (∀ v,0≤ c.park v) ∧ c.subtree 0=(k:ℤ)
abbrev Inventory (T:Tree n) (k:ℕ):= {c:Counts n //Good T k c}

def Inventory.slots (T:Tree n) (c:Inventory T k):Fin k→Fin n:=
  TreeRounding.slots T c.val c.property.1 c.property.2.1 c.property.2.2

lemma Inventory.slots_injective (T:Tree n):Function.Injective (Inventory.slots (k:=k) T):=by
  intro c d he
  have hsub: c.val.subtree=d.val.subtree:=by
    funext u
    apply Int.cast_injective (α:=ℝ)
    have h1:=slots_subtree T c.val c.property.1 c.property.2.1 c.property.2.2 u
    have h2:=slots_subtree T d.val d.property.1 d.property.2.1 d.property.2.2 u
    change (∑ i,T.toTravel.indicator u (Inventory.slots T c i))=_ at h1
    change (∑ i,T.toTravel.indicator u (Inventory.slots T d i))=_ at h2
    rw [he] at h1
    exact h1.symm.trans h2
  have hpark:c.val.park=d.val.park:=by
    funext u
    apply Int.cast_injective (α:=ℝ)
    rw [T.consistent_park c.val c.property.1,T.consistent_park d.val d.property.1,hsub]
  apply Subtype.ext
  have hh : ∀ (c d : Counts n), c.subtree=d.subtree → c.park=d.park → c=d := by
    intro c d h1 h2
    cases c; cases d
    simp only [Counts.mk.injEq] at *
    exact ⟨h1,h2⟩
  exact hh _ _ hsub hpark

instance inventoryFintype (T:Tree n):Fintype (Inventory T k):=
  Fintype.ofInjective (Inventory.slots T) (Inventory.slots_injective T)

lemma stock_good (T:Tree n):Good T k (stock (k:ℤ)):=by
  have hh:=stock_valid T (Int.natCast_nonneg k)
  exact ⟨hh.2.2,fun v=>(hh.2.1 v).1,by simp only [stock,ite_true]⟩

instance inventoryNonempty (T:Tree n):Nonempty (Inventory T k):=⟨⟨stock (k:ℤ),stock_good T⟩⟩

def pack (T:Tree n) (c:Counts n):Inventory T k:=
  if h:Good T k c then ⟨c,h⟩ else ⟨stock (k:ℤ),stock_good T⟩

end KServer.TreeRounding

end


/-! Genuine occupied-slot matching on the complete prefix tree. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PrefixTree
attribute [local instance] Classical.propDecidable Classical.decEq
variable (A:Type) [Fintype A] (L:ℕ)
variable {Y:Type} [MetricSpace Y] {k:ℕ}

def countConfig (z:Y) (a:ℕ→A→Y) (c:TreeRounding.Inventory (tree A L) k):Configuration k Y:=
  fun i=>nodeAnchor A L z a (c.slots (tree A L) i)

end KServer.PrefixTree

end


/-! Rounded occupied vertices have positive fractional park, and all positive
integer parks occur in the actual labeled list. -/


/-! Exact fixed-band aggregation of the occupied anchor drift. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_MetricService
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common complete keys have controlled anchors. Only common moving heavy
labels incur chronological travel; tiers and singleton fallback are fixed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelKeys
open FiniteExperiment TierProcess HeavyAnchorDynamics
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r)

def motion (t:ℕ):Key Y k→ℝ
  | Sum.inl ⟨none,a⟩ => if HeavyAnchorDynamics.present s law r σ tape.1 t a ∧
      HeavyAnchorDynamics.present s law r σ tape.1 (t+1) a ∧
      heavyAnchor s law r σ tape.1 t a≠heavyAnchor s law r σ tape.1 (t+1) a then r else 0
  | _=>0

end KServer.LevelKeys

end


/-! Cross-time metric rounding uses witnesses only for occupied vertices.
Its anchor surcharge is exactly the already-paid heavy travel. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointMetric
open JointExperiment JointAllocation JointHistory
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

abbrev Node:=PrefixTree.Node (LevelKeys.Key Y k) L
def motion (t:ℕ) (ω:Atom (k:=k) law hr) (d:ℕ) (key:LevelKeys.Key Y k):ℝ:=
  if hd:d<L then LevelKeys.motion s law ω.val.1 (ω.val.2 ⟨d,hd⟩) t key else 0

end KServer.JointMetric

end


/-! A finest-scale singleton region contains the request with quota at least
one. Balanced parks therefore give actual labeled service, not just a marginal
hitting probability. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointService
open JointExperiment JointAllocation JointHistory
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

abbrev Node:=PrefixTree.Node (LevelKeys.Key Y k) L

def leaf (t:ℕ) (ω:Atom (k:=k) law hr) (y:Y):Node (Y:=Y) (k:=k) (L:=L):=
  (PrefixTree.numbering (LevelKeys.Key Y k) L).symm
    ⟨⟨L,Nat.lt_succ_self L⟩,fun i=>maps law hr s t ω i.val y⟩

end KServer.JointService

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_CausalRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pushing the actual finite rounded law onto one fixed finite state space. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {α S:Type} [Fintype S]

def Law.mass (L:Law α) (f:α→S) (s:S):ℝ:=L.avg (fun a=>if f a=s then 1 else 0)
omit [Fintype S] in
lemma Law.mass_nonneg (L:Law α) (f:α→S) (s:S):0≤ L.mass f s:=by
  unfold Law.mass Law.avg
  exact sum_nonneg (fun ω _=>mul_nonneg (L.nonneg ω) (by dsimp only; split_ifs <;> norm_num))
lemma Law.mass_sum (L:Law α) (f:α→S):(∑ s,L.mass f s)=1:=by
  unfold Law.mass Law.avg
  rw [sum_comm]
  simp only [←mul_sum,sum_ite_eq,mem_univ,ite_true,mul_one,L.total]

omit [Fintype S] in
lemma Law.mass_left {T:Type} [Fintype T] (L:Law α) (f:α→S) (g:α→T) (s:S):
    (∑ z:T,L.mass (fun a=>(f a,g a)) (s,z))=L.mass f s:=by
  unfold Law.mass Law.avg
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [←mul_sum]
  congr 1
  by_cases h:f (L.point ω)=s
  · simp only [Prod.mk.injEq,h,true_and,ite_true,sum_ite_eq,mem_univ,ite_true]
  · simp only [Prod.mk.injEq,h,false_and,ite_false,sum_const_zero]

lemma Law.mass_right {T:Type} [Fintype T] (L:Law α) (f:α→S) (g:α→T) (z:T):
    (∑ s:S,L.mass (fun a=>(f a,g a)) (s,z))=L.mass g z:=by
  unfold Law.mass Law.avg
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [←mul_sum]
  congr 1
  by_cases h:g (L.point ω)=z
  · simp only [Prod.mk.injEq,h,and_true,ite_true,sum_ite_eq,mem_univ,ite_true]
  · simp only [Prod.mk.injEq,h,and_false,ite_false,sum_const_zero]
end KServer.TreeRounding

end


/-! Explicit causal finite-state implementation of a family of consecutive
couplings. Only the two prescribed marginals are supplied, not a cost conclusion. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X S:Type} [Fintype S] [Nonempty S]

structure Family (X S:Type) [Fintype S] where
  marginal:List X→ S→ ℝ
  nonneg:∀ h s,0≤ marginal h s
  normalized:∀ h,∑ s,marginal h s=1
  joint:List X→ X→ S→ S→ ℝ
  joint_nonneg:∀ h r s z,0≤ joint h r s z
  left:∀ h r s,∑ z,joint h r s z=marginal h s
  right:∀ h r z,∑ s,joint h r s z=marginal (h++[r]) z

variable (F:Family X S)
def kernel (h:List X) (r:X) (s z:S):ℝ:=
  if 0<F.marginal h s then F.joint h r s z/F.marginal h s else if z=Classical.choice ‹Nonempty S› then 1 else 0

lemma kernel_nonneg (h:List X) (r:X) (s z:S):0≤ kernel F h r s z:=by
  unfold kernel
  split_ifs with hs hz
  · exact div_nonneg (F.joint_nonneg h r s z) hs.le
  · norm_num
  · norm_num
lemma kernel_sum (h:List X) (r:X) (s:S):(∑ z,kernel F h r s z)=1:=by
  unfold kernel
  by_cases hs:0<F.marginal h s
  · simp only [ite_eq_left hs,←sum_div,F.left,div_self hs.ne']
  · simp [hs]

variable {k:ℕ} [NeZero k]
def machine : HiddenMachine.Data k X S where
  initial:=F.marginal []
  initial_nonneg:=F.nonneg []
  initial_sum:=F.normalized []
  transition h r:=kernel F (h.map Prod.fst) r
  transition_nonneg h r:=kernel_nonneg F (h.map Prod.fst) r
  transition_sum h r:=kernel_sum F (h.map Prod.fst) r
  output _ _ _ _:=0
  nullOutput _ _:=0

variable [MetricSpace X] (start:Configuration k X) (V:List X→ S→ Configuration k X)
variable (hc:∀ h r s,∃ i,V (h++[r]) s i=r)

def cost (h:List X) (s:S):List X→ ℝ
  | []=>0
  | r::σ=>∑ z,kernel F h r s z*(matching (V h s) (V (h++[r]) z)+cost (h++[r]) z σ)

def transport (h:List X) (r:X):ℝ:=∑ s,∑ z,F.joint h r s z*matching (V h s) (V (h++[r]) z)

def pathCost (h:List X):List X→ ℝ
  | []=>0
  | r::σ=>transport F V h r+pathCost (h++[r]) σ

end KServer.CausalCouplings

end


/-! Sequential balanced count sampling on one fixed finite tree. The full
old marginal is retained at every request, so one causal machine works at all
horizons. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TreeRounding
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X:Type} {n k:ℕ} [NeZero n]
variable (T:Tree n) {τ:ℝ} (hτ:22≤τ) (w:Fin n→ℝ) (hw:∀ u,0≤w u)
  (hscale:∀ u,u≠0→w (T.parent u)=τ*w u)
  (q:List X→Fin n→ℝ) (hq:∀ h v,0≤q h v) (hp:∀ h v,0≤T.park (q h) v)
  (hr:∀ h,q h 0=(k:ℝ))

structure CountState (T:Tree n) (k:ℕ) (a:Fin n→ℝ) where
  law:Law (Counts n)
  valid:∀ ω,T.Valid a (law.point ω)
  root:∀ ω,(law.point ω).subtree 0=(k:ℤ)
  mean:T.Means a law

include hq hp hr in
lemma count_initial:Nonempty (CountState T k (q [])):=by
  obtain ⟨L,hL,hm⟩:=tree_initialization T (q []) (Int.natCast_nonneg k)
    (hq []) (hp []) (by exact_mod_cast hr [])
  exact ⟨⟨L,fun ω=>(hL ω).1,fun ω=>(hL ω).2,hm⟩⟩

def initialCount:CountState T k (q []):=Classical.choice (count_initial T q hq hp hr)

include hτ hw hscale hq hp hr in
lemma count_step_exists (h:List X) (x:X) (S:CountState T k (q h)):
    ∃ L:Law (PairState n),
      (∀ f:Counts n→ℝ,L.avg (fun s=>f s.old)=S.law.avg f) ∧
      (∀ ω,T.Valid (q h) (L.point ω).old ∧ T.Valid (q (h++[x])) (L.point ω).new ∧
        (L.point ω).new.subtree 0=(k:ℤ)) ∧
      T.Means (q (h++[x])) (L.map PairState.new) ∧
      L.avg (fun s=>∑ u,w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|)≤
        132*(∑ u,w (T.parent u)*|q h u-q (h++[x]) u|):=by
  exact rounded_step T hτ w (q h) (q (h++[x])) hw hscale (Int.natCast_nonneg k)
    (by exact_mod_cast hr h) (by exact_mod_cast hr (h++[x])) (hq h) (hp h)
    (hq (h++[x])) (hp (h++[x])) S.law S.valid S.mean

def countStepLaw (h:List X) (x:X) (S:CountState T k (q h)):Law (PairState n):=
  Classical.choose (count_step_exists T hτ w hw hscale q hq hp hr h x S)

theorem countStep_spec (h:List X) (x:X) (S:CountState T k (q h)) :
    (∀ f:Counts n→ℝ,(countStepLaw T hτ w hw hscale q hq hp hr h x S).avg (fun s=>f s.old)=S.law.avg f) ∧
    (∀ ω,T.Valid (q h) ((countStepLaw T hτ w hw hscale q hq hp hr h x S).point ω).old ∧
      T.Valid (q (h++[x])) ((countStepLaw T hτ w hw hscale q hq hp hr h x S).point ω).new ∧
      ((countStepLaw T hτ w hw hscale q hq hp hr h x S).point ω).new.subtree 0=(k:ℤ)) ∧
    T.Means (q (h++[x])) ((countStepLaw T hτ w hw hscale q hq hp hr h x S).map PairState.new) ∧
    (countStepLaw T hτ w hw hscale q hq hp hr h x S).avg
      (fun s=>∑ u,w (T.parent u)*|(s.new.subtree u:ℝ)-(s.old.subtree u:ℝ)|)≤
        132*(∑ u,w (T.parent u)*|q h u-q (h++[x]) u|) :=
  Classical.choose_spec (count_step_exists T hτ w hw hscale q hq hp hr h x S)

def nextCount (h:List X) (x:X) (S:CountState T k (q h)):CountState T k (q (h++[x])) where
  law:=(countStepLaw T hτ w hw hscale q hq hp hr h x S).map PairState.new
  valid ω:=(countStep_spec T hτ w hw hscale q hq hp hr h x S).2.1 ω |>.2.1
  root ω:=(countStep_spec T hτ w hw hscale q hq hp hr h x S).2.1 ω |>.2.2
  mean:=(countStep_spec T hτ w hw hscale q hq hp hr h x S).2.2.1

def countState (h:List X):CountState T k (q h):=
  List.reverseRecOn h (initialCount T q hq hp hr)
    (fun h x S=>nextCount T hτ w hw hscale q hq hp hr h x S)

lemma countState_snoc (h:List X) (x:X):
    countState T hτ w hw hscale q hq hp hr (h++[x])=
      nextCount T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h):=by
  simp only [countState,List.reverseRecOn_concat]

def pairLaw (h:List X) (x:X):Law (PairState n):=
  countStepLaw T hτ w hw hscale q hq hp hr h x (countState T hτ w hw hscale q hq hp hr h)

def countFamily:CausalCouplings.Family X (Inventory T k) where
  marginal h:=(countState T hτ w hw hscale q hq hp hr h).law.mass (pack T)
  nonneg h:=(countState T hτ w hw hscale q hq hp hr h).law.mass_nonneg (pack T)
  normalized h:=(countState T hτ w hw hscale q hq hp hr h).law.mass_sum (pack T)
  joint h x s z:=(pairLaw T hτ w hw hscale q hq hp hr h x).mass
    (fun p=>(pack T p.old,pack T p.new)) (s,z)
  joint_nonneg h x s z:=(pairLaw T hτ w hw hscale q hq hp hr h x).mass_nonneg _ _
  left h x s:=by
    rw [Law.mass_left]
    unfold Law.mass pairLaw countStepLaw
    exact (countStep_spec T hτ w hw hscale q hq hp hr h x
      (countState T hτ w hw hscale q hq hp hr h)).1 (fun c=>@ite ℝ (pack T c=s) (Classical.decEq _ _ _) 1 0)
  right h x z:=by
    rw [Law.mass_right,countState_snoc]
    rfl

end KServer.TreeRounding

end


/-! The sequential family keeps exact new park means and the factor-132
weighted subtree transport estimate. -/


/-! An independent permanent finite tape, sampled once before the requests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {X I S:Type} [Fintype I] [Fintype S]
variable (w:I→ℝ) (hw:∀ i,0≤w i) (h1:∑ i,w i=1) (F:I→Family X S)

def mixture:Family X (I×S) where
  marginal h s:=w s.1*(F s.1).marginal h s.2
  nonneg h s:=mul_nonneg (hw s.1) ((F s.1).nonneg h s.2)
  normalized h:=by simp only [Fintype.sum_prod_type,←mul_sum,Family.normalized,mul_one,h1]
  joint h r s z:=if s.1=z.1 then w s.1*(F s.1).joint h r s.2 z.2 else 0
  joint_nonneg h r s z:=by split_ifs; exact mul_nonneg (hw _) ((F _).joint_nonneg _ _ _ _); rfl
  left h r s:=by
    simp only [Fintype.sum_prod_type]
    rw [sum_eq_single s.1]
    · simp only [ite_true,←mul_sum,Family.left]
    · intro i _ hi
      simp only [Ne.symm hi,ite_false,sum_const_zero]
    · simp only [mem_univ,not_true_eq_false,false_implies]
  right h r z:=by
    simp only [Fintype.sum_prod_type]
    rw [sum_eq_single z.1]
    · simp only [ite_true,←mul_sum,Family.right]
    · intro i _ hi
      simp only [hi,ite_false,sum_const_zero]
    · simp only [mem_univ,not_true_eq_false,false_implies]

variable [Nonempty S] [MetricSpace X] {k:ℕ} [NeZero k]

def safeConfig (z:X) (V:List X→S→ Configuration k X) (h:List X) (s:S):Configuration k X:=
  if h=[] then V h s else if ∃ i,V h s i=h.getLastD z then V h s else fun _=>h.getLastD z

end KServer.CausalCouplings

end


/-! Explicit finite-horizon cost of the same causal machine. -/


/-! Actual history-indexed count laws and their rendered labeled configurations.
Impossible histories are completed by a service-safe output, whereas every
positive experimental prefix uses the genuine allocated occupied anchors. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointRounded
open JointExperiment JointAllocation JointHistory CausalCouplings
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

abbrev T:=PrefixTree.tree (LevelKeys.Key Y k) L
abbrev State:=TreeRounding.Inventory (T (Y:=Y) (k:=k) (L:=L)) k

def family {R τ:ℝ} (hR:0≤R) (hτ:22≤τ) (tape:Tape Y k H L r):Family Y (State (Y:=Y) (k:=k) (L:=L)):=
  TreeRounding.countFamily T hτ (PrefixTree.weight (LevelKeys.Key Y k) L R τ)
    (PrefixTree.weight_nonneg _ L hR (by linarith)) (PrefixTree.parent_weight _ L (by linarith))
    (q s law hr hk tape) (q_nonneg s law hr hk tape) (q_park_nonneg s law hr hk tape) (q_root s law hr hk tape)

def rawConfig (tape:Tape Y k H L r) (h:List Y) (c:State (Y:=Y) (k:=k) (L:=L)):Configuration k Y:=
  PrefixTree.countConfig (LevelKeys.Key Y k) L (s 0) (a s law hr tape h) c

def config (tape:Tape Y k H L r):List Y→ State (Y:=Y) (k:=k) (L:=L)→ Configuration k Y:=
  safeConfig (s 0) (rawConfig s law hr tape)

end KServer.JointRounded

end


/-! The actual permanent-tape sequentially rounded experiment returns a causal
strongly lazy policy. All impossible histories were already service-completed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointPolicy
open JointExperiment JointRounded CausalCouplings RankTracking ActualCharges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

abbrev MixState:=Tape Y k H L r × State (Y:=Y) (k:=k) (L:=L)

def mixed {R τ:ℝ} (hR:0≤R) (hτ:22≤τ):Family Y (MixState (Y:=Y) (k:=k) (H:=H) (r:=r)):=
  mixture (tapeWeight r) (tapeWeight_nonneg hr) (tapeWeight_sum hr) (family s law hr hk hR hτ)

def rendered (h:List Y) (z:MixState (Y:=Y) (k:=k) (H:=H) (r:=r)):Configuration k Y:=
  config s law hr z.1 h z.2

end KServer.JointPolicy

end

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute constants for the unconditional finite-law endpoint. No metric,
finite-tree depth, horizon, law or initial tuple enters these coefficients. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
open ActualCharges RankTracking JointExperiment JointAllocation
attribute [local instance] Classical.propDecidable Classical.decEq

def core : ℝ := (6/5:ℝ)*72
def cutoff : ℝ := 7*core/Real.log 2+2*core
def quotaMultiplier : ℝ := 15840+640*(6/5:ℝ)
def keyMultiplier : ℝ := quotaMultiplier*(384*localConstant)+160*core*289
def optMultiplier : ℝ := 160*cutoff/3

def embA : ℝ := 147*TierProcess.tierDrift+2*EmbeddedCost.heavyDrift
def embB : ℝ := 98/TierProcess.heavyGamma+32+2/3+8
def embC : ℝ := 32+31440+60/Real.log (1+TierProcess.heavyDelta)+
  1050*(60/Real.log (1+TierProcess.heavyDelta)+60)
def embeddingMultiplier : ℝ := |embA|+|embB|+|embC|+1
def competitiveMultiplier : ℝ := keyMultiplier*embeddingMultiplier+optMultiplier

end KServer.GlobalEndpoint

end


/-! Main finite construction at separation ratio 32. Initial inventories are
explicitly independent of both the request law and its horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.GlobalEndpoint
open ActualCharges RankTracking JointExperiment JointAllocation
attribute [local instance] Classical.propDecidable Classical.decEq

def radii (R:ℝ) (L:ℕ) (d:Fin L):ℝ:=R/(32:ℝ)^(d.val+1)
lemma radii_pos {R:ℝ} {L:ℕ} (hR:0<R) (d:Fin L):0 < radii R L d:=
  div_pos hR (by positivity)

def quotaInventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  2*localConstant*ActualCaps.ell k*
    HierarchicalQuota.treeInventory (LevelKeys.Key Y k) k (fun d=>R/(32:ℝ)^d) L
def chargeInventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  core*(∑ d:Fin L,radii R L d)*(Fintype.card (LevelKeys.Key Y k)*
    (288*((k:ℝ)+1)*(1+ActualCaps.ell k)))
def potentialInventory (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=core*k*(∑ d:Fin L,radii R L d)
def embeddingInventory (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  (299+Fintype.card (LevelKeys.Tier k))*EmbeddedCost.inventory k (R/(32:ℝ)^L) 32 L
def baseInventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  quotaMultiplier*quotaInventory Y k R L+160*chargeInventory Y k R L+
    160*potentialInventory k R L+(k:ℝ)*R
def inventory (Y:Type) [Fintype Y] (k:ℕ) (R:ℝ) (L:ℕ):ℝ:=
  baseInventory Y k R L+keyMultiplier*ActualCaps.ell k*embeddingInventory k R L

end KServer.GlobalEndpoint

end


/-! Every finite metric admits a finite geometric prefix depth; no discreteness
assumption is introduced at the arbitrary-metric endpoint. -/

end OAI
end

section
-- module Solutions.OAIQ17_KS.KServer_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relabel a finite metric across universes without changing the experiment,
initial labels, service constraints, optimal cost or behavior-policy horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteMetricTransport
attribute [local instance] Classical.propDecidable Classical.decEq
universe u v
variable {Y:Type u} {Z:Type v}

variable [MetricSpace Y] [MetricSpace Z]

variable [Fintype Y] [Fintype Z]
omit [MetricSpace Y] [MetricSpace Z] in
def lawOn {H:ℕ} (e:Y≃Z) (law:FiniteDistribution (Fin H→Y)):FiniteDistribution (Fin H→Z):=
  ⟨fun σ=>law.val (e.symm∘σ),fun σ=>law.property.1 _,by
    calc
      (∑ σ:Fin H→Z,law.val (e.symm∘σ))=∑ σ:Fin H→Y,law.val σ:=by
        exact Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin H)) e.symm)
          _ _ (fun _=>rfl)
      _=1:=law.property.2⟩

end KServer.FiniteMetricTransport

end


/-! Unconditional finite-law theorem, with one absolute coefficient and a
law/horizon-independent inventory. Finite relabeling removes the construction's
universe-zero implementation restriction. -/

end OAI
end


