-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Prob
-- name    : ChoiSemiHonestMPC_OTUpper_Prob
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:27:39.562448+00:00
-- url     : https://prove2.me/theorems/c5de2d21-be4b-4d47-b65a-cf6179b41089
-- title:
--   Statistical distance, probability, expectation and conditioning
-- statement:
--   Basic probabilistic notation (Section 2, *Notation*). For measures, $\mathrm{TV}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$ over measurable sets $A$; for discrete distributions, $\mathrm{TV}(p,q)=\tfrac12\sum_x|p(x)-q(x)|$ (computed in $[0,\infty]$, so no summability side condition). `probE` is the probability of an event, `expectE` the expectation of a natural-number valued variable in $[0,\infty]$ (an infinite expectation is $\infty$, never $0$). `pcond μ E` is the conditional distribution given an event of positive probability (on a null event it returns $\mu$; every use conditions on an event of positive probability). `unifSubsets S k` is the uniform distribution on $k$-subsets of $S$; `bern p` is Bernoulli($p$) (with $p$ clamped to $[0,1]$; every use has $0\le p\le1$); `unifBit` a uniform bit.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Section 2, Notation, p. 12 (PDF 14)

import Mathlib

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Statistical (total variation) distance of two measures:
`sup` over measurable sets `A` of `|μ A - ν A|`.  Used for arbitrary measurable spaces
(Lemmas 4.1, 4.2); for probability measures every term lies in `[0, 1]`. -/
def tvMeasure {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ s : {s : Set α // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

/-- Statistical distance of two discrete distributions: half the `ℓ¹` distance,
`½ ∑ₓ |p x - q x|`, computed in `ℝ≥0∞` (so no summability side condition) and then
converted to `ℝ` (the sum is at most `2`). -/
def tvPMF {α : Type*} (p q : PMF α) : ℝ :=
  (∑' x, ((p x - q x) + (q x - p x))).toReal / 2

/-- Probability of an event under a discrete distribution. -/
def probE {α : Type*} (μ : PMF α) (E : α → Prop) : ℝ :=
  (μ.toOuterMeasure {x | E x}).toReal

/-- Expectation of a natural-number-valued random variable, in `ℝ≥0∞`
(an infinite expectation is `⊤`, never a junk `0`). -/
def expectE {α : Type*} (μ : PMF α) (f : α → ℕ) : ℝ≥0∞ :=
  ∑' x, μ x * (f x : ℝ≥0∞)

/-- Conditional distribution given an event of positive probability; on a null event it
returns `μ` itself (a value no statement below uses: every conditioning event is either
assumed or proved to have positive probability). -/
def pcond {α : Type*} (μ : PMF α) (E : α → Prop) : PMF α :=
  by
    classical
    exact if h : ∃ x, x ∈ {y | E y} ∧ x ∈ μ.support then μ.filter {y | E y} (by
      obtain ⟨x, hx, hs⟩ := h; exact ⟨x, hx, hs⟩) else μ

/-- Uniform distribution on the `k`-subsets of a finite set `S` (`pure ∅` when `k > |S|`,
a case in which no statement below samples). -/
def unifSubsets {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) : PMF (Finset α) :=
  if h : k ≤ S.card then
    PMF.uniformOfFinset (S.powersetCard k)
      (Finset.powersetCard_nonempty.mpr h)
  else PMF.pure ∅

/-- Bernoulli distribution with success probability `min p 1` (`p` is clamped so the
definition is total; every use below has `0 ≤ p ≤ 1`). -/
def bern (p : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => if b then ((min (Real.toNNReal p) 1 : ℝ≥0) : ℝ≥0∞)
      else 1 - ((min (Real.toNNReal p) 1 : ℝ≥0) : ℝ≥0∞))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false]
      exact add_tsub_cancel_of_le (by exact_mod_cast min_le_right _ _))

/-- A uniform bit. -/
def unifBit : PMF Bool := PMF.uniformOfFintype Bool

end ChoiSemiHonestMPC.OTUpper


