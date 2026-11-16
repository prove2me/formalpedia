-- Prove2me | Definitions.Def_BatchMaxService_Metric_Supplement_LowerBounds
-- name    : BatchMaxService_Metric_Supplement_LowerBounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:03:19.520897+00:00
-- url     : https://prove2.me/theorems/b767768f-0e59-4366-9d51-a726e5958472
-- title:
--   Promised hidden-request instances and oblivious randomized search bounds
-- statement:
--   The promised input is one identity arriving at time zero, with a fixed start and one unknown site; every possible location has the same announcement. Policies are fixed on this promise class, so they may use advance knowledge that no later requests will arrive. The literal three-site line has coordinates $-1,0,1$; a unit star has center index zero and $d$ leaf indices. The zero-leaf representation is retained as the one-site case.
--
--   $$\exists v\in\text{leaves}:\quad \operatorname{OPT}(I_v)=1,\qquad \mathbb E_\omega[\operatorname{ALG}_{A_\omega}(I_v)]\ge b.$$
--
--   The hidden-site witness is outside the random-seed integral. Randomization is an arbitrary probability-space mixture of feedback policies, almost surely feasible on each promised fixed input, with measurable extended nonnegative cost. Infinite expectation is admitted. The companion deterministic condition uses a single feasible feedback policy and a worst fixed leaf. Neither condition assumes laziness, bounded waiting, no revisits, or efficient computation. A separate concrete parked policy supplies zero-cost one-site service.
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Section 7.5 and Theorem 7.7, printed pp. 29–30 / PDF pp. 30–31; Section 6 one-site convention, printed p. 20 / PDF p. 21

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_Interaction

namespace BatchMaxService.Metric.Supplement

open MeasureTheory

variable {n : ℕ}

/-- The same announced identity/time for every possible hidden location.
    Policies in the search statements are chosen for this promise-only input class. -/
def singleRequest (s v : Fin n) : RequestInput n where
  start := s
  ids := {0}
  arrival := fun _ => 0
  location := fun _ => v
  arrival_nonneg := by intro q hq; exact le_rfl

/-- Center is index zero. Real formula avoids truncated natural subtraction. -/
def UnitStarMetric (d : ℕ) [MetricSpace (Fin (d + 1))] : Prop :=
  ∀ u v : Fin (d + 1), dist u v =
    if u = v then 0 else if u = 0 ∨ v = 0 then 1 else 2

noncomputable def starLeaves (d : ℕ) : Finset (Fin (d + 1)) :=
  Finset.univ.image Fin.succ

/-- The literal ordered line {-1,0,1}, centered at index one. -/
def ThreeSiteLineMetric [MetricSpace (Fin 3)] : Prop :=
  ∀ u v : Fin 3, dist u v = |((u.val : ℝ) - 1) - ((v.val : ℝ) - 1)|

/-- Deterministic and oblivious randomized single-request conclusions together.
    The randomized witness is outside the seed integral. Costs may be infinite;
    feasibility is almost sure separately on every promised fixed input. -/
noncomputable def HiddenSearchBounds [MetricSpace (Fin n)] (r : Rule) (s : Fin n)
    (leaves : Finset (Fin n)) (det rand : ℝ) : Prop :=
  (∀ (S : Type) (p : Policy n S),
    (∀ v : Fin n, ValidOn .blind r p (singleRequest s v)) →
    ∃ v ∈ leaves, ruleOPT r (singleRequest s v) = 1 ∧
      ENNReal.ofReal det ≤ policyCost .blind r p (singleRequest s v)) ∧
  (∀ (Ω S : Type) [MeasurableSpace Ω] (μ : Measure Ω), IsProbabilityMeasure μ →
    ∀ A : Ω → Policy n S,
      (∀ v : Fin n, ∀ᵐ ω ∂μ, ValidOn .blind r (A ω) (singleRequest s v)) →
      (∀ v : Fin n, Measurable (fun ω => policyCost .blind r (A ω) (singleRequest s v))) →
      ∃ v ∈ leaves, ruleOPT r (singleRequest s v) = 1 ∧
        ENNReal.ofReal rand ≤ ∫⁻ ω, policyCost .blind r (A ω) (singleRequest s v) ∂μ)

/-- A concrete zero-movement policy for the one-site case; it elects parked
    service after each announcement and also works with automatic forced hits. -/
noncomputable def parkedPolicy (n : ℕ) : Policy n (Finset ℕ × ℝ) where
  initial _ := ((∅, 0), 1)
  receive st fb := ((st.1 ∪ (fb.announced \ fb.served), fb.time), 10 * (fb.announced.card + 1))
  choose _ s st := by
    classical
    exact (if st.1 = ∅ then none else some ⟨st.2, [s], st.1⟩, 10)
  respond _ _ _ := ((∅, 0), 10)

end BatchMaxService.Metric.Supplement


