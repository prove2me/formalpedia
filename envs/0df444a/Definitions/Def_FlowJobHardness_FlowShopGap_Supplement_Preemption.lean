-- Prove2me | Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Preemption
-- name    : FlowJobHardness_FlowShopGap_Supplement_Preemption
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:25:06.860685+00:00
-- url     : https://prove2.me/theorems/d96da520-d914-4a4d-90be-499828fa35b3
-- title:
--   Full real-time preemption and finite rational schedule descriptions
-- statement:
--   A preemptive execution assigns to each operation $o$ a start window $[b_o,f_o)$ and a measurable set $A_o$ of actual processing times inside that window, on its prescribed machine. It is feasible when
--   $$0\le b_o\le f_o,\qquad |A_o|=p_o,$$
--   all earlier operations of a job have finished before a later one starts, and distinct operations assigned to one machine have disjoint processing sets. Thus execution has unit speed, respects the original chains and loses no work on interruption.
--
--   This gives the full real-time comparator for Theorem 1.6, including arbitrary measurable preemption. The recorded finish may pad the actual completion by idle time; trimming such padding recovers the same optimum. A returned schedule has a finite rational list of processing intervals per operation, encoded by their endpoints. No integer breakpoint restriction is imposed, and comparison remains with every feasible real-time execution. Makespan and unweighted completion sum are the corresponding finite maxima and sum, with zero for empty index sets.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, DOI 10.1145/2027216.2027218, p. 20:3, §1.1; pp. 20:24–20:30, §4.2

import Mathlib
import Definitions.Def_FlowJobHardness_FlowShopGap_Supplement_Model
set_option autoImplicit false

namespace FlowJobHardness.FlowShopGap.Supplement

open JobShopLTAS.Core MeasureTheory

/-- Full real-time unit-speed preemption: operation o executes on its assigned
machine at the measurable times active o between begin o and finish o.
Work is Lebesgue measure, and capacity holds pointwise. Execution sets need not
be finite unions of intervals. Endpoints may include idle time; this only pads
completion times and does not exclude any schedule or change optimum values. -/
structure PreemptiveExecution {m n : ℕ} (I : Instance m n) where
  begin : I.Op → ℝ
  finish : I.Op → ℝ
  active : I.Op → Set ℝ

def PreemptiveExecution.Feasible {m n : ℕ} {I : Instance m n}
    (s : PreemptiveExecution I) : Prop :=
  (∀ o, 0 ≤ s.begin o ∧ s.begin o ≤ s.finish o) ∧
  (∀ o, MeasurableSet (s.active o) ∧
    s.active o ⊆ Set.Ico (s.begin o) (s.finish o) ∧
    volume (s.active o) = ENNReal.ofReal (I.proc o)) ∧
  (∀ j (i k : Fin (I.μ j)), i < k → s.finish ⟨j, i⟩ ≤ s.begin ⟨j, k⟩) ∧
  (∀ o o', o ≠ o' → I.mach o = I.mach o' → Disjoint (s.active o) (s.active o'))

noncomputable def preemptiveValue {m n : ℕ} {I : Instance m n}
    (o : Objective) (s : PreemptiveExecution I) : ℝ :=
  match o with
  | .makespan => ⨆ k : I.Op, s.finish k
  | .sumCompletion => ∑ j : Fin n, ⨆ i : Fin (I.μ j), s.finish ⟨j, i⟩

/-- A finite output description, with unrestricted rational breakpoints.
The optimum comparator above remains the full real-time preemptive model. -/
structure PieceSchedule {m n : ℕ} (I : Instance m n) where
  begin : I.Op → ℚ
  finish : I.Op → ℚ
  pieces : I.Op → List (ℚ × ℚ)

def PieceSchedule.execution {m n : ℕ} {I : Instance m n}
    (s : PieceSchedule I) : PreemptiveExecution I where
  begin o := s.begin o
  finish o := s.finish o
  active o := {t | ∃ ab ∈ s.pieces o, (ab.1 : ℝ) ≤ t ∧ t < (ab.2 : ℝ)}

end FlowJobHardness.FlowShopGap.Supplement


