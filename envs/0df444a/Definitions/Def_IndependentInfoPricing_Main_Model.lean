-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Model
-- name    : IndependentInfoPricing_Main_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:00.221111+00:00
-- url     : https://prove2.me/theorems/ffbf5265-5e2b-44ed-af3c-9cf85bfe1527
-- title:
--   Operational information experiments and additive direct mechanisms
-- statement:
--   A buyer has finitely many state payoffs $w_i$ and a strictly positive state prior $\pi_0$, independent of the buyer's type. The normalized payoff is $v_i=\pi_0(i)w_i$, with inverse $w_i=v_i/\pi_0(i)$. After buying information the buyer chooses whether to act. The two free options give $u_0(v)=\max(0,\sum_i v_i)$.
--
--   A statistical experiment supplies a probability measure on an arbitrary measurable signal space for each state. A measurable action event $A$ gives payoff $\sum_i v_i\Pr(A\mid i)$; its optimal value is the supremum over all such events. A binary experiment $x\in[0,1]^Q$ has value
--
--   $$V(v,x)=\max\{v\cdot x,v\cdot(1-x),\sum_i v_i,0\}.$$
--
--   The module separately defines general additive direct mechanisms, classical IC with IR0, the additive relaxation with IR0 and IR1, and information IC against every report and all four response rules. Allocations and nonnegative finite payments are measurable. Revenue uses a nonnegative extended integral; the three optima are separate suprema over their operational feasible classes. Their menus need not be finite. Arbitrary-signal direct mechanisms and a reportwise compression payoff table provide the interface for Lemma 2.1. This lemma justifies the binary representation used by equation (2). No comparison of optima is built into a definition.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §§2–4.5, starting printed p.6 (PDF p.8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

abbrev Values (ι : Type) := ι → ℝ

def dot {ι : Type} [Fintype ι] (v x : Values ι) : ℝ := ∑ i, v i * x i

def outside {ι : Type} [Fintype ι] (v : Values ι) : ℝ := max 0 (∑ i, v i)

def binaryValue {ι : Type} [Fintype ι] (v x : Values ι) : ℝ :=
  max (max (dot v x) (dot v (1 - x))) (max (∑ i, v i) 0)

/-- General additive direct mechanism; the information model imposes further IC and IR. -/
structure DirectMechanism (ι : Type) where
  allocation : Values ι → Values ι
  price : Values ι → ℝ

def BasicOn {ι : Type} [Fintype ι] (T : Set (Values ι)) (m : DirectMechanism ι) : Prop :=
  Measurable (fun v : T => m.allocation v) ∧ Measurable (fun v : T => m.price v) ∧
  ∀ v ∈ T, 0 ≤ m.price v ∧ ∀ i, m.allocation v i ∈ Set.Icc (0 : ℝ) 1

def AdditiveICOn {ι : Type} [Fintype ι] (T : Set (Values ι)) (m : DirectMechanism ι) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T,
    dot v (m.allocation w) - m.price w ≤ dot v (m.allocation v) - m.price v

def ClassicalOn {ι : Type} [Fintype ι] (T : Set (Values ι)) (m : DirectMechanism ι) : Prop :=
  BasicOn T m ∧ AdditiveICOn T m ∧ ∀ v ∈ T, 0 ≤ dot v (m.allocation v) - m.price v

def RelaxedOn {ι : Type} [Fintype ι] (T : Set (Values ι)) (m : DirectMechanism ι) : Prop :=
  BasicOn T m ∧ AdditiveICOn T m ∧
  ∀ v ∈ T, outside v ≤ dot v (m.allocation v) - m.price v

/-- All four response rules, for every report, with the free IR0 and IR1 options. -/
def InformationOn {ι : Type} [Fintype ι] (T : Set (Values ι)) (m : DirectMechanism ι) : Prop :=
  BasicOn T m ∧
  (∀ v ∈ T, outside v ≤ binaryValue v (m.allocation v) - m.price v) ∧
  ∀ v ∈ T, ∀ w ∈ T,
    binaryValue v (m.allocation w) - m.price w ≤ binaryValue v (m.allocation v) - m.price v

def revenue {ι : Type} (F : Measure (Values ι)) (m : DirectMechanism ι) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (m.price v) ∂F

def opt {ι : Type} [Fintype ι] (F : Measure (Values ι)) : ℝ≥0∞ :=
  ⨆ (m : DirectMechanism ι) (_ : InformationOn Set.univ m), revenue F m

def optRelOn {ι : Type} [Fintype ι] (T : Set (Values ι)) (F : Measure (Values ι)) : ℝ≥0∞ :=
  ⨆ (m : DirectMechanism ι) (_ : RelaxedOn T m), revenue F m

def optRel {ι : Type} [Fintype ι] (F : Measure (Values ι)) : ℝ≥0∞ := optRelOn Set.univ F

def optClassical {ι : Type} [Fintype ι] (F : Measure (Values ι)) : ℝ≥0∞ :=
  ⨆ (m : DirectMechanism ι) (_ : ClassicalOn {v | ∀ i, 0 ≤ v i} m), revenue F m

/-- The prior is retained separately from normalized type laws. Types and states have product law. -/
structure Prior (Q : ℕ) where
  probability : Fin Q → ℝ
  positive : ∀ i, 0 < probability i
  total : ∑ i, probability i = 1

def normalize {Q : ℕ} (π : Prior Q) (w : Values (Fin Q)) : Values (Fin Q) :=
  fun i => π.probability i * w i

def unnormalize {Q : ℕ} (π : Prior Q) (v : Values (Fin Q)) : Values (Fin Q) :=
  fun i => v i / π.probability i

/-- An experiment may use any measurable signal space. -/
structure Experiment (ι S : Type) [MeasurableSpace S] where
  law : ι → Measure S
  probability : ∀ i, IsProbabilityMeasure (law i)

def responsePayoff {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (E : Experiment ι S) (v : Values ι) (A : Set S) : ℝ :=
  ∑ i, v i * (E.law i A).toReal

/-- The supremum is bounded by sum |v_i| since each state law is a probability. -/
def experimentValue {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (E : Experiment ι S) (v : Values ι) : ℝ :=
  sSup {r | ∃ A : Set S, MeasurableSet A ∧ r = responsePayoff E v A}

def compress {ι S : Type} [MeasurableSpace S] (E : Experiment ι S) (A : Set S) : Values ι :=
  fun i => (E.law i A).toReal

/-- Arbitrary experiments and direct reporting, before binary compression. -/
structure ExperimentMechanism (ι S : Type) [MeasurableSpace S] where
  experiment : Values ι → Experiment ι S
  price : Values ι → ℝ

def ExperimentICIR {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (m : ExperimentMechanism ι S) : Prop :=
  Measurable m.price ∧ (∀ v, 0 ≤ m.price v) ∧
  (∀ v, outside v ≤ experimentValue (m.experiment v) v - m.price v) ∧
  ∀ v w, experimentValue (m.experiment w) v - m.price w ≤
    experimentValue (m.experiment v) v - m.price v

/-- IC and both free outside options for a report-indexed gross-payoff table. -/
def GrossICIR {ι : Type} [Fintype ι] (U : Values ι → Values ι → ℝ) (p : Values ι → ℝ) : Prop :=
  (∀ v, outside v ≤ U v v - p v) ∧ ∀ v w, U v w - p w ≤ U v v - p v

def replacedGross {ι S : Type} [Fintype ι] [MeasurableSpace S]
    (m : ExperimentMechanism ι S) (report : Values ι) (x : Values ι)
    (v w : Values ι) : ℝ := by
  classical
  exact if w = report then binaryValue v x else experimentValue (m.experiment w) v

end IndependentInfoPricing.Main


