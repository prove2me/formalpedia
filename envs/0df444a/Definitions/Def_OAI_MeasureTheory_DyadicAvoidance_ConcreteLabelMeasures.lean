-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
-- name    : OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:08:42.094272+00:00
-- url     : https://prove2.me/theorems/9e6e5109-4c4a-4615-bedb-580390b4998f
-- title:
--   Fair and Bernoulli product laws for selector and terminal tables
-- statement:
--   This file defines the concrete probability laws of the random Boolean tables. Boolean values are written $0$ (false) and $1$ (true), and $p$ is a real parameter with $0 \le p \le 1$.
--
--   1. **Bit law.** $\beta_p$ is the Bernoulli law on $\{0,1\}$ with
--   $$
--   \beta_p(\{1\}) = p, \qquad \beta_p(\{0\}) = 1 - p .
--   $$
--
--   2. **Fair law.** $\beta_{1/2}$, the fair coin; the file proves $\beta_{1/2}(\{0\}) = \beta_{1/2}(\{1\}) = 1/2$.
--
--   3. **Selector law.** For a finite set $S$, $\mu^{\mathrm{sel}}_S = \bigotimes_{s \in S} \beta_{1/2}$ is the law of a table of independent fair bits indexed by $S$, a measure on $\{0,1\}^S$; every table $\sigma$ has $\mu^{\mathrm{sel}}_S(\{\sigma\}) = 2^{-|S|}$.
--
--   4. **Terminal law.** For a finite set $T$, $\mu^{\mathrm{ter}}_{T,p} = \bigotimes_{t \in T} \beta_p$ is the law of a table of independent Bernoulli($p$) bits; for every table $\tau$,
--   $$
--   \mu^{\mathrm{ter}}_{T,p}(\{\tau\}) = \prod_{t \in T} \begin{cases} p & \text{if } \tau(t) = 1, \\ 1-p & \text{if } \tau(t) = 0. \end{cases}
--   $$
--
--   5. **Outcome law.** $\mu_{S,T,p} = \mu^{\mathrm{sel}}_S \otimes \mu^{\mathrm{ter}}_{T,p}$ on $\{0,1\}^S \times \{0,1\}^T$, under which the two tables are independent; $\mu_{S,T,p}(\{(\sigma,\tau)\}) = \mu^{\mathrm{sel}}_S(\{\sigma\})\,\mu^{\mathrm{ter}}_{T,p}(\{\tau\})$.
--
--   All five are probability measures. In the dyadic avoidance construction $S$ is the set of selector-table coordinates and $T$ the set of terminal-table coordinates, so under the outcome law every selector bit is a fair coin, every terminal label equals $1$ with probability $p$, and all bits are independent.
--
--   **Formalization Note** The bit law is Mathlib's `bernoulliMeasure true false` at the point $p$ of `unitInterval`, with the bounds $0 \le p$ and $p \le 1$ passed as explicit hypotheses. Measures take values in `ENNReal`, so the masses are stated as `ENNReal.ofReal p`, `ENNReal.ofReal (1 - p)` and $(2)^{-1}$; the product laws are `Measure.pi` and `Measure.prod`, and the probability-measure facts are registered as instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteLabelMeasures.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ConcreteLabelMeasures.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault

namespace OAI

universe u_S u_T

noncomputable section

namespace Problem310.ConcreteLabels

open MeasureTheory ProbabilityTheory

/-- The actual terminal-bit law used at parameter `p`. -/
def bitLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Bool :=
  bernoulliMeasure true false ⟨p, hp0, hp1⟩

instance bitLaw_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bitLaw p hp0 hp1) := by
  unfold bitLaw
  infer_instance

@[simp] theorem bitLaw_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bitLaw p hp0 hp1 {true} = ENNReal.ofReal p := by
  simp [bitLaw, unitInterval.toNNReal, ENNReal.ofReal, Real.toNNReal_of_nonneg hp0]
  rfl

@[simp] theorem bitLaw_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bitLaw p hp0 hp1 {false} = ENNReal.ofReal (1 - p) := by
  simp [bitLaw, unitInterval.toNNReal, ENNReal.ofReal,
    Real.toNNReal_of_nonneg (sub_nonneg.mpr hp1)]
  rfl

/-- The actual fair law for selector table entries. -/
def fairLaw : Measure Bool := bitLaw (1 / 2) (by norm_num) (by norm_num)

instance fairLaw_probability : IsProbabilityMeasure fairLaw := by
  unfold fairLaw
  infer_instance

@[simp] theorem fairLaw_singleton (b : Bool) : fairLaw {b} = (2 : ENNReal)⁻¹ := by
  have hh : ENNReal.ofReal ((1 : ℝ) / 2) = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  cases b <;> norm_num [fairLaw] <;> exact hh

/-- A finite table of independent fair selectors. -/
def selectorLaw (S : Type u_S) [Fintype S] : Measure (S → Bool) :=
  Measure.pi fun _ => fairLaw

instance selectorLaw_probability (S : Type u_S) [Fintype S] :
    IsProbabilityMeasure (selectorLaw S) := by
  unfold selectorLaw
  infer_instance

/-- A finite table of independent Bernoulli terminal entries. -/
def terminalLaw (T : Type u_T) [Fintype T] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Measure (T → Bool) := Measure.pi fun _ => bitLaw p hp0 hp1

instance terminalLaw_probability (T : Type u_T) [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (terminalLaw T p hp0 hp1) := by
  unfold terminalLaw
  infer_instance

/-- Complete finite selector/terminal outcome law, with independent tables. -/
def outcomeLaw (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure ((S → Bool) × (T → Bool)) :=
  (selectorLaw S).prod (terminalLaw T p hp0 hp1)

instance outcomeLaw_probability (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (outcomeLaw S T p hp0 hp1) := by
  unfold outcomeLaw
  infer_instance

@[simp] theorem selectorLaw_singleton (S : Type u_S) [Fintype S] (ω : S → Bool) :
    selectorLaw S {ω} = ((2 : ENNReal)⁻¹) ^ Fintype.card S := by
  simp [selectorLaw, Measure.pi_singleton]

@[simp] theorem terminalLaw_singleton (T : Type u_T) [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : T → Bool) :
    terminalLaw T p hp0 hp1 {ω} =
      ∏ t, ENNReal.ofReal (if ω t then p else 1 - p) := by
  rw [terminalLaw, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro t _
  cases h : ω t <;> simp

@[simp] theorem outcomeLaw_singleton (S : Type u_S) (T : Type u_T) [Fintype S] [Fintype T]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : (S → Bool) × (T → Bool)) :
    outcomeLaw S T p hp0 hp1 {ω} =
      selectorLaw S {ω.1} * terminalLaw T p hp0 hp1 {ω.2} := by
  cases ω with
  | mk s t =>
    rw [outcomeLaw, ← Set.singleton_prod_singleton, Measure.prod_prod]

end Problem310.ConcreteLabels

end

end OAI


