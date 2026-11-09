-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_LayerSampling
-- name    : SFMQueryLower_EmptyMin_LayerSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:19.326073+00:00
-- url     : https://prove2.me/theorems/08ec42f6-557a-4a5e-a1ae-f6c265e40f13
-- title:
--   Uniform layer experiments and actual stopping-query expectations
-- statement:
--   For disjoint $k$-subsets $P,R$ of an $m$-element set, define the ternary oracle
--   $$O_{P,R}(S)=\begin{cases}0&S\cap R\ne\varnothing,\\1&S\cap R=\varnothing,\ P\nsubseteq S,\\2&S\cap R=\varnothing,\ P\subseteq S.\end{cases}$$
--   The passing event is receiving reply $2$ on an actually issued query among the first $q=\lfloor k\log k/4\rfloor$ interactions. Its probability is a normalized finite sum over every ordered disjoint pair of $k$-subsets, each with equal weight.
--
--   For the layered value oracle, define
--   $$Q_i(\Pi,\omega)=\sum_{t\ge0}\mathbf1\{\operatorname{issued}(B_\omega,f_1^\Pi,t)=S\text{ for some }S\text{ with }\operatorname{stop}_\Pi(S)=i\}.$$
--   Its expectation is first over the algorithm's unchanged seed law, then uniformly over all equal-block ordered partitions. This is the independent joint experiment of Lemma 3.2.
--
--   **Formalization Note** Finite sums use extended nonnegative values divided by the finite sample-space cardinality. Empty sample spaces give zero, but the theorem thresholds imply nonemptiness: $m\ge k^2\ge2k$ in Lemma 3.1, and consecutive blocks give a partition in Lemma 3.2. Logarithms are natural; no cost is supplied independently of actual issues.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Lemma 3.1 and stopping-layer definition, printed p. 9 / PDF p. 10; Lemma 3.2, printed p. 10 / PDF p. 11

import Definitions.Def_SFMQueryLower_EmptyMin_EmptyMinProblem
import Definitions.Def_SFMQueryLower_EmptyMin_HardFamily

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Normalized finite sum: uniform expectation on the indicated finite sample space.
The empty-space value is `0`; both sampling spaces below are nonempty at theorem sizes. -/
noncomputable def uniformAverage {α : Type} [Fintype α] (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ x : α, f x) / (Fintype.card α : ℝ≥0∞)

def LayerPair (m k : ℕ) :=
  {X : Finset (Fin m) × Finset (Fin m) //
    Disjoint X.1 X.2 ∧ X.1.card = k ∧ X.2.card = k}

noncomputable instance (m k : ℕ) : Fintype (LayerPair m k) := by
  classical
  unfold LayerPair
  infer_instance

/-- The case number is a ternary reply, not a hard-function value. -/
def layerOracle {m k : ℕ} (X : LayerPair m k) (S : Finset (Fin m)) : Fin 3 :=
  if ¬ Disjoint S X.val.2 then 0 else if ¬ X.val.1 ⊆ S then 1 else 2

/-- Exact floor budget, with natural logarithm. -/
noncomputable def layerBudget (k : ℕ) : ℕ := ⌊(k : ℝ) * Real.log k / 4⌋₊

def PassesWithin {m k : ℕ} (B : OracleStrategy (Finset (Fin m)) (Fin 3) Bool)
    (X : LayerPair m k) (q : ℕ) : Prop :=
  ∃ t < q, ∃ S, issuedQuery B (layerOracle X) t = some S ∧ layerOracle X S = 2

noncomputable def passingProbability {m k : ℕ}
    (B : OracleStrategy (Finset (Fin m)) (Fin 3) Bool) : ℝ≥0∞ := by
  classical
  exact uniformAverage (fun X : LayerPair m k => if PassesWithin B X (layerBudget k) then 1 else 0)

/-- Actual count of issues stopping at precisely source layer `i`, including repeats. -/
noncomputable def stoppingCount {n k : ℕ} (π : OrderedPartition n k)
    (B : OracleStrategy (Finset (Fin n)) ℝ Bool) (i : ℕ) : ℝ≥0∞ :=
  queryCount B (hardFunction π true) (fun S => stopLayer π S = i)

noncomputable def expectedStoppingCount {n k : ℕ} (π : OrderedPartition n k)
    (A : EmptyMinAlgorithm n) (i : ℕ) : ℝ≥0∞ :=
  expectedCount A (hardFunction π true) (fun S => stopLayer π S = i)

/-- Independent sampling: the same seed law of `A` is used for every partition.
Finite uniform averaging of these expectations is expectation under the product law. -/
noncomputable def averagedStoppingCount (k : ℕ) (A : EmptyMinAlgorithm (2 * k ^ 2))
    (i : ℕ) : ℝ≥0∞ :=
  uniformAverage (fun π : EqualPartition k => expectedStoppingCount π.val A i)

end SFMQueryLower.EmptyMin


