-- Prove2me | Definitions.Def_SparsestCutOracle_Main_FairFlow
-- name    : SparsestCutOracle_Main_FairFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:43.467444+00:00
-- url     : https://prove2.me/theorems/daa64cc1-5bd6-442b-9296-d8774ef1e029
-- title:
--   Antisymmetric flows and fair cut/flow pairs
-- statement:
--   A flow $f(u,v)$ is antisymmetric, and feasibility is $|f(u,v)|\le\operatorname{cap}(u,v)$ for every pair. Thus it vanishes off the graph. Its net flow out of $v$ is $f(v)=\sum_w f(v,w)$.
--
--   For nonnegative source and target weights $s,t$ and $\omega\ge1$, an $\omega$-fair pair $(U,f)$ obeys all five clauses of Definition 1: net supplies and absorptions do not exceed $s-t$; sources outside $U$ and targets inside $U$ are saturated to fraction $1/\omega$; and
--
--   $$f(u,v)\ge\operatorname{cap}(u,v)/\omega\quad(u\in U,\ v\notin U).$$
--
--   A fair cut is a set admitting such a flow. Signed output flow values are stored per listed edge. The capacity ratio uses the total capacity divided by the smallest positive capacity; its use in Theorem 3 is guarded by positive listed capacities and connectedness.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 8–9, flows and Definition 1

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Guarantees

namespace SparsestCutOracle.Main

abbrev Flow (n : ℕ) := Fin n → Fin n → ℝ

def netFlow {n : ℕ} (f : Flow n) (u : Fin n) : ℝ := ∑ v, f u v

/-- Capacity zero forces flow zero, including on absent edges. -/
def FeasibleFlow {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) (f : Flow n) : Prop :=
  (∀ u v, f u v = -f v u) ∧ (∀ u v, |f u v| ≤ G.w u v)

/-- Definition 1, p.9: all five clauses, with net-flow sign convention out of a vertex. -/
def FairPair {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (s t : Fin n → ℝ) (ω : ℝ) (U : Finset (Fin n)) (f : Flow n) : Prop :=
  1 ≤ ω ∧ (∀ v, 0 ≤ s v) ∧ (∀ v, 0 ≤ t v) ∧ FeasibleFlow G f ∧
  (∀ v, 0 ≤ s v - t v → 0 ≤ netFlow f v ∧ netFlow f v ≤ s v - t v) ∧
  (∀ v, s v - t v ≤ 0 → netFlow f v ≤ 0 ∧ s v - t v ≤ netFlow f v) ∧
  (∀ v, 0 ≤ s v - t v → v ∉ U → (s v - t v) / ω ≤ netFlow f v) ∧
  (∀ v, s v - t v ≤ 0 → v ∈ U → netFlow f v ≤ (s v - t v) / ω) ∧
  (∀ u ∈ U, ∀ v ∈ Uᶜ, G.w u v / ω ≤ f u v)

def FairCut {n : ℕ} (G : ClusterDecomp.WGraph (Fin n))
    (s t : Fin n → ℝ) (ω : ℝ) (U : Finset (Fin n)) : Prop :=
  ∃ f : Flow n, FairPair G s t ω U f

/-- One signed output value for each listed edge, in its given orientation, in real cells -1-e.
The set is independently read from negative integer cells. This uses O(m+n) output cells. -/
noncomputable def outputFlow {n : ℕ} (G : Graph n) (out : State) : Flow n :=
  fun u v => ∑ i : Fin G.length,
    let e := G[i.val]
    let x := out.base.core.mem (-1 - (i.val : ℤ))
    if e.u = u ∧ e.v = v then x else if e.u = v ∧ e.v = u then -x else 0

noncomputable def fairState {n : ℕ} (G : Graph n) (s t : Fin n → ℝ) (ω : ℝ) : State :=
  init (graphInts G) (graphReals G s (((List.finRange n).map t) ++ [ω]))

/-- Only positive-capacity listed edges enter the minimum. Connected n≥2 inputs have at least one. -/
noncomputable def Graph.minPositive {n : ℕ} (G : Graph n) : ℝ :=
  sInf {x : ℝ | ∃ e ∈ G, x = (e.capacity : ℝ) ∧ 0 < x}

noncomputable def Graph.capacityRatio {n : ℕ} (G : Graph n) : ℝ :=
  G.total / G.minPositive

end SparsestCutOracle.Main


