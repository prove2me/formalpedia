-- Prove2me | Definitions.Def_SubquadCutReach_Faster_Repair
-- name    : SubquadCutReach_Faster_Repair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:58:08.437194+00:00
-- url     : https://prove2.me/theorems/72a32701-37fc-474a-a11c-529c7a643148
-- title:
--   The unit-internal-capacity repair network and explicit flows
-- statement:
--   Let $H$ be the hidden skeleton, $D$ its supplied orientation rule, and $b^*$ a feasible target. The repair demand and network are computed from these objects.
--
--   $$e(v)=(b_D(v)-b^*(v))/2.$$
--
--   There are fresh source and sink vertices $p,q$, unit-capacity internal arcs directed by $D$, a $p\to v$ arc of capacity $e(v)$ for positive demand, and a $v\to q$ arc of capacity $-e(v)$ for negative demand. Flow conservation holds at every original vertex. Maximum flow compares against all real feasible flows; integral flow has nonnegative integer entries. Output is an explicit finite matrix. Residual capacities are $c(u,v)-f(u,v)+f(v,u)$, and correction reverses unit-flow internal pairs. This definition neither assumes nor constructs a realizing orientation or a maximum-flow solution.
--
--   **Formalization Note** Feasibility, source value and extended maximum value reuse the published `LinearOptimization_MaxFlowProblem`, applied to a dense enumeration with zero capacities for absent arcs. All actual repair capacities are finite, and maximum flow requires attainment of the extended supremum.
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), Lemma 3.9, Remark 3.10, §C, Lemma C.2, Definition C.3; pp.10–11,26–29 (PDF pp.12–13,28–31)

import Mathlib
import Definitions.Def_LinearOptimization_MaxFlowProblem
import Definitions.Def_SubquadCutReach_Faster_Protocol

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SubquadCutReach.Faster

/-- p=inl false, q=inl true, vertices=inr v. Terminal arcs may have large capacity. -/
abbrev Node (n : ℕ) := Bool ⊕ Fin n

noncomputable def demand {n : ℕ} (H : SimpleGraph (Fin n)) (D : Rule n)
    (b : Fin n → ℤ) (v : Fin n) : ℤ := (imbalance (induced H D) v - b v)/2

noncomputable def capacity {n : ℕ} (H : SimpleGraph (Fin n)) (D : Rule n)
    (b : Fin n → ℤ) : Node n → Node n → ℝ := by
  classical
  exact fun u v => match u,v with
    | .inr u, .inr v => if induced H D u v then 1 else 0
    | .inl false, .inr v => max 0 (demand H D b v : ℝ)
    | .inr u, .inl true => max 0 (-(demand H D b u : ℝ))
    | _, _ => 0

/-- Dense serialization of all ordered vertex pairs. Absent arcs have capacity zero;
no graph is supplied to the algorithm by this semantic enumeration. -/
def nodeAt {n : ℕ} (v : Fin (n+2)) : Node n :=
  if h : v.val < n then .inr ⟨v.val,h⟩ else if v.val = n then .inl false else .inl true

def denseArcs (n : ℕ) (e : Fin ((n+2)*(n+2))) : Fin (n+2) × Fin (n+2) :=
  (⟨e.val/(n+2), Nat.div_lt_of_lt_mul e.isLt⟩, ⟨e.val%(n+2), Nat.mod_lt _ (by omega)⟩)

noncomputable def capVector {n : ℕ} (c : Node n → Node n → ℝ) :
    Fin ((n+2)*(n+2)) → ℝ≥0∞ := fun e =>
  ENNReal.ofReal (c (nodeAt (denseArcs n e).1) (nodeAt (denseArcs n e).2))

def flowVector {n : ℕ} (f : Node n → Node n → ℝ) : Fin ((n+2)*(n+2)) → ℝ :=
  fun e => f (nodeAt (denseArcs n e).1) (nodeAt (denseArcs n e).2)

/-- Apply the published general max-flow model to the actual repair vertex enumeration. -/
def Flow {n : ℕ} (c : Node n → Node n → ℝ) (f : Node n → Node n → ℝ) : Prop :=
  LinearOptimization.IsFeasibleMaxFlow (denseArcs n) (capVector c)
    ⟨n,by omega⟩ ⟨n+1,by omega⟩ (flowVector f)

noncomputable def flowValue {n : ℕ} (f : Node n → Node n → ℝ) : ℝ :=
  LinearOptimization.flowValue (denseArcs n) ⟨n,by omega⟩ (flowVector f)

/-- The EReal supremum is attained by this feasible flow. All capacities in the
repair instance are finite, and the zero flow makes the feasible set nonempty. -/
def MaximumFlow {n : ℕ} (c : Node n → Node n → ℝ) (f : Node n → Node n → ℝ) : Prop :=
  Flow c f ∧ (flowValue f : EReal) = LinearOptimization.maxFlowValue
    (denseArcs n) (capVector c) ⟨n,by omega⟩ ⟨n+1,by omega⟩

def IntegralFlow {n : ℕ} (f : Node n → Node n → ℝ) : Prop :=
  ∀ u v, ∃ a : ℕ, f u v = a

/-- Fixed explicit matrix serialization, including terminal arcs. -/
def nodeIndex {n : ℕ} : Node n → ℕ
  | .inl false => n
  | .inl true => n+1
  | .inr v => v.val

noncomputable def outputFlow (n : ℕ) (m : Memory) : Node n → Node n → ℝ :=
  fun u v => m (nodeIndex u*(n+2)+nodeIndex v : ℕ)

noncomputable def residualCapacity {n : ℕ} (c f : Node n → Node n → ℝ)
    (u v : Node n) : ℝ := c u v - f u v + f v u

noncomputable def reversedRule {n : ℕ} (D : Rule n)
    (f : Node n → Node n → ℝ) : Rule n := fun u v =>
  if f (.inr u) (.inr v) = 1 ∨ f (.inr v) (.inr u) = 1 then !(D u v) else D u v

end SubquadCutReach.Faster


