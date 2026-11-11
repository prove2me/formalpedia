-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_CapacitatedCost
-- name    : PriceCapacities_LowerBound_CapacitatedCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:22:25.230712+00:00
-- url     : https://prove2.me/theorems/be69c309-ccd7-4030-9ee5-023e49a29ec6
-- title:
--   Feasible loads $H$ and the capacitated $(k,z)$-clustering cost $\mathrm{cost}_P(C,h)$ (§2.1)
-- statement:
--   Let $X$ be a metric space with distance $d$, $P$ a finite weighted point set in $X$ of total weight $n=\mathbf 1(P)$, $k\ge1$ and $z\ge1$. A **center tuple** is $C=(c_1,\dots,c_k)\in X^k$ (repetitions allowed). The **feasible load vectors** are
--   $$H=\Big\{h\in\mathbb R^k_{\ge0}:\ \sum_{i=1}^k h_i=n\Big\}.$$
--   A **fractional assignment** of $P$ with loads $h$ is a family $a_{xi}\ge0$ ($x\in P$, $i\in[k]$) with $\sum_i a_{xi}=P(x)$ for every $x\in P$ and $\sum_{x\in P}a_{xi}=h_i$ for every $i$; its cost is $\sum_{x\in P}\sum_i a_{xi}\,d(x,c_i)^z$. The **capacitated $(k,z)$-clustering cost** is the minimum cost of a fractional assignment of all the weight of $P$ that sends weight $h_i$ to $c_i$:
--   $$\mathrm{cost}_P(C,h)=\min_{a}\ \sum_{x\in P}\sum_{i=1}^k a_{xi}\,d(x,c_i)^z ,$$
--   the value of the primal assignment LP of p. 5 (with $d^z$ in place of $d$). The cases $z=1,2$ are capacitated $k$-median and $k$-means.
--
--   **Formalization Note.** Indices are `Fin k` (0-based); `IsFeasibleLoad n h` is $h\in H$; `capCost z P C h` is the infimum of the costs of all feasible assignments (`IsLoadAssignment`). For $h\in H$ the feasible set is nonempty (e.g. $a_{xi}=P(x)h_i/n$) and the minimum is attained (a continuous function on a compact polytope), so the infimum is the LP minimum. If $\sum_ih_i\ne\mathbf 1(P)$ there is no feasible assignment and the value is $0$; no statement uses that case. Costs are $\ge0$. The exponent is real (`Real.rpow`), and $X$ is any pseudometric space; the mission uses Euclidean spaces.
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 4, §2.1 (C, H, cost_P(C,h)); p. 5 (primal assignment LP)

import Mathlib
import Definitions.Def_PriceCapacities_LowerBound_WeightedSets

open scoped BigOperators NNReal

namespace PriceCapacities.LowerBound

/-!
# The capacitated `(k, z)`-clustering cost (§2.1)

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), p. 4, §2.1 (center tuples `C = X^k`, loads `H`, the
cost), p. 5 (primal assignment LP).

* Centers are tuples `C : Fin k → X` (`C = X^k`, repetitions allowed; index base `0`).
* `IsFeasibleLoad n h`: `h ∈ H = {h ∈ ℝ^k_{≥0} : Σ_i h_i = n}`.
* `IsLoadAssignment P h a`: `a` is a feasible point of the primal assignment LP, i.e.
  `a_{xi} ≥ 0`, `Σ_i a_{xi} = P(x)` for every `x ∈ P`, `Σ_{x ∈ P} a_{xi} = h_i` for every `i`.
* `assignmentCost z P C a = Σ_{x ∈ P} Σ_i a_{xi} d(x, c_i)^z` (real exponent `z`).
* `capCost z P C h` is the LP minimum, written as the infimum of the attained values. Its
  feasible set is nonempty exactly when `Σ_i h_i = 1(P)` (then the minimum is attained:
  transportation polytope, continuous objective); when it is empty the value is `0`, which
  never occurs for `h ∈ H`. All values are `≥ 0`, so the infimum is never `-∞`.
-/

/-- `h ∈ H`: nonnegative loads summing to `n`. -/
def IsFeasibleLoad {k : ℕ} (n : ℝ) (h : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ h i) ∧ ∑ i, h i = n

/-- `a` is a fractional assignment of all the weight of `P` sending weight `h_i` to center `i`. -/
def IsLoadAssignment {X : Type*} {k : ℕ} (P : WeightedSet X) (h : Fin k → ℝ)
    (a : X → Fin k → ℝ) : Prop :=
  (∀ x i, 0 ≤ a x i) ∧ (∀ x ∈ P.support, ∑ i, a x i = (P x : ℝ)) ∧
    ∀ i, ∑ x ∈ P.support, a x i = h i

/-- The cost `Σ_{x ∈ P} Σ_i a_{xi} d(x, c_i)^z` of a fractional assignment. -/
noncomputable def assignmentCost {X : Type*} [PseudoMetricSpace X] {k : ℕ} (z : ℝ) (P : WeightedSet X)
    (C : Fin k → X) (a : X → Fin k → ℝ) : ℝ :=
  ∑ x ∈ P.support, ∑ i, a x i * dist x (C i) ^ z

/-- The capacitated `(k, z)`-clustering cost `cost_P(C, h)`: the minimum cost of a fractional
assignment of all the weight of `P` that sends weight `h_i` to center `c_i`. -/
noncomputable def capCost {X : Type*} [PseudoMetricSpace X] {k : ℕ} (z : ℝ) (P : WeightedSet X)
    (C : Fin k → X) (h : Fin k → ℝ) : ℝ :=
  sInf {c : ℝ | ∃ a : X → Fin k → ℝ, IsLoadAssignment P h a ∧ c = assignmentCost z P C a}

end PriceCapacities.LowerBound


