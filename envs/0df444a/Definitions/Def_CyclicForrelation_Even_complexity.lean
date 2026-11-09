-- Prove2me | Definitions.Def_CyclicForrelation_Even_complexity
-- name    : CyclicForrelation_Even_complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:41.22553+00:00
-- url     : https://prove2.me/theorems/78d0d18b-ae77-4363-98b8-de4ae8518612
-- title:
--   Achievable costs and the least nonadaptive query complexity
-- statement:
--   For $n,k\in\mathbb N$, accuracy $\varepsilon$, and success level $p$, a natural number $q$ is achievable when there exists a private-randomness nonadaptive algorithm on oracle locations $(j,x)$ whose total cost is at most $q$ at every seed and whose success probability is at least $p$ on every input tuple. For $\varepsilon\ge0$, define
--   $$R^{\mathrm{na}}_\varepsilon(T_k)=\min\{q\in\mathbb N:q\text{ is achievable at success }2/3\}.$$
--   The exhaustive algorithm already proves this set nonempty. The minimum is computed by natural-number least-witness minimization; no desired lower or upper bound is included in its definition. The scale functions used in the theorem statements are
--   $$B_{n,m,\varepsilon}=\min\{N,N^{1-1/m}\varepsilon^{-2/m}\},\qquad A_{n,k,\varepsilon}=N^{1-2/k}\varepsilon^{-4/k}.$$
--   This separates the operational definition of query complexity from the rate the mission asks solvers to prove.
--
--   **Formalization Note** Only outside the source's domain, for negative accuracies, the complexity definition returns zero. Natural-number costs are cast to real numbers for inequalities, and all exponent divisions are real divisions.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), p. 4, §1.1 and Eq. (3); p. 16, Theorem 10 Eq. (27)

import Definitions.Def_CyclicForrelation_Even_queryModel
import Definitions.Def_CyclicForrelation_Even_cyclicTrace

namespace CyclicForrelation.Even

/-- Existence of a bounded algorithm, before minimizing. -/
def Achievable (n k : ℕ) (ε p : ℝ) (q : ℕ) : Prop :=
  ∃ A : NonadaptiveAlgorithm (Fin k × Cube n),
    CostAtMost A q ∧ Estimates A (traceTarget n k) ε p

/-- Exhaustive feasibility is established independently of every proposed bound. -/
theorem achievable_nonempty (n k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ q, Achievable n k ε (2 / 3) q := by
  exact ⟨Fintype.card (Fin k × Cube n), exhaustiveAlgorithm (traceTarget n k),
    exhaustive_feasible (traceTarget n k) ε (2 / 3) hε (by norm_num)⟩

/-- Least worst-case total cost at success 2/3, not a formula for that cost.
For negative accuracies only, return zero outside the source's domain. -/
noncomputable def nonadaptiveComplexity (n k : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if hε : 0 ≤ ε then Nat.find (achievable_nonempty n k ε hε) else 0

noncomputable def evenScale (n m : ℕ) (ε : ℝ) : ℝ :=
  min (cubeSize n : ℝ)
    ((cubeSize n : ℝ) ^ (1 - 1 / (m : ℝ)) * ε ^ (-2 / (m : ℝ)))

noncomputable def samplingScale (n k : ℕ) (ε : ℝ) : ℝ :=
  (cubeSize n : ℝ) ^ (1 - 2 / (k : ℝ)) * ε ^ (-4 / (k : ℝ))

end CyclicForrelation.Even


