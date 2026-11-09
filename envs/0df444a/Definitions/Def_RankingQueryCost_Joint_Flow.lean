-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Flow
-- name    : RankingQueryCost_Joint_Flow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:45.534395+00:00
-- url     : https://prove2.me/theorems/857f2ed0-70b3-43ef-9ffa-9c7ac102e2ec
-- title:
--   Incidence flows and the uniform faulty-coefficient fluctuation
-- statement:
--   For a canonically oriented identity $e=(i,j)$ put $x_e=e_i-e_j$. For a finite support $E$ and coefficients $c_e$, its incidence flow is $\sum_{e\in E}c_ex_e$. The fluctuation for weights $w$ is
--
--   $$H_E(w)=\sup_{\|v\|_2\le1}\left|\sum_{e\in E}(w_e-1)|\langle v,x_e\rangle|\right|.$$
--
--   The norm is the Euclidean norm on $\mathbb R^n$, including in the unit-ball constraint. This quantity controls reply coefficients chosen after a sample has been observed.
--
--   **Formalization Note** The real supremum is over a nonempty compact Euclidean ball and a bounded continuous finite-sum expression. No unbounded real supremum or function-space sup norm is used.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §3.1, equation (3) and Lemma 3.2, pp. 6–7, PDF pp. 7–8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Scale

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

/-- Euclidean norm, rather than the sup norm on a Lean function type. -/
noncomputable def euclideanNorm {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, z i ^ 2)

/-- Incidence vector from the smaller to the larger public label. Orientation changes
only the sign, and the coefficient theorem quantifies over both signs. -/
def incidence {n : ℕ} (e : Pair n) (i : Fin n) : ℝ :=
  (if i = e.1.1 then 1 else 0) - (if i = e.1.2 then 1 else 0)

noncomputable def flow {n : ℕ} (E : Finset (Pair n)) (c : Pair n → ℝ) : Fin n → ℝ :=
  fun i => ∑ e ∈ E, c e * incidence e i

/-- The compact Euclidean unit-ball supremum in Lemma 3.2. It is not a supremum over
arbitrary vector families. For every finite E and finite w the set is nonempty and bounded. -/
noncomputable def faultyFluctuation {n : ℕ} (E : Finset (Pair n)) (w : Pair n → ℝ) : ℝ :=
  sSup {z : ℝ | ∃ v : Fin n → ℝ, euclideanNorm v ≤ 1 ∧
    z = abs (∑ e ∈ E, (w e - 1) * abs (∑ i, v i * incidence e i))}

end RankingQueryCost.Joint


