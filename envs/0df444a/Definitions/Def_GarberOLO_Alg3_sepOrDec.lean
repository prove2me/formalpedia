-- Prove2me | Definitions.Def_GarberOLO_Alg3_sepOrDec
-- name    : GarberOLO_Alg3_sepOrDec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:52:32.132307+00:00
-- url     : https://prove2.me/theorems/0134e14d-b319-4707-a3d9-af385808a27c
-- title:
--   The Separation-or-Decomposition procedure (Lemma 5)
-- statement:
--   Given $x \in \mathbb R^d$, $\varepsilon > 0$ and a positive integer $N$, run at most $N$ iterations of the Ellipsoid procedure $\mathrm{sdState}$. Iteration $j$ at center $w_j$ queries $(v, s) = \hat{\mathcal O}_K(-w_j)$ and stops iff $(x - v)\cdot w_j \ge \varepsilon$ and $\|w_j\| \le 1$.
--
--   1. If some iteration $j < N$ stops (take the first), the procedure returns the **separating vector** $w_j$ after $j + 1$ oracle calls.
--   2. Otherwise it returns the **decomposition data** $(v_i, s_i) = \hat{\mathcal O}_K(-w_i)$, $i = 1, \dots, N$, after $N$ oracle calls.
--
--   In case 2, Algorithm 2 combines the $v_i$ with an optimal solution of Problem (5); Lemma 5 shows that $w$ separates $x$ from $\alpha K$ with margin $\varepsilon$ in case 1 and that the combination is $3\varepsilon$-close to $x$ in case 2.
--
--   **Formalization Note** Each iteration makes one call of $\hat{\mathcal O}_K$, i.e. of $\mathcal O_K$; the stopping iteration counts.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, Lemma 5, pp. 9–10

import Mathlib
import Definitions.Def_GarberOLO_Alg3_Setting
import Definitions.Def_GarberOLO_Alg3_extOracle
import Definitions.Def_GarberOLO_Alg3_sdState
import Definitions.Def_GarberOLO_Alg3_SDOut

open scoped RealInnerProductSpace

namespace GarberOLO.Alg3

open Classical in
/-- **The Separation-or-Decomposition procedure** (Lemma 5).
Garber, *Efficient Online Linear Optimization with Approximation Algorithms*, arXiv:1709.03093v1, Lemma 5, pp. 9–10: "Consider an attempt to apply the Ellipsoid method for N iterations to
the following feasibility problem: find w ∈ ℝᵈ such that: ∀ z ∈ αK : (x − z) · w ≥ ε, ‖w‖ ≤ 1,
(4) … 3. otherwise (‖w‖ ≤ 1 and (x − v) · w ≥ ε), declare Problem (4) feasible and return the
vector w. … Otherwise (the Ellipsoid method completes N iterations without declaring Problem (4)
feasible), let (v₁, s₁), …, (v_N, s_N) be the outputs of the extended approximation oracle
gathered throughout the run of the algorithm".

`sepOrDec S OK x ε N` runs at most `N` iterations of the Ellipsoid states `sdState S OK x ε`.
Iteration `j` (from 0) at center `w_j` queries `(v, s) := extOracle S OK (−w_j)` and stops
(step 3) iff `ε ≤ ⟪x − v, w_j⟫` and `‖w_j‖ ≤ 1`.
* If some iteration `j < N` stops, with `j` the first one: `isSep = true`, `w = w_j`,
  `calls = j + 1`.
* Otherwise: `isSep = false`, `vs i = extOracle S OK (−w_i)` for `i = 0, …, N − 1` (the N
  oracle outputs in order), `calls = N`.

**Formalization Note.** Each iteration makes exactly one call of the extended oracle (step 1),
so `calls` counts oracle calls; the stopping iteration counts. In the separating case `vs` is
filled with the same formula but is not part of the output; in the decomposition case `w` is
`0` and not part of the output. The optimal solution of Problem (5) is computed by
Algorithm 2 (`alg2`) from `vs`. -/
noncomputable def sepOrDec {d : ℕ} (S : Setting d)
    (OK : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (N : ℕ) : SDOut d N :=
  if h : ∃ j, j < N ∧ ε ≤ ⟪x - (extOracle S OK (-(sdState S OK x ε j).1)).1,
      (sdState S OK x ε j).1⟫ ∧ ‖(sdState S OK x ε j).1‖ ≤ 1 then
    { isSep := true
      w := (sdState S OK x ε (Nat.find h)).1
      vs := fun i => extOracle S OK (-(sdState S OK x ε i.val).1)
      calls := Nat.find h + 1 }
  else
    { isSep := false
      w := 0
      vs := fun i => extOracle S OK (-(sdState S OK x ε i.val).1)
      calls := N }

end GarberOLO.Alg3


