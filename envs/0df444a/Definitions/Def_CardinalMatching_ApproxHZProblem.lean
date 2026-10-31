-- Prove2me | Definitions.Def_CardinalMatching_ApproxHZProblem
-- name    : CardinalMatching_ApproxHZProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:46.921231+00:00
-- url     : https://prove2.me/theorems/3ee23337-af1f-4d6c-a11b-d54e5bafb1db
-- title:
--   The search problem APPROX-HZ$_c$
-- statement:
--   For a real $c$, **APPROX-HZ$_c$** is the computational problem of Theorem 9 (Chen et al. 2022): find an $\varepsilon$-approximate HZ equilibrium with $\varepsilon = n^{-c}$.
--
--   1. An instance is the binary encoding of $n\ge 1$ and an $n\times n$ matrix $u$ of rational utilities in $[0,1]$.
--   2. An answer is the encoding of a rational assignment $x$ and rational prices $p$ that form an $\varepsilon$-approximate HZ equilibrium (Definition 10) for
--   $$
--   \varepsilon = n^{-c} = \frac{1}{n^{c}},
--   $$
--   where $n$ is the instance's number of agents.
--
--   Theorem 9 asserts that for every $c>0$ this problem is PPAD-hard; it is the starting point of the reduction of Theorem 8.
--
--   **Formalization Note** Utilities lie in $[0,1]$ as assumed on p.7 ("Chen et al. assume that all utilities lie in [0, 1]").
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Theorem 9, p.6; Definition 10, pp.6–7; p.7 (utilities in [0,1])

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_IsApproxHZ
import Definitions.Def_CardinalMatching_encRatMatrix

namespace CardinalMatching

/-- **APPROX-HZ_c**, the search problem of Theorem 9 (Chen et al. 2022, cited in Tröbst–Vazirani,
*Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.6: "For any c > 0, the problem of
finding an ǫ-approximate HZ equilibrium is PPAD-hard for ǫ ≤ 1/n^c"), for a real `c`.
* An instance is the binary code `encRatMatrix n u` of `n ≥ 1` agents/goods and an `n × n`
  matrix `u` of rational utilities in `[0, 1]` (p.7: "Chen et al. assume that all utilities lie
  in [0, 1] and we will do the same for now").
* An answer is the code `encRatMatrix n x ++ encRatVec n p` of a rational assignment `x` and
  rational prices `p` forming an `ε`-approximate HZ equilibrium (Definition 10, pp.6–7) for
  `ε = n^(−c)`, where `n` is the instance's number of agents.

**Formalization Note** `ε = (n : ℝ) ^ (−c)` (real power; `n ≥ 1`), i.e. `1/n^c`, the accuracy of
Theorem 9 (any smaller accuracy is covered by a larger `c`). Agents and goods are `Fin n`. -/
noncomputable def ApproxHZProblem (c : ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (n : ℕ) (u : Fin n → Fin n → ℚ),
    1 ≤ n ∧ (∀ i j, 0 ≤ u i j ∧ u i j ≤ 1) ∧ s = encRatMatrix n u
  answer s t := ∃ (n : ℕ) (u x : Fin n → Fin n → ℚ) (p : Fin n → ℚ),
    s = encRatMatrix n u ∧ t = encRatMatrix n x ++ encRatVec n p ∧
    IsApproxHZ (fun i j => (u i j : ℝ)) ((n : ℝ) ^ (-c)) (fun i j => (x i j : ℝ))
      (fun j => (p j : ℝ))

end CardinalMatching


