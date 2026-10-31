-- Prove2me | Definitions.Def_CardinalMatching_IsApproxHZ
-- name    : CardinalMatching_IsApproxHZ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:41.686627+00:00
-- url     : https://prove2.me/theorems/6690e6d0-1325-4109-9a66-68df187f9550
-- title:
--   $\varepsilon$-approximate Hylland–Zeckhauser equilibrium
-- statement:
--   An assignment $(x_{ij})_{i\in A,j\in G}$ with $x_{ij}\ge 0$ together with non-negative prices $(p_j)_{j\in G}$ is an **$\varepsilon$-approximate HZ equilibrium** if
--
--   1. each agent $i$ satisfies $\sum_{j\in G}x_{ij}\in[1-\varepsilon,1]$;
--   2. each good $j$ satisfies $\sum_{i\in A}x_{ij}\in[1-\varepsilon,1]$;
--   3. each agent spends at most its unit budget: $p\cdot x_i\le 1$;
--   4. each agent gets a bundle at most $\varepsilon$ worse than an optimal one:
--   $$
--   u_i\cdot x_i \;\ge\; \max\Big\{u_i\cdot y \;:\; y\ge 0,\ \sum_{j\in G}y_j = 1,\ p\cdot y\le 1\Big\} - \varepsilon .
--   $$
--
--   There is no requirement that the bundle be (approximately) cheapest. This is the solution notion whose computation Chen et al. (2022) showed PPAD-hard, and which the reduction of Theorem 8 produces.
--
--   **Formalization Note** The maximum is stated literally: the set of values $u_i\cdot y$ of feasible bundles $y\ge 0$ has a greatest element $m$, and $u_i\cdot x_i\ge m-\varepsilon$. So at least one bundle must be feasible. With only "for every feasible $y$", the prices $p_j=1/(1-\varepsilon)$ and $x_{ij}=(1-\varepsilon)/n$ would be an answer on every instance, because no bundle with $\sum_j y_j=1$ is then affordable.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Definition 10, pp.6–7 (and p.7: no cheapest-bundle condition)

import Mathlib

namespace CardinalMatching

/-- **`ε`-approximate HZ equilibrium** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*,
arXiv:2402.08851v6, Definition 10, pp.6–7): an assignment `(x_ij)` together with non-negative
prices `(p_j)` such that
* each agent `i` satisfies `∑_{j∈G} x_ij ∈ [1 − ε, 1]`,
* each good `j` satisfies `∑_{i∈A} x_ij ∈ [1 − ε, 1]`,
* each agent `i` spends at most 1, i.e. `p · x_i ≤ 1`,
* each agent `i` gets a bundle which is at most `ε` worse than an optimal bundle, i.e.
  `u_i · x_i ≥ max { u_i · y | ∑_{j∈G} y_j = 1, p · y ≤ 1 } − ε`.

**Formalization Note** An assignment has `x_ij ≥ 0` (implicit in the paper). The maximum is over
bundles `y ≥ 0` (the HZ program of Definition 2, p.5). It is stated literally: the set of values
`u_i · y` of feasible bundles has a greatest element `m`, and `u_i · x_i ≥ m − ε`. So at least one
bundle must be feasible (`max ∅` does not exist): with "for every feasible `y`" alone, the prices
`p_j = 1/(1 − ε)` and `x_ij = (1 − ε)/n` would be an answer on every instance, because no bundle
with `∑_j y_j = 1` is then affordable.
As on p.7, there is **no** cheapest-bundle condition. -/
def IsApproxHZ {A G : Type} [Fintype A] [Fintype G] (u : A → G → ℝ) (ε : ℝ) (x : A → G → ℝ)
    (p : G → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧ (∀ j, 0 ≤ p j) ∧
  (∀ i, 1 - ε ≤ ∑ j, x i j ∧ ∑ j, x i j ≤ 1) ∧
  (∀ j, 1 - ε ≤ ∑ i, x i j ∧ ∑ i, x i j ≤ 1) ∧
  (∀ i, ∑ j, p j * x i j ≤ 1) ∧
  ∀ i, ∃ m : ℝ,
    IsGreatest {v : ℝ | ∃ y : G → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, y j = 1 ∧ ∑ j, p j * y j ≤ 1 ∧
      v = ∑ j, u i j * y j} m ∧
    m - ε ≤ ∑ j, u i j * x i j

end CardinalMatching


