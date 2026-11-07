-- Prove2me | Definitions.Def_SmoothedNash_frontier
-- name    : SmoothedNash_frontier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:37.726737+00:00
-- url     : https://prove2.me/theorems/d97c2cbc-e0f1-45c5-8e84-387b3f166590
-- title:
--   Frontier $F_t(A)$ of Algorithm 2
-- statement:
--   For a game $u$ and a support profile $A$, the **frontiers** $F_t(A)$, $t \ge 1$, are the level-$t$ centers that Algorithm 2 would test if it continued after any earlier return:
--   $$
--   F_1(A) = \begin{cases} N_1(A) & \text{if } b_A \text{ passes the level-}0\text{ test}, \\ \emptyset & \text{otherwise}, \end{cases}
--   \qquad
--   F_{t+1}(A) = \bigcup_{\substack{c \in F_t(A) \\ c \text{ passes the level-}t\text{ test}}} \operatorname{children}(c) \quad (t \ge 1).
--   $$
--   $F_0(A) = \{b_A\}$. The number $N_t(A) := |F_t(A)|$ of level-$t$ centers is the random quantity bounded by Lemma 2.10.
--
--   **Formalization Note** Centers are numerator vectors of the grids. Each $F_{t+1}(A)$ is a set, so it does not depend on the order in which $F_t(A)$ is processed. The level-$0$ center $b_A$ is not a grid point; it is handled by the barycenter, and the value of the frontier at $t = 0$ is the empty set, which is never used.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 2, p.15, and §2.1.2, p.14

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_rho
import Definitions.Def_SmoothedNash_grid
import Definitions.Def_SmoothedNash_gridPt
import Definitions.Def_SmoothedNash_children
import Definitions.Def_SmoothedNash_bary
import Definitions.Def_SmoothedNash_PassesTest

namespace SmoothedNash

open Classical in
/-- The frontier `F_t(A)` of Algorithm 2 for `t ≥ 1` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 2, p.15, and §2.1.2, p.14):
the level-`t` centers that would be tested if the algorithm continued after any earlier return.
`F_1(A) = N_1(A)` if the barycenter `b_A` passes the level-`0` test and `F_1(A) = ∅` otherwise;
for `t ≥ 1`, `F_{t+1}(A)` is the set of children of the centers of `F_t(A)` that pass the level-`t`
test.

**Formalization Note** Centers are numerator vectors (`grid`), and `F_{t+1}(A)` is a set, so it is
independent of the order in which `F_t(A)` is processed. The paper's `F_0(A) = {b_A}` is not a grid
point; it is handled by `bary`, and `frontier u A 0` is `∅` (never used). -/
noncomputable def frontier {m n : ℕ} (u : Game m n) (A : SupportProfile m n) :
    ℕ → Finset (Fin m → Fin n → ℕ)
  | 0 => ∅
  | 1 => if PassesTest u A (2 * rho m 0) (bary A) then grid A 1 else ∅
  | t + 2 => ((frontier u A (t + 1)).filter fun k =>
      PassesTest u A (2 * rho m (t + 1)) (gridPt A (t + 1) k)).biUnion (children A (t + 1))

end SmoothedNash


