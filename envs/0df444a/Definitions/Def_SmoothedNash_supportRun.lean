-- Prove2me | Definitions.Def_SmoothedNash_supportRun
-- name    : SmoothedNash_supportRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:43.070965+00:00
-- url     : https://prove2.me/theorems/57a539c1-11b1-46cb-b956-6f7481dbadef
-- title:
--   Algorithm 2 on one support profile
-- statement:
--   For a game $u$, an accuracy $\varepsilon$ with $D = \lceil \log_2(4m/\varepsilon) \rceil$, a frontier enumeration and a support profile $A$, this is one iteration of the outer loop of Algorithm 2 (lines 3–23).
--
--   1. Level $0$: the barycenter $b_A$ is tested; if it passes, $F_1(A) = N_1(A)$.
--   2. Levels $1 \le t < D$: every center of $F_t(A)$ is tested, and the children of the passing ones form $F_{t+1}(A)$. No return is possible at these levels.
--   3. Level $D$: the centers of $F_D(A)$ are tested in the order of the enumeration, and the first one that passes the level-$D$ test is returned. If none passes, the support yields no output.
--
--   The number of payoff-vector computations is $1 + \sum_{t=1}^{D-1} |F_t(A)|$ plus the number of level-$D$ centers tested up to and including the returned one (all of $F_D(A)$ if none is returned).
--
--   The work count of the running-time clause adds: $1$ for lines 3–4; $1$ per level iteration (lines 5–8); $mn$ per tested center (checking the inequalities (1)–(2)); $|N_1(A)|$ if $b_A$ passes (listing the first-level grid, line 18); and $2^R$ per passing center at a level $1 \le t < D$ (the $2^R$ numerator choices of its children, line 20).
--
--   **Formalization Note** If $D = 0$ (impossible when $m \ge 1$ and $\varepsilon \le 1$, where $D \ge 2$), the barycenter is tested at level $0 = D$ and returned if it passes, as in the pseudocode.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 2, p.15, and proof of Theorem 2.2, p.19

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_R
import Definitions.Def_SmoothedNash_rho
import Definitions.Def_SmoothedNash_D
import Definitions.Def_SmoothedNash_grid
import Definitions.Def_SmoothedNash_gridPt
import Definitions.Def_SmoothedNash_bary
import Definitions.Def_SmoothedNash_PassesTest
import Definitions.Def_SmoothedNash_frontier
import Definitions.Def_SmoothedNash_RunResult

namespace SmoothedNash

open Classical in
/-- One iteration of the outer loop of Algorithm 2 (lines 3–23) on the support profile `A`
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.15), with `D = ⌈log_2 (4m/ε)⌉` levels and the level-`D` frontier processed in the order
`enum A`.

Levels `t < D` are processed in full: the barycenter is tested at level `0`, every center of
`F_t(A)` (`frontier`) is tested at level `1 ≤ t < D`, and no return can happen there. At level `D`
the centers of `F_D(A)` are tested in the order `enum A (F_D(A))`, and the first one that passes the
level-`D` test is returned (lines 14–15); if none passes, the support yields no output.

The counts are:
1. `evals`: the executions of line 10, i.e. `1 + Σ_{t=1}^{D−1} |F_t(A)|` plus the number of level-`D`
   centers tested up to and including the returned one (all of `F_D(A)` if none is returned);
2. `work`, the cost model of the running-time clause (proof of Theorem 2.2, p.19): `1` for lines
   3–4, `1` per level iteration (lines 5–8), `m n` per tested center (checking (1)–(2)),
   `|N_1(A)|` if `b_A` passes (line 18, listing the first-level grid), and `2^R` per passing center
   at a level `1 ≤ t < D` (line 20, the `2^R` numerator choices of its children).

**Formalization Note** The degenerate branch `D = 0` (impossible for `m ≥ 1`, `ε ≤ 1`, where
`D ≥ 2`) follows the pseudocode: the barycenter is tested at level `0 = D` and returned if it
passes. -/
noncomputable def supportRun {m n : ℕ} (u : Game m n) (ε : ℝ)
    (enum : SupportProfile m n → Finset (Fin m → Fin n → ℕ) → List (Fin m → Fin n → ℕ))
    (A : SupportProfile m n) : RunResult m n :=
  if D m ε = 0 then
    { out := if PassesTest u A (2 * rho m 0) (bary A) then some (bary A) else none,
       evals := 1,
       work := 2 + m * n }
  else
    let before : ℕ := 1 + ∑ t ∈ Finset.Ico 1 (D m ε), (frontier u A t).card
    let L := enum A (frontier u A (D m ε))
    let p : (Fin m → Fin n → ℕ) → Bool :=
      fun k => decide (PassesTest u A (2 * rho m (D m ε)) (gridPt A (D m ε) k))
    let tested : ℕ := match L.find? p with
      | some _ => L.findIdx p + 1
      | none => L.length
    let gen : ℕ := (if PassesTest u A (2 * rho m 0) (bary A) then (grid A 1).card else 0) +
      ∑ t ∈ Finset.Ico 1 (D m ε), 2 ^ R A *
        ((frontier u A t).filter fun k => PassesTest u A (2 * rho m t) (gridPt A t k)).card
    { out := (L.find? p).map (gridPt A (D m ε)),
       evals := before + tested,
       work := 1 + (D m ε + 1) + m * n * (before + tested) + gen }

end SmoothedNash


