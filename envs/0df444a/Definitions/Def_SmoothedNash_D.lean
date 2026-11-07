-- Prove2me | Definitions.Def_SmoothedNash_D
-- name    : SmoothedNash_D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:43.737594+00:00
-- url     : https://prove2.me/theorems/05bf65f4-1828-494d-81e7-b6d3fcad439c
-- title:
--   Number of levels $D = \lceil \log_2(4m/\varepsilon) \rceil$
-- statement:
--   For $m$ players and accuracy $\varepsilon \in (0, 1]$, Algorithm 2 runs the levels $t = 0, 1, \dots, D$ with
--   $$
--   D = \Bigl\lceil \log_2 \frac{4m}{\varepsilon} \Bigr\rceil .
--   $$
--   This choice gives $2\rho_D = 4m\,2^{-D} \le \varepsilon$, so a center that passes the level-$D$ test is an $\varepsilon$-Nash equilibrium.
--
--   **Formalization Note** The ceiling is the natural-number ceiling of the real logarithm $\log_2(4m/\varepsilon)$. For $m \ge 1$ and $\varepsilon \le 1$ the logarithm is at least $2$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §2.1.2, p.14, and Algorithm 2 line 1, p.15

import Mathlib

namespace SmoothedNash

/-- The number of refinement levels `D = ⌈log_2 (4m/ε)⌉` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §2.1.2, p.14, and line 1 of
Algorithm 2, p.15).

**Formalization Note** `⌈·⌉` is `Nat.ceil` of `Real.logb 2 (4m/ε)`. For `m ≥ 1` and `ε ∈ (0, 1]` the
logarithm is at least `2`, so the ceiling is the paper's. -/
noncomputable def D (m : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 (4 * m / ε)⌉₊

end SmoothedNash


