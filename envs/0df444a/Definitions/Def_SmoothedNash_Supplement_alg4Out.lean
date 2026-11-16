-- Prove2me | Definitions.Def_SmoothedNash_Supplement_alg4Out
-- name    : SmoothedNash_Supplement_alg4Out
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:07:05.405886+00:00
-- url     : https://prove2.me/theorems/2e69af20-f562-4da5-9424-2c0f436929c4
-- title:
--   Output of Algorithm 4
-- statement:
--   The output of Algorithm 4 after $N$ iterations is $0$ if $\|F(0)\| \le \varepsilon/2$; otherwise it is $\bar x_N/\|\bar x_N\|$ if $H(\bar x_N) = \mathrm{Project}$ and $\bar x_N$ if not.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 4, lines 1–3 and 15–19, p.28

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_PredOut
import Definitions.Def_SmoothedNash_Supplement_stopPred
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The output of Algorithm 4 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 4, lines 1–3 and 15–19, p.28) after `N`
iterations with points `p`: `0` if `‖F(0)‖ ≤ ε/2`; otherwise `x̄_N/‖x̄_N‖` if `H(x̄_N) = Project`, and
`x̄_N` else. -/
noncomputable def alg4Out {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L0 L1 ε : ℝ) (p : ℕ → EuclideanSpace ℝ (Fin n) × ℝ) (N : ℕ) : EuclideanSpace ℝ (Fin n) := by
  classical
  exact if ‖F 0‖ ≤ ε / 2 then 0
    else if stopPred F L0 L1 ε (p N).1 = PredOut.project then ‖(p N).1‖⁻¹ • (p N).1
    else (p N).1

end SmoothedNash.Supplement


