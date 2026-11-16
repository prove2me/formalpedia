-- Prove2me | Definitions.Def_SmoothedNash_Supplement_IsAlg4Terminated
-- name    : SmoothedNash_Supplement_IsAlg4Terminated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:06:29.799182+00:00
-- url     : https://prove2.me/theorems/21d659bf-965e-473f-80a5-9f471e8b5466
-- title:
--   A terminated run of Algorithm 4
-- statement:
--   A run of Algorithm 4 for $N$ iterations has **terminated** if it returned at line 2 ($\|F(0)\| \le \varepsilon/2$) or the loop condition fails at $x_N$: $H(\bar x_N) \ne \mathrm{Run}$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 4, p.28

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_PredOut
import Definitions.Def_SmoothedNash_Supplement_stopPred
import Definitions.Def_SmoothedNash_Supplement_IsAlg4Trace
open MeasureTheory

namespace SmoothedNash.Supplement

/-- A terminated run of Algorithm 4 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 4, p.28): a run of `N` iterations
(`IsAlg4Trace`) that has stopped, either at line 2 (`‖F(0)‖ ≤ ε/2`) or because the loop condition
fails, `H(x̄_N) ≠ Run` (line 8). -/
def IsAlg4Terminated {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L0 L1 L2 ε θ : ℝ) (p v : ℕ → EuclideanSpace ℝ (Fin n) × ℝ) (N : ℕ) : Prop :=
  IsAlg4Trace F L0 L1 L2 ε θ p v N ∧
    (‖F 0‖ ≤ ε / 2 ∨ stopPred F L0 L1 ε (p N).1 ≠ PredOut.run)

end SmoothedNash.Supplement


