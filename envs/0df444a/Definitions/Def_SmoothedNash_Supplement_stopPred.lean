-- Prove2me | Definitions.Def_SmoothedNash_Supplement_stopPred
-- name    : SmoothedNash_Supplement_stopPred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:04:18.614037+00:00
-- url     : https://prove2.me/theorems/a3766e9f-a3b4-4518-b081-6386a08da22d
-- title:
--   Stopping predicate $H$ of Lemma 4.4
-- statement:
--   Let $a = L_0 + L_1$, $\varepsilon > 0$, and let $g(x) = \|F(x)\| - \langle F(x), x\rangle$ be the variational inequality gap of $x \in B(0,1)$. The **stopping predicate** $H$ is:
--
--   1. if $\|F(x)\| \le \varepsilon/2$, then $H(x) = \mathrm{Stop}$;
--   2. otherwise, if $x \ne 0$, $\|x\| \ge 1 - \varepsilon/(2a)$ and $g(x/\|x\|) \le \varepsilon$, then $H(x) = \mathrm{Project}$;
--   3. in all remaining cases $H(x) = \mathrm{Run}$.
--
--   It uses at most two zeroth-order queries, at $x$ and at $x/\|x\|$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 4.4, pp.27–28

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_PredOut
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The stopping predicate `H : B(0,1) → {Run, Stop, Project}` of Lemma 4.4 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53),
pp.27–28), with `a = L0 + L1` and the variational-inequality gap `g(x) = ‖F(x)‖ − ⟨F(x), x⟩`:
1. if `‖F(x)‖ ≤ ε/2`, then `H(x) = Stop`;
2. otherwise, if `x ≠ 0`, `‖x‖ ≥ 1 − ε/(2a)` and `g(x/‖x‖) ≤ ε`, then `H(x) = Project`;
3. in all remaining cases, `H(x) = Run`. -/
noncomputable def stopPred {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L0 L1 ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) : PredOut := by
  classical
  exact if ‖F x‖ ≤ ε / 2 then PredOut.stop
    else if x ≠ 0 ∧ 1 - ε / (2 * (L0 + L1)) ≤ ‖x‖ ∧
        ‖F (‖x‖⁻¹ • x)‖ - inner ℝ (F (‖x‖⁻¹ • x)) (‖x‖⁻¹ • x) ≤ ε then PredOut.project
    else PredOut.run

end SmoothedNash.Supplement


