-- Prove2me | Definitions.Def_SmoothedNash_Supplement_IsAlg4Trace
-- name    : SmoothedNash_Supplement_IsAlg4Trace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:05:39.619659+00:00
-- url     : https://prove2.me/theorems/719003ed-f7da-4867-b443-e84d56b1a4ed
-- title:
--   A run of Algorithm 4 (Follow-The-Path) for $N$ iterations
-- statement:
--   Algorithm 4 takes $F$, the bounds $L_0, L_1, L_2$, an accuracy $\varepsilon > 0$ and a row-gap bound $\theta$. Write $a = L_0 + L_1$, $h$ for the step size and $H$ for the stopping predicate of Lemma 4.4. A **run for $N$ iterations** is either the immediate return ($\|F(0)\| \le \varepsilon/2$ and $N = 0$), or $\|F(0)\| > \varepsilon/2$, $x_0 = (0, 0)$, $v_{-1}$ the initial direction, and for every $i < N$:
--
--   1. $H(\bar x_i) = \mathrm{Run}$, where $x_i = (\bar x_i, t_i)$;
--   2. $v_i$ is a unit vector in $\ker J_K(x_i)$ with $\langle v_i, v_{i-1}\rangle > 0$;
--   3. with the predictor $y_i = x_i + h v_i$, the corrector $c_i = x_{i+1} - y_i$ solves $J_K(y_i)\, c_i = -K(y_i)$ with $v_i^\top c_i = 0$.
--
--   **Formalization Note** The sequence of directions is shifted by one ($v$ at index $i$ is $v_{i-1}$). The "choose" of line 9 and the "solve" of line 11 are relations, so a statement about every run covers every admissible choice. Arithmetic is exact.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 4, p.28

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_homK
import Definitions.Def_SmoothedNash_Supplement_homJK
import Definitions.Def_SmoothedNash_Supplement_PredOut
import Definitions.Def_SmoothedNash_Supplement_stopPred
import Definitions.Def_SmoothedNash_Supplement_stepSize
import Definitions.Def_SmoothedNash_Supplement_initDir
open MeasureTheory

namespace SmoothedNash.Supplement

/-- A run of Algorithm 4 (Follow-The-Path) (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Algorithm 4, p.28) for `N` iterations of
its while loop, with inputs `F`, `L0`, `L1`, `L2`, accuracy `ε` and row-gap bound `θ`, and the stopping
predicate `H = stopPred` of Lemma 4.4. Write `a = L0 + L1`, `h = stepSize L0 L1 L2 ε θ`.

Either `‖F(0)‖ ≤ ε/2` (line 1: the algorithm returns `0` at once, and `N = 0`), or `‖F(0)‖ > ε/2`,
`x_0 = (0, 0)` and `v_{−1} = initDir` (line 6), and for every `i < N`:
1. `H(x̄_i) = Run` (line 8);
2. `v_i` is a unit vector in `ker J_K(x_i)` with `⟨v_i, v_{i−1}⟩ > 0` (line 9);
3. with `y_i = x_i + h v_i` (line 10), `c_i = x_{i+1} − y_i` solves `J_K(y_i) c_i = −K(y_i)` with
   `v_i^⊤ c_i = 0` (lines 11–12).

**Formalization Note** The points are `p i = x_i = (x̄_i, t_i) ∈ ℝ^n × ℝ` and the directions are
shifted by one: `v i = v_{i−1}`, so `v (i+1) = v_i`. Inner products and norms on `ℝ^{n+1}` are
written out (`⟨w̄, w̄'⟩ + s s'`). Line 9 ("choose") and line 11 ("solve") are relations: a run is any
sequence satisfying them, so a statement about every run covers every admissible choice. Arithmetic is
exact. -/
def IsAlg4Trace {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (L0 L1 L2 ε θ : ℝ) (p v : ℕ → EuclideanSpace ℝ (Fin n) × ℝ) (N : ℕ) : Prop :=
  (‖F 0‖ ≤ ε / 2 ∧ N = 0) ∨
  (ε / 2 < ‖F 0‖ ∧ p 0 = 0 ∧ v 0 = initDir F L0 L1 ∧
    ∀ i < N, stopPred F L0 L1 ε (p i).1 = PredOut.run ∧
      homJK F (L0 + L1) (p i) (v (i + 1)) = 0 ∧
      ‖(v (i + 1)).1‖ ^ 2 + (v (i + 1)).2 ^ 2 = 1 ∧
      0 < inner ℝ (v (i + 1)).1 (v i).1 + (v (i + 1)).2 * (v i).2 ∧
      homJK F (L0 + L1) (p i + stepSize L0 L1 L2 ε θ • v (i + 1))
          (p (i + 1) - (p i + stepSize L0 L1 L2 ε θ • v (i + 1)))
        = - homK F (L0 + L1) (p i + stepSize L0 L1 L2 ε θ • v (i + 1)) ∧
      inner ℝ (v (i + 1)).1 (p (i + 1) - (p i + stepSize L0 L1 L2 ε θ • v (i + 1))).1
        + (v (i + 1)).2 * (p (i + 1) - (p i + stepSize L0 L1 L2 ε θ • v (i + 1))).2 = 0)

end SmoothedNash.Supplement


