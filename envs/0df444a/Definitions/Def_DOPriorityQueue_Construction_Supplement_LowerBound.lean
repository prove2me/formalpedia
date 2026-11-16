-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_Supplement_LowerBound
-- name    : DOPriorityQueue_Construction_Supplement_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:40:58.874191+00:00
-- url     : https://prove2.me/theorems/3230f94e-e666-4c12-b594-43aeff41ea8b
-- title:
--   Theorem 6.1 — uniform asymptotic and pointwise lower-bound targets
-- statement:
--   Let $\varepsilon_n$ be eventually bounded and let $\delta_n\to0$ as $n\to\infty$. The asymptotic target chooses a threshold before the horizon $T$, memory size $M$, word size $w$, universe $U$ or implementation. For every $n$ beyond it, with $2n\le T$, $1\le M\le n/2$ and $n\le U$, every exact terminating opaque-token queue with insertion-field replacement privacy has a fixed vector $X\in[n]^n$ such that
--   $$\mathbb E[P(\sigma(X))]\ge\frac{n\log_2n}{32\log_2(M+2)}.$$
--   Only implementation randomness remains in this expectation. The history has exactly $2n$ calls, so this is the source's $O(n)$ witness. The factor $1/32$ follows from the two regimes of the proof on page 30.
--
--   The accompanying finite-parameter target retains equation (15) and the pathwise storage bound:
--   $$\mathbb E_{X,Q}[P]\ge\frac{n(\log_2n-2-\gamma_n)}{\log_2(2(M+2))}-2n,\qquad P\ge n-M.$$
--   Expectations take values in $[0,+\infty]$. A negative real lower bound is embedded as zero, an equivalent convention for a nonnegative quantity. All word sizes are allowed, a strengthening of the printed $w=\Theta(\log T)$ regime. These targets retain both the large and small ratio regimes and impose no finite-mean assumption.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), pp. 27–30, Theorem 6.1 and its proof, equation (15)

import Definitions.Def_DOPriorityQueue_Construction_Supplement_Opaque

set_option autoImplicit false

namespace DOPriorityQueue.Construction.Supplement

/-- Equation (15), valid also for infinite expected probes, and the pathwise
storage bound used in the small log(n)/log(M+2) regime (p. 30). -/
noncomputable def PointwiseLowerBound : Prop :=
  ∀ (n T U M w : ℕ) (Q : OpaqueProgram w M) (ε δ : ℝ),
    2 ≤ n → 2 * n ≤ T → 1 ≤ M → 2 * M ≤ n → n ≤ U →
    opaqueCorrect Q T U → insertionDO (opaqueKernel Q) T U ε δ →
    ENNReal.ofReal
      ((n : ℝ) * (Real.logb 2 n - 2 - gamma n ε δ) /
        Real.logb 2 (2 * (M + 2 : ℕ)) - 2 * n) ≤
      mixedProbes (opaqueKernel Q) (fun i : Fin n => i.val) ∧
    (∀ (X : Fin n → Fin n) fuel coins r,
      opaqueRun Q fuel (opaqueInitial Q) coins
        (experimentHistory (fun i : Fin n => i.val) X) = some r →
      n - M ≤ probeCount r.traces)

/-- Theorem 6.1's asymptotic quantifiers. Epsilon is eventually bounded and
delta tends to zero as n grows; the threshold is independent of T, M, word size,
priority bound, and implementation. A single fixed X is selected before coins.
The proof's two regimes give the explicit uniform factor 1/32. The assertion
holds for every word size, strengthening the stated Θ(log T) setting. -/
noncomputable def LowerBoundTarget : Prop :=
  ∀ ε δ : ℕ → ℝ,
    (∃ E : ℝ, ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ E) →
    Filter.Tendsto δ Filter.atTop (nhds 0) →
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ (T U M w : ℕ) (Q : OpaqueProgram w M),
        2 * n ≤ T → 1 ≤ M → 2 * M ≤ n → n ≤ U →
        opaqueCorrect Q T U → insertionDO (opaqueKernel Q) T U (ε n) (δ n) →
        ∃ X : Fin n → Fin n,
          ENNReal.ofReal ((n : ℝ) * Real.logb 2 n / (32 * Real.logb 2 (M + 2 : ℕ))) ≤
            expectedProbes (opaqueKernel Q) (experimentHistory (fun i : Fin n => i.val) X)

end DOPriorityQueue.Construction.Supplement


