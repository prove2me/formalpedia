-- Prove2me | Definitions.Def_LiuZhangBRW_Concentration_doobIncrement
-- name    : LiuZhangBRW_Concentration_doobIncrement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:17.492052+00:00
-- url     : https://prove2.me/theorems/c907188b-ef1c-4fbd-a4a4-12da061254a4
-- title:
--   Doob's martingale increment $\Delta_i=\mathbb E_i(X_i+\dots+X_n)-\mathbb E_{i-1}(X_i+\dots+X_n)$
-- statement:
--   Fix $n$ and let $\mathbb E_i=\mathbb E(\cdot\mid X_1,\dots,X_i)$. Doob's (or McDiarmid's) martingale increment of $S_n$ is, for $1\le i\le n$,
--   $$
--   \Delta_i=\mathbb E_i(X_i+\dots+X_n)-\mathbb E_{i-1}(X_i+\dots+X_n).
--   $$
--   Its sum over $i$ is $S_n-\mathbb ES_n$, and the proof of Lemma 5.3 bounds the conditional exponential moments of each $\Delta_i$.
--
--   **Formalization Note** Defined by the paper's first display with conditional expectations given `natF X i`. At $i=1$ the natural-number subtraction $i-1$ gives $0$, i.e. $\mathbb E_0=\mathbb E$.
-- source:
--   Liu, Zhang, Concentration Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs, arXiv:1601.04794 (artifact sha256 7499631b9d550f66e791c0b3df0879f26102f111fee3052e363ebbff0c72bdcb; no version stamp), §5, p. 9, unnumbered display defining Δ_i

import Mathlib
import Definitions.Def_LiuZhangBRW_Concentration_natF

open MeasureTheory

namespace LiuZhangBRW.Concentration

/-- Doob's (McDiarmid's) martingale increment of `S_n` (Liu, Zhang, *Concentration
Inequalities for Branching Random Walks with Applications to Phase Transitions in CSPs*,
arXiv:1601.04794, artifact sha256 7499631b…bdcb, §5, p. 9, unnumbered display):
`Δ_i = E_i(X_i + ⋯ + X_n) − E_{i−1}(X_i + ⋯ + X_n)`, with `E_i = E(· | X_1, …, X_i)`.

**Formalization Note** `doobIncrement μ X n i` is defined by the paper's first display, with
`E_i = condExp (natF X i) μ`. It is meaningful for `1 ≤ i ≤ n`; `i - 1` is natural-number
subtraction, and at `i = 1` it gives `natF X 0 = ⊥`, i.e. `E_0 = E`. -/
noncomputable def doobIncrement {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (n i : ℕ) : Ω → ℝ :=
  condExp (natF X i) μ (fun ω => ∑ ℓ ∈ Finset.Icc i n, X ℓ ω) -
    condExp (natF X (i - 1)) μ (fun ω => ∑ ℓ ∈ Finset.Icc i n, X ℓ ω)

end LiuZhangBRW.Concentration


