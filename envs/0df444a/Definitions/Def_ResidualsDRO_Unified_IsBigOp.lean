-- Prove2me | Definitions.Def_ResidualsDRO_Unified_IsBigOp
-- name    : ResidualsDRO_Unified_IsBigOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:03:41.939003+00:00
-- url     : https://prove2.me/theorems/9eaf4d02-ea25-4838-ab9c-ec34639f7c48
-- title:
--   Notation, p. 6 — $V_n = O_p(w_n)$: bounded in probability at rate $w_n$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, let $V_n:\Omega\to[0,\infty]$, $n\in\mathbb N$, be a sequence of random quantities and let $(w_n)$ be a deterministic sequence of reals. We say that $V_n = O_p(w_n)$ (**$V_n$ is bounded in probability at rate $w_n$**) if for every $\delta>0$ there exist a constant $M>0$ and an index $N$ such that
--
--   $$
--   P\bigl(V_n > M\,w_n\bigr)\le\delta\qquad\text{for every } n\ge N .
--   $$
--
--   The constant $M$ may depend on $\delta$ but not on $n$. For $w_n>0$ this is the notation of the paper: $V_n = R_n w_n$ with $\{R_n\}$ bounded in probability. It is the language in which every rate of convergence of the mission is stated.
--
--   **Formalization Note** $V_n$ takes values in $[0,\infty]$, so that suprema over decisions, which may be infinite, can be fed in directly; an infinite value exceeds every bound. The probability of an event that need not be measurable is its outer measure (Lean's measures are outer measures). Real quantities enter through $\max(\cdot,0)$ of their absolute value, i.e. `ENNReal.ofReal |·|`.
-- source:
--   Kannan, Bayraksan & Luedtke, Residuals-based distributionally robust optimization with covariate information, Math. Program. (2023), accepted manuscript, p. 6, Notation (O_p)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace ResidualsDRO.Unified

/-- **Bounded in probability at rate `w`** (`V_n = O_p(w_n)`, Kannan–Bayraksan–Luedtke, Notation,
p. 6): for every `δ > 0` there are a constant `M > 0` and an index `N` such that
`P(V_n > M · w_n) ≤ δ` for every `n ≥ N`. The constant `M` is chosen after `δ` and before `n`.
The quantity `V n ω` takes values in `[0, ∞]`, so an infinite value exceeds every bound; the
probability of a possibly non-measurable event is its outer measure. For a deterministic rate
`w_n > 0` this is the paper's "`V_n = R_n W_n` with `{R_n}` bounded in probability". -/
def IsBigOp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : ℕ → Ω → ℝ≥0∞)
    (w : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    P {ω | ENNReal.ofReal (M * w n) < V n ω} ≤ ENNReal.ofReal δ

end ResidualsDRO.Unified


