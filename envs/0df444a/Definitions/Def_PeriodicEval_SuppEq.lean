-- Prove2me | Definitions.Def_PeriodicEval_SuppEq
-- name    : PeriodicEval_SuppEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:22.272003+00:00
-- url     : https://prove2.me/theorems/a021e9e7-b5e4-4df4-8baa-8e842f05fb87
-- title:
--   Support of a random variable equals a set $S$
-- statement:
--   For a real random variable $Y$ on a probability space $(\Omega,\mathcal F,P)$ and a set $S\subseteq\mathbb R$, we say that **the support of $Y$ is $S$** if
--
--   1. $Y\in S$ almost surely, and
--   2. every point of $S$ is charged: $P(|Y-s|<\varepsilon)>0$ for every $s\in S$ and $\varepsilon>0$.
--
--   This is how the support table of Theorem 1 is read. It implies that the topological support of the law of $Y$ is the closure of $S$, and it distinguishes, for example, "strictly positive almost surely" ($S=(0,c_1\gamma)\cup(c_2\gamma,\infty)$) from "an atom at zero" ($0\in S$ isolated).
--
--   **Formalization Note** The topological support of a law is always closed, while the sets in Theorem 1 are not; read literally, the table would be false (in Case 1 the closed support contains $0$). The paper uses the table to conclude almost-sure solvency in Case 1 and an atom at $0$ in Cases 2a, 2b and 3 (pp.19–20).
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Theorem 1, p.14 (the support table), and §4.2, pp.19–20 (its use)

import Mathlib

open MeasureTheory

namespace PeriodicEval

/-- "The support of the random variable `Y` is `S`", as used in Theorem 1, SSRN 3971852
(June 20, 2023), p.14: `Y ∈ S` almost surely, and every point of `S` is charged, i.e.
`P(|Y − s| < ε) > 0` for every `s ∈ S` and `ε > 0`.

**Formalization Note** This is a reading. The topological support of the law of `Y` is a
closed set, whereas the paper's sets (e.g. `(0, c₁γ) ∪ (c₂γ, ∞)`) are not closed; the paper
uses the table to conclude that the optimal portfolio is strictly solvent almost surely
(Case 1) or has an atom at zero (Cases 2a, 2b, 3), pp.19–20. `SuppEq P Y S` gives both, and
implies that the topological support is the closure of `S`. -/
def SuppEq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (S : Set ℝ) : Prop :=
  (∀ᵐ ω ∂P, Y ω ∈ S) ∧ ∀ s ∈ S, ∀ ε : ℝ, 0 < ε → 0 < P {ω | |Y ω - s| < ε}

end PeriodicEval


