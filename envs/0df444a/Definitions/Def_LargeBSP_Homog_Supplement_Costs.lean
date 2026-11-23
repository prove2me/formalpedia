-- Prove2me | Definitions.Def_LargeBSP_Homog_Supplement_Costs
-- name    : LargeBSP_Homog_Supplement_Costs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T16:51:50.141831+00:00
-- url     : https://prove2.me/theorems/1d91436e-8e23-476e-b36f-f338a9794a12
-- title:
--   Assumption 3 and (6), p. 9 — bounded costs with a limiting distribution, mean cost, tail condition
-- statement:
--   Objects of the large-offering regime used by the heterogeneous-cost and budget theorems.
--
--   1. **Assumption 3.** Deterministic costs $c_1,c_2,\dots$ with limiting probability law $F_C$ form a cost regime when they are nonnegative and bounded and their empirical distribution functions converge at every nonnegative point:
--   $$\mathbb F_{C,N}(y)=\frac1N\sum_{n\le N}\mathbf 1\{c_n\le y\}\longrightarrow F_C(y)\qquad(y\ge0).$$
--   2. **Mean cost.** $\bar c=\int c\,dF_C(c)$.
--   3. **Optimal fraction.** $t$ is a maximizing fraction of $f$ if $t\in[0,1]$ and $f(s)\le f(t)$ for all $s\in[0,1]$.
--   4. **Tail condition (6).** A distribution function $F_X$ satisfies (6) if $\int_0^\infty\sqrt{F_X(x)(1-F_X(x))}\,dx<\infty$.
--
--   These are the assumptions and quantities under which Theorems 3–5 are stated.
--
--   **Formalization Note** The integral in (6) is an extended nonnegative integral, so a divergent integral is not read as $0$. The mean cost is only used for nonnegative laws with finite mean.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, §3.1, Assumption 3 and (6), p. 9; Theorem 3 (mean cost), p. 14

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Assumption 3, with the deterministic empirical cdf convergence (9). -/
def CostRegime (c : ℕ → ℝ) (κ : Measure ℝ) : Prop :=
  (∃ M : ℝ, ∀ n, 0 ≤ c n ∧ c n ≤ M) ∧
  ∀ y : ℝ, 0 ≤ y → Tendsto (fun N => empCdf c N y) atTop (𝓝 (cdf κ y))

/-- Mean marginal cost, Theorem 3. The measures used here are nonnegative laws. -/
noncomputable def meanCost (κ : Measure ℝ) : ℝ := ∫ a, a ∂κ

/-- A limiting surplus maximizer; membership, and every competitor, use [0,1]. -/
def MaxFraction (f : ℝ → ℝ) (t : ℝ) : Prop :=
  t ∈ Set.Icc 0 1 ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, f s ≤ f t

/-- Source tail condition (6), as a finite nonnegative integral. -/
def TailCondition (ν : Measure ℝ) : Prop :=
  (∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt (cdf ν y * (1 - cdf ν y)))) < ⊤

end LargeBSP.Homog.Supplement


