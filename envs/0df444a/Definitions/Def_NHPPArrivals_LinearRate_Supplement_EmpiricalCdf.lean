-- Prove2me | Definitions.Def_NHPPArrivals_LinearRate_Supplement_EmpiricalCdf
-- name    : NHPPArrivals_LinearRate_Supplement_EmpiricalCdf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:06:55.033429+00:00
-- url     : https://prove2.me/theorems/e15d3fce-fd48-4429-af09-84cad10719d3
-- title:
--   Conditional samples on a common space and the empirical cdf (6)
-- statement:
--   For each $n$, let $Y_n$ be a measurable vector on a common probability space $(\Xi,Q)$ whose law is the actual NHPP vector conditioned on $N(T)=n$ and scaled by $T$. This condition specifies neither independence nor a limiting assertion. For a vector $x=(x_1,\ldots,x_n)$, define
--   $$\bar F_n(t)=\frac{\#\{j\le n:x_j\le t\}}{n},\qquad E(F,G)=\sup_{0\le t\le1}|F(t)-G(t)|.$$
--   These definitions make the almost-sure assertions of Theorems 2 and 3 statements on a common sampling space, rather than assertions about a fixed finite-rate trajectory. The empirical cdf at count zero defaults to zero and has no effect on a limit at infinity. The summation index in (6)'s indicator is corrected from the printed $j$ to the bound index, as required by (1) and the term empirical cdf. The real supremum is used only for bounded cdf errors in the theorems.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, p. 471, §3.2, (6), (8)–(10); compare (1), p. 465

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_Supplement_ConditionalSample

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory ProbabilityTheory

/-- A common sampling space for conditional samples as n grows. This specifies
only their law from the actual process, not an iid/order-statistic conclusion
or any convergence. No independence between different sample sizes is needed. -/
def ConditionalRows {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ) (T : ℝ)
    (Q : Measure Ξ) (Y : (n : ℕ) → Ξ → Fin n → ℝ) : Prop :=
  ∀ n, Measurable (Y n) ∧ Q.map (Y n) = conditionalVectorLaw P N X T n

/-- Formula (6), with its indicator using the summation index. At n=0 the
real-division convention returns zero; all limits concern n→∞. -/
noncomputable def empiricalCdf {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => x i ≤ t)).card : ℝ) / n

noncomputable def uniformError (F G : ℝ → ℝ) : ℝ :=
  sSup ((fun t => |F t - G t|) '' Set.Icc (0 : ℝ) 1)

end NHPPArrivals.LinearRate.Supplement


