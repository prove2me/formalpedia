-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Supplement_Approximation
-- name    : HamSimTradeoff_AncillaDepth_Supplement_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:10.635244+00:00
-- url     : https://prove2.me/theorems/d9cf735e-5583-40ca-9973-814965ff0ff2
-- title:
--   Uniform approximation and approximate degree
-- statement:
--   For real $f$, PolynomialApprox means there exists a real polynomial of natural degree at most $n$ with uniform error at most $\varepsilon$ on $[-1,1]$. Define
--   $$\widetilde{\deg}_\varepsilon(f)=\inf\{n\in\mathbb N:\exists P,\deg P\le n,\ |f-P|\le\varepsilon\},\qquad E_n(f)=\inf\{e\ge0:\exists P,\deg P\le n,\ |f-P|\le e\}.$$
--   All uses require continuous bounded $f$ on this compact interval and positive tolerance, making the degree set nonempty and the error set nonempty and bounded below. Polynomial minimax attainment identifies the second infimum with (8.7). Values of the totalized definitions outside this domain are never used by the theorem items.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #334 (October 2026), p. 35, Definition 8.1; p. 37, Definition 8.8

import Mathlib
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth.Supplement
noncomputable section

def PolynomialApprox (f : ℝ → ℝ) (n : ℕ) (eps : ℝ) : Prop :=
  ∃ P : Polynomial ℝ, P.natDegree ≤ n ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x - P.eval x| ≤ eps

/-- Continuous bounded f and eps>0 ensure the set is nonempty. -/
def approximateDegree (f : ℝ → ℝ) (eps : ℝ) : ℕ :=
  sInf {n : ℕ | PolynomialApprox f n eps}

/-- Nonnegative feasible errors: for continuous f on the compact interval the infimum is attained. -/
def bestError (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  sInf {e : ℝ | 0 ≤ e ∧ PolynomialApprox f n e}

def IntervalFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1, f x ∈ Set.Icc (-1 : ℝ) 1

end
end HamSimTradeoff.AncillaDepth.Supplement


