-- Prove2me | Definitions.Def_Komlos_gaussian_fold_analysis
-- name    : Komlos_gaussian_fold_analysis
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-09-06T10:29:25.727089+00:00
-- url     : https://prove2.me/theorems/eba18b8d-17d2-4dfb-bf94-546504d02fe1
-- title:
--   Gaussian kernel, tail, and translated interval mass for convex folding
-- statement:
--   For real $x$ and $r$, define the unnormalized Gaussian density, its upper tail, and its translated interval integral by
--   $$g(x)=e^{-x^2/2},\qquad T(x)=\int_x^\infty g(t)\,dt,\qquad A_r(x)=\int_x^{x+r}g(t)\,dt.$$
--   For $r\ge0$, $A_r(x)$ is the unnormalized mass of an interval of length $r$. These quantities describe the one-dimensional integrals in the planar comparison used in Banaszczyk's folding argument. For negative $r$, the interval integral has its usual oriented meaning.
-- source:
--   Shashwat Garg, Algorithms for Combinatorial Discrepancy, TU Eindhoven PhD thesis (2018), Chapter 3, proof of Lemma 19 and Lemmas 20-21, printed pp. 22-24. https://pure.tue.nl/ws/files/107722737/20181010_Garg.pdf . The notation g,T,A packages the Gaussian integrands and intervals appearing there; no normalizing factor is included.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set MeasureTheory
open scoped intervalIntegral
set_option autoImplicit false

namespace GaussianFoldAnalysis
noncomputable def kernel (x : ℝ) : ℝ := Real.exp (-x ^ 2 / 2)
noncomputable def tail (x : ℝ) : ℝ := ∫ t in Ioi x, kernel t
noncomputable def intervalMass (r x : ℝ) : ℝ := ∫ t in x..x + r, kernel t
end GaussianFoldAnalysis


