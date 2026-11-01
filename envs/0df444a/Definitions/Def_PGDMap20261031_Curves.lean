-- Prove2me | Definitions.Def_PGDMap20261031_Curves
-- name    : PGDMap20261031_Curves
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-31T13:00:32.12767+00:00
-- url     : https://prove2.me/theorems/5f043b3d-163d-4156-8dab-b6a5b80b252f
-- title:
--   Exact PGD residual branches and normalized step domain
-- statement:
--   The normalized step is $h=\gamma L$ and the strong-convexity ratio is $q=\mu/L$. Define $b=1+hq$, the two explicit finite-horizon residual branches $A_N,B_N$, and $K_N=\max\{A_N,B_N\}$ for $N\ge2$. The $q=0$ branch is defined by its continuous formula; one update has its own expression. The finite geometric sum and the prefix coefficient support the analytic certificate, with a separate branch at $h=1$.
--
--   The intended rate domain is $N\ge1$, $q\ge0$, $0<h<2$. Scalar functions are total outside that domain; theorems impose the domain hypotheses explicitly. No theorem or axiom is embedded in this definition file.
-- source:
--   Three author manuscripts dated 2026-10-30: Exact Residual Curves for Proximal Gradient Descent with a Fixed Penalty; Optimal Constant Stepsizes for the Exact PGD Residual Curve; Jointly Optimal Bregman Geometry and Stepsize for Positive Entropy Mixtures. Definitions preceding Theorem 1 in each manuscript.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PGDMap20261031

def base (h q : ℝ) : ℝ := 1 + h * q

def branchA (N : ℕ) (h q : ℝ) : ℝ :=
  if q = 0 then 2 / (h * (2 * (N : ℝ) - h))
  else 2 * q / ((base h q) ^ (2 * N) - 1 - h ^ 2 * q)

def branchB (N : ℕ) (h q : ℝ) : ℝ :=
  2 * (1 + q) * (1 - h) ^ (2 * N - 2) /
    ((base h q) ^ (2 * N) - (1 - h) ^ (2 * N))

def curveOne (h q : ℝ) : ℝ := 2 / (h * (2 - h + h * q))

def curve (N : ℕ) (h q : ℝ) : ℝ :=
  if N = 1 then curveOne h q else max (branchA N h q) (branchB N h q)

def validStep (h : ℝ) : Prop := 0 < h ∧ h < 2

def geometricSum (k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (2 * k), (z ^ j)⁻¹

def prefixCoefficient (k : ℕ) (h q : ℝ) : ℝ :=
  base h q / (2 * h) *
    (if h = 1 then geometricSum k (1 / base h q)
     else min (geometricSum k (1 / base h q))
       (geometricSum k ((1 - h) / base h q)))

end PGDMap20261031


