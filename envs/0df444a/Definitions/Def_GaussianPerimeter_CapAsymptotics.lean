-- Prove2me | Definitions.Def_GaussianPerimeter_CapAsymptotics
-- name    : GaussianPerimeter_CapAsymptotics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T10:05:57.121863+00:00
-- url     : https://prove2.me/theorems/4c89edde-50b0-48f1-a1a0-d5a4c3459902
-- title:
--   Cap Asymptotics
-- statement:
--   Definitions and structural lemmas for Cap Asymptotics, from XinyuanXie-hub (XinyuanXie-hub/GaussianPerimeter; see pinned Apache-2.0 LICENSE)'s pinned Asymptotic lower bound for Gaussian perimeter of convex bodies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/CapAsymptotics.lean

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace GaussianPerimeter
noncomputable def capProfile (n : ℕ) (u : ℝ) : ℝ :=
  (1 - u ^ 2) ^ (((n : ℝ) - 2) / 2)
noncomputable def capNormalizer (n : ℕ) : ℝ :=
  ∫ u in (-1 : ℝ)..1, capProfile n u
noncomputable def capTail (n : ℕ) (t : ℝ) : ℝ :=
  (∫ u in t..1, capProfile n u) / capNormalizer n
noncomputable def capRho (a : ℝ) (n : ℕ) : ℝ :=
  a * Real.sqrt (Real.sqrt (n : ℝ))
noncomputable def capRadius (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  Real.sqrt ((Real.sqrt ((n : ℝ) - 1) + w) ^ 2 + capRho a n ^ 2)
noncomputable def capThreshold (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  capRho a n / capRadius a n w
noncomputable def capScale (a : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-(capRho a n ^ 2) / 2) / (Real.sqrt (2 * Real.pi) * capRho a n)) *
    Real.exp (a ^ 4 / 4)
noncomputable def capMajorant (a : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  let t := capThreshold a n w
  (1 - t ^ 2) ^ ((n : ℝ) / 2) / ((n : ℝ) * t * capNormalizer n)
noncomputable def scaledProfile (n : ℕ) (x : ℝ) : ℝ :=
  (max (1 - x ^ 2 / (n : ℝ)) 0) ^ (((n : ℝ) - 2) / 2)
end GaussianPerimeter


