-- Prove2me | Definitions.Def_BianchiIX_Analysis_CoordinateFactor
-- name    : BianchiIX_Analysis_CoordinateFactor
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T23:05:41.951304+00:00
-- url     : https://prove2.me/theorems/846813e7-cd8b-4661-9c1d-4274efed2200
-- title:
--   A coordinate segment and its integral factor
-- statement:
--   For $n\in\mathbb N$, $i\in\{0,\ldots,n-1\}$,
--   and $y\in\mathbb R^n$, define $\gamma_i(y,s)$ by replacing the $i$th
--   coordinate of $y$ by $sy_i$. Let $e_i$ be the $i$th coordinate unit vector.
--   For $f:\mathbb R^n\to\mathbb R$, define
--   $$\mathcal F_i[f](y)=\int_0^1 df_{\gamma_i(y,s)}(e_i)\,ds.$$
--   The derivative in this total definition is zero at points where $f$ is
--   not differentiable.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CoordinateFactor.lean

import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def coordinateSegment {n : ℕ} (i : Fin n) (Y : Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  Function.update Y i (s * Y i)

def coordinateFactor {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (Y : Fin n → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)











end BianchiIX


