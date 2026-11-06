-- Prove2me | Definitions.Def_BianchiIX_Analysis_RootCurveExtension
-- name    : BianchiIX_Analysis_RootCurveExtension
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T20:27:44.437752+00:00
-- url     : https://prove2.me/theorems/c032f518-331f-4ccf-8c56-8c02c4fe34eb
-- title:
--   Joining root-amplitude extensions to an interval curve
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
--
--   For real functions $f,d_f$ and real endpoints $l,r$, define $F$ and $V$ by
--   $$F(x)=\begin{cases}
--   \mathcal R_{f(l),d_f(l),-1}(x-l),&x<l,\\
--   \mathcal R_{f(r),d_f(r),1}(x-r),&x\geq l,\ r<x,\\
--   f(x),&\text{otherwise},
--   \end{cases}$$
--   $$V(x)=\begin{cases}
--   d_f(l)\chi(-(x-l)/f(l)),&x<l,\\
--   d_f(r)\chi((x-r)/f(r)),&x\geq l,\ r<x,\\
--   d_f(x),&\text{otherwise}.
--   \end{cases}$$
--   Write $F_f,V_f$ when comparing several pairs of input functions.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootCurveExtension.lean

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Joining the two root-amplitude tails to a curve without changing its original interval. -/

open Set Filter
open scoped Topology

namespace BianchiIX

noncomputable section

def rootCurveExtension (l r : ℝ) (f df : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < l then rootExtension (f l) (df l) (-1) (x - l)
  else if r < x then rootExtension (f r) (df r) 1 (x - r) else f x

def rootCurveDerivative (l r : ℝ) (f df : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < l then df l * rootCutoff (-(x - l) / f l)
  else if r < x then df r * rootCutoff ((x - r) / f r) else df x





























end
end BianchiIX


