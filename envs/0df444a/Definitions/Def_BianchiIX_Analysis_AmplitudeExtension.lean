-- Prove2me | Definitions.Def_BianchiIX_Analysis_AmplitudeExtension
-- name    : BianchiIX_Analysis_AmplitudeExtension
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T20:28:20.993666+00:00
-- url     : https://prove2.me/theorems/eead4bc9-85b9-471b-9434-44a8f1da8e37
-- title:
--   Positive amplitude extensions through square roots
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
--
--   For real functions $U,d_U$, set
--   $$r_U(x)=\sqrt{U(x)},\qquad b_U(x)=\frac{d_U(x)}{2\sqrt{U(x)}}.$$
--   Let $F_U,V_U$ be the root-curve construction applied to $(r_U,b_U)$, and set
--   $$\widetilde U(x)=F_U(x)^2.$$
--   For another pair $W,d_W$, use the analogous notation.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeExtension.lean

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace BianchiIX

open Set

def amplitudeRootDerivative (U dU : ℝ → ℝ) (x : ℝ) : ℝ :=
  dU x / (2 * Real.sqrt (U x))







def amplitudeCurveExtension (l r : ℝ) (U dU : ℝ → ℝ) (x : ℝ) : ℝ :=
  rootCurveExtension l r (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU) x ^ 2





















end BianchiIX


