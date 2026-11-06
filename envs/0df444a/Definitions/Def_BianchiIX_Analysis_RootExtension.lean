-- Prove2me | Definitions.Def_BianchiIX_Analysis_RootExtension
-- name    : BianchiIX_Analysis_RootExtension
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T20:27:25.648147+00:00
-- url     : https://prove2.me/theorems/83511d5f-6f72-49e7-b8df-5ad5ba73b9df
-- title:
--   The root-amplitude cutoff, primitive, and endpoint extension
-- statement:
--   Define
--   $$\chi(t)=\max(1-t,0),\qquad P(t)=\int_0^t\chi(u)\,du,\qquad
--   \mathcal R_{s,d,e}(x)=s+edsP(ex/s).$$
--   The integral is oriented, and division uses the total reciprocal $0^{-1}=0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/RootExtension.lean

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The positive root-amplitude extension in Section 4.2. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

noncomputable section

def rootCutoff (t : ℝ) : ℝ := max (1 - t) 0

def rootPrimitive (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, rootCutoff u















/-- The argument is the signed displacement from the endpoint; `e` is the outward orientation. -/
def rootExtension (s d e x : ℝ) : ℝ := s + e * d * s * rootPrimitive (e * x / s)





























end
end BianchiIX


