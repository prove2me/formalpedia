-- Prove2me | Definitions.Def_BianchiIX_Statistics_TreeMeasure
-- name    : BianchiIX_Statistics_TreeMeasure
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T17:35:26.357196+00:00
-- url     : https://prove2.me/theorems/c116d1a0-f138-4dde-8b69-130441e32dd0
-- title:
--   Extending a positive word by digits equal to one
-- statement:
--   For a finite word $v$ of positive
--   integers define $\widehat v_n=v_n$ when $n<|v|$ and $\widehat v_n=1$
--   otherwise. This gives an infinite positive-digit sequence with prefix $v$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeMeasure.lean

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Distortion and stopping-loss bounds on the recursively constructed branch tree. -/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX

def extendPositiveWord (w : List ℕ+) (n : ℕ) : ℕ+ := w[n]?.getD 1



namespace InverseBranchTree













end InverseBranchTree
end BianchiIX


