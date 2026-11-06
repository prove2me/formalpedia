-- Prove2me | Definitions.Def_BianchiIX_Statistics_ObservableTransfer
-- name    : BianchiIX_Statistics_ObservableTransfer
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T18:22:02.144759+00:00
-- url     : https://prove2.me/theorems/7efda423-7dc3-4a73-b002-d088f8074b22
-- title:
--   Finite time averages of real sequences
-- statement:
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/ObservableTransfer.lean

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
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Continuous observables have the same time averages on asymptotic phase sequences. -/

open Set Filter
open scoped Topology

namespace BianchiIX

noncomputable def timeAverage (u : ℕ → ℝ) (n : ℕ) : ℝ := (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u j













namespace InverseBranchTree.BranchEstimates







end InverseBranchTree.BranchEstimates
end BianchiIX


