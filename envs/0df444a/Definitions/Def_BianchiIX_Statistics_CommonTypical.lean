-- Prove2me | Definitions.Def_BianchiIX_Statistics_CommonTypical
-- name    : BianchiIX_Statistics_CommonTypical
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T18:22:15.783677+00:00
-- url     : https://prove2.me/theorems/2a91b957-7b0d-46f3-9322-9963e92593f7
-- title:
--   A common typical set for a family of observables
-- statement:
--   Let $F:X\to X$, let $(f_i:X\to\mathbb R)_{i\in I}$
--   be a family of observables, and let $l_i\in\mathbb R$. Define
--   $$A_n^Ff(x)=\frac1n\sum_{j=0}^{n-1}f(F^jx)\quad(n\geq1),\qquad A_0^Ff(x)=0,$$
--   $$\mathcal B(F,f,l)=\{x\in X:\ \forall i\in I,\ A_n^Ff_i(x)\longrightarrow l_i\}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/CommonTypical.lean

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
import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-! One measurable, exactly invariant typical set for a countable family of bounded observables. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

def commonTypicalSet {X ι : Type*} (F : X → X) (f : ι → X → ℝ) (l : ι → ℝ) : Set X :=
  {x | ∀ i, Tendsto (fun n => birkhoffAverage ℝ F (f i) n x) atTop (𝓝 (l i))}











namespace InverseBranchTree.BranchEstimates









end InverseBranchTree.BranchEstimates
end BianchiIX


