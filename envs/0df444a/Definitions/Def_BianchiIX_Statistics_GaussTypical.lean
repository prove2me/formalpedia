-- Prove2me | Definitions.Def_BianchiIX_Statistics_GaussTypical
-- name    : BianchiIX_Statistics_GaussTypical
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T18:22:35.387731+00:00
-- url     : https://prove2.me/theorems/786de1da-7d57-4e51-a100-d68eabb76303
-- title:
--   Gauss cylinder observables and their common typical set
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   Let $G(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$, with $G(0)=0$.
--   For a finite word $w=(a_0,\ldots,a_{k-1})$ of natural numbers, set
--   $$C_w=(g_{a_0}\circ\cdots\circ g_{a_{k-1}})((0,1)),\qquad
--   g_a(t)=1/(a+t),$$
--   where the empty composition is the identity and $0^{-1}=0$. Define
--   $$f_w=\mathbf1_{C_w},\qquad m_w=\mu_G(C_w),\qquad
--   \mathcal B_G=\left\{x\in\mathbb R:\ \forall w,\
--   \frac1n\sum_{j=0}^{n-1}f_w(G^jx)\longrightarrow m_w\right\}.$$
--   For a positive-digit sequence $a$, write $\pi(a)$ for its continued-fraction
--   code, $\sigma^j a$ for its tail beginning at $j$, and $a|_k$ for its first
--   $k$ digits.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussTypical.lean

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_CommonTypical
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Concrete cylinder statistics, conditional only on the stated pointwise ergodic theorem. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BianchiIX

noncomputable section

def gaussCylinderObservable (w : List ℕ) : ℝ → ℝ :=
  (gaussCylinder w).indicator (fun _ => 1)

def gaussCylinderTypicalSet : Set ℝ :=
  commonTypicalSet gaussMap gaussCylinderObservable
    (fun w => (gaussMeasure (gaussCylinder w)).toReal)























namespace InverseBranchTree.BranchEstimates





end InverseBranchTree.BranchEstimates
end
end BianchiIX


