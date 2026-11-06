-- Prove2me | Definitions.Def_BianchiIX_Statistics_EraStatistics
-- name    : BianchiIX_Statistics_EraStatistics
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T20:01:57.168108+00:00
-- url     : https://prove2.me/theorems/0288a201-2763-4109-8b42-fc8b13d86298
-- title:
--   The simultaneous phase and digit statistics of an era sequence
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
--
--   Define the natural-valued digit, tail observables, and truncations by
--   $$D(x)=\lfloor1/x\rfloor_{\mathbb N},\qquad
--   H_k(x)=\mathbf1_{(0,1/k)}(x)\quad(k\geq1),\qquad
--   D_R(x)=\min(D(x),R)\quad(R\in\mathbb N).$$
--   Here the natural floor is zero for negative arguments, and $0^{-1}=0$.
--   Write
--   $$p_k=\frac{\log((k+1)^2/(k(k+2)))}{\log2},\qquad
--   q_k=\frac{\log(1+1/k)}{\log2},\qquad
--   t_R=\frac{\log(R+1)}{\log2}.$$
--   For a real sequence $u$, define
--   $$A_n(u)=\frac1n\sum_{j=0}^{n-1}u_j\quad(n\geq1),\qquad A_0(u)=0.$$
--
--   For a positive-digit sequence $a$ and a real sequence $y$, let
--   $\mathcal E(a,y)$ mean all of the following statements:
--   $$A_N(f\circ y)\to\int f\,d\mu_G
--   \quad\text{for every }f:\mathbb R\to\mathbb R
--   \text{ continuous on }[0,1],$$
--   $$A_N(j\mapsto\mathbf1_{\{(\sigma^ja)|_{|w|}=w\}})\to m_w
--   \quad\text{for every finite positive-digit word }w,$$
--   $$A_N(j\mapsto\mathbf1_{\{a_j=k\}})\to p_k,\qquad
--   A_N(j\mapsto\mathbf1_{\{k\leq a_j\}})\to q_k\quad(k\geq1),$$
--   $$A_N(j\mapsto\min(a_j,R))\to t_R\quad(R\in\mathbb N),\qquad
--   A_N(j\mapsto a_j)\to+\infty.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EraStatistics.lean

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The complete statistical reduction for asymptotic Gauss recurrences. -/

open Set Filter MeasureTheory
open scoped Topology

namespace BianchiIX

/-- All phase and digit statistics asserted by the era-statistics reduction. -/
structure EraStatistics (a : ℕ → ℕ+) (y : ℕ → ℝ) : Prop where
  continuous_average : ∀ f : ℝ → ℝ, ContinuousOn f (Icc (0 : ℝ) 1) →
    Tendsto (timeAverage (fun j => f (y j))) atTop (𝓝 (∫ x, f x ∂gaussMeasure))
  block_frequency : ∀ w : List ℕ, (∀ k ∈ w, 1 ≤ k) →
    Tendsto (timeAverage (fun j => if digitPrefix (shiftDigits a j) w.length = w then 1 else 0))
      atTop (𝓝 (gaussMeasure (gaussCylinder w)).toReal)
  digit_frequency : ∀ k : ℕ+,
    Tendsto (timeAverage (fun j => if (a j : ℕ) = (k : ℕ) then 1 else 0)) atTop
      (𝓝 (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2))
  tail_frequency : ∀ k : ℕ+,
    Tendsto (timeAverage (fun j => if (k : ℕ) ≤ (a j : ℕ) then 1 else 0)) atTop
      (𝓝 (Real.log (1 + 1 / (k : ℝ)) / Real.log 2))
  truncated_average : ∀ R : ℕ,
    Tendsto (timeAverage (fun j => min (a j : ℝ) (R : ℝ))) atTop
      (𝓝 (Real.log ((R : ℝ) + 1) / Real.log 2))
  divergent_average : Tendsto (timeAverage (fun j => (a j : ℝ))) atTop atTop





namespace InverseBranchTree.BranchEstimates



end InverseBranchTree.BranchEstimates
end BianchiIX


