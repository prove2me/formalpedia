-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_Collision
-- name    : OAI_NumberTheory_PiExponent_Analysis_Collision
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:28:43.865459+00:00
-- url     : https://prove2.me/theorems/e7e8f0df-8e23-43cf-aaac-4464d5084082
-- title:
--   Holomorphic error term in the determinant estimate
-- statement:
--   For a natural number $K$ and real parameters $w_0$, $v_0$, and $w_\star$, this definition assigns the real quantity
--
--   $$E_{\mathrm{hol}}(K,w_0,v_0,w_\star)=\frac{100K}{w_0}+\frac{\log 2}{v_0}+\frac{\log(200K)}{w_\star}.$$
--
--   The declaration itself imposes no positivity, nonzero, or size conditions on these inputs; such hypotheses belong to any later estimate that uses the expression. In the source development it packages the holomorphic contribution appearing in a determinant upper bound.
-- source:
--   OpenAI math, source commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Analysis/Collision.lean, definition holomorphicError, lines 12-13: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean#L12-L13

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix



namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent

noncomputable def holomorphicError (K : ℕ) (w0 v0 wstar : ℝ) : ℝ :=
  100 * K / w0 + Real.log 2 / v0 + Real.log (200 * K) / wstar





end PiExponent

end OAI


