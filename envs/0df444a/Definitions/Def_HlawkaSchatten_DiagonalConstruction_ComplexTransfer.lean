-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
-- name    : HlawkaSchatten_DiagonalConstruction_ComplexTransfer
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:02:51.961307+00:00
-- url     : https://prove2.me/theorems/1cf7bb14-a189-4df6-b9d5-0fd9d8e16714
-- title:
--   The abstract seven-term Hlawka deficit and the seven vectors of a triple (powerDeficit, sevenVectors, sevenProjections)
-- statement:
--   Three definitions that carry the real cyclic bound over to complex vectors:
--
--   - `powerDeficit`, for a real exponent $p$, a real constant $K$, and seven real numbers $a=(a_0,\dots,a_6)$, forms the same combination as the Hlawka deficit, but applied directly to $a_k^{1/p}$ rather than to `lpNorm` of a vector:
--   $$
--   \mathrm{powerDeficit}(p,K,a) = (2K-1)\big(a_0^{1/p}+a_1^{1/p}+a_2^{1/p}\big) + a_6^{1/p} - K\big(a_3^{1/p}+a_4^{1/p}+a_5^{1/p}\big).
--   $$
--   - `sevenVectors`, for three finite families of complex numbers $x,y,z$, packages the seven vectors that occur in a triple's Hlawka deficit into one length-seven family:
--   $$
--   \mathrm{sevenVectors}(x,y,z) = (x,\,y,\,z,\,x+y,\,x+z,\,y+z,\,x+y+z).
--   $$
--   - `sevenProjections`, for a real exponent $p$ and a point $u$ on the unit circle, applies `projectionPower` to each of these seven vectors:
--   $$
--   \mathrm{sevenProjections}(p,x,y,z,u)_k = \mathrm{projectionPower}\big(p,\ \mathrm{sevenVectors}(x,y,z)_k,\ u\big).
--   $$
--
--   `powerDeficit` is the abstract, coordinate-free shape of the Hlawka-deficit combination once each `lpNorm`-to-the-$p$ value has been replaced by a free real variable; `sevenVectors` and `sevenProjections` supply exactly the seven real numbers that combination needs, for a triple of complex vectors, at a fixed rotation of the circle. Together they are the link between the real bound proved for `lpNorm` and the complex case, via an average over the circle.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ComplexTransfer.lean#L23-L38

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CircleProjection
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Transfer to complex coordinates

Finite convex combinations of real circle projections obey the real bound.
Continuity preserves this statement on their closure. The circle average
belongs to that closure and reproduces all seven complex norms with one
common positive factor.
-/

namespace HlawkaSchatten.DiagonalConstruction

open MeasureTheory

noncomputable def powerDeficit (p K : ℝ) (a : Fin 7 → ℝ) : ℝ :=
  (2 * K - 1) * ((a 0) ^ (1 / p) + (a 1) ^ (1 / p) + (a 2) ^ (1 / p)) +
    (a 6) ^ (1 / p) - K * ((a 3) ^ (1 / p) + (a 4) ^ (1 / p) + (a 5) ^ (1 / p))



variable {ι : Type*} [Fintype ι]

def sevenVectors (x y z : ι → ℂ) : Fin 7 → ι → ℂ := ![x, y, z, x + y, x + z, y + z, x + y + z]

noncomputable def sevenProjections (p : ℝ) (x y z : ι → ℂ) (u : Circle) : Fin 7 → ℝ :=
  fun k ↦ projectionPower p (sevenVectors x y z k) u







end HlawkaSchatten.DiagonalConstruction


