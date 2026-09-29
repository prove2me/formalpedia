-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalConstruction_CircleProjection
-- name    : HlawkaSchatten_DiagonalConstruction_CircleProjection
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-28T16:00:18.164358+00:00
-- url     : https://prove2.me/theorems/0b276893-3ac6-4ea7-8c0a-db371c5ca176
-- title:
--   Haar-averaged real projections on the unit circle (circleMeasure, circleMoment, projectionPower, finiteProjection)
-- statement:
--   Background structure and four quantities, all built from the unit circle group `Circle` (unit complex numbers) with its Borel measurable-space structure:
--
--   - The circle first receives its Borel $\sigma$-algebra (`MeasurableSpace Circle`) and the matching `BorelSpace Circle` instance, needed to integrate against a measure on it.
--   - `circleMeasure` is the Haar probability measure on `Circle`, normalized so the whole circle has measure $1$.
--   - `circleMoment` is the $p$-th absolute moment of the real part of a Haar-random point $u$ on the circle:
--   $$
--   \mathrm{circleMoment}(p) = \int_{u\in\mathrm{Circle}} \big|\operatorname{Re}(u)\big|^p \, d\,\mathrm{circleMeasure}.
--   $$
--   - `projectionPower`, for a real exponent $p$, a finite family of complex numbers $z=(z_i)_{i\in\iota}$, and a point $u$ on the circle, sums the $p$-th power of the absolute real part of each rotated entry:
--   $$
--   \mathrm{projectionPower}(p,z,u) = \sum_i \big|\operatorname{Re}(u\,z_i)\big|^p.
--   $$
--   - `finiteProjection`, for weights $w=(w_k)_{k\in\kappa}$, rotations $u=(u_k)_{k\in\kappa}$ on the circle, and $z=(z_i)_{i\in\iota}$, builds a single real-valued family indexed by $\kappa\times\iota$:
--   $$
--   \mathrm{finiteProjection}(p,w,u,z)_{(k,i)} = w_k^{1/p}\,\operatorname{Re}(u_k\,z_i).
--   $$
--
--   These realize, for $p>0$, the $p$-th power of each complex `lpNorm` value, up to the constant factor $\mathrm{circleMoment}(p)$, as the average over the unit circle of the real projection power sum `projectionPower`: `projectionPower` computes the real coordinate power sum after rotating by $u$, `circleMoment` is that same average taken at a single unit vector, and `finiteProjection` packages a finite sample of weighted rotations into one real-coordinate family, so that a real inequality proved for `lpNorm` can be transferred to the complex `lpNorm` values.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/CircleProjection.lean#L18-L87

import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Real projections averaged over the unit circle -/

namespace HlawkaSchatten.DiagonalConstruction

open MeasureTheory

 noncomputable instance : MeasurableSpace Circle := borel Circle
private instance : BorelSpace Circle := ⟨rfl⟩

noncomputable abbrev circleMeasure : Measure Circle :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Circle)



noncomputable def circleMoment (p : ℝ) : ℝ := ∫ u : Circle, |(u : ℂ).re| ^ p ∂circleMeasure







variable {ι : Type*} [Fintype ι]

noncomputable def projectionPower (p : ℝ) (z : ι → ℂ) (u : Circle) : ℝ :=
  ∑ i, |((u : ℂ) * z i).re| ^ p





variable {κ : Type*} [Fintype κ]

noncomputable def finiteProjection (p : ℝ) (w : κ → ℝ) (u : κ → Circle) (z : ι → ℂ) : κ × ι → ℝ :=
  fun k ↦ w k.1 ^ (1 / p) * (((u k.1 : Circle) : ℂ) * z k.2).re





end HlawkaSchatten.DiagonalConstruction


