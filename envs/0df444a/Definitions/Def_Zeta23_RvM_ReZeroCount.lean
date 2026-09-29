-- Prove2me | Definitions.Def_Zeta23_RvM_ReZeroCount
-- name    : Zeta23_RvM_ReZeroCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:23:44.229773+00:00
-- url     : https://prove2.me/theorems/08b31224-dfac-415a-a521-65f6cfeb7ccc
-- title:
--   The symmetrised function $g_T$ for counting zeros of $\operatorname{Re}\zeta$
-- statement:
--   Definition for the Jensen half of Backlund's bound: `symZeta T` is the symmetrised function
--   $$g_T(z) \;:=\; \frac{\zeta(z+iT)+\zeta(z-iT)}{2},$$
--   which is analytic away from $1\pm iT$ and, by Schwarz reflection ($\zeta(\bar s)=\overline{\zeta(s)}$, proved in `Zeta23/ZetaReflect.lean`), equals $\operatorname{Re}\zeta(\sigma+iT)$ for real $z=\sigma$.
--
--   **Role.** The module bounds the number of zeros of $\operatorname{Re}\zeta(\sigma+iT)$ on $\sigma\in[1/2,2]$ by $O(\log T)$: since $g_T$ is analytic and $g_T(2)=\operatorname{Re}\zeta(2+iT)\ge 2-\pi^2/6>1/3$, one rescales the disc $|z-2|\le1.9$ to the unit disc and applies the ported PNT+ `ZerosBound` (with radii $r=0.8$, $R=0.9$) together with the growth bound `zeta_growth_right` on both summands. The resulting count `reZeroSet_card_le` is consumed by `Zeta23/RvM/Backlund.lean` for `backlund_horizontal`, the $O(\log T)$ estimate on the horizontal segments of the Riemann–von Mangoldt contour.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/ReZeroCount.lean

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_BacklundDefs
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ReZeroCount.lean — the Jensen half (J) of Backlund's bound:
the number of zeros of Re ζ(σ + iT) on σ ∈ [1/2, 2] is ≪ log T.
Route: g(z) := (ζ(z+iT) + ζ(z−iT))/2 is analytic away from 1 ± iT and equals Re ζ(σ+iT) for real σ
(riemannZeta_conj); g(2) = Re ζ(2+iT) ≥ 2 − π²/6 > 1/3; rescale |z−2| ≤ 1.9 to the unit disc and
apply the ported PNT+ ZerosBound (r = 0.8, R = 0.9) with zeta_growth_right on both summands.
Used by Zeta23/RvM/Backlund.lean for backlund_horizontal.
-/

open Complex Set Metric

noncomputable section

namespace Zeta23.RvM


/-- the symmetrised function g_T(z) := (ζ(z+iT) + ζ(z−iT))/2; equals Re ζ(σ+iT) for real σ. -/
def symZeta (T : ℝ) (z : ℂ) : ℂ := (riemannZeta (z + T * I) + riemannZeta (z - T * I)) / 2







end Zeta23.RvM


