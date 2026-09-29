-- Prove2me | Definitions.Def_Zeta23_Statement_SeamClosed
-- name    : Zeta23_Statement_SeamClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:10:48.101835+00:00
-- url     : https://prove2.me/theorems/5f0c8f8f-04d5-4faf-8280-f1b0d01b93cc
-- title:
--   The closed $\zeta$-seam and the zero configuration of $\zeta$
-- statement:
--   The $\zeta$-seam is closed: all four fields of `Zeta23.ZetaSeam` are theorems of Mathlib, so the abstract zero configuration of $\zeta$'s nontrivial zeros is hypothesis-free.
--
--   **Members.**
--   - `zetaSeam : ZetaSeam` — the seam, fully discharged with no hypotheses: it is assembled by `ZetaSeam.of_reflect` from `zeta_reflect_zero` and `zeta_mult_reflect` (`Zeta23/ZetaReflect.lean`, Schwarz reflection plus order transport through the functional equation), the remaining fields `one_le_mult` and `finite_window` having been discharged in `Zeta23/Statement/Seam.lean`.
--   - `zetaZeroConfig : ZeroConfig` — the nontrivial zeros of $\zeta$ with their multiplicities as an abstract `Zeta23.ZeroConfig`, with carrier $=\{\rho \mid \mathrm{IsNontrivialZero}\ \rho\}$ and multiplicity $=$ `zeroMult`, both holding by `rfl` (definitional equality).
--
--   **Role.** This is the pivot between the concrete analytic facts about `riemannZeta` and the abstract development: the Riemann–von Mangoldt count (`Zeta23.RiemannVonMangoldt zetaZeroConfig`), the explicit-formula zero sums, and the tail/zero-side matrix analysis are all stated and instantiated at `zetaZeroConfig`, hypothesis-free.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Statement/SeamClosed.lean

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_ZetaReflect

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement/SeamClosed.lean — the ζ-seam is closed.
All four fields of Zeta23.ZetaSeam are theorems of Mathlib:
  one_le_mult, finite_window  — Zeta23/Statement/Seam.lean ;
  reflect_zero, mult_reflect  — Zeta23/ZetaReflect.lean (Schwarz reflection
                                 riemannZeta_conj + functional equation at the analyticOrderAt level).
Hence the abstract ZeroConfig of ζ's nontrivial zeros and [eq:trivialchain] are hypothesis-free.
-/

noncomputable section

namespace Zeta23

/-- The ζ-seam, fully discharged: no hypotheses. -/
theorem zetaSeam : ZetaSeam := ZetaSeam.of_reflect zeta_reflect_zero zeta_mult_reflect

/-- The nontrivial zeros of ζ with multiplicities, as an abstract Zeta23.ZeroConfig — hypothesis-free.
carrier = {ρ | IsNontrivialZero ρ}, mult = zeroMult (both rfl). -/
def zetaZeroConfig : ZeroConfig := zetaZeros zetaSeam





end Zeta23


