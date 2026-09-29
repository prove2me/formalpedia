-- Prove2me | Definitions.Def_Zeta23_GammaFacts_IntMu
-- name    : Zeta23_GammaFacts_IntMu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:06:16.983558+00:00
-- url     : https://prove2.me/theorems/76d4d15a-3508-4076-99a4-3bafaa3de554
-- title:
--   Stirling hypothesis for the archimedean density $\mu$
-- statement:
--   This bundle defines **`StirlingHyp`**, the Stirling-field statement taken as a standing hypothesis in `Zeta23/GammaFacts/IntMu.lean`: there exists a constant $C$ such that for all real $\tau$ with $|\tau| \ge 1$,
--   $$\Bigl|\mu(\tau) - \frac{1}{2\pi}\log\frac{|\tau|}{2\pi}\Bigr| \le \frac{C}{\tau^2},$$
--   where $\mu(\tau) = \frac{1}{2\pi}\mathrm{Re}\,\frac{\Gamma'}{\Gamma}(\frac14 + \frac{i\tau}{2}) - \frac{\log\pi}{2\pi}$ is the archimedean density of `Defs.lean` [eq:mudef]. This is exactly the `stirling` field of the `GammaFacts` structure (H-Γ, [eq:mufacts]) — Stirling's formula for $\Gamma'/\Gamma$ on the critical line, in quantitative form.
--
--   The surrounding module proves the two Γ-half integrals of [eq:muints] from this hypothesis: $\int_T^{2T}\mu(\tau)\,d\tau = T\ell_1/(2\pi) + O(1/T)$ and $\int_T^{2T}\mu(\tau)^2\,d\tau = (T\ell_1^2/4\pi^2)(1 + O(l^{-2}))$. The Stirling asymptotic itself is proved in `Zeta23/GammaFacts/StirlingVert.lean`, so `GammaFacts` assembles in `Complete.lean` with no unproved Γ-input; these integrals feed the prime-side trace computation [prop:trace] of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/IntMu.lean, docstring tags [eq:mufacts], [eq:muints]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/IntMu.lean — the [eq:muints] Γ-half integrals.
Paper: "∫_T^{2T} μ(τ)dτ = Tℓ₁/(2π) + O(1/T)", "∫_T^{2T} μ(τ)² dτ = (Tℓ₁²/4π²)(1 + O(l⁻²))",
via "(eq:muints) follows from (eq:mufacts) … and ∫_T^{2T} log²(τ/2π) dτ = T(ℓ₁² + 1 − 2log²2)".
Both theorems take the Stirling field as a hypothesis (hst); the Stirling asymptotic itself is
proved elsewhere in the repository, so GammaFacts assembles with no Γ-hypothesis beyond it.
-/

noncomputable section

namespace Zeta23
namespace MuInts

open MeasureTheory intervalIntegral

/-- The Stirling-field statement, as a standing hypothesis (same statement as
GammaFacts.stirling). -/
def StirlingHyp : Prop := ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
  |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2





end MuInts
end Zeta23


