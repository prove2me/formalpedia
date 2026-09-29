-- Prove2me | Definitions.Def_Zeta23_GammaFacts_Series
-- name    : Zeta23_GammaFacts_Series
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:05:38.093182+00:00
-- url     : https://prove2.me/theorems/f59541fa-bd5d-4b87-8ddc-87d034140e2c
-- title:
--   Offset Weierstrass factor for the digamma partial-fraction series
-- statement:
--   This bundle defines **`wTerm`**, the offset Weierstrass factor used in `Zeta23/GammaFacts/Series.lean`: for $n \in \mathbb{N}$ and $z \in \mathbb{C}$,
--   $$1 + \mathrm{wTerm}(n, z) = \Bigl(1 + \frac{z}{n+1}\Bigr)e^{-z/(n+1)},$$
--   i.e. $\mathrm{wTerm}(n,z) := (1 + \frac{z}{n+1})e^{-z/(n+1)} - 1$. The bound $\|\mathrm{wTerm}(n,z)\| \le 3(\|z\|/(n+1))^2$ for $n + 1 \ge \|z\|$ makes the infinite product $\Gamma(z)^{-1} = z\,e^{\gamma z}\prod_n (1 + \mathrm{wTerm}(n,z))$ (the Weierstrass product) amenable to the M-test.
--
--   The surrounding module carries out the route (modelled on Mathlib's cotangent development): finite identity for $\mathrm{GammaSeq}^{-1}$, limit to the Weierstrass product, then logarithmic differentiation to the digamma partial-fraction series
--   $$\psi(z) = -\gamma - \frac{1}{z} + \sum_{n \ge 0}\Bigl(\frac{1}{n+1} - \frac{1}{z+n+1}\Bigr) \quad (z \in \mathbb{C}\setminus\mathbb{Z}_{\le 0}),$$
--   the Mathlib-missing piece needed for the H-Γ fields [eq:mufacts]. This series is the input to the vertical-line Stirling estimate (`StirlingVert.lean`) and hence to the proof of the `GammaFacts` package consumed by the prime side of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
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

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Series.lean — the digamma partial-fraction series.

Target:  digamma z = −γ − 1/z + ∑'_{n≥0} (1/(n+1) − 1/(z+n+1))   for z ∈ ℂ_ℤ,
the Mathlib-missing piece needed for the remaining H-Γ fields
([eq:mufacts]; see Zeta23/GammaFacts.lean).  Route (modelled on Mathlib's
Analysis/SpecialFunctions/Trigonometric/Cotangent.lean, which does the same for
sin → cot):
  1. Weierstrass factors  1 + wTerm n z = (1 + z/(n+1))·e^{−z/(n+1)}, with
     ‖wTerm n z‖ ≤ 3(‖z‖/(n+1))² for n+1 ≥ ‖z‖  (M-test input);
  2. the finite identity  (GammaSeq z N)⁻¹ = z·e^{(H_N − log N)z}·∏_{n<N}(1+wTerm n z);
  3. N → ∞ (GammaSeq_tendsto_Gamma + tendsto_harmonic_sub_log):
       Γ(z)⁻¹ = z·e^{γz}·∏'_n (1 + wTerm n z)            [Weierstrass product]
  4. logDeriv via Complex.logDeriv_tprod_eq_tsum          [digamma series].
This file has steps 1–3; step 4 is `digamma_series` at the bottom.
-/

noncomputable section

namespace Zeta23
namespace DigammaSeries

open Complex Filter Topology

/-- Offset Weierstrass factor: `1 + wTerm n z = (1 + z/(n+1))·e^{−z/(n+1)}`. -/
def wTerm (n : ℕ) (z : ℂ) : ℂ := (1 + z / (n + 1)) * Complex.exp (-(z / (n + 1))) - 1







/-! ### The finite identity and the Weierstrass product -/








end DigammaSeries
end Zeta23


