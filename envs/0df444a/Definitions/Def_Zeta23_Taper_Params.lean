-- Prove2me | Definitions.Def_Zeta23_Taper_Params
-- name    : Zeta23_Taper_Params
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:12:08.158351+00:00
-- url     : https://prove2.me/theorems/2f638804-d18b-42f2-91fc-ff0c41234130
-- title:
--   Consumer-facing taper definitions at the parameter pack $P$
-- statement:
--   The consumer-facing layer of the taper development: the versions of the taper quantities taking a parameter pack `P : Params` (containing the profile $\varrho$, the exponent $\lambda$, the width $w$) and a height $T:\mathbb R$, rather than raw $(\varrho,L,w)$.
--
--   **Members.**
--   - `Params.psi'` — the majorant $\psi$ of [eq:psidef] at the pack's parameters, $\psi(r)=\min(L,\,2/|r|,\,c_\varrho/(wr^2))$ with value $L$ at $r=0$; defined as `Taper.psi P.ϱ (P.L T) P.w`. Since `Defs.lean` uses the same body, `P.psi T = P.psi' T` holds by `rfl` (`psi_eq_psi'`), and both names are available.
--   - `Params.C1` — the constant $C_1:=\lVert\varphi''\rVert_1$ of [prop:tail] at the pack's parameters, `Taper.C1 P.ϱ (P.L T) P.w`.
--
--   **Role.** This file is part 1 of the `Params` layer, split out of the umbrella `Zeta23/Taper.lean` so that `Zeta23/Main.lean` can import the $\varphi$-facts ([eq:phidef], [eq:abdef], $C_1$, and [eq:hfbound] for $\varphi$, under the hypotheses `P.Valid` and $8w\le L$ [eq:wrange]) without pulling in the heavier `Taper/Decay` and `Taper/Fourier` modules. The remaining `Params`-layer facts ($\hat\varphi/\Phi$, $\psi$, $g$, $A_\varphi$, Plancherel) live in `Zeta23/Taper.lean`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Params.lean, docstring tag [prop:tail]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Params.lean.  Consumer-facing layer, part 1:
the `P : Params`, `T : ℝ` versions of everything that depends only on Taper/Basic, Taper/Norms
and Taper/Strip (φ facts [eq:phidef], [eq:abdef], C₁ and [eq:hfbound] for φ), plus the rfl
bridges to Defs.  Split out of Zeta23/Taper.lean so that Zeta23/Main.lean can import it without
pulling Taper/Decay, Taper/Fourier.  Hypotheses: `hP : P.Valid`,
`hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).  The remaining Params-layer facts (φ̂/Φ, ψ, g, A_φ,
Plancherel) are in the umbrella Zeta23/Taper.lean.
-/

open Complex MeasureTheory Real Set Filter Topology

namespace Zeta23

namespace Params

variable (P : Params) (T : ℝ)


/-- ψ (value `L` at `r = 0`); see `Taper.psi`.  Since Defs uses the same body,
`P.psi T = P.psi' T` is `rfl` (`psi_eq_psi'`); both names are available. -/
noncomputable def psi' (r : ℝ) : ℝ := Taper.psi P.ϱ (P.L T) P.w r


/-- `C₁ := ‖φ''‖₁` [prop:tail]. -/
noncomputable def C1 : ℝ := Taper.C1 P.ϱ (P.L T) P.w

variable {P T}


/-! #### hypothesis-free facts -/

section
variable (hP : P.Valid)
include hP
end

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ -/

/-! #### [eq:abdef] -/

/-! #### [eq:hfbound] for φ ([prop:tail]) -/

end

end Params

end Zeta23


