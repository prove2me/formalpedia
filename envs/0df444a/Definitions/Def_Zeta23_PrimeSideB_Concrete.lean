-- Prove2me | Definitions.Def_Zeta23_PrimeSideB_Concrete
-- name    : Zeta23_PrimeSideB_Concrete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:19:29.210574+00:00
-- url     : https://prove2.me/theorems/91bebbe4-0748-45f7-8b0e-dd1d49f79517
-- title:
--   Bridge from concrete parameters $(P, T)$ to the abstract prime-side layer
-- statement:
--   This bundle provides the glue that turns the concrete parameter record $P = (\varrho, \lambda, w)$ of `Zeta23/Defs.lean` (with height $T$ separate) into the abstract prime-side layer over which §5 is proved.
--
--   The members: `Params.toSetting P T` is the abstract parameter triple $\langle T, \lambda, w \rangle$ (a `PrimeSide.Setting`); `Params.localFun P T` is the concrete taper data at height $T$ packaged as an abstract `PrimeSide.LocalFun`, namely $(\hat\varphi|_{\mathbb{R}},\ \Phi|_{\mathbb{R}},\ A_\varphi,\ g,\ a,\ b) = (P.\mathtt{phiHatR}\,T,\ P.\mathtt{PhiR}\,T,\ P.\mathtt{Aphi}\,T,\ P.g\,T,\ P.a\,T,\ P.b\,T)$ — under this bridge the abstract quantities $L, X, d, \tau_k, h$ and traces agree with their `Params` counterparts by `rfl`. `PrimeSide.LocalHypsEventually` names the hypothesis that the taper facts `LocalHyps` hold for this concrete data for all sufficiently large $T$ — a statement proved in `Zeta23/PrimeSideA/Bridge.lean` from Taper.lean and Poisson.lean, carried here as a named assumption.
--
--   Role: with this bridge, `Zeta23/PrimeSideB/Traces.lean` builds the concrete `Data P` record and derives its `Facts`, producing `thm_traces_of_localHyps : … → ThmTracesHyp P Z` — the concrete form of [thm:traces] consumed by the §6 assembly and the headline theorems in `Zeta23/Main.lean`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/Concrete.lean

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideTemp

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# The concrete prime-side data as an instance of the abstract layer
Small, dependency-light file (imports only `PrimeSideA.Basic` and `PrimeSideTemp`):

* `Params.toSetting P T = ⟨T, λ, w⟩`, `Params.localFun P T = ⟨φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b⟩(T)` and the
  `rfl` bridges (`trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T`, …);
* `PrimeSide.LocalHypsEventually cϱ P` — "the taper facts `LocalHyps` hold for the concrete data for
  all large `T`" (proved in `Zeta23/PrimeSideA/Bridge.lean`);
* `PrimeSide.evBound_of_eventuallyAt` — an `EventuallyAt`-form result specialised to the concrete
  data is an `EvBound` in `T`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)

/-- The abstract-layer parameter triple `(T, λ, w)` (`PrimeSide.Setting`). -/
def toSetting : PrimeSide.Setting := ⟨T, P.lam, P.w⟩

/-- The concrete taper data at height `T` as an abstract `PrimeSide.LocalFun`:
`(φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b)` = `(P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T)`. -/
def localFun : PrimeSide.LocalFun := ⟨P.phiHatR T, P.PhiR T, P.Aphi T, P.g T, P.a T, P.b T⟩


end Params

namespace PrimeSide

variable (P : Params) (T : ℝ)




/-- The taper facts `LocalHyps` hold for the concrete data for all large `T`
(proved in `Zeta23/PrimeSideA/Bridge.lean`; here a named hypothesis). -/
def LocalHypsEventually (cϱ : ℝ) (P : Params) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → LocalHyps cϱ (P.toSetting T) (P.localFun T)

variable {P}




end PrimeSide

end Zeta23

end


