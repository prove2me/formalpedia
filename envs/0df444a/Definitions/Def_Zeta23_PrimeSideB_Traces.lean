-- Prove2me | Definitions.Def_Zeta23_PrimeSideB_Traces
-- name    : Zeta23_PrimeSideB_Traces
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:21:41.335051+00:00
-- url     : https://prove2.me/theorems/394b1e74-fddc-41ee-927e-e41b517854d9
-- title:
--   The concrete data record for [thm:traces]
-- statement:
--   This bundle instantiates the abstract [thm:traces] interface with the actual objects of the formalization. Given parameters $P = (\varrho, \lambda, w)$ and a zero configuration $Z$, `PrimeSide.concreteData P Z` is the `Data P` record whose fourteen fields are the concrete quantities, as functions of $T$: the taper moments $a, b$ (`P.a`, `P.b`); the traces $\operatorname{tr}\tilde G$ and $\operatorname{tr}\tilde G^2$ (`P.trGtilde`, `P.trGtildeSq`); the zero count $N(T, 2T)$ of $Z$; the total form $\mathcal{M} = \mathtt{MtotalA}$ over the bridge $(P.\mathtt{toSetting}\,T,\ P.\mathtt{localFun}\,T)$; the six bilinear pieces $\mathcal{M}[u_1, u_2] = \mathtt{Mform}\,(P.\mathtt{PhiR}\,T)\,T\,u_1\,u_2$ for $u_i$ among $\mu$, $P_X$, $\Pi_X$ (the explicit-formula density components at cutoff $X = P.X\,T$); the integral $\int_T^{2T} \mu(\tau)^2\, d\tau$; and the arithmetic sum $\sum_{n \le X} \Lambda(n)^2/n\; g(\log n)$ (`sumA2g`).
--
--   Role: the surrounding module derives `Facts (concreteData P Z)` from `P.Valid`, the published inputs `PaperInputs Z` (H-RvM, H-$\Gamma$, H-cheb, H-MV), the §5 sub-results ([prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross], [prop:PP] with its sandwich), and the taper facts `LocalHypsEventually`, and concludes `thm_traces_of_localHyps : … → ThmTracesHyp P Z` — the concrete trace estimates [eq:tr1], [eq:tr2], [eq:ratio] consumed by the §6 assembly on the way to Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/Traces.lean, docstring tag [thm:traces]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE1
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
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
# [thm:traces] for the concrete data — instantiating the abstract assembly
`Zeta23/PrimeSideB.lean` proves [thm:traces] for abstract real functions of `T`
(`PrimeSide.Facts D → TracesBounds …`).  This file plugs in the concrete objects:

* `Params.toSetting P T = ⟨T, λ, w⟩` and `Params.localFun P T = ⟨φ̂, Φ, A_φ, g, a, b⟩(T)` turn
  (`P : Params`, `T`) into the abstract prime-side layer (`Setting`, `LocalFun`), and
  `trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T` etc. hold by `rfl`;
* `PrimeSide.concreteData P Z` is the `Data P` record of the actual traces / 𝓜-terms / ∫μ² / Σa_n²g;
* `PrimeSide.concreteFacts` derives `Facts (concreteData P Z)` from `P.Valid`, `PaperInputs Z`
  (H-RvM, H-Γ, H-cheb, H-MV), [prop:trace]/[lem:ends]/[eq:Msplit]/[prop:mumu]/[prop:cross],
  [prop:PP] + sandwich, and `LocalHypsEventually cϱ P` (the taper facts [eq:psidef],
  [eq:abdef], [eq:gbounds], [eq:Phi2FT], [lem:poisson] … for the concrete φ — proved in
  `Zeta23/PrimeSideA/Bridge.lean` from Taper.lean / Poisson.lean);
* `thm_traces_of_localHyps : … → ThmTracesHyp P Z`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace PrimeSide

open PaperParams

variable (P : Params)

/-- The concrete `Data P`: the actual prime-side traces, 𝓜-terms, `∫_T^{2T} μ²` and
`Σ_{n≤X} Λ(n)²/n g(log n)`, and `N(T,2T)` of the zero configuration `Z`. -/
def concreteData (Z : ZeroConfig) : Data P where
  aT := P.a
  bT := P.b
  trG := P.trGtilde
  trG2 := P.trGtildeSq
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalA (P.toSetting T) (P.localFun T)
  Mmumu := fun T => Mform (P.PhiR T) T mu mu
  MPP := fun T => Mform (P.PhiR T) T (PX (P.X T)) (PX (P.X T))
  MmuP := fun T => Mform (P.PhiR T) T mu (PX (P.X T))
  MmuPi := fun T => Mform (P.PhiR T) T mu (PiX (P.X T))
  MPPi := fun T => Mform (P.PhiR T) T (PX (P.X T)) (PiX (P.X T))
  MPiPi := fun T => Mform (P.PhiR T) T (PiX (P.X T)) (PiX (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), mu τ ^ 2
  sumL2g := fun T => sumA2g (P.X T) (P.g T)

variable {P}




end PrimeSide

end Zeta23

end


