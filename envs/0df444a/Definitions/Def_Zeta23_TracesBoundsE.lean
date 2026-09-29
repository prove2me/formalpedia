-- Prove2me | Definitions.Def_Zeta23_TracesBoundsE
-- name    : Zeta23_TracesBoundsE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:02:19.222563+00:00
-- url     : https://prove2.me/theorems/ab933b0d-4b65-4774-ac6d-3e01e1261f71
-- title:
--   Trace bounds of [thm:traces] with an abstract error rate
-- statement:
--   A generalisation of `TracesBounds`: the structure `TracesBoundsE P Err aT trG trG2 Ncnt` records the four conclusions of the paper's Theorem [thm:traces] ([eq:tr1] in both forms, [eq:tr2] second form, [eq:ratio]) with an arbitrary error rate $\mathrm{Err}:\mathbb R\to\mathbb R$ in place of the paper's specific rate $\mathcal E_T$. Here $P$ is the parameter pack and $aT,\,trG,\,trG2,\,Ncnt$ are real functions of $T$ standing for the taper constant $a$, $\operatorname{tr}\tilde G$, $\operatorname{tr}\tilde G^2$ and the zero count $N(T,2T)$. Each field is an `EvBound` (an explicit inequality $\exists C>0,\exists T_0,\forall T\ge T_0$):
--
--   $$\texttt{tr1}:\ \bigl|\operatorname{tr}\tilde G - a\,L\,N\bigr| \le C\,L\sqrt X,\qquad \texttt{tr1'}:\ \bigl|\operatorname{tr}\tilde G - L\,N\bigr| \le C\,\mathrm{Err}(T)\cdot L\,N,$$
--   $$\texttt{tr2}:\ \Bigl|\operatorname{tr}\tilde G^2 - \frac{TL}{2\pi}\bigl(\ell_1^2+\tfrac{L^2}{3}\bigr)\Bigr| \le C\,\mathrm{Err}(T)\cdot\frac{TL}{2\pi}\bigl(\ell_1^2+\tfrac{L^2}{3}\bigr),\qquad \texttt{ratio}:\ \Bigl|\frac{(\operatorname{tr}\tilde G)^2}{\operatorname{tr}\tilde G^2} - F(\lambda_1)\,N\Bigr| \le C\,\mathrm{Err}(T)\cdot F(\lambda_1)\,N,$$
--
--   where $F$ is the paper's variational function `Ffun` and $\lambda_1 = $ `P.lam1 T`.
--
--   **Role.** This is a deliberately light file (importing only `Zeta23.PrimeSideTemp`) so that `Zeta23/Assembly.lean` can import it; `TracesBounds` of `PrimeSideTemp.lean` is the instance $\mathrm{Err}:=P.\mathrm{calE}$ (the paper's $\mathcal E_T$), supplied along the paper's route by `Zeta23/PrimeSideB/Traces.lean` via `TracesBounds.toE`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/TracesBoundsE.lean, docstring tag [thm:traces]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_PrimeSideTemp

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
  Bracketed labels ([prop:cross], [eq:Msplit], …) and section numbers (§5.4, …) refer to that paper.
-/

/-!
# [thm:traces] conclusions with an ABSTRACT error rate

LIGHT file (imports only Zeta23.PrimeSideTemp) so that Zeta23/Assembly.lean can import it:
`TracesBoundsE P Err aT trG trG2 Ncnt` = the four conclusions of the paper [thm:traces] ([eq:tr1] both forms,
[eq:tr2] second form, [eq:ratio]) with an arbitrary rate `Err : ℝ → ℝ` in place of the paper's 𝓔_T;
`TracesBounds` (Zeta23/PrimeSideTemp.lean) is the instance `Err := P.calE`, supplied by the paper's route
(Zeta23/PrimeSideB/Traces.lean via `TracesBounds.toE`).
-/

noncomputable section

open Filter Topology Real

namespace Zeta23

/-! ## [thm:traces] conclusions with an abstract rate -/

/-- The four conclusions of [thm:traces] with an abstract error rate `Err` (cf. `TracesBounds`,
Zeta23/PrimeSideTemp.lean, which is the case `Err = P.calE` = the paper's 𝓔_T). -/
structure TracesBoundsE (P : Params) (Err aT trG trG2 Ncnt : ℝ → ℝ) : Prop where
  tr1 : EvBound (fun T => trG T - aT T * P.L T * Ncnt T) (fun T => P.L T * Real.sqrt (P.X T))
  tr1' : EvBound (fun T => trG T - P.L T * Ncnt T) (fun T => Err T * (P.L T * Ncnt T))
  tr2 : EvBound (fun T => trG2 T - P.mainTr2 T) (fun T => Err T * P.mainTr2 T)
  ratio : EvBound (fun T => trG T ^ 2 / trG2 T - Ffun (P.lam1 T) * Ncnt T)
    (fun T => Err T * (Ffun (P.lam1 T) * Ncnt T))






end Zeta23

end


