-- Prove2me | Definitions.Def_InfHorizonVP_clarkeTangentCone
-- name    : InfHorizonVP_clarkeTangentCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:54.64638+00:00
-- url     : https://prove2.me/theorems/3b5926a1-3234-4bf0-a11a-e62fb0368093
-- title:
--   Clarke tangent cone $T_C(\bar x)$
-- statement:
--   For $C\subseteq E$ nonempty, let $d_C(x)=\inf_{\xi\in C}\|x-\xi\|$. The **Clarke tangent cone** to $C$ at $\bar x$ is
--   $$
--   T_C(\bar x)=\{v\in E\mid d_C^\circ(\bar x;v)=0\},
--   $$
--   where $d_C^\circ$ is the Clarke directional derivative of the (1-Lipschitz) distance function.
--
--   **Formalization Note** The Clarke directional derivative is the published `QuasiHemiVI.Existence.clarkeDeriv`.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.4

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Clarke tangent cone `T_C(x̄)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.4: "Let d_C : E → R be the distance function from a
nonempty subset C of E defined by d_C(x) := inf_{ξ∈C} ‖x−ξ‖. … Let x̄ be a point in C. A vector
v ∈ E is called a tangent to C at x̄ if d°_C(x̄; v) = 0. The set of all tangents to C at x̄ is
called the Clarke tangent cone to C at x̄ and is denoted by T_C(x̄) := {v ∈ E | d°_C(x̄; v) = 0}."

**Formalization Note.** `d_C = Metric.infDist · C`; `d°_C` is the Clarke directional derivative
`QuasiHemiVI.Existence.clarkeDeriv` (a real `limsup`, genuine here since `d_C` is 1-Lipschitz). -/
noncomputable def clarkeTangentCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x : E) : Set E :=
  {v | QuasiHemiVI.Existence.clarkeDeriv (fun y => Metric.infDist y C) x v = 0}

end InfHorizonVP


