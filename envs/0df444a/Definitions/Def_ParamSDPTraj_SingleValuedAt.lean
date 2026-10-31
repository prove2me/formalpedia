-- Prove2me | Definitions.Def_ParamSDPTraj_SingleValuedAt
-- name    : ParamSDPTraj_SingleValuedAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:46.858052+00:00
-- url     : https://prove2.me/theorems/a354685b-2a7f-474a-b95e-d3bd31efc94d
-- title:
--   Single-valued at a point
-- statement:
--   A set-valued map $F$ is **single-valued** at $t$ if $F(t)$ is a singleton.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 2.10, p.7

import Mathlib

namespace ParamSDPTraj

/-- **Single-valued at a point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 2.10, p.7: "We say that F is single-valued at t ∈ T if F(t) is a singleton". -/
def SingleValuedAt {E : Type*} (F : ℝ → Set E) (t : ℝ) : Prop :=
  ∃ x, F t = {x}

end ParamSDPTraj


