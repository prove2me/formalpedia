-- Prove2me | Definitions.Def_ParamSDPTraj_MultiValuedAt
-- name    : ParamSDPTraj_MultiValuedAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:37.354895+00:00
-- url     : https://prove2.me/theorems/e6dc94bc-3f85-4c14-bc0a-d841c01052c9
-- title:
--   Multi-valued at a point
-- statement:
--   A set-valued map $F$ is **multi-valued** at $t$ if $F(t)$ is neither empty nor a singleton.
-- source:
--   Bellon, Henrion, Kungurtsev, Mareček, Parametric Semidefinite Programming: Geometry of the Trajectory of Solutions, arXiv:2104.05445v3, Definition 2.10, p.7

import Mathlib
import Definitions.Def_ParamSDPTraj_SingleValuedAt

namespace ParamSDPTraj

/-- **Multi-valued at a point.**
Bellon, Henrion, Kungurtsev, Mareček, *Parametric Semidefinite Programming: Geometry of the
Trajectory of Solutions*, arXiv:2104.05445v3, Definition 2.10, p.7: "We say that F is multi-valued at t ∈ T if F(t) is neither empty nor
a singleton". -/
def MultiValuedAt {E : Type*} (F : ℝ → Set E) (t : ℝ) : Prop :=
  (F t).Nonempty ∧ ¬ SingleValuedAt F t

end ParamSDPTraj


