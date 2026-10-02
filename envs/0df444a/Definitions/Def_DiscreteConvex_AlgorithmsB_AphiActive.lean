-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_AphiActive
-- name    : DiscreteConvex_AlgorithmsB_AphiActive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:51:12.845356+00:00
-- url     : https://prove2.me/theorems/f0a15a39-9956-42d8-a5a7-d919949fda6d
-- title:
--   AphiActive
-- statement:
--   Membership in the arc set $A_\phi=\{(u,v)\mid\phi(u,v)=0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, Eq. (10.22).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.297, Eq. (10.22)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Membership in the arc set `Aϕ = {(u,v) | ϕ(u,v)=0}` of Eq. (10.22). -/
def AphiActive (phi : V → V → ℝ) (u v : V) : Prop := u ≠ v ∧ phi u v = 0

end DiscreteConvex.AlgorithmsB


