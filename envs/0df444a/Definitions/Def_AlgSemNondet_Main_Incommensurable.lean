-- Prove2me | Definitions.Def_AlgSemNondet_Main_Incommensurable
-- name    : AlgSemNondet_Main_Incommensurable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:45:27.183197+00:00
-- url     : https://prove2.me/theorems/e803ffa8-9193-44af-9f8d-83b23b563e67
-- title:
--   Definition 3.11 — incommensurability over a field
-- statement:
--   Let $V$ be a vector space over a field $K$. Two vectors $u, v \in V$ are **incommensurable over $K$** if both are nonzero and $(u, v)$ is linearly independent over $K$.
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Definition 3.11, p.13, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib

namespace AlgSemNondet.Main

/-- Definition 3.11 (incommensurability). Two vectors `u, v` of a `K`-vector space are
incommensurable over `K` if they are nonzero and linearly independent over `K`. -/
def Incommensurable (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (u v : V) : Prop :=
  u ≠ 0 ∧ v ≠ 0 ∧ LinearIndependent K ![u, v]

end AlgSemNondet.Main


