-- Prove2me | Definitions.Def_SteinerCutDominants_Intersect
-- name    : SteinerCutDominants_Intersect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:33.760124+00:00
-- url     : https://prove2.me/theorems/d1e66ee3-7f74-49ad-88e5-2c5ddb14049c
-- title:
--   Intersecting sets
-- statement:
--   Two sets $A$ and $B$ **intersect** if $A\cap B$, $A\setminus B$ and $B\setminus A$ are all nonempty.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §3, p.6

import Mathlib

namespace SteinerCutDominants

/-- Two sets `A` and `B` intersect if `A ∩ B`, `A \ B` and `B \ A` are all nonempty (Conforti,
Kaibel, *Steiner Cut Dominants*, arXiv:2209.14802v2, §3, p.6). -/
def Intersect {V : Type} [DecidableEq V] (A B : Finset V) : Prop :=
  (A ∩ B).Nonempty ∧ (A \ B).Nonempty ∧ (B \ A).Nonempty

end SteinerCutDominants


