-- Prove2me | Definitions.Def_FASTournament_IsMinimalFAS
-- name    : FASTournament_IsMinimalFAS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:24.961+00:00
-- url     : https://prove2.me/theorems/44111f34-2e1b-41f1-ba6a-8f3367db5dcd
-- title:
--   Minimal feedback arc set
-- statement:
--   A feedback arc set $F$ of $G$ is **minimal** if no proper subset of $F$ is a feedback arc set. Claim 1 lists the 41 minimal FASs of $G_1$; their incidence vectors are the rows of the matrix used in the proof of Lemma 4.1.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Claim 1, p.24

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsFAS

namespace FASTournament

/-- **Minimal feedback arc set.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, Claim 1, p.24 ("the family of all minimal feedback arc sets of G1").

An FAS of `G` none of whose proper subsets is an FAS (minimal under inclusion). -/
def IsMinimalFAS {V : Type*} (G : Digraph V) (F : Finset (Arc G)) : Prop :=
  IsFAS G F ∧ ∀ F' : Finset (Arc G), F' ⊂ F → ¬ IsFAS G F'

end FASTournament


