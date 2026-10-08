-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_IsBerge
-- name    : StrongPerfectGraph_Main_IsBerge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:22:17.855528+00:00
-- url     : https://prove2.me/theorems/8f72bd29-e3fb-405b-84b1-e0ebb8f8ddc1
-- title:
--   Berge graph
-- statement:
--   A finite simple graph $G$ is **Berge** when every hole of $G$ and every antihole of $G$ has even length. With $\mathcal H(G)$ denoting the induced cycles of length at least four, this means
--
--   $$\forall C\in\mathcal H(G)\cup\mathcal H(\overline G),\qquad |C|\equiv0\pmod2.$$
--
--   The definition excludes induced odd cycles of length at least five in both the graph and its complement. It is the right-hand property in the strong perfect graph theorem.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 51, §1, definitions of hole, antihole, and Berge

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsHole

namespace StrongPerfectGraph.Main

/-- Every hole and antihole has even length. -/
def IsBerge {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ c : List V, IsHole G c → Even c.length) ∧
    (∀ c : List V, IsHole Gᶜ c → Even c.length)

end StrongPerfectGraph.Main


