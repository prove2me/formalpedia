-- Prove2me | Definitions.Def_PrivLittlestone_worldInput
-- name    : PrivLittlestone_worldInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:49.752923+00:00
-- url     : https://prove2.me/theorems/57852df5-4a39-45f0-8fdd-adbcfb365613
-- title:
--   Input seen by the learner in challenge world $b$
-- statement:
--   In **challenge world $b \in \{0,1\}$**, the learner receives the record $z^b_t$ of each pair $(z^0_t, z^1_t)$ supplied by the adversary.
--
--   **Formalization Note** $b = 0$ is `false` (first component) and $b = 1$ is `true`.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Definition 2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_InputStrategy
import Definitions.Def_PrivLittlestone_Adversary

namespace PrivLittlestone

/-- The input strategy seen by the learner in **challenge world `b`** (He–He, *Private Online
Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256
21480556…c562), Definition 2.1, p.4): "the learner receives `z^b_t`".

**Formalization Note** The hidden bit `b ∈ {0,1}` is `Bool`, with `false` = world 0 (first
component) and `true` = world 1 (second component). -/
def worldInput {X : Type*} {T : ℕ} (adv : Adversary X T) (b : Bool) : InputStrategy X T :=
  fun t g => if b then (adv t g).2 else (adv t g).1

end PrivLittlestone


