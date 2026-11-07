-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_Valid
-- name    : MultiSelectPandora_RawSSDP_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:52.71229+00:00
-- url     : https://prove2.me/theorems/29163a3d-adea-49c2-85fc-e7a6c8a17aa8
-- title:
--   Well-formed tables
-- statement:
--   A table is well formed when:
--
--   1. the initial state is a state, $h$ has one entry per state, and each action has a list of outcomes per state;
--   2. the outcomes of an action at a state form a probability law on states;
--   3. an action without a group is a no-op with reward $0$, as *end* of Table 1, and at least one exists;
--   4. a group has at most two actions.
--
--   The last two record the framework as this paper states it: "each action can be taken at most once", *end* pads the remaining rounds, and "taking either removes the other from the set of available actions, a constraint the framework allows".
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §3.1, p.7 (PDF p.8); p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_outcomes

namespace MultiSelectPandora

/-- **A well-formed table.** Beyhaghi–Han–Luqman manuscript, §3.1, p.7 (PDF p.8), and p.8 (PDF p.9).

**Formalization Note.** (1) `init` is a state, `h` has one entry per state, and each action a list of outcomes per state. (2) Outcomes
are probability laws on states. (3) A repeatable action is a no-op, as `end` of Table 1, and at least one exists, so an action is always
available; a repeatable action with a nontrivial effect is not in the framework ("each action can be taken at most once"). (4) A group has
at most two actions: the framework of p.7 allows "taking either removes the other", and this is the only exclusion the page states. -/
def RawSSDP.Valid (S : RawSSDP) : Prop :=
  S.init < S.L ∧ S.h.length = S.L ∧
  (∀ act ∈ S.actions, act.2.length = S.L) ∧
  (∀ a < S.actions.length, ∀ st < S.L,
    (∀ o ∈ S.outcomes a st, 0 ≤ o.1 ∧ o.2.2 < S.L) ∧ ((S.outcomes a st).map fun o => o.1).sum = 1) ∧
  (∀ a < S.actions.length, (S.actions.getD a (none, [])).1 = none →
    ∀ st < S.L, S.outcomes a st = [(1, 0, st)]) ∧
  (∃ act ∈ S.actions, act.1 = none) ∧
  ∀ g : ℕ, (S.actions.filter fun act => act.1 = some g).length ≤ 2

end MultiSelectPandora


