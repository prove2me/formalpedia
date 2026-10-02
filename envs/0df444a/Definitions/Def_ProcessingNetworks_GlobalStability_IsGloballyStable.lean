-- Prove2me | Definitions.Def_ProcessingNetworks_GlobalStability_IsGloballyStable
-- name    : ProcessingNetworks_GlobalStability_IsGloballyStable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:08:58.259795+00:00
-- url     : https://prove2.me/theorems/9056d8b6-9530-4451-a80d-d68b8d2686d7
-- title:
--   Definition 8.22 — global stability of a queueing network
-- statement:
--   **Definition 8.22.** A queueing network is **globally stable** if it is stable in the sense
--   of Definition 3.6 (its ambient Markov chain is positive recurrent) under *every* simply
--   structured, non-idling control policy.
--
--   Subcriticality was widely conjectured, until the early 1990s, to already imply global
--   stability for every queueing network; the Rybko–Stolyar and Dai–Wang examples (Chapter 1)
--   refuted this, motivating this chapter's search for additional structural conditions (the
--   feedforward family of mission VI; the ring and re-entrant-line families of this mission) under
--   which subcriticality *does* suffice.
--
--   **Formalization note.** Formalized abstractly over an uninterpreted type `Policy` of control
--   policies and two predicates on it, since the concrete notions of "simply structured control
--   policy" and "positive recurrence under a policy" belong to mission I's apparatus
--   (`BaselineAssumptions`, `MarkovRepresentation`, `IsStable`), which this chunk does not depend
--   on (`BRIEF.md` lists only missions III and V). This mission's own theorems (8.21, 8.24, 8.25)
--   all work at the checkable fluid-model tier, `FluidModelGloballyStable`, which Theorem 6.2
--   connects to this Markov-chain-level notion — the same two-tier pattern as Definitions
--   6.1/6.3.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 151, Definition 8.22

import Mathlib

namespace ProcessingNetworks.GlobalStability

/-- Definition 8.22 (global stability of a queueing network), Dai & Harrison p. 151 (PDF p. 167):
a queueing network is globally stable if it is stable in the sense of Definition 3.6 (its ambient
Markov chain is positive recurrent) under *every* simply structured, non-idling control policy.
Stated abstractly over a type `Policy` of control policies with predicates
`IsSimplyStructuredNonIdling` and `IsMarkovStableUnder`, since the network-level notions of
"simply structured control policy" (Section 2.3) and "positive recurrence under a given policy"
(Definition 3.6) belong to mission I, not a dependency of this chunk (`BRIEF.md` lists only
missions III and V) — this mission works at the fluid-model tier (Definition 8.23,
`FluidModelGloballyStable`) instead, connected to this network-level notion the same way
Definition 6.1 connects to Definition 3.6 via Theorem 6.2. -/
def IsGloballyStable {Policy : Type*} (IsSimplyStructuredNonIdling : Policy → Prop)
    (IsMarkovStableUnder : Policy → Prop) : Prop :=
  ∀ π : Policy, IsSimplyStructuredNonIdling π → IsMarkovStableUnder π

end ProcessingNetworks.GlobalStability


