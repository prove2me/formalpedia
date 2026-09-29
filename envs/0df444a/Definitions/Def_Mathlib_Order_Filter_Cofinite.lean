-- Prove2me | Definitions.Def_Mathlib_Order_Filter_Cofinite
-- name    : Mathlib_Order_Filter_Cofinite
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/cb033856-180d-5674-a3d3-917ada46a674
-- title:
--   Countability of the cofinite filter's sets on a countable type
-- statement:
--   Two general facts about the cofinite filter are recorded for an arbitrary countable index type $\iota$. The lemma [`Filter.cofinite.sets.countable`](../def/Mathlib_Order_Filter_Cofinite.html#L5) asserts that the collection of members of `Filter.cofinite` on $\iota$ — that is, the family of subsets $s \subseteq \iota$ whose complement $s^{c}$ is finite, viewed as a subset of the power set of $\iota$ — is a countable set in the sense of `Set.Countable`. The proof rests on the fact that the finite subsets of a countable type form a countable family together with the involution $s \mapsto s^{c}$ on subsets of $\iota$, which is a bijection and hence injective on any set; the cofinite sets are exactly the preimage of the finite sets under this involution.
--
--   The accompanying instance packages the same statement in type-theoretic form: for a countable type $\iota$, the subtype of subsets of $\iota$ belonging to `Filter.cofinite`, regarded as a type via the coercion of its set of members, carries a `Countable` instance. The two formulations are interchanged through the equivalence between countability of a set and countability of its associated subtype.
--
--   **Relation to Mathlib.** `Filter.cofinite`, `Set.Countable` and `compl_bijective` are Mathlib notions; this module only adds the countability statement for the members of the cofinite filter on a countable type, in both its set-level and its typeclass form.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Order/Filter/Cofinite.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Order_Filter_Cofinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

lemma Filter.cofinite.sets.countable (ι : Type*) [Countable ι] :
    (Filter.cofinite : Filter ι).sets.Countable :=
  Set.Countable.mono (fun _ h ↦ h) <|
  Set.Countable.preimage_of_injOn Set.Countable.setOf_finite compl_bijective.1.injOn

instance (ι : Type*) [Countable ι] : Countable (.cofinite : Filter ι).sets := by
  rw [Set.countable_coe_iff]
  exact Filter.cofinite.sets.countable ι


