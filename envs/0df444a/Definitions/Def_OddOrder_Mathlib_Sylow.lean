-- Prove2me | Definitions.Def_OddOrder_Mathlib_Sylow
-- name    : OddOrder_Mathlib_Sylow
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:14.376944+00:00
-- url     : https://prove2.me/theorems/47a62989-55d4-4ff1-ba2b-d1431356fc86
-- title:
--   Sylow subgroups: $p$-elements of the normalizer
-- statement:
--   A small generic lemma file extracted from the class-sum congruence development. It proves that a $p$-element normalizing a Sylow $p$-subgroup lies in it: if $P$ is Sylow and $u\in N_G(P)$ generates a $p$-group, then $u\in P$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Mathlib/Sylow.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Mathlib/Sylow.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.Sylow

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **A `p`-element normalizing a Sylow `p`-subgroup lies in it.** If `P` is a Sylow `p`-subgroup
of `G` and `u ∈ N_G(P)` generates a `p`-group `⟨u⟩` (i.e. `u` is a `p`-element), then `u ∈ P`.

This is the "`y` is a `p`-element of `L`, and so `y ∈ P`" step of Peterfalvi (6.7.1): in
`L = N_G(P)` the Sylow `p`-subgroup `P` is normal, hence the unique one, so every `p`-element of `L`
lies in `P`.  Proof: `P ⊔ ⟨u⟩` is a `p`-group (both factors are `p`-groups and `⟨u⟩ ≤ N_G(P)`,
`IsPGroup.to_sup_of_normal_left'`); since `P` is a *maximal* `p`-subgroup (`Sylow.is_maximal'`) and
`P ≤ P ⊔ ⟨u⟩`, this forces `P ⊔ ⟨u⟩ = P`, whence `u ∈ P`. -/
theorem mem_sylow_of_mem_normalizer_of_isPGroup {p : ℕ} [Fact p.Prime] (P : Sylow p G) {u : G}
    (hu : u ∈ Subgroup.normalizer (P : Subgroup G)) (hup : IsPGroup p (Subgroup.zpowers u)) :
    u ∈ (P : Subgroup G) := by
  -- `⟨u⟩ ≤ N_G(P)`, so `P ⊔ ⟨u⟩` is a `p`-group.
  have hzle : Subgroup.zpowers u ≤ Subgroup.normalizer (P : Subgroup G) :=
    Subgroup.zpowers_le.mpr hu
  have hsup : IsPGroup p ((P : Subgroup G) ⊔ Subgroup.zpowers u : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' P.2 hup hzle
  -- `P` is maximal among `p`-subgroups, and `P ≤ P ⊔ ⟨u⟩`, so the join collapses to `P`.
  have heq : ((P : Subgroup G) ⊔ Subgroup.zpowers u : Subgroup G) = (P : Subgroup G) :=
    P.3 hsup le_sup_left
  -- `u ∈ ⟨u⟩ ≤ P ⊔ ⟨u⟩ = P`.
  have humem : u ∈ ((P : Subgroup G) ⊔ Subgroup.zpowers u : Subgroup G) :=
    (le_sup_right : Subgroup.zpowers u ≤ _) (Subgroup.mem_zpowers u)
  rwa [heq] at humem

end OddOrder.RepresentationTheory


