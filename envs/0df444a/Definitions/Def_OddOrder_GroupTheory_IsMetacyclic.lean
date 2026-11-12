-- Prove2me | Definitions.Def_OddOrder_GroupTheory_IsMetacyclic
-- name    : OddOrder_GroupTheory_IsMetacyclic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:29.918273+00:00
-- url     : https://prove2.me/theorems/dea9d498-06ee-44bb-9b25-b3c11cc7cf11
-- title:
--   Metacyclic groups
-- statement:
--   The shared notion of metacyclic group, absent from Mathlib: $G$ is metacyclic if there is a cyclic normal subgroup $N$ with $G/N$ cyclic. It is needed for BG §4 Lemma 4.10, Proposition 4.11 (Huppert's classification) and Theorem 4.12.
--
--   The main definition is `IsMetacyclic`.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/IsMetacyclic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/IsMetacyclic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.SemidirectProduct

namespace OddOrder.GroupTheory

variable (G : Type*) [Group G]

/-- **Metacyclic group**: there exists a cyclic normal subgroup `N ≤ G` with `G ⧸ N` cyclic.

教科書 (Huppert, BG §4) の標準定義. `N = ⊥` の取り方で巡回群を包含し,
`N = ⊤` の取り方で trivial-quotient 系も包含する. -/
def IsMetacyclic : Prop :=
  ∃ N : Subgroup G, ∃ _ : N.Normal, IsCyclic N ∧ IsCyclic (G ⧸ N)

variable {G}

namespace IsMetacyclic

/-- Every cyclic group is metacyclic: take `N = ⊥`. -/
theorem of_isCyclic [IsCyclic G] : IsMetacyclic G := by
  refine ⟨⊥, Subgroup.normal_bot, ?_, ?_⟩
  · -- `↥(⊥ : Subgroup G)` is `Unique` (only the identity 1), hence trivially cyclic
    exact ⟨⟨1, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩⟩
  · -- `IsCyclic (G ⧸ ⊥)` follows from `IsCyclic G` via the surjective quotient map
    exact isCyclic_of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)

/-- A metacyclic group has cyclic commutator subgroup.

Since `G ⧸ N` is cyclic (hence abelian), `commutator G ≤ N` by
`Subgroup.Normal.quotient_commutative_iff_commutator_le`; and a subgroup of the cyclic
group `N` is cyclic (`Subgroup.isCyclic`), so `commutator G` is cyclic via the
group isomorphism `(commutator G).subgroupOf N ≃* commutator G`.

**BG §4** Thm 4.12(a) の補題段 (mmd L1592: "R metacyclic ⇒ R′ cyclic"). -/
theorem isCyclic_commutator (hmeta : IsMetacyclic G) : IsCyclic (commutator G) := by
  obtain ⟨N, hN, hN_cyc, hQ_cyc⟩ := hmeta
  have := hN
  have : IsCyclic (G ⧸ N) := hQ_cyc
  have hle : commutator G ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have : IsCyclic N := hN_cyc
  have : IsCyclic ↥((commutator G).subgroupOf N) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).surjective

end IsMetacyclic

end OddOrder.GroupTheory


