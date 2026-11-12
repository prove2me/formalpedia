-- Prove2me | Definitions.Def_OddOrder_GroupTheory_ElementaryAbelianFamily
-- name    : OddOrder_GroupTheory_ElementaryAbelianFamily
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:46:19.035253+00:00
-- url     : https://prove2.me/theorems/e6223159-e4b8-4d06-9029-632ae4059858
-- title:
--   Elementary abelian subgroup families $\mathcal{E}_p^n(G)$
-- statement:
--   A shared module introducing the Bender–Glauberman family $\mathcal{E}_p^n(G)$ of elementary abelian $p$-subgroups of a given order $p^n$ (equivalently rank $n$), which BG uses throughout §4–§16. The maximal family $\mathcal{E}^*$ is handled by the existing predicate `IsMaximalElementaryAbelian`; only the order-indexed family is new here.
--
--   The main declaration: `elemAbelianOfRank`.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ElementaryAbelianFamily.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ElementaryAbelianFamily.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **BG `ℰ_p^n(G)`**: the elementary abelian `p`-subgroups of `G` of order `p^n`
(equivalently, of rank `n`). The single-element form `ℰ^1(A)` (order-`p` subgroups of `A`)
is `{X ∈ elemAbelianOfRank G p 1 | X ≤ A}`. -/
def elemAbelianOfRank (G : Type*) [Group G] (p n : ℕ) : Set (Subgroup G) :=
  {A | A.IsElementaryAbelian p ∧ Nat.card A = p ^ n}

@[simp]
theorem mem_elemAbelianOfRank {p n : ℕ} {A : Subgroup G} :
    A ∈ elemAbelianOfRank G p n ↔ A.IsElementaryAbelian p ∧ Nat.card A = p ^ n :=
  Iff.rfl

end OddOrder.GroupTheory


