-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_Theorem88CaseB
-- name    : OddOrder_Peterfalvi_S10_Theorem88CaseB
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:35.725764+00:00
-- url     : https://prove2.me/theorems/b089d4b0-8cbc-4b77-94e8-25c705956255
-- title:
--   Peterfalvi (8.8) case (b) and result (8.9)
-- statement:
--   Formalizes Theorem (8.8) case (b) (Peterfalvi, *Character Theory for the Odd Order Theorem*, Section 10, pp. 44-49) and the result (8.9) concerning a minimal simple group of odd order.
--
--   Main declarations: `Theorem88CaseBData` (Peterfalvi (8.8), case (b)).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_Theorem88CaseB.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_Theorem88CaseB.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness
import Definitions.Def_OddOrder_GroupTheory_TISubset

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (8.8), case (b)** (book p. 46): `G` contains a cyclic subgroup
`W = W₁ × W₂` with `W₁ ≠ 1` and `W₂ ≠ 1`, which satisfies (8.4.e), and two maximal
subgroups `S` and `T` such that

* (b1) `S = [S,S] ⋊ W₁`, `T = [T,T] ⋊ W₂` and `S ∩ T = W`;
* (b2) `S` or `T` is of Type II;
* (b3) `S` and `T` are of Type II, III, IV or V (that is, `IsTypeNonI`);
* (b4) every maximal subgroup of `G` is conjugate to `S` or to `T`, or is of Type I.

Every clause of the book statement is a field: the direct-product decomposition
(`W_eq`, `W1_inf_W2_eq_bot`), the nontriviality of both factors, the (8.4.e)
normalizer law, the two semidirect decompositions and the intersection `S ∩ T = W`,
the Type-II member, the type restriction and the covering. -/
structure Theorem88CaseBData (G : Type*) [Group G] where
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  /-- `W = W₁ × W₂`, first half: `W` is the join of the two factors. -/
  W_eq : W = W1 ⊔ W2
  /-- `W = W₁ × W₂`, second half: the two factors intersect trivially. -/
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W_cyclic : IsCyclic ↥W
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  /-- **(8.4.e)** for `W`: every nonempty subset `X` of `V = W − (W₁ ∪ W₂)` has
  `N_G(X) = W`. -/
  normalizer_V : ∀ X : Set G, X.Nonempty →
    X ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) → Subgroup.normalizer X = W
  /-- (b3) for `S`. -/
  S_nonI : IsTypeNonI S
  /-- (b3) for `T`. -/
  T_nonI : IsTypeNonI T
  /-- (b2). -/
  one_typeII : IsTypeII S ∨ IsTypeII T
  /-- (b1): `W₁ ≤ S` and `S = [S,S] ⋊ W₁` (so `W₁` complements `S' = [S,S]` in `S`). -/
  W1_le_S : W1 ≤ S
  W2_le_T : W2 ≤ T
  S_compl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (W1.subgroupOf S)
  T_compl : Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)
  /-- (b1), last clause: `S ∩ T = W`. -/
  S_inf_T_eq_W : S ⊓ T = W
  /-- (b4): every maximal subgroup of `G` is conjugate to `S` or to `T`, or is of Type I. -/
  cover : ∀ M : Subgroup G, M ∈ maximalSubgroups G →
    IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = T)

end OddOrder.Peterfalvi.S10


