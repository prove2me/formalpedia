-- Prove2me | Definitions.Def_OddOrder_GroupTheory_SCN
-- name    : OddOrder_GroupTheory_SCN
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:38.405233+00:00
-- url     : https://prove2.me/theorems/6ef2afdd-9042-4251-a566-1d93ae00a645
-- title:
--   Self-centralizing normal abelian subgroups (SCN)
-- statement:
--   The shared notion of SCN subgroup (self-centralizing normal abelian subgroup), absent from Mathlib. It is needed for BG §4 Prop 4.4 (existence of SCN in $p$-groups), Lemma 4.7 (rank $\ge3$ iff $\mathrm{SCN}_3$ is nonempty), BG §5 Lemma 5.1 and Isaacs Ch. 7 on $J(P)$.
--
--   Main definitions: `IsSCN` (an SCN subgroup), `IsMaximalAbelianNormal` (a maximal abelian normal subgroup, BG Prop 4.4(a)), `IsSCN_n` (membership in $\mathrm{SCN}_n(R)$, BG §4) and `IsSCN₃` (the case $n=3$).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/SCN.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/SCN.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_GroupTheory_CriticalSubgroup
import Definitions.Def_OddOrder_GroupTheory_PRank
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Basic

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **SCN subgroup** (Self-Centralizing Normal abelian subgroup):
`A ≤ G` is SCN iff `A` is normal in `G`, abelian, and equals its own centralizer
`C_G(A) = A`.

教科書 (Isaacs FGT Ch.7, BG §4) 標準定義. `A = C_G(A)` 条件は **A self-centralizing**
を意味し, abelian + normal と組み合わせて p-群構造解析の鍵となる. -/
structure IsSCN (A : Subgroup G) : Prop where
  /-- `A` is normal in `G`. -/
  isNormal : A.Normal
  /-- `A` is abelian. -/
  isMulCommutative : IsMulCommutative A
  /-- `A` is self-centralizing: `C_G(A) = A`. -/
  selfCentralizing : Subgroup.centralizer (A : Set G) = A

namespace IsSCN

variable {A : Subgroup G}

/-- An SCN subgroup is contained in the center of its centralizer (trivially since
`C_G(A) = A` and `A` is abelian, hence in the center of itself). -/
theorem centralizer_le (h : IsSCN A) : Subgroup.centralizer (A : Set G) ≤ A :=
  h.selfCentralizing.le

/-- Transport an `SCN` subgroup across a group isomorphism. -/
theorem map_equiv {G' : Type*} [Group G'] (e : G ≃* G') (h : IsSCN A) :
    IsSCN (A.map e.toMonoidHom) := by
  refine ⟨h.isNormal.map e.toMonoidHom e.surjective, ?_, ?_⟩
  · exact IsMulCommutative.of_setLike_mul_comm fun x hx y hy => by
      let : IsMulCommutative A := h.isMulCommutative
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      have hab : a * b = b * a :=
        congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
      simpa [map_mul] using congrArg e hab
  · rw [Subgroup.coe_map]
    rw [← Subgroup.map_centralizer_eq_of_bijective (A : Set G) e.toMonoidHom e.bijective,
      h.selfCentralizing]

end IsSCN

section MaximalAbelianNormal

/-- **Maximal abelian normal subgroup** (BG Prop 4.4(a) の右辺): `A ≤ G` is normal,
abelian, and maximal with respect to being abelian among the normal subgroups of `G`
(any abelian normal `N ⊇ A` equals `A`).

In a `p`-group this is exactly the set `SCN(R)` (BG Proposition 4.4(a)). -/
structure IsMaximalAbelianNormal (A : Subgroup G) : Prop where
  /-- `A` is normal in `G`. -/
  isNormal : A.Normal
  /-- `A` is abelian. -/
  isMulCommutative : IsMulCommutative A
  /-- `A` is maximal among abelian normal subgroups: any abelian normal `N ⊇ A` is `A`. -/
  maximal : ∀ N : Subgroup G, N.Normal → IsMulCommutative N → A ≤ N → N = A

/-- **BG Proposition 4.4(a)**, backward direction (`p`-group). In a `p`-group, a normal
subgroup maximal with respect to being abelian is self-centralizing, hence SCN.

Proof: normality and commutativity are immediate; self-centralization
`C_G(A) = A` is Gorenstein 5.3.12
(`centralizer_eq_self_of_maximal_abelian_normal`), whose maximality hypothesis is
supplied by `h.maximal`. -/
theorem IsMaximalAbelianNormal.isSCN {p : ℕ} [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {A : Subgroup G} (h : IsMaximalAbelianNormal A) :
    IsSCN A := by
  have := h.isNormal
  have := h.isMulCommutative
  -- Element-level commutativity of `A`, needed by Gorenstein 5.3.12.
  have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  -- Element-level maximality of `A` among abelian normal subgroups.
  have hA_max : ∀ N : Subgroup G, N.Normal →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → A ≤ N → N = A := by
    intro N hN_normal hN_comm hAN
    exact h.maximal N hN_normal (IsMulCommutative.of_comm fun x y =>
      Subtype.ext (hN_comm x x.2 y y.2)) hAN
  exact
    { isNormal := h.isNormal
      isMulCommutative := h.isMulCommutative
      selfCentralizing :=
        centralizer_eq_self_of_maximal_abelian_normal hG hA_comm hA_max }

/-- **Every abelian normal subgroup lies below a maximal abelian normal one** (`[Finite G]`).
Standard finiteness argument: among the (finitely many) abelian normal subgroups containing
`B`, pick a `≤`-maximal one. Underlies "`SCN(R)` covers every normal abelian subgroup",
used in BG §4 (e.g. translating `SCN₃(R) = ∅` into a bound on `d_n(R)`). -/
theorem exists_maximalAbelianNormal_ge [Finite G] {B : Subgroup G}
    (hBnorm : B.Normal) (hBcomm : IsMulCommutative B) :
    ∃ A : Subgroup G, B ≤ A ∧ IsMaximalAbelianNormal A := by
  obtain ⟨A, hBA, hAmax⟩ :=
    exists_maximal_ge_of_wellFoundedGT
      (fun N : Subgroup G => N.Normal ∧ IsMulCommutative N) B ⟨hBnorm, hBcomm⟩
  refine ⟨A, hBA, { isNormal := hAmax.1.1, isMulCommutative := hAmax.1.2, maximal := ?_ }⟩
  intro N hN_norm hN_comm hAN
  exact le_antisymm (hAmax.2 ⟨hN_norm, hN_comm⟩ hAN) hAN

/-- **A maximal abelian normal subgroup of maximal `p`-rank exists** (`[Finite G]`).
Companion to Gorenstein Lemma 4.14: produces an `A` that is maximal-abelian-normal *and*
realises `d_n(G) = ⨆ { m(B) : B normal abelian }` (`∀ B normal abelian, pRank B ≤ pRank A`),
i.e. exactly the subgroup to which Lemma 4.14 applies. -/
theorem exists_maxRank_maximalAbelianNormal [Finite G] (p : ℕ) :
    ∃ A : Subgroup G, IsMaximalAbelianNormal A ∧
      ∀ B : Subgroup G, B.Normal → IsMulCommutative B → pRank B p ≤ pRank A p := by
  classical
  have hbot : IsMulCommutative (⊥ : Subgroup G) :=
    IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _)
  obtain ⟨A₀, -, hA₀⟩ :=
    exists_maximalAbelianNormal_ge (B := (⊥ : Subgroup G)) inferInstance hbot
  have : Nonempty {A : Subgroup G // IsMaximalAbelianNormal A} := ⟨⟨A₀, hA₀⟩⟩
  obtain ⟨A, hA⟩ := Finite.exists_max
    (fun A : {A : Subgroup G // IsMaximalAbelianNormal A} => pRank (A : Subgroup G) p)
  refine ⟨A.1, A.2, fun B hBnorm hBcomm => ?_⟩
  obtain ⟨A_B, hBA_B, hA_Bmax⟩ := exists_maximalAbelianNormal_ge hBnorm hBcomm
  calc pRank B p
      ≤ pRank A_B p := pRank_le_of_injective (Subgroup.inclusion_injective hBA_B)
    _ ≤ pRank (A : Subgroup G) p := hA ⟨A_B, hA_Bmax⟩

end MaximalAbelianNormal

section SCN_n

/-- **`SCN_n(R)` membership** (BG §4, p.33): `A ∈ SCN_n(R)` iff `A` is SCN and its
generator number `m(A)` is at least `n`.

For an abelian `p`-group `A` the BG invariant `m(A)` (minimum number of generators)
equals the `F_p`-dimension of `Ω₁(A)`, i.e. `pRank A p`; an SCN subgroup is abelian, so
we express `m(A) ≥ n` as `n ≤ pRank A p`. -/
def IsSCN_n (p n : ℕ) (A : Subgroup G) : Prop :=
  IsSCN A ∧ n ≤ pRank A p

/-- **`SCN₃(R)` membership** (BG §4, the case `n = 3`, used in BG Lem 4.7 / §5 / §7):
`A ∈ SCN₃(R)` iff `A` is SCN of rank `≥ 3`. -/
abbrev IsSCN₃ (p : ℕ) (A : Subgroup G) : Prop := IsSCN_n p 3 A

theorem IsSCN_n.isSCN {p n : ℕ} {A : Subgroup G} (h : IsSCN_n p n A) : IsSCN A := h.1

theorem IsSCN_n.le_pRank {p n : ℕ} {A : Subgroup G} (h : IsSCN_n p n A) :
    n ≤ pRank A p := h.2

/-- Membership in `SCN_n` is antitone in `n`: an `SCN_n` subgroup is also `SCN_m` for
`m ≤ n`. In particular `SCN₃(R) ⊆ SCN_2(R) ⊆ SCN_1(R)`. -/
theorem IsSCN_n.mono {p m n : ℕ} {A : Subgroup G} (hmn : m ≤ n) (h : IsSCN_n p n A) :
    IsSCN_n p m A :=
  ⟨h.1, hmn.trans h.2⟩

/-- Transport `SCN_n` membership across a group isomorphism. -/
theorem IsSCN_n.map_equiv [Finite G] {G' : Type*} [Group G'] [Finite G']
    {p n : ℕ} {A : Subgroup G} (e : G ≃* G') (h : IsSCN_n p n A) :
    IsSCN_n p n (A.map e.toMonoidHom) := by
  refine ⟨h.isSCN.map_equiv e, ?_⟩
  exact h.le_pRank.trans
    (pRank_le_of_injective
      (f := (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).toMonoidHom)
      (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).injective)

/-- A normal abelian subgroup of `p`-rank at least `3` is contained in an `SCN₃`
subgroup of a finite `p`-group.

This is the reusable Prop 4.4(a) step in BG Lemma 5.1(b): enlarge the normal abelian
subgroup to a maximal abelian normal subgroup, identify it as SCN in a `p`-group, and
transport the rank lower bound along inclusion. -/
theorem exists_scn3_ge_of_normal_abelian_pRank_ge_three
    [Finite G] {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    {B : Subgroup G} (hBnorm : B.Normal) (hBcomm : IsMulCommutative B)
    (hBrank : 3 ≤ pRank B p) :
    ∃ A : Subgroup G, IsSCN₃ p A ∧ B ≤ A := by
  obtain ⟨A, hBA, hAmax⟩ := exists_maximalAbelianNormal_ge hBnorm hBcomm
  have hAscn : IsSCN A := hAmax.isSCN hG
  have hrank_le : pRank B p ≤ pRank A p :=
    pRank_le_of_injective (Subgroup.inclusion_injective hBA)
  exact ⟨A, ⟨hAscn, hBrank.trans hrank_le⟩, hBA⟩

end SCN_n

end OddOrder.GroupTheory


