-- Prove2me | Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
-- name    : OddOrder_GroupTheory_ThompsonSubgroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:46:09.27326+00:00
-- url     : https://prove2.me/theorems/418fe48f-c73b-4da3-b005-0c239641e561
-- title:
--   The Thompson subgroup $J(P)$ (Isaacs Ch. 7)
-- statement:
--   Defines the Thompson subgroup $J(P)$, the core definition of Isaacs, *Finite Group Theory*, Chapter 7 (pp. 201–202), absent from Mathlib. It is used repeatedly in Ch. 7, BG App. A and B, and BG §6, §8, §9 (Uniqueness Theorem).
--
--   Main definitions: `Subgroup.maxElemAbelianIn P p` (the set $\mathcal{E}(P)$ of elementary abelian $p$-subgroups of $P$ of maximal order), `Subgroup.thompsonJ P p` ($J(P)=\langle\mathcal{E}(P)\rangle$), and results that $J(H)$ is characteristic (top form and in $P$).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ThompsonSubgroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas

namespace Subgroup

variable {G : Type*} [Group G]

/-- `[Finite G]` のとき, `Subgroup G` 自体も有限. `Subgroup G ↪ Set G` 経由. -/
instance instFiniteSubgroupOfFinite [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

/-- **Maximum-order elementary abelian subgroups of `P`** (Isaacs Ch.7 L3727 の `E(P)`).

`E(P) = {E ≤ P | E は p-elementary abelian で, 任意の elem-ab subgroup F ≤ P について
|F| ≤ |E|}`. -/
def maxElemAbelianIn (P : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {E | E ≤ P ∧ E.IsElementaryAbelian p ∧
       ∀ F : Subgroup G, F ≤ P → F.IsElementaryAbelian p → Nat.card F ≤ Nat.card E}

/-- **Thompson subgroup** `J(P) = ⟨E(P)⟩` (Isaacs Ch.7 def, p.201).

`P` 内の最大位数 elementary abelian 部分群すべての (Subgroup G 内での) 上限. -/
def thompsonJ (P : Subgroup G) (p : ℕ) : Subgroup G :=
  ⨆ E ∈ maxElemAbelianIn P p, E

/-- `E ∈ maxElemAbelianIn P p` の生成元は `J(P)` に含まれる. -/
theorem le_thompsonJ_of_mem_maxElemAbelianIn {P E : Subgroup G} {p : ℕ}
    (hE : E ∈ maxElemAbelianIn P p) : E ≤ thompsonJ P p :=
  le_iSup_of_le E (le_iSup_of_le hE le_rfl)

/-- **`J` commutes with injective images**: for an injective homomorphism
`f : G →* N` and a subgroup `P ≤ G`, `J(f(P)) = f(J(P))`.

The maximum-order elementary abelian subgroups of `f(P)` are exactly the
`f`-images of those of `P` (injectivity preserves both the elementary-abelian
property and cardinality, and every subgroup of `f(P)` is `f(its preimage)`).

Used in §7D Step 8 (Isaacs Thm 7.8) to relate `J` of a Sylow of `M` computed
inside `↥M` versus inside the ambient group. -/
theorem thompsonJ_map_of_injective [Finite G] {N : Type*} [Group N]
    {f : G →* N} (hf : Function.Injective f) (P : Subgroup G) (p : ℕ) :
    thompsonJ (P.map f) p = (thompsonJ P p).map f := by
  -- A subgroup `E ≤ P.map f` is the image of `E.comap f ≤ P`, with equal card and
  -- elementary-abelian status preserved.
  have key_comap : ∀ E : Subgroup N, E ∈ maxElemAbelianIn (P.map f) p →
      E.comap f ∈ maxElemAbelianIn P p ∧ (E.comap f).map f = E := by
    intro E hE
    obtain ⟨hE_le, hE_el, hE_max⟩ := hE
    -- `E ≤ P.map f ≤ range f`, so `(E.comap f).map f = E`.
    have hE_le_range : E ≤ f.range := hE_le.trans (Subgroup.map_le_range f P)
    have hmap_comap : (E.comap f).map f = E :=
      Subgroup.map_comap_eq_self hE_le_range
    refine ⟨⟨?_, ?_, ?_⟩, hmap_comap⟩
    · -- `E.comap f ≤ P`.
      rw [← Subgroup.comap_map_eq_self_of_injective hf P]
      exact Subgroup.comap_mono hE_le
    · -- `E.comap f` elementary abelian: its image `E` is, and `f` injective.
      have hmap_el : ((E.comap f).map f).IsElementaryAbelian p := by
        rw [hmap_comap]; exact hE_el
      exact hmap_el.of_map hf
    · -- Max-order: any elem-ab `F ≤ P` has `|F| = |F.map f| ≤ |E| = |E.comap f|`.
      intro F hF_P hF_el
      have hFmap_le : F.map f ≤ P.map f := Subgroup.map_mono hF_P
      have hFmap_el : (F.map f).IsElementaryAbelian p :=
        Subgroup.IsElementaryAbelian.map hf hF_el
      have hcard_F : Nat.card (F.map f) = Nat.card F := Subgroup.card_map_of_injective hf
      have hcard_E : Nat.card E = Nat.card (E.comap f) := by
        conv_lhs => rw [← hmap_comap]
        exact Subgroup.card_map_of_injective hf
      have hstep : Nat.card (F.map f) ≤ Nat.card E := hE_max (F.map f) hFmap_le hFmap_el
      rw [← hcard_E, ← hcard_F]; exact hstep
  -- The image of a max elem-ab subgroup of `P` is a max elem-ab subgroup of `P.map f`.
  have key_map : ∀ E : Subgroup G, E ∈ maxElemAbelianIn P p →
      E.map f ∈ maxElemAbelianIn (P.map f) p := by
    intro E hE
    obtain ⟨hE_le, hE_el, hE_max⟩ := hE
    refine ⟨Subgroup.map_mono hE_le, Subgroup.IsElementaryAbelian.map hf hE_el, ?_⟩
    -- Max-order in `P.map f`: any elem-ab `F ≤ P.map f` is `(F.comap f).map f`,
    -- and `F.comap f ≤ P` elem-ab, so `|F| = |F.comap f| ≤ |E| = |E.map f|`.
    intro F hF_le hF_el
    have hF_le_range : F ≤ f.range := hF_le.trans (Subgroup.map_le_range f P)
    have hF_mapcomap : (F.comap f).map f = F := Subgroup.map_comap_eq_self hF_le_range
    have hFcomap_le : F.comap f ≤ P := by
      rw [← Subgroup.comap_map_eq_self_of_injective hf P]; exact Subgroup.comap_mono hF_le
    have hFcomap_el : (F.comap f).IsElementaryAbelian p := by
      have hmap_el : ((F.comap f).map f).IsElementaryAbelian p := by
        rw [hF_mapcomap]; exact hF_el
      exact hmap_el.of_map hf
    have hcard_F : Nat.card F = Nat.card (F.comap f) := by
      conv_lhs => rw [← hF_mapcomap]
      exact Subgroup.card_map_of_injective hf
    have hcard_E : Nat.card (E.map f) = Nat.card E := Subgroup.card_map_of_injective hf
    calc Nat.card F = Nat.card (F.comap f) := hcard_F
      _ ≤ Nat.card E := hE_max (F.comap f) hFcomap_le hFcomap_el
      _ = Nat.card (E.map f) := hcard_E.symm
  -- Combine the two correspondences.
  apply le_antisymm
  · -- `J(P.map f) ≤ (J P).map f`.
    refine iSup_le fun E => iSup_le fun hE => ?_
    obtain ⟨hEcomap_mem, hmapcomap⟩ := key_comap E hE
    rw [← hmapcomap]
    exact Subgroup.map_mono (le_thompsonJ_of_mem_maxElemAbelianIn hEcomap_mem)
  · -- `(J P).map f ≤ J(P.map f)`: flip to `J P ≤ comap` and use `iSup_le`.
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun E => iSup_le fun hE => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_thompsonJ_of_mem_maxElemAbelianIn (key_map E hE)

/-- Computing `J` inside `↥P` and pushing forward along `P.subtype` agrees with computing
`J(P)` in the ambient group. -/
theorem thompsonJ_top_map_subtype [Finite G] (P : Subgroup G) (p : ℕ) :
    (thompsonJ (⊤ : Subgroup ↥P) p).map P.subtype = thompsonJ P p := by
  rw [← thompsonJ_map_of_injective P.subtype_injective (⊤ : Subgroup ↥P) p,
    ← MonoidHom.range_eq_map, P.range_subtype]

/-- `J(P)`, viewed inside `↥P`, is `J` of the whole group `↥P`. -/
theorem thompsonJ_subgroupOf_self [Finite G] (P : Subgroup G) (p : ℕ) :
    (thompsonJ P p).subgroupOf P = thompsonJ (⊤ : Subgroup ↥P) p := by
  rw [← thompsonJ_top_map_subtype P p, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]

/-- **`J(H)` is characteristic** (top form): every automorphism of `H` permutes the
maximum-order elementary abelian subgroups of `H`, hence fixes their join. -/
instance thompsonJ_top_characteristic [Finite G] (p : ℕ) :
    (thompsonJ (⊤ : Subgroup G) p).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  rw [← thompsonJ_map_of_injective ϕ.injective (⊤ : Subgroup G) p]
  congr 1
  simp

/-- **`J(P)` is characteristic in `P`** (Isaacs Ch.7, p. 201): a special case of Thm 7.2,
stated in the `Subgroup ↥P` form used by the local hypotheses of Isaacs Thm 6.23. -/
instance thompsonJ_subgroupOf_characteristic [Finite G] (P : Subgroup G) (p : ℕ) :
    ((thompsonJ P p).subgroupOf P).Characteristic := by
  rw [thompsonJ_subgroupOf_self]
  infer_instance

end Subgroup


