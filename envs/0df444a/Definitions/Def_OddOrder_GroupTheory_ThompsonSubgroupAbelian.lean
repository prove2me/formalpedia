-- Prove2me | Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroupAbelian
-- name    : OddOrder_GroupTheory_ThompsonSubgroupAbelian
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:28:58.356205+00:00
-- url     : https://prove2.me/theorems/282e51de-9a1f-43b8-b39b-0ee4784254ff
-- title:
--   The abelian Thompson subgroup $J_a(P)$ (Gorenstein version)
-- statement:
--   Defines the Gorenstein version of the Thompson subgroup, $J_a(P)=\langle\mathcal{A}(P)\rangle$, where $\mathcal{A}(P)$ is the set of abelian subgroups of $P$ of maximal order, with basic lemmas from Gorenstein, *Finite Groups* (1968), Ch. 8 §2 (pp. 270–271; Lemmas 2.1 and 2.3). This is the version of $J$ meant in Bender–Glauberman Thm 6.2, whose proof is delegated to Gorenstein 8.2.11 (Glauberman's $Z(J)$-theorem). It differs from the elementary abelian version `thompsonJ`.
--
--   Main definitions: `maxAbelianIn` ($\mathcal{A}(P)$), `thompsonJAbelian` ($J_a(P)$), and characteristic-subgroup results (`thompsonJAbelian_top_characteristic`, and Gorenstein Lemma 2.2(d) that $J_a(P)$ is characteristic in $P$).
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ThompsonSubgroupAbelian.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ThompsonSubgroupAbelian.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Basic
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh02
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Mann
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Commutator.Basic

namespace Subgroup

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

/-- **Maximum-order abelian subgroups of `P`** (Gorenstein Ch.8 §2 の `A(P)`, p. 270).

`A(P) = {A ≤ P | A は abelian で, 任意の abelian subgroup B ≤ P について |B| ≤ |A|}`.

⚠ elementary 版 `maxElemAbelianIn` (Isaacs の `E(P)`) とは別物 — こちらは
elementary 性を課さない (Gorenstein 原文どおり素数にも言及しない). -/
def maxAbelianIn (P : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ P ∧ IsMulCommutative A ∧
       ∀ B : Subgroup G, B ≤ P → IsMulCommutative B → Nat.card B ≤ Nat.card A}

/-- **Abelian Thompson subgroup** `J_a(P) = ⟨A | A ∈ A(P)⟩` (Gorenstein Ch.8 §2, p. 271).

BG Thm 6.2 の literal `J(S)` はこの版 (BG 記号表 p.170 → **G** 8.2.11). -/
def thompsonJAbelian (P : Subgroup G) : Subgroup G :=
  ⨆ A ∈ maxAbelianIn P, A

/-- `A ∈ A(P)` の生成元は `J_a(P)` に含まれる. -/
theorem le_thompsonJAbelian_of_mem_maxAbelianIn {P A : Subgroup G}
    (hA : A ∈ maxAbelianIn P) : A ≤ thompsonJAbelian P :=
  le_iSup_of_le A (le_iSup_of_le hA le_rfl)

/-- **`A(·)` の comap 転送**: 単射 `f : G →* N` について `E ∈ A(P.map f)` なら
`E.comap f ∈ A(P)` かつ `(E.comap f).map f = E`. -/
theorem comap_mem_maxAbelianIn_of_injective {N : Type*} [Group N]
    {f : G →* N} (hf : Function.Injective f) {P : Subgroup G} {E : Subgroup N}
    (hE : E ∈ maxAbelianIn (P.map f)) :
    E.comap f ∈ maxAbelianIn P ∧ (E.comap f).map f = E := by
  obtain ⟨hE_le, hE_comm, hE_max⟩ := hE
  have hE_le_range : E ≤ f.range := hE_le.trans (Subgroup.map_le_range f P)
  have hmap_comap : (E.comap f).map f = E :=
    Subgroup.map_comap_eq_self hE_le_range
  refine ⟨⟨?_, ?_, ?_⟩, hmap_comap⟩
  · rw [← Subgroup.comap_map_eq_self_of_injective hf P]
    exact Subgroup.comap_mono hE_le
  · have := hE_comm
    exact E.comap_injective_isMulCommutative hf
  · intro B hB_P hB_comm
    have := hB_comm
    have hBmap_le : B.map f ≤ P.map f := Subgroup.map_mono hB_P
    have hcard_B : Nat.card (B.map f) = Nat.card B :=
      Subgroup.card_map_of_injective hf
    have hcard_E : Nat.card E = Nat.card (E.comap f) := by
      conv_lhs => rw [← hmap_comap]
      exact Subgroup.card_map_of_injective hf
    have hstep : Nat.card (B.map f) ≤ Nat.card E :=
      hE_max (B.map f) hBmap_le (map_isMulCommutative B f)
    rw [← hcard_E, ← hcard_B]
    exact hstep

/-- **`A(·)` の map 転送**: 単射 `f : G →* N` について `A ∈ A(P)` なら
`A.map f ∈ A(P.map f)`. -/
theorem map_mem_maxAbelianIn_of_injective {N : Type*} [Group N]
    {f : G →* N} (hf : Function.Injective f) {P A : Subgroup G}
    (hA : A ∈ maxAbelianIn P) :
    A.map f ∈ maxAbelianIn (P.map f) := by
  obtain ⟨hA_le, hA_comm, hA_max⟩ := hA
  have := hA_comm
  refine ⟨Subgroup.map_mono hA_le, map_isMulCommutative A f, ?_⟩
  intro B hB_le hB_comm
  have hB_le_range : B ≤ f.range := hB_le.trans (Subgroup.map_le_range f P)
  have hB_mapcomap : (B.comap f).map f = B := Subgroup.map_comap_eq_self hB_le_range
  have hBcomap_le : B.comap f ≤ P := by
    rw [← Subgroup.comap_map_eq_self_of_injective hf P]
    exact Subgroup.comap_mono hB_le
  have hBcomap_comm : IsMulCommutative (B.comap f) := by
    have := hB_comm
    exact B.comap_injective_isMulCommutative hf
  have hcard_B : Nat.card B = Nat.card (B.comap f) := by
    conv_lhs => rw [← hB_mapcomap]
    exact Subgroup.card_map_of_injective hf
  have hcard_A : Nat.card (A.map f) = Nat.card A := Subgroup.card_map_of_injective hf
  calc Nat.card B = Nat.card (B.comap f) := hcard_B
    _ ≤ Nat.card A := hA_max (B.comap f) hBcomap_le hBcomap_comm
    _ = Nat.card (A.map f) := hcard_A.symm

/-- **`J_a` は単射準同型と可換**: `f : G →* N` 単射, `P ≤ G` について
`J_a(f(P)) = f(J_a(P))` (Gorenstein Lemma 2.2(c) の一般形). -/
theorem thompsonJAbelian_map_of_injective {N : Type*} [Group N]
    {f : G →* N} (hf : Function.Injective f) (P : Subgroup G) :
    thompsonJAbelian (P.map f) = (thompsonJAbelian P).map f := by
  have key_comap : ∀ E : Subgroup N, E ∈ maxAbelianIn (P.map f) →
      E.comap f ∈ maxAbelianIn P ∧ (E.comap f).map f = E := fun E hE =>
    comap_mem_maxAbelianIn_of_injective hf hE
  have key_map : ∀ A : Subgroup G, A ∈ maxAbelianIn P →
      A.map f ∈ maxAbelianIn (P.map f) := fun A hA =>
    map_mem_maxAbelianIn_of_injective hf hA
  apply le_antisymm
  · refine iSup_le fun E => iSup_le fun hE => ?_
    obtain ⟨hEcomap_mem, hmapcomap⟩ := key_comap E hE
    rw [← hmapcomap]
    exact Subgroup.map_mono (le_thompsonJAbelian_of_mem_maxAbelianIn hEcomap_mem)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun A => iSup_le fun hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_thompsonJAbelian_of_mem_maxAbelianIn (key_map A hA)

/-- `↥P` 内で計算した `J_a` を `P.subtype` で押し出すと ambient の `J_a(P)` に一致. -/
theorem thompsonJAbelian_top_map_subtype (P : Subgroup G) :
    (thompsonJAbelian (⊤ : Subgroup ↥P)).map P.subtype = thompsonJAbelian P := by
  rw [← thompsonJAbelian_map_of_injective P.subtype_injective (⊤ : Subgroup ↥P),
    ← MonoidHom.range_eq_map, P.range_subtype]

/-- `J_a(P)` を `↥P` 内で見ると, 全体群 `↥P` の `J_a`. -/
theorem thompsonJAbelian_subgroupOf_self (P : Subgroup G) :
    (thompsonJAbelian P).subgroupOf P = thompsonJAbelian (⊤ : Subgroup ↥P) := by
  rw [← thompsonJAbelian_top_map_subtype P, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]

/-- **`J_a(H)` は characteristic** (top 形): 自己同型は `A(H)` を置換するので
join `J_a(H)` を固定する. -/
instance thompsonJAbelian_top_characteristic :
    (thompsonJAbelian (⊤ : Subgroup G)).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ => ?_
  rw [← thompsonJAbelian_map_of_injective ϕ.injective (⊤ : Subgroup G)]
  congr 1
  simp

/-- **Gorenstein Lemma 2.2(d)**: `J_a(P)` は `P` 内 characteristic
(`Subgroup ↥P` の `Subgroup.Characteristic` 形). -/
instance thompsonJAbelian_subgroupOf_characteristic (P : Subgroup G) :
    ((thompsonJAbelian P).subgroupOf P).Characteristic := by
  rw [thompsonJAbelian_subgroupOf_self]
  infer_instance

end Subgroup


