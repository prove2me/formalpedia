-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh02
-- name    : OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh02
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:53:56.961249+00:00
-- url     : https://prove2.me/theorems/61b3b65a-20dc-415f-856c-3d3c1559b64c
-- title:
--   Isaacs Thm 2.20 (Lucchini) and Chapter 4 forward dependencies from Chapter 2
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, §2D, Thm 2.20 (Lucchini). Logically a Chapter 2 theorem, it sits in the Chapter 4 directory because the case $K=\bot$ depends on Chapter 4 §4A–§4B (additivity of the lower central series). It also holds auxiliary lemmas moved from the Chapter 4 main file: iterated commutator infrastructure, that $Z(F(G))$ absorbs a minimal normal subgroup, variants of minimal normal nilpotent implies elementary abelian, and the first step of the Lucchini argument for $K=\bot$.
--
--   The main definition is `iterCommutator` (the iterated right commutator $[\ldots[E,F],F],\ldots,F]$).
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable

open scoped commutatorElement Pointwise

namespace OddOrder.Isaacs.Ch04

variable {G : Type*} [Group G]

/-- **Iterated right commutator**: `iterCommutator E F n = ⁅...⁅E, F⁆, F⁆..., F⁆`. -/
def iterCommutator (E F : Subgroup G) : ℕ → Subgroup G
  | 0 => E
  | n + 1 => ⁅iterCommutator E F n, F⁆

@[simp]
theorem iterCommutator_zero (E F : Subgroup G) :
    iterCommutator E F 0 = E := rfl

@[simp]
theorem iterCommutator_succ (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F (n + 1) = ⁅iterCommutator E F n, F⁆ := rfl

/-- **iterCommutator は F の lcs 経由で押し込められる**: `E ≤ F` ⇒
`iterCommutator E F n ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype`.

特に `F` が冪零 (Group.IsNilpotent ↥F) なら, 十分大きな `n` で `lcs ↥F n = ⊥`,
よって `iterCommutator E F n = ⊥`. これが Lucchini K = ⊥ case の核心 (Z(F(G))
absorbs G-minimal). -/
theorem iterCommutator_le_lowerCentralSeries_map
    {E F : Subgroup G} (hE : E ≤ F) (n : ℕ) :
    iterCommutator E F n ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, Subgroup.lowerCentralSeries_zero]
    rw [← MonoidHom.range_eq_map, F.range_subtype]
    exact hE
  | succ n ih =>
    rw [iterCommutator_succ]
    have hRange : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [← MonoidHom.range_eq_map]; exact F.range_subtype
    have hMapLcs : ((⊤ : Subgroup ↥F).lowerCentralSeries (n + 1)).map F.subtype =
        ⁅(((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype), F⁆ := by
      change ⁅(⊤ : Subgroup ↥F).lowerCentralSeries n, (⊤ : Subgroup ↥F)⁆.map F.subtype = _
      rw [Subgroup.map_commutator, hRange]
    rw [hMapLcs]
    exact Subgroup.commutator_mono ih le_rfl

/-- **iterCommutator は ambient G の lcs に押し込められる**: 任意 `E, F ⊆ G` で
`iterCommutator E F n ≤ (⊤ : Subgroup G).lowerCentralSeries n`. `E ≤ F` 不要
(E, F は ⊤ ≤ G で挟まれる).

`E ≤ ⊤` と `F ≤ ⊤` 経由で `iterCommutator E F n ≤ iterCommutator ⊤ ⊤ n = lcs G n`. -/
theorem iterCommutator_le_lowerCentralSeries (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F n ≤ (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, Subgroup.lowerCentralSeries_zero]
    exact le_top
  | succ n ih =>
    rw [iterCommutator_succ, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mono ih le_top

/-- **ambient G 冪零 ⇒ iterCommutator は最終的に ⊥** (任意 E, F).
`E ≤ F` 制約のない一般版 (上の `iterCommutator_eq_bot_of_isNilpotent` は `E ≤ F` 必要). -/
theorem iterCommutator_eq_bot_of_isNilpotent_ambient
    [Group.IsNilpotent G] (E F : Subgroup G) :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹_›
  refine ⟨n, le_antisymm ?_ bot_le⟩
  exact (iterCommutator_le_lowerCentralSeries E F n).trans (le_of_eq hn)

/-- **冪零 ambient G + nontrivial normal E ⇒ ⁅E, F⁆ < E**: 厳密降下.

`⁅E, F⁆ = E` なら iterCommutator E F は定常 (induction で各 n で = E). しかし
`iterCommutator_eq_bot_of_isNilpotent_ambient` で ∃ n, iter = ⊥. ⇒ E = ⊥ 矛盾. -/
theorem commutator_lt_self_of_isNilpotent_ambient
    [Group.IsNilpotent G] {E F : Subgroup G} [E.Normal] (hE : E ≠ ⊥) :
    ⁅E, F⁆ < E := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_left E F) ?_
  intro heq
  have hconst : ∀ n, iterCommutator E F n = E := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterCommutator_succ, ih]
      exact heq
  obtain ⟨n, hn⟩ := iterCommutator_eq_bot_of_isNilpotent_ambient E F
  rw [hconst n] at hn
  exact hE hn

/-- **iterCommutator は normal を保つ**. `E, F ⊴ G` ⇒ `iter E F n ⊴ G`. -/
theorem iterCommutator_normal {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    (iterCommutator E F n).Normal := by
  induction n with
  | zero => exact ‹E.Normal›
  | succ n ih =>
    have := ih
    rw [iterCommutator_succ]
    infer_instance

/-- **iterCommutator は antitone (decreasing)**. `E, F ⊴ G` ⇒
`iter E F (n+1) ≤ iter E F n`.

(直観: `iter E F n ⊴ G ⊇ F` で `F` は `iter E F n` を normalize するので
`⁅iter, F⁆ ≤ iter`.) -/
theorem iterCommutator_succ_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F (n + 1) ≤ iterCommutator E F n := by
  have : (iterCommutator E F n).Normal := iterCommutator_normal n
  rw [iterCommutator_succ]
  exact Subgroup.commutator_le_left (iterCommutator E F n) F

/-- **F 冪零 ⇒ iterCommutator は最終的に ⊥**: `E ≤ F` + `F` (as group `↥F`) が冪零
⇒ ∃ n, `iter E F n = ⊥`. -/
theorem iterCommutator_eq_bot_of_isNilpotent
    {E F : Subgroup G} (hE : E ≤ F) [hF : Group.IsNilpotent ↥F] :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hF
  refine ⟨n, le_antisymm ?_ bot_le⟩
  calc iterCommutator E F n
      ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype :=
        iterCommutator_le_lowerCentralSeries_map hE n
    _ ≤ ⊥ := by rw [hn]; exact (Subgroup.map_bot F.subtype).le

/-- **iterCommutator は E 内に留まる**: `E, F ⊴ G ⇒ iter E F n ≤ E`. -/
theorem iterCommutator_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F n ≤ E := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (iterCommutator_succ_le_self n).trans ih

/-- **Z(F(G)) absorbs G-minimal normal in F(G)** ⭐ (Lucchini K=⊥ aux 解消の核補題):
`E ⊴ G` minimal normal, `E ≤ F`, `F ⊴ G` 冪零 ⇒ `E ≤ centralizer F`.

**証明** (Isaacs §4A lcs 経路):
1. `iterCommutator E F` の降下列を考える. 各項は G-normal (`iterCommutator_normal`),
   decreasing (`iterCommutator_succ_le_self`), `E` 内 (`iterCommutator_le_self`).
2. `F` 冪零 で `iter n = ⊥` for some `n` (`iterCommutator_eq_bot_of_isNilpotent`).
3. 最小 `k` で `iter k = ⊥` を取る. `k = 0` だと `E = ⊥` で `E` minimal 仮定と矛盾.
4. `k = j + 1` で, `iter j ≠ ⊥`, `iter j ⊴ G`, `iter j ≤ E`. **E の minimality**
   より `iter j = E`.
5. `⁅E, F⁆ = ⁅iter j, F⁆ = iter (j+1) = iter k = ⊥`. 故に `E ≤ centralizer F`.

**下流**: Ch.2 §2D Lucchini K=⊥ aux. -/
theorem le_centralizer_of_isMinimalNormal {E F : Subgroup G}
    (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E) (hEF : E ≤ F)
    [F.Normal] [Group.IsNilpotent ↥F] :
    E ≤ Subgroup.centralizer (F : Set G) := by
  classical
  have hE_norm : E.Normal := hMin.1
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  -- Find smallest k with iter E F k = ⊥.
  have hExists : ∃ k, iterCommutator E F k = ⊥ :=
    iterCommutator_eq_bot_of_isNilpotent hEF
  set k := Nat.find hExists with hk_def
  have hk_iter : iterCommutator E F k = ⊥ := Nat.find_spec hExists
  -- k = 0 ⇒ E = ⊥, 矛盾.
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · exfalso
    rw [hk0, iterCommutator_zero] at hk_iter
    exact hMin.2.1 hk_iter
  -- k = j + 1, j minimality に達しない.
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
  have hIter_j_ne : iterCommutator E F j ≠ ⊥ := fun h => by
    have hjk : j < k := hj ▸ Nat.lt_succ_self j
    exact absurd (Nat.find_min' hExists h) (not_le.mpr hjk)
  have : (iterCommutator E F j).Normal := iterCommutator_normal j
  have hIter_j_le : iterCommutator E F j ≤ E := iterCommutator_le_self j
  rcases hMin.2.2 _ inferInstance hIter_j_le with h_bot | h_eq_E
  · exact absurd h_bot hIter_j_ne
  · -- iter j = E, hence ⁅E, F⁆ = iter (j+1) = iter k = ⊥.
    rw [← h_eq_E, ← iterCommutator_succ,
        show j + 1 = k from hj.symm]
    exact hk_iter

/-- **Helper**: 部分群 `E` で `↥E` 可解 + 非自明 ⇒ `⁅E, E⁆ < E`.

mathlib `Group.IsSolvable.commutator_lt_of_ne_bot` は**環境** `[Group.IsSolvable G]` を要求するが,
証明が実際に使うのは `↥E` の可解性だけ (`↥E` 内で `commutator_lt_top_of_nontrivial` を
当てて `E.subtype` で押す). ambient の可解性を仮定しない Isaacs 3.11 で要る形.

冪零の場合は mathlib instance `IsNilpotent.to_isSolvable` が `Group.IsSolvable ↥E` を供給する
ので, 呼び出し側は `[Group.IsNilpotent ↥E]` のままでよい. -/
theorem commutator_lt_self_of_isSolvable_subtype
    {G : Type*} [Group G]
    (E : Subgroup G) [Group.IsSolvable ↥E] [Nontrivial ↥E] :
    ⁅E, E⁆ < E := by
  rw [← E.range_subtype, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
      Subgroup.map_subtype_lt_map_subtype]
  exact Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E

/-- Every subgroup of a cyclic group is characteristic.

This proof uses a generator directly: an automorphism sends the generator to another power of the
generator, so it sends each element `x` of a subgroup to an integral power of `x`, still in that
subgroup. -/
theorem characteristic_of_subgroup_of_isCyclic
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_comap]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (φ g))
  have hφx : φ x = x ^ m := by
    calc
      φ x = φ (g ^ n) := by rw [hn]
      _ = (φ g) ^ n := by rw [map_zpow]
      _ = (g ^ m) ^ n := by rw [hm]
      _ = g ^ (m * n) := by rw [← zpow_mul]
      _ = g ^ (n * m) := by rw [mul_comm]
      _ = (g ^ n) ^ m := by rw [zpow_mul]
      _ = x ^ m := by rw [hn]
  change φ x ∈ H
  rw [hφx]
  exact H.zpow_mem hx m

end OddOrder.Isaacs.Ch04


