-- Prove2me | Definitions.Def_OddOrder_GroupTheory_ChermakDelgado
-- name    : OddOrder_GroupTheory_ChermakDelgado
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:07.027339+00:00
-- url     : https://prove2.me/theorems/3fe24ab4-86bd-4ce6-8cea-716cf3903b75
-- title:
--   Chermak–Delgado measure, lattice, and subgroup
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, §1G (pp. 41–44, Theorems 1.41–1.46): the Chermak–Delgado measure, the lattice of subgroups attaining the maximum measure, and the Chermak–Delgado subgroup (Lemmas 1.42, 1.43 are proved in this file).
--
--   Main definitions: `chermakDelgadoMeasure` ($m_G(H)=|H|\cdot|C_G(H)|$), `chermakDelgadoLattice` ($L(G)$, the subgroups of maximum measure) and `chermakDelgadoSubgroup` ($M$, the minimal element of $L(G)$). Also proved: $M$ is abelian (Cor 1.45, part 2) and characteristic (part 4).
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/ChermakDelgado.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ChermakDelgado.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Lattice
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Ring

namespace Subgroup

variable {G : Type*} [Group G]

open scoped Pointwise

/-- **Chermak-Delgado measure** of a subgroup: `m_G(H) := |H| · |C_G(H)|`.

Isaacs §1G p.41 の定義. 無限群でも well-defined だが (`Nat.card` が 0 を返す),
実質的に意味があるのは [Finite G] 下. -/
noncomputable def chermakDelgadoMeasure (H : Subgroup G) : ℕ :=
  Nat.card H * Nat.card (centralizer (H : Set G) : Subgroup G)

@[simp]
theorem chermakDelgadoMeasure_def (H : Subgroup G) :
    H.chermakDelgadoMeasure = Nat.card H * Nat.card (centralizer (H : Set G) : Subgroup G) :=
  rfl

/-- **Chermak-Delgado lattice** `L(G)`: the collection of subgroups attaining the maximum
Chermak-Delgado measure. Isaacs §1G p.42 (Thm 1.44 statement). -/
def chermakDelgadoLattice (G : Type*) [Group G] : Set (Subgroup G) :=
  {H | ∀ K : Subgroup G, K.chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure}

/-- **Chermak-Delgado subgroup** `M`: the minimal element of the maximum-measure lattice.
Isaacs Cor 1.45 で唯一の極小元として定義される (本ファイルで Cor 1.45 として証明). -/
noncomputable def chermakDelgadoSubgroup (G : Type*) [Group G] : Subgroup G :=
  ⨅ H ∈ chermakDelgadoLattice G, H

/-- **Isaacs Lemma 1.42**: `m_G(H) ≤ m_G(C_G(H))`.
等号成立は `H = C_G(C_G(H))` のとき (本ファイル `..._eq_iff` 系で別途扱う).

証明: `H ≤ C_G(C_G(H))` (`le_centralizer_centralizer`, mathlib 拡張) から
`|H| ≤ |C_G(C_G(H))|`, 両辺に `|C_G(H)|` を掛けて結論. -/
theorem chermakDelgadoMeasure_le_centralizer [Finite G] (H : Subgroup G) :
    H.chermakDelgadoMeasure
      ≤ (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  -- Goal: |H| * |C_H| ≤ |C_H| * |C_(C_H)|
  rw [Nat.mul_comm (Nat.card ↥(centralizer (H : Set G)))]
  -- Goal: |H| * |C_H| ≤ |C_(C_H)| * |C_H|
  exact Nat.mul_le_mul_right _
    (Nat.card_le_card_of_injective (Subgroup.inclusion H.le_centralizer_centralizer)
      (Subgroup.inclusion_injective _))

/-- **Isaacs Lemma 1.43**: `m_G(H) · m_G(K) ≤ m_G(D) · m_G(J)` for `D = H ⊓ K`, `J = H ⊔ K`.

証明戦略 (Isaacs p.42):
- `|H|·|K| = |HK|·|D|` (H1).
- `|C_H|·|C_K| = |C_H·C_K|·|C_H ∩ C_K| = |C_H·C_K|·|C_J|` (H1 + `centralizer_sup`).
- `HK ⊆ J` ⟹ `|HK| ≤ |J|`.
- `C_H·C_K ⊆ C_D` ⟹ `|C_H·C_K| ≤ |C_D|`.
- 組合せて `|HK|·|C_H·C_K| ≤ |J|·|C_D|`, 両辺に `|D|·|C_J|` を掛けて結論. -/
theorem chermakDelgadoMeasure_mul_le [Finite G] (H K : Subgroup G) :
    H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      ≤ (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure := by
  set D := H ⊓ K with hD_def
  set J := H ⊔ K with hJ_def
  set C_H : Subgroup G := centralizer (H : Set G) with hCH_def
  set C_K : Subgroup G := centralizer (K : Set G) with hCK_def
  set C_D : Subgroup G := centralizer (D : Set G) with hCD_def
  set C_J : Subgroup G := centralizer (J : Set G) with hCJ_def
  -- 核心等式: C_J = C_H ⊓ C_K
  have hCJ_inf : C_J = C_H ⊓ C_K := centralizer_sup H K
  -- H1 for H, K
  have h1_HK : Nat.card (↑H * ↑K : Set G) * Nat.card ↥D = Nat.card H * Nat.card K :=
    card_HK_mul_card_inf_eq_card_mul_card H K
  -- H1 for C_H, C_K
  have h1_CHCK :
      Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card ↥(C_H ⊓ C_K)
        = Nat.card C_H * Nat.card C_K :=
    card_HK_mul_card_inf_eq_card_mul_card C_H C_K
  rw [← hCJ_inf] at h1_CHCK
  -- HK ⊆ J (集合包含)
  have hHK_sub_J : (↑H * ↑K : Set G) ⊆ (J : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)
  -- C_H * C_K ⊆ C_D (集合包含); C_H ⊆ C_D, C_K ⊆ C_D ⟹ 積も ⊆
  have hC_sub_CD : (C_H : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_left : D ≤ H)))
  have hCK_sub_CD : (C_K : Set G) ⊆ (C_D : Set G) :=
    SetLike.coe_subset_coe.mpr (centralizer_le (SetLike.coe_subset_coe.mpr (inf_le_right : D ≤ K)))
  have hCHCK_sub_CD : ((C_H : Set G) * (C_K : Set G) : Set G) ⊆ (C_D : Set G) := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (hC_sub_CD hh) (hCK_sub_CD hk)
  -- cardinality monotonicity (with [Finite G])
  have hHK_le_J : Nat.card (↑H * ↑K : Set G) ≤ Nat.card J :=
    Nat.card_mono (Set.toFinite _) hHK_sub_J
  have hCHCK_le_CD : Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) ≤ Nat.card C_D :=
    Nat.card_mono (Set.toFinite _) hCHCK_sub_CD
  have main_ineq :
      Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G)
        ≤ Nat.card J * Nat.card C_D :=
    Nat.mul_le_mul hHK_le_J hCHCK_le_CD
  -- 仕上げ: 代数的整理
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def, chermakDelgadoMeasure_def,
      chermakDelgadoMeasure_def]
  calc Nat.card H * Nat.card C_H * (Nat.card K * Nat.card C_K)
      = (Nat.card H * Nat.card K) * (Nat.card C_H * Nat.card C_K) := by ring
    _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ↥D)
          * (Nat.card ((C_H : Set G) * (C_K : Set G) : Set G) * Nat.card C_J) := by
          rw [h1_HK, h1_CHCK]
    _ = (Nat.card (↑H * ↑K : Set G) * Nat.card ((C_H : Set G) * (C_K : Set G) : Set G))
          * (Nat.card ↥D * Nat.card C_J) := by ring
    _ ≤ (Nat.card J * Nat.card C_D) * (Nat.card ↥D * Nat.card C_J) :=
          Nat.mul_le_mul_right _ main_ineq
    _ = Nat.card ↥D * Nat.card C_D * (Nat.card J * Nat.card C_J) := by ring

/-- 数論的補助: `a * b = c * d`, `a ≤ c`, `b ≤ d`, `c, b > 0` のとき `a = c ∧ b = d`. -/
private lemma _eq_of_mul_eq_of_le {a b c d : ℕ} (h_eq : a * b = c * d)
    (ha : a ≤ c) (hb : b ≤ d) (hc : 0 < c) (hb_pos : 0 < b) :
    a = c ∧ b = d := by
  have h1 : a * b ≤ c * b := Nat.mul_le_mul_right b ha
  have h2 : c * b ≤ c * d := Nat.mul_le_mul_left c hb
  have h_cb : a * b = c * b := le_antisymm h1 (h_eq ▸ h2)
  have ha_eq : a = c := Nat.eq_of_mul_eq_mul_right hb_pos h_cb
  subst ha_eq
  have hb_eq : b = d := Nat.eq_of_mul_eq_mul_left hc h_eq
  exact ⟨rfl, hb_eq⟩

/-- 数論的補助 (対称): `a * b = m * m`, `a ≤ m`, `b ≤ m` のとき `a = m ∧ b = m`. -/
private lemma _eq_of_mul_eq_sq_of_le {a b m : ℕ} (h_eq : a * b = m * m)
    (ha : a ≤ m) (hb : b ≤ m) : a = m ∧ b = m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact ⟨Nat.le_zero.mp ha, Nat.le_zero.mp hb⟩
  · rcases Nat.eq_zero_or_pos b with hb_z | hb_pos
    · subst hb_z
      rw [Nat.mul_zero] at h_eq
      have : m = 0 := by
        rcases Nat.mul_eq_zero.mp h_eq.symm with h | h <;> exact h
      omega
    · exact _eq_of_mul_eq_of_le h_eq ha hb hm hb_pos

/-- `H, K ∈ L(G)` ならば Lemma 1.43 の不等式は**等号**になる: measure の最大性から
`m_G(D)·m_G(J) ≤ m_G(H)²= m_G(H)·m_G(K)` で、逆向きが 1.43。

Thm 1.44 (a)(b) が共通して使う入口。 -/
theorem chermakDelgadoLattice_measure_mul_eq [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      = (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure := by
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  refine le_antisymm (chermakDelgadoMeasure_mul_le H K) ?_
  calc (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
      ≤ H.chermakDelgadoMeasure * H.chermakDelgadoMeasure := Nat.mul_le_mul (hH _) (hH _)
    _ = H.chermakDelgadoMeasure * K.chermakDelgadoMeasure := by rw [hsame]

/-- `H, K ∈ L(G)` のとき `m_G(H⊓K) = m_G(H) = m_G(H⊔K)` (Thm 1.44 (a) の中身)。 -/
private theorem _lattice_measure_inf_and_sup_eq [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    (H ⊓ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure ∧
      (H ⊔ K).chermakDelgadoMeasure = H.chermakDelgadoMeasure := by
  have hsame : H.chermakDelgadoMeasure = K.chermakDelgadoMeasure := le_antisymm (hK H) (hH K)
  have h_prod_eq : (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure
                 = H.chermakDelgadoMeasure * H.chermakDelgadoMeasure := by
    rw [← chermakDelgadoLattice_measure_mul_eq hH hK, hsame]
  exact _eq_of_mul_eq_sq_of_le h_prod_eq (hH _) (hH _)

/-- **Isaacs Thm 1.44 (a)**: `L(G)` is closed under intersection. -/
theorem chermakDelgadoLattice_inf_mem [Finite G] {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊓ K ∈ chermakDelgadoLattice G := by
  intro L
  rw [(_lattice_measure_inf_and_sup_eq hH hK).1]
  exact hH L

/-- **Isaacs Thm 1.44 (c)**: For `H ∈ L`: `C_G(H) ∈ L`. -/
theorem chermakDelgadoLattice_centralizer_mem [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    (centralizer (H : Set G) : Subgroup G) ∈ chermakDelgadoLattice G := by
  intro L
  have h_eq : (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure
            = H.chermakDelgadoMeasure :=
    le_antisymm (hH _) (chermakDelgadoMeasure_le_centralizer H)
  rw [h_eq]
  exact hH L

/-- L(G) is nonempty (max measure exists for finite G). -/
theorem chermakDelgadoLattice_nonempty [Finite G] :
    (chermakDelgadoLattice G).Nonempty := by
  have : Nonempty (Subgroup G) := ⟨⊥⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨H_max, h_max⟩ :=
    Finite.exists_max (fun H : Subgroup G => H.chermakDelgadoMeasure)
  exact ⟨H_max, h_max⟩

/-- L(G) is finite. -/
theorem chermakDelgadoLattice_finite [Finite G] :
    (chermakDelgadoLattice G).Finite := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  exact Set.toFinite _

/-- M = sInf L (alternative form of `chermakDelgadoSubgroup`). -/
theorem chermakDelgadoSubgroup_eq_sInf :
    chermakDelgadoSubgroup G = sInf (chermakDelgadoLattice G) := by
  rw [chermakDelgadoSubgroup, sInf_eq_iInf]

/-- 補助: 有限・閉じた sublattice の `sInf` は中身に入っている. -/
private theorem _sInf_mem_of_finite_subset [Finite G] (S : Set (Subgroup G))
    (hfin : S.Finite) :
    S.Nonempty → S ⊆ chermakDelgadoLattice G → sInf S ∈ chermakDelgadoLattice G := by
  induction S, hfin using Set.Finite.induction_on with
  | empty => intro hne _; exact (Set.not_nonempty_empty hne).elim
  | @insert a t hat ht_fin ih =>
    intro _hne hsub
    rcases t.eq_empty_or_nonempty with rfl | ht_ne
    · -- t = ∅, so S = {a}. sInf {a} = a, and a ∈ L
      rw [Set.insert_eq, Set.union_empty, sInf_singleton]
      exact hsub (Set.mem_insert _ _)
    · -- t nonempty
      have hsub_t : t ⊆ chermakDelgadoLattice G :=
        fun H hH => hsub (Set.mem_insert_of_mem _ hH)
      have ha_in : a ∈ chermakDelgadoLattice G := hsub (Set.mem_insert _ _)
      have h_ih := ih ht_ne hsub_t
      rw [sInf_insert]
      exact chermakDelgadoLattice_inf_mem ha_in h_ih

/-- **Isaacs Cor 1.45 part 1**: `M = chermakDelgadoSubgroup G ∈ L(G)`. -/
theorem chermakDelgadoSubgroup_mem_lattice [Finite G] :
    chermakDelgadoSubgroup G ∈ chermakDelgadoLattice G := by
  rw [chermakDelgadoSubgroup_eq_sInf]
  exact _sInf_mem_of_finite_subset _ chermakDelgadoLattice_finite
    chermakDelgadoLattice_nonempty Set.Subset.rfl

/-- `M ≤ H` for any `H ∈ L`. -/
theorem chermakDelgadoSubgroup_le_of_mem [Finite G] {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    chermakDelgadoSubgroup G ≤ H := by
  rw [chermakDelgadoSubgroup_eq_sInf]
  exact sInf_le hH

/-- `M ≤ C_G(M)` ── M ∈ L で `C_G(M) ∈ L` (Thm 1.44(c)) なので `M ≤ C_G(M)`. -/
theorem chermakDelgadoSubgroup_le_centralizer [Finite G] :
    chermakDelgadoSubgroup G
      ≤ (centralizer ((chermakDelgadoSubgroup G : Subgroup G) : Set G) : Subgroup G) :=
  chermakDelgadoSubgroup_le_of_mem
    (chermakDelgadoLattice_centralizer_mem chermakDelgadoSubgroup_mem_lattice)

/-- **Isaacs Cor 1.45 part 2**: `M` is abelian (`IsMulCommutative`). -/
instance chermakDelgadoSubgroup_isMulCommutative [Finite G] :
    IsMulCommutative (chermakDelgadoSubgroup G) :=
  le_centralizer_iff_isMulCommutative.mp chermakDelgadoSubgroup_le_centralizer

/-- Chermak-Delgado 測度は群自己同型の下で不変. -/
private lemma chermakDelgadoMeasure_map_equiv (ϕ : G ≃* G) (K : Subgroup G) :
    (K.map ϕ.toMonoidHom).chermakDelgadoMeasure = K.chermakDelgadoMeasure := by
  rw [chermakDelgadoMeasure_def, chermakDelgadoMeasure_def]
  have h_card_K : Nat.card (K.map ϕ.toMonoidHom : Subgroup G) = Nat.card K :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective K ϕ.toMonoidHom ϕ.injective).symm.toEquiv
  have h_centralizer :
      (centralizer ((K.map ϕ.toMonoidHom : Subgroup G) : Set G) : Subgroup G)
        = (centralizer (K : Set G) : Subgroup G).map ϕ.toMonoidHom := by
    apply SetLike.coe_injective
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · intro hg
      refine ⟨ϕ.symm g, ?_, by simp⟩
      intro k hk
      -- hg (ϕ k) hkmap : ϕ k * g = g * ϕ k
      have h1 : ϕ k * g = g * ϕ k :=
        hg (ϕ k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
      have h2 := congrArg ϕ.symm h1
      simp only [MulEquiv.map_mul, MulEquiv.symm_apply_apply] at h2
      -- h2 : k * ϕ.symm g = ϕ.symm g * k
      exact h2
    · rintro ⟨a, ha, rfl⟩ y hy
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      -- ha k hk : k * a = a * k
      have h1 : k * a = a * k := ha k hk
      have h2 := congrArg ϕ h1
      simp only [MulEquiv.map_mul] at h2
      -- h2 : ϕ k * ϕ a = ϕ a * ϕ k
      exact h2
  rw [h_card_K, h_centralizer]
  congr 1
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective
      (centralizer (K : Set G) : Subgroup G) ϕ.toMonoidHom ϕ.injective).symm.toEquiv

/-- comap 版の不変性. -/
private lemma chermakDelgadoMeasure_comap_equiv (ϕ : G ≃* G) (K : Subgroup G) :
    (K.comap ϕ.toMonoidHom).chermakDelgadoMeasure = K.chermakDelgadoMeasure := by
  rw [comap_equiv_eq_map_symm', chermakDelgadoMeasure_map_equiv]

/-- 自己同型は L(G) を保つ (comap 形式). -/
private lemma chermakDelgadoLattice_comap_mem (ϕ : G ≃* G) {K : Subgroup G}
    (hK : K ∈ chermakDelgadoLattice G) :
    K.comap ϕ.toMonoidHom ∈ chermakDelgadoLattice G := by
  intro J
  rw [chermakDelgadoMeasure_comap_equiv]
  exact hK J

/-- **Isaacs Cor 1.45 part 4**: `M` is characteristic.

`L(G)` は自己同型で不変 ⟹ `M = sInf L(G)` も不変. -/
instance chermakDelgadoSubgroup_characteristic [Finite G] :
    (chermakDelgadoSubgroup G).Characteristic := by
  rw [characteristic_iff_le_comap]
  intro ϕ
  rw [chermakDelgadoSubgroup_eq_sInf]
  -- 目標: sInf L ≤ (sInf L).comap ϕ
  -- 各 x ∈ sInf L について, ϕ x ∈ sInf L を示せばよい
  intro x hx
  rw [mem_comap, Subgroup.mem_sInf]
  intro K hK
  -- K ∈ L. ϕ x ∈ K ↔ x ∈ K.comap ϕ. K.comap ϕ ∈ L (measure-invariant).
  -- x ∈ sInf L ≤ K.comap ϕ. ✓
  have hKcomap : K.comap ϕ.toMonoidHom ∈ chermakDelgadoLattice G :=
    chermakDelgadoLattice_comap_mem ϕ hK
  rw [Subgroup.mem_sInf] at hx
  exact hx _ hKcomap

end Subgroup


