-- Prove2me | Definitions.Def_OddOrder_GroupTheory_FittingSelfCentralizing
-- name    : OddOrder_GroupTheory_FittingSelfCentralizing
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:45.086913+00:00
-- url     : https://prove2.me/theorems/bb6f229e-8c39-4cba-8528-d3a78b5f87aa
-- title:
--   The Fitting subgroup of a solvable group is self-centralizing
-- statement:
--   Formalizes P. Hall's theorem $C_G(F(G))\le F(G)$ for finite solvable $G$ (Bender–Glauberman Prop. 1.3; Gorenstein Thm 6.1.3). It is a general theorem of finite group theory, so it sits in the shared layer, where it is available to leaves such as the CN-group structure needed for Gorenstein's Thm 12.1.5.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/FittingSelfCentralizing.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/FittingSelfCentralizing.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
import Mathlib.Order.Minimal
import Mathlib.GroupTheory.Solvable

namespace OddOrder.GroupTheory

/-- Minimal `G`-normal subgroup inside `C` but not inside `F`.

This is a finite-lattice helper for the self-centralizing theorem below. -/
private theorem exists_minimal_normal_le_not_le
    {G : Type*} [Group G] [Finite G] {C F : Subgroup G} [C.Normal]
    (hC_not_le_F : ¬ C ≤ F) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ C ∧ ¬ K ≤ F ∧
      ∀ K' : Subgroup G, K'.Normal → K' ≤ K → ¬ K' ≤ F → K ≤ K' := by
  classical
  let S : Set (Subgroup G) := {K | K.Normal ∧ K ≤ C ∧ ¬ K ≤ F}
  have hS_fin : S.Finite := Set.toFinite S
  have hS_nonempty : S.Nonempty := ⟨C, inferInstance, le_rfl, hC_not_le_F⟩
  obtain ⟨K, hK_min⟩ := hS_fin.exists_minimal hS_nonempty
  obtain ⟨⟨hK_normal, hK_le_C, hK_not_le_F⟩, hK_minimal⟩ := hK_min
  refine ⟨K, hK_normal, hK_le_C, hK_not_le_F, ?_⟩
  intro K' hK'_normal hK'_le hK'_not_le_F
  have hK'_mem : K' ∈ S := ⟨hK'_normal, hK'_le.trans hK_le_C, hK'_not_le_F⟩
  exact hK_minimal hK'_mem hK'_le

/-- If `K ≤ C_G(F)`, then `K ∩ F` is central in `K`. -/
private theorem inf_subgroupOf_le_center_of_le_centralizer
    {G : Type*} [Group G] {K F : Subgroup G}
    (hK_le_C : K ≤ Subgroup.centralizer (F : Set G)) :
    (K ⊓ F).subgroupOf K ≤ Subgroup.center K := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx_inf : (x : G) ∈ K ⊓ F := hx
  have hxF : (x : G) ∈ F := hx_inf.2
  have hyC : (y : G) ∈ Subgroup.centralizer (F : Set G) := hK_le_C y.2
  exact (Subgroup.mem_centralizer_iff.mp hyC (x : G) hxF).symm

/-- **BG Proposition 1.3** (P. Hall): for a finite solvable group, the Fitting subgroup
self-centralizes: `C_G(F(G)) ≤ F(G)`.

This proof avoids the still-missing chief-factor intersection API of Prop. 1.2.  If
`C_G(F(G))` had a normal subgroup `K` minimal among those not contained in `F(G)`, then
`[K,K] < K` by solvability and minimality forces `[K,K] ≤ F(G)`.  Since `K ≤ C_G(F(G))`,
`K ∩ F(G)` is central in `K`, and `K/(K ∩ F(G))` is abelian; hence `K` is nilpotent,
contradicting maximality of `F(G)`. -/
theorem centralizer_fitting_le_fitting
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] :
    Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting G : Subgroup G) : Set G) ≤
      OddOrder.Isaacs.Ch01.fitting G := by
  classical
  set F : Subgroup G := OddOrder.Isaacs.Ch01.fitting G with hF_def
  set C : Subgroup G := Subgroup.centralizer (F : Set G) with hC_def
  have hF_normal : F.Normal := by
    dsimp [F]
    infer_instance
  have hC_normal : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer
  by_contra hC_not_le_F
  obtain ⟨K, hK_normal, hK_le_C, hK_not_le_F, hK_min⟩ :=
    exists_minimal_normal_le_not_le (C := C) (F := F) hC_not_le_F
  have hK_normal_inst : K.Normal := hK_normal
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    apply hK_not_le_F
    rw [hK_bot]
    exact bot_le
  have hcomm_lt : ⁅K, K⁆ < K := Group.IsSolvable.commutator_lt_of_ne_bot hK_ne_bot
  have hcomm_le_F : ⁅K, K⁆ ≤ F := by
    by_contra hcomm_not_le_F
    have hK_le_comm : K ≤ ⁅K, K⁆ :=
      hK_min ⁅K, K⁆ inferInstance (Subgroup.commutator_le_left K K) hcomm_not_le_F
    exact hcomm_lt.not_ge hK_le_comm
  let N : Subgroup K := (K ⊓ F).subgroupOf K
  have hN_normal : N.Normal := by
    dsimp [N]
    infer_instance
  have hN_le_center : N ≤ Subgroup.center K := by
    dsimp [N]
    exact inf_subgroupOf_le_center_of_le_centralizer hK_le_C
  have hcomm_K_le_N : commutator K ≤ N := by
    intro x hx
    have hx_map : (x : G) ∈ (commutator K).map K.subtype := ⟨x, hx, rfl⟩
    rw [Subgroup.map_subtype_commutator] at hx_map
    exact ⟨x.2, hcomm_le_F hx_map⟩
  have hquot_mul_comm : ∀ x y : K ⧸ N, x * y = y * x :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_K_le_N).is_comm.comm
  have hquot_nilpotent : Group.IsNilpotent (K ⧸ N) := by
    rw [Subgroup.nilpotent_iff_lowerCentralSeries]
    refine ⟨1, ?_⟩
    rw [Subgroup.top_lowerCentralSeries_one, commutator_eq_bot_iff_center_eq_top, eq_top_iff]
    intro q _
    rw [Subgroup.mem_center_iff]
    intro r
    exact hquot_mul_comm r q
  have hker_le_center : (QuotientGroup.mk' N).ker ≤ Subgroup.center K := by
    rw [QuotientGroup.ker_mk']
    exact hN_le_center
  have hK_nilpotent : Group.IsNilpotent K :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N) hker_le_center
  have hK_le_fitting : K ≤ OddOrder.Isaacs.Ch01.fitting G :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  apply hK_not_le_F
  simpa [F, hF_def] using hK_le_fitting

end OddOrder.GroupTheory


