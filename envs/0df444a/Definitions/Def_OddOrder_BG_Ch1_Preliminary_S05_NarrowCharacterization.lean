-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowCharacterization
-- name    : OddOrder_BG_Ch1_Preliminary_S05_NarrowCharacterization
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:21:59.880562+00:00
-- url     : https://prove2.me/theorems/9c1926bc-26e5-4340-b67e-c815c08b537b
-- title:
--   BG §5: narrow $p$-groups, Theorem 5.3 and Corollary 5.4
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Chapter I §5: the characterization of narrow $p$-groups, namely that for $r(R)\ge3$, $R$ is narrow if and only if $\mathcal{E}^2(R)\cap\mathcal{E}^*(R)\ne\emptyset$ (Theorem 5.3 and Corollary 5.4). The bundle consists of lemmas only.
--
--   The bundle also proves 17 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S05_NarrowCharacterization.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S05_NarrowCharacterization.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowSCN

namespace OddOrder.BG.Ch1.S05

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped IsMulCommutative commutatorElement

variable {R : Type*} [Group R]

/-- **BG Theorem 5.3(d) support**: since `R' ≤ T = C_R(Ω₁(Z₂(R)))`,
the disjointness `S ∩ T = 1` implies `S ∩ R' = 1`.

This isolates the already-green commutator-to-`T` input from the remaining hard
centralizer decomposition proof. -/
theorem inf_commutator_eq_bot_of_inf_centralizer_omega1UpperCentralTwo_eq_bot
    {p : ℕ} {S : Subgroup R}
    (hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥) :
    S ⊓ commutator R = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [← hST]
  exact ⟨hx.1, commutator_le_centralizer_omega1UpperCentralTwo hx.2⟩

theorem isElementaryAbelian_of_card_prime [Finite R] {p : ℕ} [Fact p.Prime]
    {S : Subgroup R} (hS : Nat.card S = p) : S.IsElementaryAbelian p := by
  have hScyc : IsCyclic S := isCyclic_of_prime_card hS
  constructor
  · have : IsCyclic S := hScyc
    let : CommGroup S := IsCyclic.commGroup
    intro x y
    exact mul_comm x y
  · intro x
    have hx := pow_card_eq_one' (G := S) (x := x)
    simpa [hS] using hx

private theorem sup_eq_of_card_prime_ne_of_le_isElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] {E H K : Subgroup R}
    (hE : E.IsElementaryAbelian p) (hEcard : Nat.card E = p ^ 2)
    (hHE : H ≤ E) (hKE : K ≤ E) (hHcard : Nat.card H = p) (hKcard : Nat.card K = p)
    (hHKne : H ≠ K) : H ⊔ K = E := by
  classical
  let H' : Subgroup E := H.subgroupOf E
  let K' : Subgroup E := K.subgroupOf E
  have hH'card : Nat.card H' = p := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHE).toEquiv).trans hHcard
  have hK'card : Nat.card K' = p := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv).trans hKcard
  have hH'K'ne : H' ≠ K' := by
    intro h'
    apply hHKne
    calc H = H'.map E.subtype := (Subgroup.map_subgroupOf_eq_of_le hHE).symm
      _ = K'.map E.subtype := by rw [h']
      _ = K := Subgroup.map_subgroupOf_eq_of_le hKE
  have hInf_bot : H' ⊓ K' = ⊥ := by
    have hInf_dvd : Nat.card ↥(H' ⊓ K') ∣ p := by
      rw [← hH'card]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hInf_dvd with hInf_card | hInf_card
    · exact Subgroup.eq_bot_of_card_eq _ hInf_card
    · exfalso
      have hInf_eq_H : H' ⊓ K' = H' :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hInf_card, hH'card])
      have hInf_eq_K : H' ⊓ K' = K' :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hInf_card, hK'card])
      exact hH'K'ne (hInf_eq_H.symm.trans hInf_eq_K)
  let : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  have : H'.Normal := by infer_instance
  have hsup_card : Nat.card ↥(H' ⊔ K') = p ^ 2 := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card H' K'
    rw [← Subgroup.normal_mul H' K', hInf_bot, Subgroup.card_bot, hH'card, hK'card,
      mul_one] at hcard
    simpa [pow_two] using hcard
  have hsup_top : H' ⊔ K' = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    simpa [Subgroup.card_top, hEcard] using hsup_card
  have hmap : (H' ⊔ K').map E.subtype = H ⊔ K := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hHE,
      Subgroup.map_subgroupOf_eq_of_le hKE]
  calc H ⊔ K = (H' ⊔ K').map E.subtype := hmap.symm
    _ = (⊤ : Subgroup E).map E.subtype := by rw [hsup_top]
    _ = E := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨e, _, rfl⟩ := hx
        exact e.2
      · intro hx
        rw [Subgroup.mem_map]
        exact ⟨⟨x, hx⟩, trivial, rfl⟩

private theorem centralizer_le_centralizer_of_sup_omega1Center_eq
    {p : ℕ} {S E : Subgroup R} (hE : omega1Center R p ⊔ S = E) :
    Subgroup.centralizer (S : Set R) ≤ Subgroup.centralizer (E : Set R) := by
  rw [← hE, Subgroup.centralizer_sup]
  refine le_inf ?_ le_rfl
  intro x _
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_center_iff.mp (omega1Center_le_center hz) x).symm

private theorem exists_card_prime_centralizer_pRank_le_two_of_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p)
    (hExists : ∃ E : Subgroup R, Nat.card E = p ^ 2 ∧ IsMaximalElementaryAbelian p E) :
    ∃ S : Subgroup R, Nat.card S = p ∧
      pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 := by
  obtain ⟨E, hEcard, hEstar⟩ := hExists
  have hEelem : E.IsElementaryAbelian p := hEstar.isElementaryAbelian
  obtain ⟨K, L, hKle, hLle, hKcard, hLcard, hKLne⟩ :=
    Subgroup.exists_distinct_subgroups_card_prime_of_isElementaryAbelian_card_prime_sq
      (G := R) (H := E) (Fact.out : p.Prime) hEelem hEcard
  have hZleE : omega1Center R p ≤ E := omega1Center_le_of_maximalElementaryAbelian hEstar
  have hZcard : Nat.card (omega1Center R p) = p :=
    (omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEcard hEstar).2
  have hCErank : pRank ↥(Subgroup.centralizer (E : Set R)) p ≤ 2 :=
    pRank_centralizer_le_two_of_maximalElementaryAbelian_card_prime_sq hEcard hEstar
  by_cases hKZ : K = omega1Center R p
  · have hLZ : L ≠ omega1Center R p := by
      intro hLZ
      exact hKLne (hKZ.trans hLZ.symm)
    have hZE_sup : omega1Center R p ⊔ L = E :=
      sup_eq_of_card_prime_ne_of_le_isElementaryAbelian_card_prime_sq
        hEelem hEcard hZleE hLle hZcard hLcard (fun h => hLZ h.symm)
    have hC_le : Subgroup.centralizer (L : Set R) ≤ Subgroup.centralizer (E : Set R) :=
      centralizer_le_centralizer_of_sup_omega1Center_eq hZE_sup
    have hLrank : pRank ↥(Subgroup.centralizer (L : Set R)) p ≤ 2 :=
      (pRank_le_of_injective (G := ↥(Subgroup.centralizer (E : Set R)))
        (H := ↥(Subgroup.centralizer (L : Set R)))
        (f := Subgroup.inclusion hC_le) (Subgroup.inclusion_injective hC_le)).trans hCErank
    exact ⟨L, hLcard, hLrank⟩
  · have hZE_sup : omega1Center R p ⊔ K = E :=
      sup_eq_of_card_prime_ne_of_le_isElementaryAbelian_card_prime_sq
        hEelem hEcard hZleE hKle hZcard hKcard (fun h => hKZ h.symm)
    have hC_le : Subgroup.centralizer (K : Set R) ≤ Subgroup.centralizer (E : Set R) :=
      centralizer_le_centralizer_of_sup_omega1Center_eq hZE_sup
    have hKrank : pRank ↥(Subgroup.centralizer (K : Set R)) p ≤ 2 :=
      (pRank_le_of_injective (G := ↥(Subgroup.centralizer (E : Set R)))
        (H := ↥(Subgroup.centralizer (K : Set R)))
        (f := Subgroup.inclusion hC_le) (Subgroup.inclusion_injective hC_le)).trans hCErank
    exact ⟨K, hKcard, hKrank⟩

private theorem exists_elementaryAbelian_card_prime_sq_le_centralizer_of_card_prime
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    ∃ E : Subgroup R, E.IsElementaryAbelian p ∧ Nat.card E = p ^ 2 ∧
      S ≤ E ∧ E ≤ Subgroup.centralizer (S : Set R) := by
  classical
  obtain ⟨A, hA⟩ := scn3_nonempty_of_three_le_pRank hp hpg h3
  obtain ⟨B, hB_normal, hB_elem, hBcard⟩ :=
    exists_normal_isElementaryAbelian_card_prime_cube_of_scn3 hpg hA
  have : B.Normal := hB_normal
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  have hB_ne_bot : B ≠ ⊥ := by
    intro hBbot
    have hcard_one : Nat.card B = 1 := by rw [hBbot, Subgroup.card_bot]
    have hp3_gt_one : 1 < p ^ 3 := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by norm_num)
    exact (ne_of_gt hp3_gt_one) (by rw [← hBcard, hcard_one])
  have hnotSB : ¬ S ≤ B := by
    intro hSB
    have hB_le_C : B ≤ C := by
      intro b hb
      dsimp [C]
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (hB_elem.comm ⟨s, hSB hs⟩ ⟨b, hb⟩)
    let Bsub : Subgroup C := B.subgroupOf C
    have hBsub_elem : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_le_C).symm hB_elem
    have hBsub_card : Nat.card Bsub = p ^ 3 := by
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_C).toEquiv).trans hBcard
    have hBrank : 3 ≤ pRank C p :=
      pow_le_card_of_le_pRank Bsub hBsub_elem hBsub_card
    have : 3 ≤ 2 := hBrank.trans hSrank
    omega
  have hSBinf : S ⊓ B = ⊥ := by
    have hInf_dvd : Nat.card ↥(S ⊓ B) ∣ p := by
      rw [← hScard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hInf_dvd with hInf_card | hInf_card
    · exact Subgroup.eq_bot_of_card_eq _ hInf_card
    · exfalso
      have hInf_eq_S : S ⊓ B = S :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hInf_card, hScard])
      have hSB : S ≤ B := by
        intro x hx
        have hxInf : x ∈ S ⊓ B := by simpa [hInf_eq_S] using hx
        exact hxInf.2
      exact hnotSB hSB
  obtain ⟨b, hbB, hbZ, hbne⟩ :=
    OddOrder.GroupTheory.exists_mem_center_of_normal_ne_bot hpg (K := B) hB_ne_bot
  let U : Subgroup R := Subgroup.zpowers b
  have hb_pow : b ^ p = 1 := by
    simpa using congrArg Subtype.val (hB_elem.pow_eq_one (⟨b, hbB⟩ : B))
  have hb_order : orderOf b = p := orderOf_eq_prime hb_pow hbne
  have hUcard : Nat.card U = p := by
    rw [show U = Subgroup.zpowers b from rfl, Nat.card_zpowers, hb_order]
  have hU_elem : U.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hUcard
  have hU_le_B : U ≤ B := Subgroup.zpowers_le.mpr hbB
  have hU_le_center : U ≤ Subgroup.center R := Subgroup.zpowers_le.mpr hbZ
  have hSUinf : S ⊓ U = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxSB : x ∈ S ⊓ B := ⟨hx.1, hU_le_B hx.2⟩
    rwa [hSBinf] at hxSB
  have hS_le_cent_U : S ≤ Subgroup.centralizer (U : Set R) := by
    intro s _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_center_iff.mp (hU_le_center hu) s).symm
  let E0 : Subgroup R := S ⊔ U
  have hE0_elem : E0.IsElementaryAbelian p := by
    simpa [E0] using
      Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hU_elem hS_le_cent_U
  have hU_normal : U.Normal := by
    refine { conj_mem := fun x hx g => ?_ }
    have hx_center : x ∈ Subgroup.center R := hU_le_center hx
    have hconj : g * x * g⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hx_center g
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hconj]
  have hE0card : Nat.card E0 = p ^ 2 := by
    have hUSinf : U ⊓ S = ⊥ := by rwa [inf_comm]
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card U S
    rw [← Subgroup.normal_mul U S, hUSinf, Subgroup.card_bot, hUcard, hScard, mul_one] at hcard
    simpa [E0, sup_comm, pow_two, mul_comm] using hcard
  have hS_le_C : S ≤ C := by
    intro s hs
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  have hU_le_C : U ≤ C := by
    intro u hu
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro s _
    exact Subgroup.mem_center_iff.mp (hU_le_center hu) s
  have hE0_le_C : E0 ≤ C := by
    dsimp [E0]
    exact sup_le hS_le_C hU_le_C
  exact ⟨E0, hE0_elem, hE0card, le_sup_left, hE0_le_C⟩

private theorem exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    (hExists : ∃ S : Subgroup R, Nat.card S = p ∧
      pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    ∃ E : Subgroup R, Nat.card E = p ^ 2 ∧ IsMaximalElementaryAbelian p E := by
  obtain ⟨S, hScard, hSrank⟩ := hExists
  obtain ⟨E0, hE0elem, hE0card, hSleE0, hE0leC⟩ :=
    exists_elementaryAbelian_card_prime_sq_le_centralizer_of_card_prime hp hpg h3 hScard hSrank
  obtain ⟨F, hE0F, hFstar⟩ := exists_maximalElementaryAbelian_ge hE0elem
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hFelem : F.IsElementaryAbelian p := hFstar.isElementaryAbelian
  have hSleF : S ≤ F := hSleE0.trans hE0F
  have hFleC : F ≤ C := by
    intro f hf
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (hFelem.comm ⟨s, hSleF hs⟩ ⟨f, hf⟩)
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFleC).symm hFelem
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleC).toEquiv
  have hlogFsub_le : Nat.log p (Nat.card Fsub) ≤ 2 :=
    (pRank_le_iff.mp hSrank) Fsub hFsub_elem
  have hlogF_le : Nat.log p (Nat.card F) ≤ 2 := by
    simpa [Fsub, hFsub_card] using hlogFsub_le
  have hE0_card_le_F : Nat.card E0 ≤ Nat.card F :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hE0F) (Subgroup.inclusion_injective hE0F)
  have hpow_le : p ^ 2 ≤ Nat.card F := by
    simpa [hE0card] using hE0_card_le_F
  have hlogF_ge : 2 ≤ Nat.log p (Nat.card F) :=
    Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hpow_le
  have hlogF_eq : Nat.log p (Nat.card F) = 2 := le_antisymm hlogF_le hlogF_ge
  have hFcard : Nat.card F = p ^ 2 := by
    have hcard_pow := hFelem.card_eq_pow_finrank
    have hlog_fin := hFelem.log_card_eq_finrank
    rw [hcard_pow, ← hlog_fin, hlogF_eq]
  exact ⟨F, hFcard, hFstar⟩

theorem le_of_inf_ne_bot_of_card_prime
    [Finite R] {p : ℕ} [Fact p.Prime] {S H : Subgroup R}
    (hScard : Nat.card S = p) (hInf_ne : S ⊓ H ≠ ⊥) : S ≤ H := by
  classical
  let L : Subgroup S := (S ⊓ H).subgroupOf S
  have : Fact (Nat.card S).Prime := ⟨by rw [hScard]; exact (Fact.out : p.Prime)⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card L with hLbot | hLtop
  · exfalso
    apply hInf_ne
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxL : (⟨x, hx.1⟩ : S) ∈ L := by
      dsimp [L]
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hLbot, Subgroup.mem_bot] at hxL
    exact Subtype.ext_iff.mp hxL
  · intro s hs
    have hsL : (⟨s, hs⟩ : S) ∈ L := by
      rw [hLtop]
      exact trivial
    exact (Subgroup.mem_subgroupOf.mp hsL).2

/-- **BG Theorem 5.3(d) support**: with centralizer p-rank at most two,
the subgroup generated by an order-p subgroup S and Omega_1 of the center is
itself a maximal elementary abelian subgroup of order p squared. -/
private theorem sup_omega1Center_maximalElementaryAbelian_of_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (h3 : 3 ≤ pRank R p)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2)
    (hZcard : Nat.card (omega1Center R p) = p) :
    Nat.card ↥(S ⊔ omega1Center R p) = p ^ 2 ∧
      IsMaximalElementaryAbelian p (S ⊔ omega1Center R p) := by
  classical
  let Z : Subgroup R := omega1Center R p
  let E : Subgroup R := S ⊔ Z
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  have hZ_elem : Z.IsElementaryAbelian p := by
    dsimp [Z]
    exact omega1Center_isElementaryAbelian
  have hS_le_cent_Z : S ≤ Subgroup.centralizer (Z : Set R) := by
    intro s _
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (omega1Center_le_center hz) s).symm
  have hE_elem : E.IsElementaryAbelian p := by
    dsimp [E]
    exact Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hZ_elem hS_le_cent_Z
  have hSZinf : S ⊓ Z = ⊥ := by
    simpa [Z] using
      inf_omega1Center_eq_bot_of_card_prime_centralizer_pRank_le_two
        h3 hScard hSrank
  have hZ_normal : Z.Normal := by
    refine { conj_mem := fun x hx g => ?_ }
    have hx_center : x ∈ Subgroup.center R := omega1Center_le_center hx
    have hconj : g * x * g⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hx_center g
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hconj]
  have hEcard : Nat.card E = p ^ 2 := by
    have hZSinf : Z ⊓ S = ⊥ := by rwa [inf_comm]
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Z S
    rw [← Subgroup.normal_mul Z S, hZSinf, Subgroup.card_bot, hZcard, hScard,
      mul_one] at hcard
    simpa [E, sup_comm, pow_two, mul_comm] using hcard
  obtain ⟨F, hE_le_F, hFstar⟩ := exists_maximalElementaryAbelian_ge hE_elem
  have hFelem : F.IsElementaryAbelian p := hFstar.isElementaryAbelian
  have hSleE : S ≤ E := by
    dsimp [E]
    exact le_sup_left
  have hSleF : S ≤ F := hSleE.trans hE_le_F
  have hFleC : F ≤ C := by
    intro f hf
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (hFelem.comm ⟨s, hSleF hs⟩ ⟨f, hf⟩)
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFleC).symm hFelem
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleC).toEquiv
  have hlogFsub_le : Nat.log p (Nat.card Fsub) ≤ 2 :=
    (pRank_le_iff.mp hSrank) Fsub hFsub_elem
  have hlogF_le : Nat.log p (Nat.card F) ≤ 2 := by
    simpa [Fsub, hFsub_card] using hlogFsub_le
  have hE_card_le_F : Nat.card E ≤ Nat.card F :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hE_le_F)
      (Subgroup.inclusion_injective hE_le_F)
  have hpow_le : p ^ 2 ≤ Nat.card F := by
    simpa [hEcard] using hE_card_le_F
  have hlogF_ge : 2 ≤ Nat.log p (Nat.card F) :=
    Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hpow_le
  have hlogF_eq : Nat.log p (Nat.card F) = 2 := le_antisymm hlogF_le hlogF_ge
  have hFcard : Nat.card F = p ^ 2 := by
    have hcard_pow := hFelem.card_eq_pow_finrank
    have hlog_fin := hFelem.log_card_eq_finrank
    rw [hcard_pow, ← hlog_fin, hlogF_eq]
  have hE_eq_F : E = F :=
    Subgroup.eq_of_le_of_card_ge hE_le_F (by rw [hEcard, hFcard])
  have hEstar : IsMaximalElementaryAbelian p E := by
    rw [hE_eq_F]
    exact hFstar
  exact ⟨by simpa [E] using hEcard, by simpa [E] using hEstar⟩

private theorem centralizer_eq_sup_inf_of_card_prime_inf_bot_index_prime
    [Finite R] {p : ℕ} [Fact p.Prime] {S T : Subgroup R} [T.Normal]
    (hScard : Nat.card S = p) (hST : S ⊓ T = ⊥) (hTindex : T.index = p) :
    Subgroup.centralizer (S : Set R) =
      S ⊔ (Subgroup.centralizer (S : Set R) ⊓ T) := by
  classical
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  let K : Subgroup R := C ⊓ T
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  have hSleC : S ≤ C := by
    intro s hs
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  let Ssub : Subgroup C := S.subgroupOf C
  let Ksub : Subgroup C := K.subgroupOf C
  have hSsub_card : Nat.card Ssub = p := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv).trans hScard
  have hSsub_inf : Ssub ⊓ Ksub = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change (x : R) = 1
    have hxST : (x : R) ∈ S ⊓ T := ⟨hx.1, hx.2.2⟩
    rwa [hST, Subgroup.mem_bot] at hxST
  have hSsub_le_center : Ssub ≤ Subgroup.center C := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp c.2 (s : R) hs).symm
  have hSsub_normal : Ssub.Normal := by
    refine { conj_mem := fun x hx g => ?_ }
    have hx_center : x ∈ Subgroup.center C := hSsub_le_center hx
    have hconj : g * x * g⁻¹ = x := by
      have hcomm := Subgroup.mem_center_iff.mp hx_center g
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hcomm]
        _ = x := by group
    rwa [hconj]
  have hrel_dvd : K.relIndex C ∣ p := by
    have hrel : K.relIndex C = T.relIndex C := by
      dsimp [K]
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right T C
    rw [hrel, ← hTindex]
    exact Subgroup.relIndex_dvd_index_of_normal T C
  have hrel_ne_one : K.relIndex C ≠ 1 := by
    intro hrel_one
    have hCleK : C ≤ K := Subgroup.relIndex_eq_one.mp hrel_one
    have hSleT : S ≤ T := by
      intro s hs
      exact (hCleK (hSleC hs)).2
    have hSbot : S = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro s hs
      have hsST : s ∈ S ⊓ T := ⟨hs, hSleT hs⟩
      rwa [hST] at hsST
    have hcard_one : Nat.card S = 1 := by rw [hSbot, Subgroup.card_bot]
    have hp_gt_one : 1 < p := (Fact.out : p.Prime).one_lt
    omega
  have hKrel : K.relIndex C = p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hrel_dvd with h | h
    · exact absurd h hrel_ne_one
    · exact h
  have hKsub_index : Ksub.index = p := by
    change K.relIndex C = p
    exact hKrel
  have hCcard : Nat.card C = p * Nat.card Ksub := by
    have hmul : Ksub.index * Nat.card Ksub = Nat.card C := Ksub.index_mul_card
    rw [hKsub_index] at hmul
    exact hmul.symm
  have hSup_card : Nat.card ↥(Ssub ⊔ Ksub) = p * Nat.card Ksub := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Ssub Ksub
    rw [← Subgroup.normal_mul Ssub Ksub, hSsub_inf, Subgroup.card_bot, hSsub_card,
      mul_one] at hcard
    simpa [SetLike.coe_sort_coe, Subgroup.coe_mul] using hcard
  have hSup_top : Ssub ⊔ Ksub = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    simpa [Subgroup.card_top, hCcard] using hSup_card
  calc
    C = (⊤ : Subgroup C).map C.subtype := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_map]
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
      · intro hx
        rw [Subgroup.mem_map] at hx
        rcases hx with ⟨x, _, rfl⟩
        exact x.2
    _ = (Ssub ⊔ Ksub).map C.subtype := by rw [hSup_top]
    _ = S ⊔ (C ⊓ T) := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hSleC,
        Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    _ = S ⊔ (Subgroup.centralizer (S : Set R) ⊓ T) := by rfl

/-- **BG Theorem 5.3(d) support**: under `r(R) ≥ 3` and the existence of some
`E ∈ ℰ²(R) ∩ ℰ*(R)` (so that Lemma 5.2 applies), every order-`p` subgroup `S` with
`r(C_R(S)) ≤ 2` satisfies `S ∩ T = 1` for `T = C_R(Ω₁(Z₂(R)))` (mmd L1862:
`SZ ⊄ T` together with `Z ≤ T` forces `S ∩ T = 1`). -/
private theorem inf_centralizer_omega1UpperCentralTwo_eq_bot_of_exists_maximalElementaryAbelian
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p)
    (hEx : ∃ E : Subgroup R, Nat.card E = p ^ 2 ∧ IsMaximalElementaryAbelian p E)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ := by
  classical
  let Z : Subgroup R := omega1Center R p
  let T : Subgroup R := Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)
  obtain ⟨Ew, hEwcard, hEwstar⟩ := hEx
  have hZcard : Nat.card Z = p := by
    dsimp [Z]
    exact (omega1Center_lt_and_card_eq_prime_of_maximalElementaryAbelian_card_prime_sq
      hpg h3 hEwcard hEwstar).2
  rcases sup_omega1Center_maximalElementaryAbelian_of_centralizer_pRank_le_two
      h3 hScard hSrank hZcard with ⟨hEcard, hEstar⟩
  let E : Subgroup R := S ⊔ Z
  have hEnot_le_T : ¬ E ≤ T := by
    dsimp [E, T]
    exact (lemma52 hp hpg h3 (S ⊔ omega1Center R p) hEcard hEstar).1
  by_contra hST_ne_bot
  have hSleT : S ≤ T := by
    dsimp [T] at hST_ne_bot ⊢
    exact le_of_inf_ne_bot_of_card_prime hScard hST_ne_bot
  have hZleT : Z ≤ T := by
    intro z hz
    dsimp [Z, T]
    exact center_le_centralizer_omega1UpperCentralTwo (omega1Center_le_center hz)
  have hEleT : E ≤ T := by
    dsimp [E]
    exact sup_le hSleT hZleT
  exact hEnot_le_T hEleT

private theorem inf_centralizer_omega1UpperCentralTwo_eq_bot_of_narrow
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    (h3 : 3 ≤ pRank R p) (hnarrow : IsNarrow p R)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ :=
  inf_centralizer_omega1UpperCentralTwo_eq_bot_of_exists_maximalElementaryAbelian
    hp hpg h3
    (exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
      hp hpg h3 (exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow))
    hScard hSrank

/-- **Rank-2 centralizer squeeze (general form)**: if `|S| = p`, `r(C_R(S)) ≤ 2`, and
`K ≤ C_R(S)` meets `S` trivially, then `K` is cyclic. Otherwise `K` contains an
`E_{p²}` (existence half of Lemma 4.5(a),
`S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`); joining it with the
order-`p` factor `S` — which centralizes it — yields an elementary abelian subgroup of
order `p³` inside `C_R(S)`, contradicting `r(C_R(S)) ≤ 2`.

Instances: `C_T(S)` for Thm 5.3(d) (mmd L1865-1867) and `C_H(R₀)` for Thm 5.5
(mmd L1901-1904). -/
theorem isCyclic_of_le_centralizer_of_inf_eq_bot_of_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    {S K : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2)
    (hK_le : K ≤ Subgroup.centralizer (S : Set R)) (hSK : S ⊓ K = ⊥) :
    IsCyclic ↥K := by
  classical
  let C : Subgroup R := Subgroup.centralizer (S : Set R)
  by_contra hnc
  -- `Ω₁`-level input: an `E_{p²}` inside the noncyclic `p`-group `K` (Lem 4.5(a) half).
  obtain ⟨E', hE'_elem, hE'_card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      (hpg.to_subgroup K) hp hnc
  -- Push `E'` down to a subgroup of `R`.
  let E : Subgroup R := E'.map K.subtype
  have hE_le_K : E ≤ K := Subgroup.map_subtype_le E'
  have hE_elem : E.IsElementaryAbelian p := hE'_elem.map K.subtype_injective
  have hE_card : Nat.card E = p ^ 2 := by
    have h := Nat.card_congr
      (Subgroup.equivMapOfInjective E' K.subtype K.subtype_injective).toEquiv
    dsimp [E]
    rw [← h]
    exact hE'_card
  have hS_elem : S.IsElementaryAbelian p := isElementaryAbelian_of_card_prime hScard
  -- `S` centralizes `E` since `E ≤ C_R(S)`.
  have hS_le_cent_E : S ≤ Subgroup.centralizer (E : Set R) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hK_le (hE_le_K he)) s hs).symm
  let F : Subgroup R := S ⊔ E
  have hF_elem : F.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.sup_of_le_centralizer hS_elem hE_elem hS_le_cent_E
  have hS_le_C : S ≤ C := by
    intro s hs
    dsimp [C]
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (hS_elem.comm ⟨t, ht⟩ ⟨s, hs⟩)
  have hE_le_C : E ≤ C := fun e he => hK_le (hE_le_K he)
  have hF_le_C : F ≤ C := sup_le hS_le_C hE_le_C
  have hSE_inf : S ⊓ E = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxSK : x ∈ S ⊓ K := ⟨hx.1, hE_le_K hx.2⟩
    rwa [hSK] at hxSK
  -- Compute `p³ ≤ |F|` inside the commutative group `F`.
  have hS_le_F : S ≤ F := le_sup_left
  have hE_le_F : E ≤ F := le_sup_right
  let Ssub : Subgroup F := S.subgroupOf F
  let Esub : Subgroup F := E.subgroupOf F
  have hSsub_card : Nat.card Ssub = p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_F).toEquiv).trans hScard
  have hEsub_card : Nat.card Esub = p ^ 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_F).toEquiv).trans hE_card
  have hsub_inf : Ssub ⊓ Esub = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    change (x : R) = 1
    have hxR : (x : R) ∈ S ⊓ E := ⟨hx.1, hx.2⟩
    rwa [hSE_inf, Subgroup.mem_bot] at hxR
  let : IsMulCommutative F := IsMulCommutative.of_comm hF_elem.comm
  have : Ssub.Normal := by infer_instance
  have hsup_card : Nat.card ↥(Ssub ⊔ Esub) = p * p ^ 2 := by
    have hcard := Subgroup.card_HK_mul_card_inf_eq_card_mul_card Ssub Esub
    rw [← Subgroup.normal_mul Ssub Esub, hsub_inf, Subgroup.card_bot, hSsub_card,
      hEsub_card, mul_one] at hcard
    simpa using hcard
  have hF_card_ge : p ^ 3 ≤ Nat.card F := by
    have hle : Nat.card ↥(Ssub ⊔ Esub) ≤ Nat.card (⊤ : Subgroup F) :=
      Subgroup.card_le_of_le le_top
    rw [Subgroup.card_top] at hle
    calc p ^ 3 = p * p ^ 2 := by ring
      _ = Nat.card ↥(Ssub ⊔ Esub) := hsup_card.symm
      _ ≤ Nat.card F := hle
  -- Transport into `C_R(S)` and contradict the rank bound.
  let Fsub : Subgroup C := F.subgroupOf C
  have hFsub_elem : Fsub.IsElementaryAbelian p :=
    IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hF_le_C).symm hF_elem
  have hFsub_card : Nat.card Fsub = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF_le_C).toEquiv
  have hlog_ge : 3 ≤ Nat.log p (Nat.card Fsub) := by
    rw [hFsub_card]
    exact Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt hF_card_ge
  have h3rank : 3 ≤ pRank C p := hlog_ge.trans (le_pRank Fsub hFsub_elem)
  have : (3 : ℕ) ≤ 2 := h3rank.trans hSrank
  omega

/-- **BG Theorem 5.3(d) core (cyclicity)**: `C_T(S) = C_R(S) ∩ T` is cyclic
(mmd L1865-1867); instance of the general rank-2 squeeze with `K := C_R(S) ⊓ T`. -/
private theorem isCyclic_inf_centralizer_omega1UpperCentralTwo_of_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R)
    {S : Subgroup R} (hScard : Nat.card S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2)
    (hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥) :
    IsCyclic ↥(Subgroup.centralizer (S : Set R) ⊓
      Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)) := by
  refine isCyclic_of_le_centralizer_of_inf_eq_bot_of_pRank_le_two hp hpg hScard hSrank
    inf_le_left ?_
  refine le_antisymm ?_ bot_le
  intro x hx
  have hxST : x ∈ S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) :=
    ⟨hx.1, hx.2.2⟩
  rwa [hST] at hxST

/-- **BG Theorem 5.3** (narrow 特徴づけ): 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`。すると
`R` が narrow ⇔ `ℰ²(R) ∩ ℰ*(R) ≠ ∅` (位数 `p²` の elem-ab で位数 `p³` の elem-ab に含まれない
ものが存在)。

mmd L1838-1873。⇒ は narrow witness `R₀` から `r(C_R(R₀)) ≤ 2`
(`exists_card_prime_centralizer_pRank_le_two_of_narrow`) を経て `SZ ∈ ℰ²∩ℰ*` を構成
(`exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two`)。
⇐ は `E = Z×S` 分解で位数 `p` の `S` (`r(C_R(S)) ≤ 2`) を取り、Thm 5.3(d) の分解
`C_R(S) = S × C_T(S)`, `C_T(S)` cyclic から narrow witness を得る。 -/
theorem narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    IsNarrow p R ↔
      ∃ E : Subgroup R, Nat.card ↥E = p ^ 2 ∧ IsMaximalElementaryAbelian p E := by
  constructor
  · intro hnarrow
    exact exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
      hp hpg h3 (exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow)
  · intro hEx
    obtain ⟨S, hScard, hSrank⟩ :=
      exists_card_prime_centralizer_pRank_le_two_of_maximalElementaryAbelian_card_prime_sq
        hpg h3 hEx
    have hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ :=
      inf_centralizer_omega1UpperCentralTwo_eq_bot_of_exists_maximalElementaryAbelian
        hp hpg h3 hEx hScard hSrank
    obtain ⟨Ew, hEwcard, hEwstar⟩ := hEx
    have hTindex : (Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)).index = p :=
      (lemma52 hp hpg h3 Ew hEwcard hEwstar).2.2
    have hdecomp :=
      centralizer_eq_sup_inf_of_card_prime_inf_bot_index_prime hScard hST hTindex
    have hcyc :=
      isCyclic_inf_centralizer_omega1UpperCentralTwo_of_centralizer_pRank_le_two
        hp hpg hScard hSrank hST
    refine Or.inr ⟨S, Subgroup.centralizer (S : Set R) ⊓
      Subgroup.centralizer (omega1UpperCentralTwo R p : Set R), hScard, hcyc, ?_, hdecomp⟩
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxST : x ∈ S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) :=
      ⟨hx.1, hx.2.2⟩
    rwa [hST] at hxST

/-- **BG Theorem 5.3(d)** (narrow の centralizer 分解, 下流 App.E E.3 が cite): narrow な
有限 `p`-群 `R` (`r(R)≥3`) と位数 `p` の `S ≤ R` で `r(C_R(S)) ≤ 2` なら、`T = C_R(Ω₁(Z₂(R)))`
に対し `C_T(S)` は cyclic, `S ∩ R' = S ∩ T = 1`, かつ `C_R(S) = S × C_T(S)`。

mmd L1859-1867。`C_T(S) = C_R(S) ⊓ T`。内部直積 `C_R(S)=S×C_T(S)` は
`S ⊓ T = ⊥` と `centralizer S = S ⊔ (C_R(S)⊓T)` で表す。 -/
theorem narrow_centralizer_decomp [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) (hnarrow : IsNarrow p R)
    (S : Subgroup R) (hScard : Nat.card ↥S = p)
    (hSrank : pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2) :
    IsCyclic ↥(Subgroup.centralizer (S : Set R) ⊓
        Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)) ∧
    S ⊓ commutator R = ⊥ ∧
    S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ ∧
    Subgroup.centralizer (S : Set R) =
      S ⊔ (Subgroup.centralizer (S : Set R) ⊓
        Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)) := by
  classical
  have hST : S ⊓ Subgroup.centralizer (omega1UpperCentralTwo R p : Set R) = ⊥ :=
    inf_centralizer_omega1UpperCentralTwo_eq_bot_of_narrow hp hpg h3 hnarrow hScard hSrank
  obtain ⟨Ew, hEwcard, hEwstar⟩ :=
    exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
      hp hpg h3 (exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow)
  have hTindex : (Subgroup.centralizer (omega1UpperCentralTwo R p : Set R)).index = p :=
    (lemma52 hp hpg h3 Ew hEwcard hEwstar).2.2
  exact ⟨isCyclic_inf_centralizer_omega1UpperCentralTwo_of_centralizer_pRank_le_two
      hp hpg hScard hSrank hST,
    inf_commutator_eq_bot_of_inf_centralizer_omega1UpperCentralTwo_eq_bot hST,
    hST,
    centralizer_eq_sup_inf_of_card_prime_inf_bot_index_prime hScard hST hTindex⟩

/-- **BG Corollary 5.4**: 奇素数 `p`, 有限 `p`-群 `R`, `r(R) ≥ 3`。すると `R` が narrow ⇔
位数 `p` の `S ≤ R` で `r(C_R(S)) ≤ 2` となるものが存在。

mmd L1875-1879。Thm 5.3 + `S↦SZ ∈ ℰ²∩ℰ*` から。 -/
theorem narrow_iff_exists_card_prime_centralizer_pRank_le_two
    [Finite R] {p : ℕ} [Fact p.Prime] (hp : Odd p) (hpg : IsPGroup p R) (h3 : 3 ≤ pRank R p) :
    IsNarrow p R ↔
      ∃ S : Subgroup R, Nat.card ↥S = p ∧
        pRank ↥(Subgroup.centralizer (S : Set R)) p ≤ 2 := by
  constructor
  · intro hnarrow
    exact exists_card_prime_centralizer_pRank_le_two_of_narrow hp hpg h3 hnarrow
  · intro h
    exact (narrow_iff_exists_maximalElementaryAbelian_card_prime_sq hp hpg h3).2
      (exists_maximalElementaryAbelian_card_prime_sq_of_card_prime_centralizer_pRank_le_two
        hp hpg h3 h)

end OddOrder.BG.Ch1.S05


