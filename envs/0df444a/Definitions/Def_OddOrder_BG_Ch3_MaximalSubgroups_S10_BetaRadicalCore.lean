-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadicalCore
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadicalCore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:55:46.973845+00:00
-- url     : https://prove2.me/theorems/3e008c13-d811-4d18-8c85-dd57d81d8d04
-- title:
--   BG §10: the $\beta$-radical spine, core (Theorem 10.6, Corollary 10.7, Lemma 10.8)
-- statement:
--   Formalizes the first part of the $\beta$-radical spine of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §10: Theorem 10.6, Corollary 10.7 and Lemma 10.8. It is the upstream file of a three-way split, followed by the Proposition 10.14 file and then the Corollary 10.9 / Proposition 10.10 file.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 30 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadicalCore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadicalCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructure
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_ForwardFromKeystone
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLengthTransfer

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- **BG Theorem 10.6** (mmd L2779): `p` prime、`H` を `G` の真部分群とすると、`H` は `p`-length
one を持つ。`M ∈ ℳ(H)` を取り `M` で示す: `r_p(M) ≤ 2` は Thm 4.18、`≥ 3` は Thm 10.2 +
Lem 6.3/10.4 + Thm 3.6。 -/
theorem proper_hasPLengthOne [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (H : Subgroup G) (hH : H < ⊤) :
    Ch1.hasPLengthOne p ↥H := by
  classical
  -- Reduce to a maximal subgroup `M ⊇ H`: `p`-length one passes to subgroups (Lemma 1.21(a)).
  obtain ⟨M, hMco, hHM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom H).resolve_left hH.ne
  have hM : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMco
  suffices hMpl : Ch1.hasPLengthOne p ↥M by
    exact Ch1.hasPLengthOne_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHM)
      (Ch1.hasPLengthOne_subgroup hMpl (H.subgroupOf M))
  by_cases hpα : p ∈ alpha M
  · -- `r_p(M) ≥ 3` branch (`p ∈ α(M)`): the representation-theory keystone (BG Theorem 3.6).
    have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    have hoddM : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
    have hp_dvd_M : p ∣ Nat.card ↥M :=
      (Nat.mem_primeFactors.mp (alpha_subset_primeFactors M hpα)).2.1
    have hMnt : Nontrivial ↥M := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      exact lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd Nat.card_pos hp_dvd_M)
    -- `N := M_α` viewed inside `↥M`: a normal Hall `α(M)`-subgroup.
    set N : Subgroup ↥M := (Malpha M).subgroupOf M with hN_def
    have hNnorm : N.Normal := by rw [hN_def]; infer_instance
    have hHallN : Ch03.IsHallSubgroup (alpha M) N := by
      rw [hN_def]; exact Malpha_subgroupOf_isHall_of_isHall (Malpha_isHall hG hM)
    have hcoprime : Nat.Coprime (Nat.card ↥N) N.index := hHallN.coprime_index
    -- `N ≤ ↥M'` (Theorem 10.2: `M_α ⊆ M_σ ⊆ M'`); and `↥M'` is proper (solvable, nontrivial).
    have hN_der : N ≤ commutator ↥M := by
      have h1 : Malpha M ≤ derivedInG M :=
        (Malpha_le_Msigma hG hM).trans (Msigma_le_derived hG hM)
      rw [derivedInG] at h1
      rw [hN_def, Subgroup.subgroupOf]
      calc (Malpha M).comap M.subtype
          ≤ ((commutator ↥M).map M.subtype).comap M.subtype := Subgroup.comap_mono h1
        _ = commutator ↥M :=
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
    have hN_lt : N < ⊤ :=
      lt_of_le_of_lt hN_der (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥M))
    -- `p ∣ |N|` (Hall + `p ∈ α(M)`), hence `M_α ≠ 1`.
    have hp_dvd_N : p ∣ Nat.card ↥N := by
      have hp_prod : p ∣ Nat.card ↥N * N.index := by
        rw [Subgroup.card_mul_index]; exact hp_dvd_M
      rcases (Nat.Prime.dvd_mul Fact.out).mp hp_prod with h | h
      · exact h
      · exact absurd hpα (hHallN.index_no_pi p
          (Nat.mem_primeFactors.mpr ⟨Fact.out, h, Subgroup.index_ne_zero_of_finite⟩))
    have hMα_ne : Malpha M ≠ ⊥ := by
      intro hbot
      have hN_bot : N = ⊥ := by rw [hN_def, hbot]; simp
      rw [hN_bot, Subgroup.card_bot] at hp_dvd_N
      exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hp_dvd_N)
    -- Schur–Zassenhaus: a complement `K` to `N` in `↥M`; `K ≠ ⊥` (else `N = ⊤`).
    obtain ⟨K, hKcompl⟩ := Subgroup.exists_right_complement'_of_coprime hcoprime
    have hK_ne : K ≠ ⊥ := by
      intro hKbot
      have hsup := hKcompl.isCompl.sup_eq_top
      rw [hKbot, sup_bot_eq] at hsup
      exact hN_lt.ne hsup
    -- Choose a prime `q ∈ π(K/K')` (`K` is solvable and nontrivial, hence not perfect).
    have hKnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne
    have hKsolv : Group.IsSolvable ↥K :=
      Group.isSolvable_of_isSolvable_injective K.subtype_injective
    have hidx_ne1 : (commutator ↥K).index ≠ 1 := fun h =>
      (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)).ne
        (Subgroup.index_eq_one.mp h)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hidx_ne1
    have hqK' : q ∈ ((commutator ↥K).index).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Subgroup.index_ne_zero_of_finite⟩
    -- Lemma 10.4(b): an order-`q` element `x ∈ K` with `C_{M_α}(⟨x⟩)` a `Z`-group.
    obtain ⟨x, hxK, hxord, hxZ⟩ :=
      exists_prime_orderOf_zgroupCentralizer_of_complement hG hM hMα_ne hKcompl hq hqK'
    -- Theorem 3.6: `⁅N, K⁆` has `p`-length one (with `R₀ = ⟨x⟩`).
    have hR₀le : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
    have hR₀prime : (Nat.card ↥(Subgroup.zpowers x)).Prime := by
      rw [Nat.card_zpowers, hxord]; exact hq
    have hpl_comm : Ch1.hasPLengthOne p ↥⁅N, K⁆ :=
      pLengthOne_commutator_of_zgroupCentralizer hMsolv hoddM hNnorm hcoprime hKcompl
        hR₀le hR₀prime hxZ p
    -- Lemma 6.3(a): `⁅N, K⁆ = N` (since `N ≤ ↥M'`).
    rw [Ch1.S06.commutator_eq_self_of_isComplement'_le_commutator hKcompl hN_der] at hpl_comm
    -- Lift `N`'s `p`-length one to `↥M` along the `p'`-quotient `↥M/N` (`p ∈ α(M)`).
    have hquot : ¬ p ∣ Nat.card (↥M ⧸ N) := fun hdvd => hHallN.index_no_pi p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpα
    exact Ch1.hasPLengthOne_of_normal_pPrime_quotient hquot hpl_comm
  · -- `r_p(M) ≤ 2` branch (`p ∉ α(M)`): BG Theorem 4.18 (landed).
    exact maximal_hasPLengthOne_of_not_mem_alpha hG hM hpα

/-- A Sylow `r`-subgroup `P` of `G` contained in `K ≤ G` restricts to a Sylow `r`-subgroup of
`↥K` with carrier `P.subgroupOf K` (local replica of the private `S07`/`S10_LocalLemmas` helper). -/
theorem exists_sylow_subgroupOf_of_le {r : ℕ} [Fact r.Prime] [Finite G] (P : Sylow r G)
    {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) :
    ∃ Q : Sylow r ↥K, (Q : Subgroup ↥K) = (P : Subgroup G).subgroupOf K := by
  have hpg : IsPGroup r ↥((P : Subgroup G).subgroupOf K) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]; exact hn)
  have hidx : ¬ r ∣ ((P : Subgroup G).subgroupOf K).index := fun h =>
    P.not_dvd_index (dvd_trans h (Subgroup.relIndex_dvd_index_of_le hPK))
  exact ⟨hpg.toSylow hidx, hpg.toSylow_coe hidx⟩

/-- **Shared setup for Corollary 10.7** (mmd L2795): a *nontrivial* Sylow `p`-subgroup `P` of `G`
lies in some maximal subgroup `M` with `N_G(P) ⊆ M`; consequently `p ∈ σ(M)` and `P ≤ M`. Then
`↥M` has `p`-length one by Theorem 10.6, so Lemma 6.6 (applied inside `↥M`) controls `P`. -/
private theorem exists_sigma_maximal_of_sylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hPne : (P : Subgroup G) ≠ ⊥) :
    ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M ∧
      p ∈ sigma M ∧ (P : Subgroup G) ≤ M := by
  -- `N_G(P) < ⊤` (else `P ⊴ G`, contradicting simplicity / nonsolvability).
  have hNlt : Subgroup.normalizer ((P : Subgroup G) : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hPnormal : (P : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hPnormal with hbot | htop'
    · exact hPne hbot
    · have hsolv : Group.IsSolvable ↥(P : Subgroup G) := by
        have := (P.isPGroup').isNilpotent; infer_instance
      rw [htop'] at hsolv
      have := hsolv
      exact hG.notSolvable (Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv (G := G)).toMonoidHom) (Subgroup.topEquiv (G := G)).surjective)
  obtain ⟨M, hMco, hNM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer ((P : Subgroup G) : Set G))).resolve_left
      hNlt.ne
  have hM : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMco
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
  refine ⟨M, hM, hNM, ?_, hPM⟩
  rw [mem_sigma_iff]
  have hp_dvd_M : p ∣ Nat.card ↥M := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hPne (Subgroup.card_eq_one.mp hn)
    exact (hn ▸ dvd_pow_self p hn0).trans (Subgroup.card_dvd_of_le hPM)
  refine ⟨Nat.mem_primeFactors.mpr ⟨Fact.out, hp_dvd_M, Nat.card_pos.ne'⟩, ?_⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_subgroupOf_of_le P hPM
  exact ⟨Q, by rw [hQ, Subgroup.map_subgroupOf_eq_of_le hPM]; exact hNM⟩

/-- `derivedInG H = ⁅H, H⁆` as subgroups of `G`. -/
private theorem derivedInG_eq_commutator (H : Subgroup G) :
    derivedInG H = ⁅H, H⁆ := by
  rw [derivedInG, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

/-- `Omega` is natural along a multiplicative equivalence. -/
private theorem omega_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (p n : ℕ) :
    (Omega A p n).map e.toMonoidHom = Omega B p n := by
  rw [Omega, MonoidHom.map_closure]
  congr 1
  ext h
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨g, hg, rfl⟩; rw [← map_pow, hg, map_one]
  · intro hh; exact ⟨e.symm h, by rw [← map_pow, hh, map_one], e.apply_symm_apply h⟩

/-- An element centralizing `Q` fixes `Q` under conjugation: `c ∈ C_G(Q) ⟹ conj c • Q = Q`. -/
private theorem conj_smul_eq_of_mem_centralizer {H : Type*} [Group H] {Q : Subgroup H} {c : H}
    (hc : c ∈ Subgroup.centralizer (Q : Set H)) : MulAut.conj c • Q = Q := by
  ext z
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hz
    have h := Subgroup.mem_centralizer_iff.mp hc _ hz
    have hzeq : c⁻¹ * z * c = z := by
      have hcc : c⁻¹ * z * c * c = z * c := by rw [h]; group
      exact mul_right_cancel hcc
    rw [hzeq] at hz; exact hz
  · intro hz
    have h := Subgroup.mem_centralizer_iff.mp hc z hz
    have hzeq : c⁻¹ * z * c = z := by rw [mul_assoc, h]; group
    rw [hzeq]; exact hz

/-- Conjugating a subgroup `Q ≤ M` by an element `a ∈ M` stays inside `M`. -/
private theorem conj_smul_le_of_mem {M Q : Subgroup G} (hQM : Q ≤ M) {a : G} (haM : a ∈ M) :
    MulAut.conj a • Q ≤ M := by
  rintro w hw
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hw
  have hwe : w = a * (a⁻¹ * w * a) * a⁻¹ := by group
  rw [hwe]
  exact M.mul_mem (M.mul_mem haM (hQM hw)) (M.inv_mem haM)

/-- Conjugation preserves the cardinality of a subgroup. -/
private theorem card_conj_smul (g : G) (H : Subgroup G) :
    Nat.card ↥(MulAut.conj g • H) = Nat.card ↥H := by
  rw [show MulAut.conj g • H = H.map (MulAut.conj g : G →* G) from rfl]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- `conj n • Q = Q ⟹ n ∈ N_G(Q)`. -/
private theorem mem_setNormalizer_of_conj_smul_eq {Q : Subgroup G} {n : G}
    (h : MulAut.conj n • Q = Q) : n ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro z
  change z ∈ Q ↔ n * z * n⁻¹ ∈ Q
  constructor
  · intro hz
    have hmem : n * z * n⁻¹ ∈ MulAut.conj n • Q :=
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr (by
        rw [MulAut.smul_def, MulAut.conj_inv_apply, show n⁻¹ * (n * z * n⁻¹) * n = z from by group]
        exact hz)
    rwa [h] at hmem
  · intro hz
    have hz' : n * z * n⁻¹ ∈ MulAut.conj n • Q := by rwa [h]
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at hz'
    rwa [show n⁻¹ * (n * z * n⁻¹) * n = z from by group] at hz'

/-- `n ∈ N_G(Q) ⟹ conj n • Q = Q`. -/
theorem conj_smul_eq_self_of_mem_setNormalizer {Q : Subgroup G} {n : G}
    (h : n ∈ Subgroup.normalizer (Q : Set G)) : MulAut.conj n • Q = Q := by
  ext z
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  rw [Subgroup.mem_set_normalizer_iff] at h
  have hz := h (n⁻¹ * z * n)
  rwa [show n * (n⁻¹ * z * n) * n⁻¹ = z from by group] at hz

/-- `Subgroup.center` is natural along a multiplicative equivalence. -/
private theorem center_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext b
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    intro b'
    calc b' * e z = e (e.symm b') * e z := by rw [e.apply_symm_apply]
      _ = e (e.symm b' * z) := by rw [map_mul]
      _ = e (z * e.symm b') := by rw [hz (e.symm b')]
      _ = e z * e (e.symm b') := by rw [map_mul]
      _ = e z * b' := by rw [e.apply_symm_apply]
  · intro hb
    refine ⟨e.symm b, fun a => e.injective ?_, e.apply_symm_apply b⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hb (e a)

/-- **Corollary 10.7(a)** (mmd L2796): if `V` is a complement to `P ∈ Syl_p(G)` in `N_G(P)`
(`P ⊓ V = ⊥`, `P ⊔ V = N_G(P)`), then `P = ⁅P, V⁆` and `P ≤ N_G(P)'`.

Take a maximal `M ⊇ N_G(P)` (so `p ∈ σ(M)` and `↥M` has `p`-length one by Theorem 10.6). Lemma
6.6(2) inside `↥M` gives `P ≤ ⁅N_G(P), N_G(P)⁆ = N_G(P)'`; Lemma 6.3(a) inside `↥N_G(P)` (where
`P` is normal, `V` a complement, and `P ≤ ↥N_G(P)'`) then upgrades this to `⁅P, V⁆ = P`. -/
private theorem sylow_structure_a [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {V : Subgroup G}
    (hV : V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hPVinf : (P : Subgroup G) ⊓ V = ⊥)
    (hPVsup : (P : Subgroup G) ⊔ V = Subgroup.normalizer ((P : Subgroup G) : Set G)) :
    (P : Subgroup G) = ⁅(P : Subgroup G), V⁆ ∧
      (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
  classical
  set N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G) with hNdef
  by_cases hPne : (P : Subgroup G) = ⊥
  · -- Degenerate: `P = ⊥`, so `⁅⊥, V⁆ = ⊥` and `⊥ ≤ _`.
    exact ⟨by rw [hPne]; simp, hPne ▸ bot_le⟩
  -- Main case: pull in a maximal `M ⊇ N_G(P)` with `p ∈ σ(M)`.
  obtain ⟨M, hM, hNM, hpσ, hPM⟩ := exists_sigma_maximal_of_sylow hG P hPne
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMlt : M < ⊤ := (mem_maximalSubgroups.mp hM).lt_top
  have hpl1 : Ch1.hasPLengthOne p ↥M := proper_hasPLengthOne hG M hMlt
  -- `P` restricts to a Sylow `p`-subgroup `Q` of `↥M`.
  obtain ⟨Q, hQ⟩ := exists_sylow_subgroupOf_of_le P hPM
  have hQder : (Q : Subgroup ↥M) ≤ commutator ↥M := by
    have h := sylow_le_derived_of_mem_sigma hG hM hpσ Q
    rwa [derivedInG, Subgroup.map_le_map_iff_of_injective M.subtype_injective] at h
  -- `(Q).map = P` and `N_{↥M}(Q).map = N_G(P)` (since `N_G(P) ≤ M`).
  have hQmapP : (Q : Subgroup ↥M).map M.subtype = (P : Subgroup G) := by
    rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPM]
  have hnormmap : (Subgroup.normalizer ((Q : Subgroup ↥M) : Set ↥M)).map M.subtype = N := by
    have h1 : Subgroup.normalizer ((Q : Subgroup ↥M) : Set ↥M) = N.subgroupOf M := by
      rw [hQ, ← Subgroup.subgroupOf_normalizer_eq hPM, hNdef]
    rw [h1, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNM]
  -- Lemma 6.6(2) inside `↥M`: `Q ≤ N_{↥M}(Q)'`, push to `G`: `P ≤ N_G(P)'`.
  have hQcomm := Ch1.S06.sylow_le_commutator_normalizer_of_le_commutator Q hpl1 hQder
  have hP_der : (P : Subgroup G) ≤ derivedInG N := by
    have hmap := Subgroup.map_mono (f := M.subtype) hQcomm
    rwa [Subgroup.map_commutator, hQmapP, hnormmap, ← derivedInG_eq_commutator] at hmap
  refine ⟨?_, hP_der⟩
  -- `⁅P, V⁆ = P` via Lemma 6.3(a) inside `↥N_G(P)`.
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hVN : V ≤ N := hV
  have hNlt : N < ⊤ := lt_of_le_of_lt hNM hMlt
  have hNsolv : Group.IsSolvable ↥N := hG.isSolvable_of_lt_top N hNlt
  have hPsubN_normal : ((P : Subgroup G).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr hNdef.le
  have hinf : ((P : Subgroup G).subgroupOf N) ⊓ (V.subgroupOf N) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hxinf : (x : G) ∈ (P : Subgroup G) ⊓ V := ⟨hx.1, hx.2⟩
    rw [hPVinf, Subgroup.mem_bot] at hxinf
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxinf
  have hmulu : (↑((P : Subgroup G).subgroupOf N) : Set ↥N) * (↑(V.subgroupOf N) : Set ↥N)
      = Set.univ := by
    rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hPN hVN, hPVsup, Subgroup.subgroupOf_self,
      Subgroup.coe_top]
  have hCompl : ((P : Subgroup G).subgroupOf N).IsComplement' (V.subgroupOf N) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) hmulu
  have hPsubN_comm : (P : Subgroup G).subgroupOf N ≤ commutator ↥N := by
    have h := hP_der
    rw [derivedInG] at h
    calc (P : Subgroup G).subgroupOf N
        ≤ ((commutator ↥N).map N.subtype).comap N.subtype := Subgroup.comap_mono h
      _ = commutator ↥N := Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  have hcomm63 :=
    Ch1.S06.commutator_eq_self_of_isComplement'_le_commutator hCompl hPsubN_comm
  have hmap := congrArg (Subgroup.map N.subtype) hcomm63
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hPN, inf_eq_left.mpr hVN] at hmap
  exact hmap.symm

/-- **Corollary 10.7(b)** (mmd L2787): if `r(P) ≤ 2` then `P` is abelian, or `P` is the central
product of a nonabelian exponent-`p` group `P₁` of order `p³` and a cyclic `P₂` with
`Ω₁(P₂) = Z(P₁)`. The coprime conjugation action `φ : V →* MulAut P` (with `V` a complement to `P`
in `N_G(P)`) satisfies `[P, V] = P` (part (a)), i.e. `actionCommutator φ = ⊤`; Blackburn's
classification (Theorem 4.16) then yields the dichotomy, which we transport from `↥P` to `G`. -/
private theorem sylow_structure_b [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {V : Subgroup G}
    (hV : V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hPVinf : (P : Subgroup G) ⊓ V = ⊥)
    (hPVsup : (P : Subgroup G) ⊔ V = Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hrank : rank ↥(P : Subgroup G) ≤ 2) :
    IsMulCommutative (P : Subgroup G) ∨
      ∃ P₁ P₂ : Subgroup G, P₁ ≤ (P : Subgroup G) ∧ P₂ ≤ (P : Subgroup G) ∧
        IsExpPExtraspecial p ↥P₁ ∧ Nat.card ↥P₁ = p ^ 3 ∧ IsCyclic ↥P₂ ∧
        (Omega ↥P₂ p 1).map P₂.subtype = (Subgroup.center ↥P₁).map P₁.subtype ∧
        IsCentralProduct (P : Subgroup G) P₁ P₂ := by
  classical
  by_cases hPne : (P : Subgroup G) = ⊥
  · -- Degenerate: trivial `P` is abelian.
    refine Or.inl ?_
    rw [hPne]
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  -- Coprime conjugation action `φ : ↥V →* MulAut ↥P`.
  set φ : ↥V →* MulAut ↥(P : Subgroup G) :=
    (P : Subgroup G).normalizerMonoidHom.comp (Subgroup.inclusion hV) with hφ_def
  have hφcoe : ∀ (v : ↥V) (y : ↥(P : Subgroup G)),
      (P : Subgroup G).subtype ((φ v) y) = (v : G) * (P : Subgroup G).subtype y * (v : G)⁻¹ :=
    fun v y => rfl
  -- `actionCommutator φ = ⊤`, i.e. `[P, V] = P` (part (a)).
  obtain ⟨hPVeq, -⟩ := sylow_structure_a hG P hV hPVinf hPVsup
  have hge : ⁅(P : Subgroup G), V⁆ ≤ (Ch04.actionCommutator φ).map (P : Subgroup G).subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_map]
    refine ⟨(⟨g₁, hg₁⟩ : ↥(P : Subgroup G)) * (φ ⟨g₂, hg₂⟩) (⟨g₁, hg₁⟩)⁻¹,
      Subgroup.subset_closure ⟨_, _, rfl⟩, ?_⟩
    rw [map_mul, hφcoe ⟨g₂, hg₂⟩ (⟨g₁, hg₁⟩)⁻¹, commutatorElement_def]
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv]
    group
  have hmapeq : (Ch04.actionCommutator φ).map (P : Subgroup G).subtype = (P : Subgroup G) :=
    le_antisymm (Subgroup.map_subtype_le _) ((le_of_eq hPVeq).trans hge)
  have hactTop : Ch04.actionCommutator φ = ⊤ := by
    apply Subgroup.map_injective (P : Subgroup G).subtype_injective
    rw [hmapeq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- Blackburn 4.16 hypotheses.
  have hPnt : Nontrivial ↥(P : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
  have hpdvdG : p ∣ Nat.card G := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hn0 : n ≠ 0 := fun h => hPne (Subgroup.card_eq_one.mp (by rw [hn, h, pow_zero]))
    exact (hn ▸ dvd_pow_self p hn0).trans (Subgroup.card_subgroup_dvd_card _)
  have hp_odd : Odd p := hG.odd.of_dvd_nat hpdvdG
  have hAodd : Odd (Nat.card ↥V) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card V)
  have hrank2 : pRank ↥(P : Subgroup G) p ≤ 2 := le_trans (pRank_le_rank p) hrank
  -- Coprimality `(|V|, |P|) = 1`: `|V|` is the index of the Sylow `p`-subgroup `P` in `N_G(P)`.
  have hcop : Nat.Coprime (Nat.card ↥V) (Nat.card ↥(P : Subgroup G)) := by
    set N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G) with hNdef
    have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
    have hVN : V ≤ N := hV
    have hPsubN_normal : ((P : Subgroup G).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr hNdef.le
    have hinf : ((P : Subgroup G).subgroupOf N) ⊓ (V.subgroupOf N) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
      have hxinf : (x : G) ∈ (P : Subgroup G) ⊓ V := ⟨hx.1, hx.2⟩
      rw [hPVinf, Subgroup.mem_bot] at hxinf
      rw [Subgroup.mem_bot]; exact Subtype.ext hxinf
    have hmulu : (↑((P : Subgroup G).subgroupOf N) : Set ↥N) * (↑(V.subgroupOf N) : Set ↥N)
        = Set.univ := by
      rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hPN hVN, hPVsup,
          Subgroup.subgroupOf_self,
        Subgroup.coe_top]
    have hCompl : ((P : Subgroup G).subgroupOf N).IsComplement' (V.subgroupOf N) :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) hmulu
    -- `|V| = [N : P]`, which is coprime to `p` (Sylow index).
    obtain ⟨PN, hPNeq⟩ := exists_sylow_subgroupOf_of_le P hPN
    have hVcard : Nat.card ↥V = (PN : Subgroup ↥N).index := by
      rw [hPNeq, hCompl.symm.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv]
    have hpV : ¬ p ∣ Nat.card ↥V := by rw [hVcard]; exact PN.not_dvd_index
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpV).symm).pow_right n
  -- Blackburn 4.16: the dichotomy on `↥P`.
  obtain ⟨_, hcase⟩ :=
    OddOrder.BG.Ch1.S04.blackburnRankTwoClassification hp_odd P.isPGroup' hcop hrank2 hactTop hAodd
  rcases hcase with hcomm | hcp
  · exact Or.inl hcomm
  right
  obtain ⟨R₁, R₂, hcp', hR₁nc, hR₁card, hR₁exp, hR₂cyc, hΩeq⟩ := hcp
  -- Transport the factors `R₁, R₂` from `↥P` to `G`.
  set P₁ : Subgroup G := R₁.map (P : Subgroup G).subtype with hP₁def
  set P₂ : Subgroup G := R₂.map (P : Subgroup G).subtype with hP₂def
  set ι₁ : ↥R₁ ≃* ↥P₁ :=
    Subgroup.equivMapOfInjective R₁ (P : Subgroup G).subtype (P : Subgroup G).subtype_injective
    with hι₁
  set ι₂ : ↥R₂ ≃* ↥P₂ :=
    Subgroup.equivMapOfInjective R₂ (P : Subgroup G).subtype (P : Subgroup G).subtype_injective
    with hι₂
  have hcomp₁ : (P : Subgroup G).subtype.comp R₁.subtype = P₁.subtype.comp ι₁.toMonoidHom := by
    ext x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hι₁, MulEquiv.coe_toMonoidHom]
    exact (Subgroup.coe_equivMapOfInjective_apply R₁ (P : Subgroup G).subtype
      (P : Subgroup G).subtype_injective x).symm
  have hcomp₂ : (P : Subgroup G).subtype.comp R₂.subtype = P₂.subtype.comp ι₂.toMonoidHom := by
    ext x
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hι₂, MulEquiv.coe_toMonoidHom]
    exact (Subgroup.coe_equivMapOfInjective_apply R₂ (P : Subgroup G).subtype
      (P : Subgroup G).subtype_injective x).symm
  have hP₁card : Nat.card ↥P₁ = p ^ 3 := (Nat.card_congr ι₁.toEquiv).symm.trans hR₁card
  have hP₁exp : Monoid.exponent ↥P₁ = p := (Monoid.exponent_eq_of_mulEquiv ι₁).symm.trans hR₁exp
  have hP₁nc : ¬ IsMulCommutative ↥P₁ := by
    intro h
    exact hR₁nc ⟨⟨fun a b => ι₁.injective (by
      rw [map_mul, map_mul]; exact h.is_comm.comm (ι₁ a) (ι₁ b))⟩⟩
  have hR₁es : IsExtraspecial p ↥R₁ :=
    OddOrder.BG.Ch1.S04.isExtraspecial_of_noncomm_card_prime_cube_exp_prime hR₁card hR₁nc hR₁exp
  have hP₁es : IsExtraspecial p ↥P₁ :=
    OddOrder.BG.Ch1.S04.isExtraspecial_of_noncomm_card_prime_cube_exp_prime hP₁card hP₁nc hP₁exp
  refine ⟨P₁, P₂, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ⟨hP₁es, hP₁exp⟩, hP₁card,
    ?_, ?_, ?_⟩
  · -- `IsCyclic ↥P₂` by transport along `ι₂`.
    have := hR₂cyc
    exact isCyclic_of_surjective ι₂.toMonoidHom ι₂.surjective
  · -- `Ω₁(P₂) = Z(P₁)` (in `G`), transported from Blackburn's `↥P`-level equality.
    have key := congrArg (Subgroup.map (P : Subgroup G).subtype) hΩeq
    rw [Subgroup.map_map, Subgroup.map_map, hcomp₂, hcomp₁, ← Subgroup.map_map,
      ← Subgroup.map_map, omega_map_mulEquiv, hR₁es.commutator_eq_center,
      center_map_mulEquiv] at key
    exact key
  · -- `IsCentralProduct P P₁ P₂` by mapping the `↥P`-level central product.
    refine ⟨?_, ?_⟩
    · have h := congrArg (Subgroup.map (P : Subgroup G).subtype) hcp'.sup_eq
      rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.map_sup] at h
    · have h := congrArg (Subgroup.map (P : Subgroup G).subtype) hcp'.commutator_eq_bot
      rwa [Subgroup.map_commutator, Subgroup.map_bot] at h

/-- **Corollary 10.7(c)** (mmd L2801): `Q ≤ P`, `x ∈ G`, `Q^x ≤ P ⟹ Q^x = Q^y` for some
`y ∈ N_G(P)`. Theorem 10.1(a) replaces `x` by some `m ∈ M` (`Q^x = Q^m`); Lemma 6.6(3) inside
`↥M` then produces `g ∈ N_{↥M}(P)` with `Q^m = Q^g`. -/
private theorem sylow_structure_c [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (Q : Subgroup G) (hQP : Q ≤ (P : Subgroup G)) (x : G)
    (hxQ : MulAut.conj x • Q ≤ (P : Subgroup G)) :
    ∃ y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      MulAut.conj x • Q = MulAut.conj y • Q := by
  by_cases hQbot : Q = ⊥
  · exact ⟨1, Subgroup.one_mem _, by rw [hQbot]; simp⟩
  by_cases hPne : (P : Subgroup G) = ⊥
  · exact absurd (le_bot_iff.mp (hPne ▸ hQP)) hQbot
  obtain ⟨M, hM, hNM, hpσ, hPM⟩ := exists_sigma_maximal_of_sylow hG P hPne
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMlt : M < ⊤ := (mem_maximalSubgroups.mp hM).lt_top
  have hpl1 : Ch1.hasPLengthOne p ↥M := proper_hasPLengthOne hG M hMlt
  obtain ⟨PM, hPM_eq⟩ := exists_sylow_subgroupOf_of_le P hPM
  have hQM : Q ≤ M := hQP.trans hPM
  have hQp : IsPGroup p ↥Q := P.isPGroup'.to_le hQP
  -- Step 1: Theorem 10.1(a) brings `x` into `M`: `x = m * c`, `conj x • Q = conj m • Q`.
  obtain ⟨m, hmM, c, hcC, hxmc⟩ :=
    (fusion_control_of_mem_sigma hG hM hpσ hQbot hQp).1 hQM x (hxQ.trans hPM)
  have hxm : MulAut.conj x • Q = MulAut.conj m • Q := by
    rw [hxmc, map_mul, mul_smul, conj_smul_eq_of_mem_centralizer hcC]
  have hmP : MulAut.conj m • Q ≤ (P : Subgroup G) := hxm ▸ hxQ
  -- Step 2: Lemma 6.6(3) inside `↥M`, with element `⟨m, hmM⟩⁻¹`.
  set mM : ↥M := ⟨m, hmM⟩ with hmMdef
  have hYne : (Q.subgroupOf M : Set ↥M).Nonempty := ⟨1, Subgroup.one_mem _⟩
  have hYS : (Q.subgroupOf M : Set ↥M) ⊆ (PM : Subgroup ↥M) := by
    rw [hPM_eq]
    exact fun z hz => Subgroup.mem_subgroupOf.mpr (hQP (Subgroup.mem_subgroupOf.mp hz))
  have hYx : ∀ z ∈ (Q.subgroupOf M : Set ↥M), (mM⁻¹)⁻¹ * z * mM⁻¹ ∈ (PM : Subgroup ↥M) := by
    intro z hz
    rw [inv_inv, hPM_eq, Subgroup.mem_subgroupOf]
    have hzQ : (z : G) ∈ Q := Subgroup.mem_subgroupOf.mp hz
    have hcoe : ((mM * z * mM⁻¹ : ↥M) : G) = m * (z : G) * m⁻¹ := by
      simp only [hmMdef, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    have hmem : m * (z : G) * m⁻¹ ∈ MulAut.conj m • Q := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
      have hsimp : m⁻¹ * (m * (z : G) * m⁻¹) * m = (z : G) := by group
      rw [hsimp]; exact hzQ
    exact hmP hmem
  obtain ⟨c', hc'C, g', hg'N, hcg⟩ :=
    Ch1.S06.exists_mem_centralizer_mul_normalizer_of_conj_subset_sylow PM hpl1 hYne hYS hYx
  -- `conj mM • Q' = conj g'⁻¹ • Q'` (since `c'⁻¹` centralizes `Q'`).
  have hmMeq : mM = g'⁻¹ * c'⁻¹ := by rw [← inv_inv mM, ← hcg, mul_inv_rev]
  have heq : MulAut.conj mM • (Q.subgroupOf M) = MulAut.conj g'⁻¹ • (Q.subgroupOf M) := by
    rw [hmMeq, map_mul, mul_smul, conj_smul_eq_of_mem_centralizer (Subgroup.inv_mem _ hc'C)]
  -- Translate to `G`.
  have hg'M : (↑g'⁻¹ : G) ∈ M := SetLike.coe_mem _
  have hmM_le : MulAut.conj m • Q ≤ M := hmP.trans hPM
  have hg'Q_le : MulAut.conj (↑g'⁻¹ : G) • Q ≤ M := conj_smul_le_of_mem hQM hg'M
  have hkey : MulAut.conj m • Q = MulAut.conj (↑g'⁻¹ : G) • Q := by
    have hmap := congrArg (Subgroup.map M.subtype) heq
    rw [Subgroup.conj_smul_subgroupOf hQM, Subgroup.conj_smul_subgroupOf hQM,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype] at hmap
    simp only [hmMdef, Subgroup.coe_mk] at hmap
    rwa [inf_eq_left.mpr hmM_le, inf_eq_left.mpr hg'Q_le] at hmap
  refine ⟨(↑g'⁻¹ : G), ?_, hxm.trans hkey⟩
  have hg'inv_N : g'⁻¹ ∈ Subgroup.normalizer ((PM : Subgroup ↥M) : Set ↥M) :=
    Subgroup.inv_mem _ hg'N
  rw [hPM_eq, ← Subgroup.subgroupOf_normalizer_eq hPM, Subgroup.mem_subgroupOf] at hg'inv_N
  exact hg'inv_N

/-- **Corollary 10.7(d)** (mmd L2803): for every `Q ≤ P`, `N_P(Q) = N_G(Q) ⊓ P` is a Sylow
`p`-subgroup of `N_G(Q)`. A Sylow `p` `R` of `N_G(Q)` containing `N_P(Q)` has image `RG ≤ N_G(Q)`;
using Sylow conjugacy and (c), `RG` (up to `N_G(Q)`-conjugacy by an element fixing `Q`) lands inside
`P`, so `RG = N_P(Q)`. -/
private theorem sylow_structure_d [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (Q : Subgroup G) (hQP : Q ≤ (P : Subgroup G)) :
    ∃ S : Sylow p ↥(Subgroup.normalizer (Q : Set G)),
      (S : Subgroup ↥(Subgroup.normalizer (Q : Set G))).map
          (Subgroup.normalizer (Q : Set G)).subtype =
        Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G) := by
  set NQ : Subgroup G := Subgroup.normalizer (Q : Set G) with hNQ
  -- `N_P(Q) = NQ ⊓ P`, a `p`-group; embed it in a Sylow `R` of `↥NQ`.
  have hNPQ_pg : IsPGroup p ↥((NQ ⊓ (P : Subgroup G)).subgroupOf NQ) :=
    (P.isPGroup'.to_le (inf_le_right : NQ ⊓ (P : Subgroup G) ≤ (P : Subgroup G))).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left)).symm
  obtain ⟨R, hR⟩ := hNPQ_pg.exists_le_sylow
  set RG : Subgroup G := (R : Subgroup ↥NQ).map NQ.subtype with hRGdef
  have hRG_le_NQ : RG ≤ NQ := Subgroup.map_subtype_le _
  have hRG_pg : IsPGroup p ↥RG :=
    R.2.of_equiv (Subgroup.equivMapOfInjective _ _ NQ.subtype_injective)
  have hQ_le_NPQ : Q ≤ NQ ⊓ (P : Subgroup G) := le_inf Subgroup.le_normalizer hQP
  have hNPQ_le_RG : NQ ⊓ (P : Subgroup G) ≤ RG := by
    have h := Subgroup.map_mono (f := NQ.subtype) hR
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_left : NQ ⊓ (P:Subgroup G) ≤ NQ)]
      at h
  have hQ_le_RG : Q ≤ RG := hQ_le_NPQ.trans hNPQ_le_RG
  -- Hard step: `RG ≤ P`.
  have hRG_le_P : RG ≤ (P : Subgroup G) := by
    obtain ⟨P', hRGP'⟩ := hRG_pg.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
    have hRGgP : RG ≤ MulAut.conj g • (P : Subgroup G) := by
      rw [← Sylow.coe_subgroup_smul, hg]; exact hRGP'
    have hg1RG : MulAut.conj g⁻¹ • RG ≤ (P : Subgroup G) := by
      have h1 : MulAut.conj g⁻¹ • RG ≤ MulAut.conj g⁻¹ • (MulAut.conj g • (P : Subgroup G)) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hRGgP
      rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
    have hg1Q : MulAut.conj g⁻¹ • Q ≤ (P : Subgroup G) :=
      (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQ_le_RG).trans hg1RG
    obtain ⟨y, hyN, hyQ⟩ := sylow_structure_c hG P Q hQP g⁻¹ hg1Q
    set n : G := y⁻¹ * g⁻¹ with hndef
    have hnQ_smul : MulAut.conj n • Q = Q := by
      rw [hndef, map_mul, mul_smul, hyQ, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hnQ : n ∈ NQ := mem_setNormalizer_of_conj_smul_eq hnQ_smul
    have hnRGP : MulAut.conj n • RG ≤ (P : Subgroup G) := by
      rw [hndef, map_mul, mul_smul]
      have hstep := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj y⁻¹)).mpr hg1RG
      rwa [conj_smul_eq_self_of_mem_setNormalizer (Subgroup.inv_mem _ hyN)] at hstep
    have hnRGNQ : MulAut.conj n • RG ≤ NQ := conj_smul_le_of_mem hRG_le_NQ hnQ
    have hnRG_le_RG : MulAut.conj n • RG ≤ RG := (le_inf hnRGNQ hnRGP).trans hNPQ_le_RG
    have heqRG : MulAut.conj n • RG = RG :=
      Subgroup.eq_of_le_of_card_ge hnRG_le_RG (card_conj_smul n RG).ge
    rw [← heqRG]; exact hnRGP
  exact ⟨R, le_antisymm (le_inf hRG_le_NQ hRG_le_P) hNPQ_le_RG⟩

/-- **Corollary 10.7(e)** (mmd L2805): if `R` is a `p`-subgroup, `Q ≤ P ⊓ R`, and `Q ⊴ N_G(P)`
(i.e. `N_G(P) ≤ N_G(Q)`), then `Q ⊴ N_G(R)`. A Sylow conjugate `a` carries `R` into `P`; applying
(c) to `Q` (via `a⁻¹`, then via `a⁻¹ z` for `z ∈ N_G(R)`) shows `a ∈ N_G(Q)` and then `z ∈ N_G(Q)`,
using `N_G(P) ≤ N_G(Q)`. -/
private theorem sylow_structure_e [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (R Q : Subgroup G) (hRp : IsPGroup p ↥R) (hQPR : Q ≤ (P : Subgroup G) ⊓ R)
    (hNPQ : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  set NQ : Subgroup G := Subgroup.normalizer (Q : Set G) with hNQ
  have hQP : Q ≤ (P : Subgroup G) := hQPR.trans inf_le_left
  have hQR : Q ≤ R := hQPR.trans inf_le_right
  -- Sylow conjugacy: `R ≤ conj a • P`, so `conj a⁻¹ • R ≤ P`.
  obtain ⟨P', hRP'⟩ := hRp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P P'
  have hRaP : R ≤ MulAut.conj a • (P : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, ha]; exact hRP'
  have ha1R : MulAut.conj a⁻¹ • R ≤ (P : Subgroup G) := by
    have h1 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj a⁻¹)).mpr hRaP
    rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
  -- `a ∈ N_G(Q)`.
  have ha1Q : MulAut.conj a⁻¹ • Q ≤ (P : Subgroup G) :=
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQR).trans ha1R
  obtain ⟨y₁, hy₁N, hy₁Q⟩ := sylow_structure_c hG P Q hQP a⁻¹ ha1Q
  have hy₁aQ : MulAut.conj (y₁⁻¹ * a⁻¹) • Q = Q := by
    rw [map_mul, mul_smul, hy₁Q, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have haQ : a ∈ NQ := by
    have hmem : y₁⁻¹ * a⁻¹ ∈ NQ := mem_setNormalizer_of_conj_smul_eq hy₁aQ
    have hainv : a⁻¹ ∈ NQ := by
      have hp := NQ.mul_mem (hNPQ hy₁N) hmem
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at hp
    simpa using NQ.inv_mem hainv
  -- Main: every `z ∈ N_G(R)` normalizes `Q`.
  intro z hz
  have hzR : MulAut.conj z • R = R := conj_smul_eq_self_of_mem_setNormalizer hz
  have hzQR : MulAut.conj z • Q ≤ R := by
    rw [← hzR]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQR
  have ha1zQ : MulAut.conj (a⁻¹ * z) • Q ≤ (P : Subgroup G) := by
    rw [map_mul, mul_smul]
    exact ((Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj a⁻¹)).mpr hzQR).trans
      ha1R
  obtain ⟨y₂, hy₂N, hy₂Q⟩ := sylow_structure_c hG P Q hQP (a⁻¹ * z) ha1zQ
  have hy₂azQ : MulAut.conj (y₂⁻¹ * (a⁻¹ * z)) • Q = Q := by
    rw [map_mul, mul_smul, hy₂Q, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hmem2 : y₂⁻¹ * (a⁻¹ * z) ∈ NQ := mem_setNormalizer_of_conj_smul_eq hy₂azQ
  have hzeq : z = a * (y₂ * (y₂⁻¹ * (a⁻¹ * z))) := by group
  rw [hzeq]
  exact NQ.mul_mem haQ (NQ.mul_mem (hNPQ hy₂N) hmem2)

/-- **Schur–Zassenhaus complement to the Sylow `p`-subgroup in its normalizer**: since `P` is a
normal Sylow `p`-subgroup of `N_G(P)` of order coprime to its index, there is a complement `V`
with `P ⊓ V = ⊥` and `P ⊔ V = N_G(P)`. This supplies the complement consumed by part (b).
(Public: §12 uses this to extract `P ≤ N_G(P)'` from `sylow_structure` (Lemma 12.8(c)).) -/
theorem exists_sylow_complement_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    ∃ V : Subgroup G, V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
      (P : Subgroup G) ⊓ V = ⊥ ∧
      (P : Subgroup G) ⊔ V = Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  set N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G) with hNdef
  have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hPsubN_normal : ((P : Subgroup G).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr hNdef.le
  obtain ⟨PN, hPNeq⟩ := exists_sylow_subgroupOf_of_le P hPN
  have hcop : Nat.Coprime (Nat.card ↥((P : Subgroup G).subgroupOf N))
      ((P : Subgroup G).subgroupOf N).index := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hcard : Nat.card ↥((P : Subgroup G).subgroupOf N) = p ^ n := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv]; exact hn
    have hidx : ¬ p ∣ ((P : Subgroup G).subgroupOf N).index := hPNeq ▸ PN.not_dvd_index
    rw [hcard]
    exact (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hidx).pow_left n
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨K.map N.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hPVN : (P : Subgroup G) ⊓ K.map N.subtype ≤ N := inf_le_left.trans hPN
    have hsubinf : ((P : Subgroup G) ⊓ K.map N.subtype).subgroupOf N = ⊥ := by
      change ((P : Subgroup G) ⊓ K.map N.subtype).comap N.subtype = ⊥
      rw [Subgroup.comap_inf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
      exact disjoint_iff.mp hK.isCompl.disjoint
    rw [← Subgroup.map_subgroupOf_eq_of_le hPVN, hsubinf, Subgroup.map_bot]
  · have hsup : (P : Subgroup G).subgroupOf N ⊔ K = ⊤ := hK.isCompl.sup_eq_top
    have hmap := congrArg (Subgroup.map N.subtype) hsup
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap

/-- **BG Corollary 10.7** (mmd L2787): `p` prime, `P ∈ Syl_p(G)`。
(a) `V` を `N_G(P)` 内の `P` の補群 (`P⊓V=1`, `P⊔V=N_G(P)`) とすると `P=[P,V]⊆N_G(P)'`;
(b) `r(P)≤2` ⇒ `P` abelian、または `P` は位数 `p³` exp `p` の nonabelian `P₁` と cyclic `P₂`
  (`Ω₁(P₂)=Z(P₁)`) の central product;
(c) `Q⊆P`, `Q^x⊆P` ⇒ `Q^x=Q^y` (`y∈N_G(P)`);
(d) 任意の `Q≤P` で `N_P(Q)` (= `N_G(Q)⊓P`) は `N_G(Q)` の Sylow `p`-部分群;
(e) `R` `p`-部分群, `Q⊆P∩R`, `Q⊴N_G(P)` (= `N_G(P)≤N_G(Q)`) ⇒ `Q⊴N_G(R)`。 -/
theorem sylow_structure [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) :
    (∀ V : Subgroup G, V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) →
      (P : Subgroup G) ⊓ V = ⊥ →
      (P : Subgroup G) ⊔ V = Subgroup.normalizer ((P : Subgroup G) : Set G) →
      (P : Subgroup G) = ⁅(P : Subgroup G), V⁆ ∧
        (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G))) ∧
    (rank ↥(P : Subgroup G) ≤ 2 →
      IsMulCommutative (P : Subgroup G) ∨
      ∃ P₁ P₂ : Subgroup G, P₁ ≤ (P : Subgroup G) ∧ P₂ ≤ (P : Subgroup G) ∧
        IsExpPExtraspecial p ↥P₁ ∧ Nat.card ↥P₁ = p ^ 3 ∧ IsCyclic ↥P₂ ∧
        (Omega ↥P₂ p 1).map P₂.subtype = (Subgroup.center ↥P₁).map P₁.subtype ∧
        IsCentralProduct (P : Subgroup G) P₁ P₂) ∧
    (∀ Q : Subgroup G, Q ≤ (P : Subgroup G) → ∀ x : G, MulAut.conj x • Q ≤ (P : Subgroup G) →
      ∃ y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), MulAut.conj x • Q = MulAut.conj y • Q) ∧
    (∀ Q : Subgroup G, Q ≤ (P : Subgroup G) →
      ∃ S : Sylow p ↥(Subgroup.normalizer (Q : Set G)),
        (S : Subgroup ↥(Subgroup.normalizer (Q : Set G))).map
            (Subgroup.normalizer (Q : Set G)).subtype =
          Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G)) ∧
    (∀ R Q : Subgroup G, IsPGroup p ↥R → Q ≤ (P : Subgroup G) ⊓ R →
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.normalizer (Q : Set G) →
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (Q : Set G)) := by
  refine ⟨fun V hV hPVinf hPVsup => sylow_structure_a hG P hV hPVinf hPVsup, ?_,
    fun Q hQP x hxQ => sylow_structure_c hG P Q hQP x hxQ,
    fun Q hQP => sylow_structure_d hG P Q hQP,
    fun R Q hRp hQPR hNPQ => sylow_structure_e hG P R Q hRp hQPR hNPQ⟩
  intro hrank
  obtain ⟨V, hV, hPVinf, hPVsup⟩ := exists_sylow_complement_normalizer P
  exact sylow_structure_b hG P hV hPVinf hPVsup hrank

/-- **Narrowness of Sylow `p` of `M` for `p ∈ π(M) - β(M)`** (BG Lemma 10.8 setup, mmd L2812):
if `p ∈ π(M)` and `p ∉ β(M)`, then every Sylow `p`-subgroup of `M` is narrow.

If `p ∉ α(M)` then `r_p(M) ≤ 2`, so the Sylow has rank `≤ 2` and is narrow directly. If
`p ∈ α(M) ⊆ σ(M)`, then a Sylow `p`-subgroup of `M` *is* a Sylow `p`-subgroup of `G`
(`isSylow_sylowMap_of_mem_sigma`: no normalizer growth out of `M`); and `p ∈ α(M)` with
`p ∉ β(M)` forces `¬ idealPrime p G`, which (with `r_p(G) ≥ 3`) means some — hence every, by
conjugacy — Sylow `p`-subgroup of `G` has a maximal elementary abelian subgroup of order `p²`,
i.e. is narrow (`narrow_iff_exists_maximalElementaryAbelian_card_prime_sq`).

(De-privatised 2026-06-19: also consumed by BG Theorem 15.2 (`S15_MF`) to discharge the
narrowness of `Q = O_q(M)` in the `q ∈ β(M)` gate.) -/
theorem isNarrow_sylow_of_not_mem_beta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpπ : p ∈ (Nat.card ↥M).primeFactors) (hpβ : p ∉ beta M) (P : Sylow p ↥M) :
    IsNarrow p ↥(P : Subgroup ↥M) := by
  have hp_prime : p.Prime := Fact.out
  have hp_odd : Odd p := hG.odd.of_dvd_nat (dvd_trans (Nat.mem_primeFactors.mp hpπ).2.1
    (Subgroup.card_subgroup_dvd_card M))
  by_cases hpα : p ∈ alpha M
  · -- `p ∈ α(M) ⊆ σ(M)`: the Sylow of `M` is a Sylow of `G`, narrow from `¬ idealPrime`.
    have hpσ : p ∈ sigma M := alpha_subset_sigma hG hM hpα
    have h3M : 3 ≤ pRank ↥M p := ((mem_alpha_iff M p).mp hpα).2
    have h3G : 3 ≤ pRank G p := le_trans h3M (pRank_le_of_injective M.subtype_injective)
    -- `S` is a Sylow `p`-subgroup of `G` isomorphic to `P`.
    obtain ⟨S, hS_eq⟩ := isSylow_sylowMap_of_mem_sigma hpσ P
    have ePS : ↥(P : Subgroup ↥M) ≃* ↥(S : Subgroup G) :=
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).trans
        (MulEquiv.subgroupCongr hS_eq.symm)
    -- `¬ idealPrime p G` (else `p ∈ β(M)`).
    have hnotideal : ¬ idealPrime p G := fun hideal => hpβ ⟨hpα, hideal⟩
    -- `¬ idealPrime` with `3 ≤ pRank G p` yields a narrow Sylow `Q` of `G`.
    rw [mem_idealPrime_iff, not_and_or] at hnotideal
    rcases hnotideal with h3 | hQex
    · exact absurd h3G h3
    · push Not at hQex
      obtain ⟨Q, A, hAcard, hAmax⟩ := hQex
      have h3Q : 3 ≤ pRank ↥(Q : Subgroup G) p := by rw [pRank_sylow_eq Q]; exact h3G
      have hQnarrow : IsNarrow p ↥(Q : Subgroup G) :=
        (Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq hp_odd Q.2 h3Q).mpr
          ⟨A, hAcard, hAmax⟩
      -- Transfer narrowness `Q → S` (conjugate Sylows) then `S → P`.
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
      have hgeq : MulAut.conj g • (Q : Subgroup G) = (S : Subgroup G) := by
        rw [← Sylow.coe_subgroup_smul, hg]
      have eQS : ↥(Q : Subgroup G) ≃* ↥(S : Subgroup G) :=
        (Subgroup.equivSMul (MulAut.conj g) (Q : Subgroup G)).trans
          (MulEquiv.subgroupCongr hgeq)
      exact IsNarrow.of_mulEquiv ePS.symm (IsNarrow.of_mulEquiv eQS hQnarrow)
  · -- `p ∉ α(M)`: `r_p(M) ≤ 2`, so the Sylow has rank `≤ 2`.
    have hr2 : pRank ↥M p ≤ 2 := by
      by_contra h
      exact hpα ⟨hpπ, by omega⟩
    exact isNarrow_of_pRank_le_two (by rw [pRank_sylow_eq P]; exact hr2)

/-- **`HasNormalPComplement` is invariant under group isomorphism.** Transport the normal
complement `N` to `N.map e`; each Sylow `Q` of the target pulls back along `e` to a Sylow of the
source, where it complements `N`, and the cardinalities/coprimality transfer. (Public form of the
private helper in `S7B2_NormalJ_PComplement`; needed to move `HasNormalPComplement` between
`↥(commutator ↥M)` and `↥(derivedInG M)`.) -/
theorem hasNormalPComplement_of_mulEquiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] {p : ℕ} [Fact p.Prime] (e : A ≃* B)
    (hA : Ch05.HasNormalPComplement p A) : Ch05.HasNormalPComplement p B := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hA
  refine ⟨N.map e.toMonoidHom, Subgroup.Normal.map hN_normal _ e.surjective, fun Q => ?_⟩
  have h_range_top : (e.toMonoidHom).range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hQ_le_range : (Q : Subgroup B) ≤ (e.toMonoidHom).range := by rw [h_range_top]; exact le_top
  let Q' : Sylow p A := Q.comapOfInjective e.toMonoidHom e.injective hQ_le_range
  have hQ'_compl : Subgroup.IsComplement' N (Q' : Subgroup A) := hN_compl Q'
  have hQ'_eq : (Q' : Subgroup A) = (Q : Subgroup B).comap e.toMonoidHom := by
    simp [Q', Sylow.coe_comapOfInjective]
  have hQ_map : (Q' : Subgroup A).map e.toMonoidHom = (Q : Subgroup B) := by
    rw [hQ'_eq, Subgroup.map_comap_eq, h_range_top, top_inf_eq]
  have hG_card : Nat.card A = Nat.card B := Nat.card_congr e.toEquiv
  have hN_card : Nat.card (N.map e.toMonoidHom : Subgroup B) = Nat.card N :=
    (Nat.card_congr (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).toEquiv).symm
  have hQ_card : Nat.card (Q : Subgroup B) = Nat.card (Q' : Subgroup A) := by
    rw [← hQ_map]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
  have h_card_eq : Nat.card N * Nat.card (Q' : Subgroup A) = Nat.card A := hQ'_compl.card_mul_card
  have h_card_H : Nat.card (N.map e.toMonoidHom : Subgroup B) * Nat.card (Q : Subgroup B) =
      Nat.card B := by rw [hN_card, hQ_card, h_card_eq, hG_card]
  have hp_ndvd_N : ¬ p ∣ Nat.card N := by
    rw [← hQ'_compl.index_eq_card]; exact Q'.not_dvd_index
  obtain ⟨k, hQ'_pow⟩ := IsPGroup.iff_card.mp Q'.isPGroup'
  have hp_prime : p.Prime := Fact.out
  have h_coprime' : Nat.Coprime (Nat.card N) (Nat.card (Q' : Subgroup A)) := by
    rw [hQ'_pow]; exact ((hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
  have h_coprime : Nat.Coprime (Nat.card (N.map e.toMonoidHom : Subgroup B))
      (Nat.card (Q : Subgroup B)) := by rw [hN_card, hQ_card]; exact h_coprime'
  exact Subgroup.isComplement'_of_coprime h_card_H h_coprime

/-- **BG Lemma 10.8(c) — normal `p`-complements** (mmd L2812), forward-conditional on the keystone
(via Theorem 10.6): for `p ∈ π(M) - β(M)`, both `M'` and `M_σ` have normal `p`-complements.

A Sylow `p`-subgroup of `M` is narrow (`isNarrow_sylow_of_not_mem_beta`) and `M` has `p`-length
one (Theorem 10.6 — `proper_hasPLengthOne`), so Theorem 5.6(c)
(`narrow_sylow_solvable_structure`) gives a normal `p`-complement for `↥(commutator ↥M)`;
transport it to `↥(derivedInG M)` by isomorphism, and inherit it for `↥(Msigma M)`
(`Msigma ⊆ M'`, `hasNormalPComplement_of_subgroup`). -/
theorem derived_msigma_hasNormalPComplement_of_not_mem_beta [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ}
    [Fact p.Prime] (hpπ : p ∈ (Nat.card ↥M).primeFactors) (hpβ : p ∉ beta M) :
    Ch05.HasNormalPComplement p ↥(derivedInG M) ∧ Ch05.HasNormalPComplement p ↥(Msigma M) := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hoddM : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hp_dvd : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpπ).2.1
  have hM_lt : M < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1
  -- Some Sylow `p`-subgroup of `M`, narrow; `M` has `p`-length one (Theorem 10.6).
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  have hPnarrow : IsNarrow p ↥(P : Subgroup ↥M) := isNarrow_sylow_of_not_mem_beta hG hM hpπ hpβ P
  have hpl : 3 ≤ pRank ↥(P : Subgroup ↥M) p → Ch1.hasPLengthOne p ↥M :=
    fun _ => proper_hasPLengthOne hG M hM_lt
  -- Theorem 5.6(c): `↥(commutator ↥M)` has a normal `p`-complement.
  have hNPC_comm : Ch05.HasNormalPComplement p ↥(commutator ↥M) :=
    (Ch1.S05.narrow_sylow_solvable_structure hoddM hp_dvd P hPnarrow hpl).2.2.1
  -- Transport to `↥(derivedInG M) = ↥((commutator ↥M).map M.subtype)`.
  have hNPC_der : Ch05.HasNormalPComplement p ↥(derivedInG M) :=
    hasNormalPComplement_of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥M) M.subtype M.subtype_injective) hNPC_comm
  refine ⟨hNPC_der, ?_⟩
  -- `M_σ ⊆ M'`: inherit the complement, then transport to `↥(Msigma M)`.
  have hMσ_le : Msigma M ≤ derivedInG M := Msigma_le_derived hG hM
  exact hasNormalPComplement_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMσ_le)
    (Ch05.hasNormalPComplement_of_subgroup hNPC_der ((Msigma M).subgroupOf (derivedInG M)))

/-- A subgroup whose order is coprime to the index of a normal subgroup `K` lies in `K`:
the image of `Q` in the quotient `H/K` has order dividing both `|Q|` and `[H:K]`, hence
trivial. (Used for "a normal `p`-complement contains every `p'`-subgroup"; also §12,
Lemma 12.1(b): `E₃ ≤ E'` once each Sylow subgroup of `E` at a `τ₃`-prime lies in `E'`.) -/
theorem le_of_coprime_card_index {H : Type*} [Group H] [Finite H] {K Q : Subgroup H}
    [K.Normal] (h : Nat.Coprime (Nat.card ↥Q) K.index) : Q ≤ K := by
  have hdvd1 : Nat.card ↥(Q.map (QuotientGroup.mk' K)) ∣ Nat.card ↥Q :=
    Subgroup.card_map_dvd Q (QuotientGroup.mk' K)
  have hdvd2 : Nat.card ↥(Q.map (QuotientGroup.mk' K)) ∣ K.index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  have hone : Nat.card ↥(Q.map (QuotientGroup.mk' K)) = 1 :=
    Nat.dvd_one.mp (h ▸ Nat.dvd_gcd hdvd1 hdvd2)
  have hbot : Q.map (QuotientGroup.mk' K) = ⊥ := Subgroup.card_eq_one.mp hone
  have hle : Q ≤ (QuotientGroup.mk' K).ker := (Subgroup.map_eq_bot_iff (H := Q)).mp hbot
  rwa [QuotientGroup.ker_mk'] at hle

/-- **Engine for Lemma 10.8(a)** (unconditional): in a finite group `H`, if `H` has a normal
`p`-complement for every prime `p ∈ π(H) - π`, then the `π`-radical `O_π(H)` is a Hall
`π`-subgroup of `H`.

`O_π(H)` is always a `π`-group; the content is that its index is coprime to `π`. Writing
`T = π(H) - π`, one has `O_π(H) = O_{Tᶜ}(H) = ⋂_{p∈T} O_{p'}(H)` (each `O_{p'}(H)` being the
normal `p`-complement). For a prime `r ∈ π` dividing the index, a Sylow `r`-subgroup `P`
is a `p'`-group for every `p ∈ T` (as `r ≠ p`), hence lies in each normal `p`-complement
(`le_of_coprime_card_index`) and so in `O_π(H)` — contradicting `r ∣ [H : O_π(H)]`. -/
theorem isHall_oPiCore_of_forall_hasNormalPComplement {H : Type*} [Group H] [Finite H]
    (π : Set ℕ)
    (hNPC : ∀ p : ℕ, p.Prime → p ∈ (Nat.card H).primeFactors → p ∉ π →
      Ch05.HasNormalPComplement p H) :
    Ch03.IsHallSubgroup π (Ch03.oPiCore π H) := by
  classical
  set T : Set ℕ := {p | p ∈ (Nat.card H).primeFactors ∧ p ∉ π} with hT
  -- `O_π(H) = O_{Tᶜ}(H)`: both have the same prime divisors among `π(H)`.
  have hcardCore : ∀ ρ : Set ℕ, Nat.card ↥(Ch03.oPiCore ρ H) ∣ Nat.card H :=
    fun ρ => Subgroup.card_subgroup_dvd_card _
  have hmemH : ∀ {ρ : Set ℕ} {q : ℕ}, q ∈ (Nat.card ↥(Ch03.oPiCore ρ H)).primeFactors →
      q ∈ (Nat.card H).primeFactors :=
    fun {ρ q} hq => Nat.primeFactors_mono (hcardCore ρ) Nat.card_pos.ne' hq
  have hEq : Ch03.oPiCore π H = Ch03.oPiCore Tᶜ H := by
    apply le_antisymm
    · refine Ch03.Subgroup.IsPiGroup.le_oPiCore (fun q hq => ?_)
      have hqπ : q ∈ π := Ch03.oPiCore.isPiGroup π q hq
      rw [Set.mem_compl_iff, hT, Set.mem_ofPred_eq, not_and, not_not]
      exact fun _ => hqπ
    · refine Ch03.Subgroup.IsPiGroup.le_oPiCore (fun q hq => ?_)
      have hqTc : q ∈ Tᶜ := Ch03.oPiCore.isPiGroup Tᶜ q hq
      rw [Set.mem_compl_iff, hT, Set.mem_ofPred_eq, not_and, not_not] at hqTc
      exact hqTc (hmemH hq)
  rw [hEq]
  refine ⟨fun q hq => ?_, ?_⟩
  · -- `O_{Tᶜ}(H)` is a `π`-group: a prime divisor `q` is in `Tᶜ` and in `π(H)`, hence in `π`.
    have hqTc : q ∈ Tᶜ := Ch03.oPiCore.isPiGroup Tᶜ q hq
    rw [Set.mem_compl_iff, hT, Set.mem_ofPred_eq, not_and, not_not] at hqTc
    exact hqTc (hmemH hq)
  · -- index coprime to `π`: a prime `r ∈ π` dividing the index gives a Sylow `r` inside `O_{Tᶜ}`.
    intro r hridx hrπ
    obtain ⟨hr_prime, hr_dvd_idx, -⟩ := Nat.mem_primeFactors.mp hridx
    have : Fact r.Prime := ⟨hr_prime⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r H))
    have hP_le : (P : Subgroup H) ≤ Ch03.oPiCore Tᶜ H := by
      rw [← Ch03.iInf_oPiCore_compl_singleton T]
      refine le_iInf₂ fun p hp => ?_
      obtain ⟨hpH, hpπ⟩ := hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hpH
      have : Fact p.Prime := ⟨hp_prime⟩
      have hrp_ne : r ≠ p := fun h => hpπ (h ▸ hrπ)
      obtain ⟨N', hN'normal, hN'compl⟩ := hNPC p hp_prime hpH hpπ
      have := hN'normal
      obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p H))
      have hN'idx : N'.index = Nat.card ↥(Q : Subgroup H) := (hN'compl Q).symm.index_eq_card
      have hcardN' : Nat.card ↥N' = (Q : Subgroup H).index := ((hN'compl Q).index_eq_card).symm
      -- `N'` is a `{p}ᶜ`-group (`p ∤ |N'| = [H : Q]`), so `N' ≤ O_{p'}(H)`.
      have hN'pi : Ch03.Subgroup.IsPiGroup ({p}ᶜ : Set ℕ) N' := by
        intro s hs
        rw [hcardN'] at hs
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl
        exact Q.not_dvd_index (Nat.dvd_of_mem_primeFactors hs)
      -- `P` (an `r`-group, `r ≠ p`) has order coprime to `[H : N'] = |Q|`, so `P ≤ N'`.
      have hPcop : Nat.Coprime (Nat.card ↥(P : Subgroup H)) N'.index := by
        rw [hN'idx]
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
        obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp Q.isPGroup'
        rw [hk, hj]
        exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hr_prime hp_prime).mpr hrp_ne)
      exact (le_of_coprime_card_index hPcop).trans hN'pi.le_oPiCore
    exact P.not_dvd_index (hr_dvd_idx.trans (Subgroup.index_dvd_of_le hP_le))

/-- For a normal subgroup `D ◁ G'` of a finite group, the `π`-radical of `↥D` is the
restriction of the `π`-radical of `G'`: `O_π(G').subgroupOf D = O_π(↥D)`. (Both inclusions
use `IsPiGroup.le_oPiCore`: `≤` since `O_π(G') ∩ D` is a normal `π`-subgroup of `↥D`; `≥`
since `O_π(↥D)` is characteristic in `D ◁ G'`, hence a normal `π`-subgroup of `G'`.) -/
theorem oPiCore_subgroupOf_eq_of_normal {G' : Type*} [Group G'] [Finite G'] (π : Set ℕ)
    (D : Subgroup G') [D.Normal] :
    (Ch03.oPiCore π G').subgroupOf D = Ch03.oPiCore π ↥D := by
  apply le_antisymm
  · have : ((Ch03.oPiCore π G').subgroupOf D).Normal :=
      Subgroup.Normal.subgroupOf inferInstance D
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore (fun q hq => ?_)
    refine Ch03.oPiCore.isPiGroup (G := G') π q ?_
    have hcard : Nat.card ↥((Ch03.oPiCore π G').subgroupOf D) =
        Nat.card ↥(Ch03.oPiCore π G' ⊓ D) := by
      rw [← Subgroup.subgroupOf_map_subtype (Ch03.oPiCore π G') D]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).toEquiv
    rw [hcard] at hq
    exact Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hq
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have : ((Ch03.oPiCore π ↥D).map D.subtype).Normal := inferInstance
    have hpi : Ch03.Subgroup.IsPiGroup π ((Ch03.oPiCore π ↥D).map D.subtype) := by
      intro q hq
      refine Ch03.oPiCore.isPiGroup (G := ↥D) π q ?_
      rwa [← Nat.card_congr (Subgroup.equivMapOfInjective _ D.subtype D.subtype_injective).toEquiv]
        at hq
    exact hpi.le_oPiCore ⟨x, hx, rfl⟩

/-- A finite group with a normal `p`-complement for every prime `p` is nilpotent.
For each prime `p`, the engine `isHall_oPiCore_of_forall_hasNormalPComplement` (applied with
`π = {p}`, using the complements at all `q ≠ p`) shows `O_p(H) = oPiCore {p} H` is a Hall
`{p}`-subgroup, i.e. a normal Sylow `p`-subgroup; so every Sylow is normal and `H` is nilpotent
(`Group.isNilpotent_of_finite_tfae`). Companion to the Hall engine. -/
theorem isNilpotent_of_forall_hasNormalPComplement {H : Type*} [Group H] [Finite H]
    (h : ∀ p : ℕ, p.Prime → p ∈ (Nat.card H).primeFactors → Ch05.HasNormalPComplement p H) :
    Group.IsNilpotent H := by
  refine ((Group.isNilpotent_of_finite_tfae (G := H)).out 0 3).mpr ?_
  intro p hp P
  have := hp
  have hHall : Ch03.IsHallSubgroup ({p} : Set ℕ) (Ch03.oPiCore ({p} : Set ℕ) H) :=
    isHall_oPiCore_of_forall_hasNormalPComplement _ (fun q hq_prime hq_mem _ => h q hq_prime hq_mem)
  have hOp_pg : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) H) :=
    Ch04.isPGroup_of_isPiGroup_singleton hHall.1
  have hp_ndvd : ¬ p ∣ (Ch03.oPiCore ({p} : Set ℕ) H).index := fun hdvd =>
    hHall.2 p (Nat.mem_primeFactors.mpr ⟨hp.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) rfl
  -- `O_p(H)` has full `p`-order, hence is a Sylow `p`-subgroup.
  have hcard : Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ) H) = p ^ (Nat.card H).factorization p := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hOp_pg
    have hmul : Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ) H) *
        (Ch03.oPiCore ({p} : Set ℕ) H).index = Nat.card H := Subgroup.card_mul_index _
    have hfac : (Nat.card H).factorization p = k := by
      rw [← hmul, hk,
        Nat.factorization_mul (pow_ne_zero k hp.out.pos.ne') Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, hp.out.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hp_ndvd, add_zero]
    rw [hk, hfac]
  set Q : Sylow p H := Sylow.ofCard (Ch03.oPiCore ({p} : Set ℕ) H) hcard with hQdef
  have hQcoe : (Q : Subgroup H) = Ch03.oPiCore ({p} : Set ℕ) H := Sylow.coe_ofCard _ hcard
  have hQnorm : (Q : Subgroup H).Normal := by rw [hQcoe]; infer_instance
  have := Sylow.unique_of_normal Q hQnorm
  rw [Subsingleton.elim P Q, hQcoe]
  infer_instance

/-- **Engine for Lemma 10.8(b)** (unconditional): a finite solvable group `K` with a normal
`p`-complement for every prime `p ∈ π(K) − β` has a *nilpotent* Hall `βᶜ`-subgroup.

A Hall `βᶜ`-subgroup `W` exists by solvability (`hall_E_exists`); each prime divisor of `|W|`
lies in `π(K) − β`, so `K` (hence `W ≤ K`) has a normal `p`-complement
(`hasNormalPComplement_of_subgroup`), making `W` nilpotent
(`isNilpotent_of_forall_hasNormalPComplement`). -/
theorem exists_isNilpotent_isHall_compl {K : Type*} [Group K] [Finite K] [Group.IsSolvable K]
    (β : Set ℕ)
    (hNPC : ∀ p : ℕ, p.Prime → p ∈ (Nat.card K).primeFactors → p ∉ β →
      Ch05.HasNormalPComplement p K) :
    ∃ W : Subgroup K, Ch03.IsHallSubgroup βᶜ W ∧ Group.IsNilpotent ↥W := by
  obtain ⟨W, hW⟩ := Ch03.hall_E_exists (G := K) βᶜ
  refine ⟨W, hW, isNilpotent_of_forall_hasNormalPComplement (fun p hp_prime hp_mem => ?_)⟩
  have : Fact p.Prime := ⟨hp_prime⟩
  have hpβc : p ∈ βᶜ := hW.1 p hp_mem
  have hpK : p ∈ (Nat.card K).primeFactors :=
    Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card W) Nat.card_pos.ne' hp_mem
  exact Ch05.hasNormalPComplement_of_subgroup (hNPC p hp_prime hpK hpβc) W

/-- **BG Lemma 10.8(a)** (mmd L2841, forward-conditional via Theorem 10.6): `M_β` is a Hall
`β(M)`-subgroup of `G`.

Proof (BG p.81): for `p ∈ π(M) − β(M)`, `M' = ↥(commutator ↥M)` has a normal `p`-complement
(Lemma 10.8(c) = `derived_msigma_hasNormalPComplement_of_not_mem_beta`). Hence the `β(M)`-radical
`O_{β(M)}(M')` is a Hall `β(M)`-subgroup of `M'`
(`isHall_oPiCore_of_forall_hasNormalPComplement`). As `O_{β(M)}(M') = O_{β(M)}(M).subgroupOf M'`
(`oPiCore_subgroupOf_eq_of_normal`, `M' ◁ M`) and `[M : M']` is coprime to `β(M)`
(`M_α ⊆ M'` is Hall `α(M) ⊇ β(M)`), `O_{β(M)}(M)` is Hall `β(M)` in `M`; finally `σ(M) ⊇ β(M)`
and `not_dvd_index_of_mem_sigma` lift this to `G`. -/
theorem Mbeta_isHall [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (beta M) (Mbeta M) := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hβσ : beta M ⊆ sigma M := fun p hp => alpha_subset_sigma hG hM (beta_subset_alpha M hp)
  -- internal: `O_{σ(M)}(↥M) ≤ commutator ↥M` (from `M_σ ≤ M'`).
  have hMσ_le : Ch03.oPiCore (sigma M) ↥M ≤ commutator ↥M := by
    have h := Msigma_le_derived hG hM
    simp only [Msigma, derivedInG, opiCoreInG] at h
    exact Subgroup.map_subtype_le_map_subtype.mp h
  have hOβ_le_comm : Ch03.oPiCore (beta M) ↥M ≤ commutator ↥M :=
    (Ch03.oPiCore_mono hβσ ↥M).trans hMσ_le
  -- `O_{β(M)}(M')` is Hall `β(M)` in `M' = ↥(commutator ↥M)` (crux + Lemma 10.8(c)).
  have hHallD : Ch03.IsHallSubgroup (beta M) (Ch03.oPiCore (beta M) ↥(commutator ↥M)) := by
    apply isHall_oPiCore_of_forall_hasNormalPComplement
    intro p hp_prime hpπD hpβ
    have : Fact p.Prime := ⟨hp_prime⟩
    have hpM : p ∈ (Nat.card ↥M).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card (commutator ↥M)) Nat.card_pos.ne' hpπD
    have h4 := (derived_msigma_hasNormalPComplement_of_not_mem_beta hG hM hpM hpβ).1
    exact hasNormalPComplement_of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥M) M.subtype M.subtype_injective).symm h4
  -- `[M : M']` is coprime to `β(M)`: `M_α ⊆ M'` is Hall `α(M) ⊇ β(M)`.
  have hidxD : ∀ p : ℕ, p ∈ beta M → p.Prime → ¬ p ∣ (commutator ↥M).index := by
    intro p hpβ hp_prime hp_dvd
    have hMα_le : Ch03.oPiCore (alpha M) ↥M ≤ commutator ↥M :=
      (Ch03.oPiCore_mono (alpha_subset_sigma hG hM) ↥M).trans hMσ_le
    have hHallα : Ch03.IsHallSubgroup (alpha M) (Ch03.oPiCore (alpha M) ↥M) := by
      have h := Malpha_subgroupOf_isHall_of_isHall (Malpha_isHall hG hM)
      simpa only [Malpha, opiCoreInG_subgroupOf] using h
    exact hHallα.2 p (Nat.mem_primeFactors.mpr ⟨hp_prime,
      hp_dvd.trans (Subgroup.index_dvd_of_le hMα_le), Subgroup.index_ne_zero_of_finite⟩)
      (beta_subset_alpha M hpβ)
  -- `O_{β(M)}(↥M)` is Hall `β(M)` in `↥M`.
  have hT1 : Ch03.IsHallSubgroup (beta M) (Ch03.oPiCore (beta M) ↥M) := by
    refine isHallSubgroup_of_subgroupOf_isHall_of_forall_not_dvd_index hOβ_le_comm ?_ hidxD
    rw [oPiCore_subgroupOf_eq_of_normal (beta M) (commutator ↥M)]
    exact hHallD
  -- lift `↥M`-Hall to `G`-Hall via `σ(M) ⊇ β(M)`.
  refine isHallSubgroup_of_subgroupOf_isHall_of_forall_not_dvd_index (Mbeta_le M) ?_ ?_
  · simpa only [Mbeta, opiCoreInG_subgroupOf] using hT1
  · intro p hpβ hp_prime
    have : Fact p.Prime := ⟨hp_prime⟩
    exact not_dvd_index_of_mem_sigma (hβσ hpβ)

/-- **BG Lemma 10.8** (mmd L2810): `M ∈ ℳ`。
(a) `M_β` は `M` および `G` の Hall 部分群;
(b) `M'` と `M_σ` は nilpotent な Hall `β(M)'`-部分群を持つ;
(c) `p ∈ π(M)−β(M)` ⇒ `M'` と `M_σ` は normal `p`-complement を持つ (`M_β` を含む)。

⚠ **原典 (c) はさらに「`p` は `|M/O_{p'}(M)|` の最大素因子」を含むが、この束には入っていない**。
その条項自体は直下の `largestPrime_quotient_oPiCore_compl_of_not_mem_beta` で証明済。
書籍の (a)(b)(c) を完全な形で 1 statement にしたものは `bgLem108` (本ファイル、下方)。
(以前ここには「quotient 型整備後に追加予定」と書かれていたが stale だった —
issue 0177 §13 の一括走査で発見, 2026-08-08。) -/
theorem isHall_Mbeta [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Ch03.IsHallSubgroup (beta M) (Mbeta M) ∧
    (∃ W : Subgroup G, W ≤ derivedInG M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (derivedInG M)) ∧
      Group.IsNilpotent ↥W) ∧
    (∃ W : Subgroup G, W ≤ Msigma M ∧
      Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf (Msigma M)) ∧ Group.IsNilpotent ↥W) ∧
    (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥M).primeFactors → p ∉ beta M →
      Ch05.HasNormalPComplement p ↥(derivedInG M) ∧
      Ch05.HasNormalPComplement p ↥(Msigma M)) := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- (c) = Lemma 10.8(c), landed.
  have h4 : ∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥M).primeFactors → p ∉ beta M →
      Ch05.HasNormalPComplement p ↥(derivedInG M) ∧ Ch05.HasNormalPComplement p ↥(Msigma M) :=
    fun p hp_prime hpπ hpβ => by
      have : Fact p.Prime := ⟨hp_prime⟩
      exact derived_msigma_hasNormalPComplement_of_not_mem_beta hG hM hpπ hpβ
  -- Common producer for (b): a nilpotent Hall `βᶜ`-subgroup of a subgroup `A ≤ M` with
  -- normal `p`-complements outside `β(M)`.
  have produce : ∀ A : Subgroup G, Group.IsSolvable ↥A →
      (∀ p : ℕ, p.Prime → p ∈ (Nat.card ↥A).primeFactors → p ∉ beta M →
        Ch05.HasNormalPComplement p ↥A) →
      ∃ W : Subgroup G, W ≤ A ∧
        Ch03.IsHallSubgroup (beta M)ᶜ (W.subgroupOf A) ∧ Group.IsNilpotent ↥W := by
    intro A hAsolv hANPC
    have := hAsolv
    obtain ⟨W₀, hW₀hall, hW₀nil⟩ :=
      exists_isNilpotent_isHall_compl (K := ↥A) (beta M) hANPC
    have := hW₀nil
    refine ⟨W₀.map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
      exact hW₀hall
    · let e := Subgroup.equivMapOfInjective W₀ A.subtype A.subtype_injective
      exact Group.nilpotent_of_surjective e.toMonoidHom e.surjective
  refine ⟨Mbeta_isHall hG hM, ?_, ?_, h4⟩
  · -- (b) for `M' = derivedInG M`.
    have : Group.IsSolvable ↥(derivedInG M) := by
      let e := Subgroup.equivMapOfInjective (commutator ↥M) M.subtype M.subtype_injective
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    refine produce (derivedInG M) inferInstance (fun p hp_prime hpπA hpβ => ?_)
    have hpM : p ∈ (Nat.card ↥M).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
        Nat.card_pos.ne' hpπA
    exact (h4 p hp_prime hpM hpβ).1
  · -- (b) for `M_σ = Msigma M`.
    have : Group.IsSolvable ↥(Msigma M) := by
      let e := Subgroup.equivMapOfInjective (Ch03.oPiCore (sigma M) ↥M) M.subtype
          M.subtype_injective
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    refine produce (Msigma M) inferInstance (fun p hp_prime hpπA hpβ => ?_)
    have hpM : p ∈ (Nat.card ↥M).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le (Msigma_le M)) Nat.card_pos.ne' hpπA
    exact (h4 p hp_prime hpM hpβ).2

/-- **BG Lemma 10.8(c), largest-prime part** (mmd L2843, forward-conditional via Theorem 10.6):
for `p ∈ π(M) − β(M)`, `p` is the largest prime divisor of `|M / O_{p'}(M)|`. Together with
`derived_msigma_hasNormalPComplement_of_not_mem_beta` (the normal-`p`-complement part) this is the
full Lemma 10.8(c). It is the first conjunct of Theorem 5.6 applied to a narrow Sylow `p`-subgroup
of the `p`-length-one group `↥M`. -/
theorem largestPrime_quotient_oPiCore_compl_of_not_mem_beta [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ}
    [Fact p.Prime] (hpπ : p ∈ (Nat.card ↥M).primeFactors) (hpβ : p ∉ beta M) :
    ∀ q ∈ (Nat.card (↥M ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} ↥M)).primeFactors, q ≤ p := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hoddM : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hp_dvd : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpπ).2.1
  have hM_lt : M < ⊤ := lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  have hPnarrow : IsNarrow p ↥(P : Subgroup ↥M) := isNarrow_sylow_of_not_mem_beta hG hM hpπ hpβ P
  have hpl : 3 ≤ pRank ↥(P : Subgroup ↥M) p → Ch1.hasPLengthOne p ↥M :=
    fun _ => proper_hasPLengthOne hG M hM_lt
  exact (Ch1.S05.narrow_sylow_solvable_structure hoddM hp_dvd P hPnarrow hpl).1

/-- **Consequence of Lemma 10.8(c)** (mmd L2862): for `p ∈ π(M) − β(M)` and a prime `q > p`, every
Sylow `q`-subgroup of `M` lies in `O_{p'}(M)` ("`O_{p'}(M)` contains all `q`-elements"). Indeed
`q ∤ |M / O_{p'}(M)|` because every prime divisor of that quotient is `≤ p < q`
(`largestPrime_quotient_oPiCore_compl_of_not_mem_beta`), so a Sylow `q`-subgroup has order coprime
to the (normal) `O_{p'}(M)`'s index (`le_of_coprime_card_index`). Used in Corollary 10.9(a),
case `X ⊄ M'` (`p < q`). -/
theorem sylow_le_oPiCore_compl_of_lt_of_not_mem_beta [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpπ : p ∈ (Nat.card ↥M).primeFactors) (hpβ : p ∉ beta M)
    (hpq : p < q) (Q : Sylow q ↥M) :
    (Q : Subgroup ↥M) ≤ Ch03.oPiCore {r : ℕ | r ≠ p} ↥M := by
  apply le_of_coprime_card_index
  have hq_ndvd : ¬ q ∣ (Ch03.oPiCore {r : ℕ | r ≠ p} ↥M).index := by
    rw [Subgroup.index_eq_card]
    intro hdvd
    exact absurd (largestPrime_quotient_oPiCore_compl_of_not_mem_beta hG hM hpπ hpβ q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)) (not_le.mpr hpq)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  rw [hk]
  exact Nat.Coprime.pow_left k ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hq_ndvd)

end OddOrder.BG.Ch3.S10


