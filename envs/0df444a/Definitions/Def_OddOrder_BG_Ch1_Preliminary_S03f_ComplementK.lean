-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_ComplementK
-- name    : OddOrder_BG_Ch1_Preliminary_S03f_ComplementK
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:09:10.947545+00:00
-- url     : https://prove2.me/theorems/259641c3-5e2f-400b-9b31-4d32d6390c9b
-- title:
--   BG §3: Theorem 3.6, Phase B, the complement $K$ ((3.12)–(3.16))
-- statement:
--   Phase B of the minimal-counterexample proof of Theorem 3.6 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3, as a standalone lemma using no induction hypothesis, only the phase A facts. It establishes the structure of the complement $K$, steps (3.12)–(3.16).
--
--   The main declaration: `complement_structure`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03f_ComplementK.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03f_ComplementK.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03_FrobeniusActions
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Prelim
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLengthTransfer
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorQuotientAction
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_ZGroup

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement Pointwise IsMulCommutative

open OddOrder.GroupTheory OddOrder.Isaacs.Ch04 OddOrder.BG.Ch1.OperatorQuotientAction

set_option maxHeartbeats 2400000 in
-- the `IsMulCommutative` scoped instances (priority 50) cycle with `CommMagma.to_isCommutative`;
-- failing class searches must exhaust that branch (cf. `S03f_Thm36`)
set_option synthInstance.maxHeartbeats 400000 in
/-- **BG Theorem 3.6, Phase B** ((3.12)–(3.16), mmd L975-L1010): the complement `K`.
IH-free segment of the minimal-counterexample proof.  From the phase A facts it produces an
`R`-invariant complement `K` to `V = F(H)` in the preimage of `F(H/V)`, an invariant Sylow
`p`-subgroup `P` of `N_H(K)`, and the structure facts (3.12)–(3.16) they satisfy. -/
theorem complement_structure
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {p : ℕ} (hp : p.Prime)
    {H R : Subgroup G} [H.Normal]
    (hcompl : Subgroup.IsComplement' H R)
    (hHall : Nat.Coprime (Nat.card ↥H) (Nat.card ↥R))
    (hcounter : ¬ hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G))
    (h36 : (⁅H, R⁆ : Subgroup G) = H)
    (h38 : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥H = ⊥)
    (hfit : OddOrder.Isaacs.Ch01.fitting ↥H = OddOrder.Isaacs.Ch01.opCore p ↥H)
    (hVp : IsPGroup p ↥(OddOrder.Isaacs.Ch01.fitting ↥H))
    (hVelem : IsElementaryAbelian p ↥(OddOrder.Isaacs.Ch01.fitting ↥H))
    (hCHV : Subgroup.centralizer
        ((OddOrder.Isaacs.Ch01.fitting ↥H : Subgroup ↥H) : Set ↥H)
      = OddOrder.Isaacs.Ch01.fitting ↥H)
    (h311 : ∀ (A' B' : Subgroup G) [A'.Normal] [B'.Normal], A' ≤ H → B' ≤ H →
      A' ⊓ B' = ⊥ → A' = ⊥ ∨ B' = ⊥) :
    ∃ K P : Subgroup ↥H,
      OddOrder.Isaacs.Ch03.IsAInvariant
        ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) K ∧
      OddOrder.Isaacs.Ch03.IsAInvariant
        ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) P ∧
      OddOrder.Isaacs.Ch03.IsAInvariant
        ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype)
        (OddOrder.Isaacs.Ch01.fitting ↥H) ∧
      ¬ p ∣ Nat.card ↥K ∧
      OddOrder.Isaacs.Ch01.fitting ↥H ⊓ K = ⊥ ∧
      P ≤ Subgroup.normalizer (K : Set ↥H) ∧
      IsPGroup p ↥P ∧
      ¬ p ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting
        (↥H ⧸ (OddOrder.Isaacs.Ch01.fitting ↥H : Subgroup ↥H))) ∧
      (¬ p ∣ Nat.card (↥H ⧸ (OddOrder.Isaacs.Ch01.fitting ↥H : Subgroup ↥H)) → False) ∧
      K.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch01.fitting ↥H))
        = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ (OddOrder.Isaacs.Ch01.fitting ↥H : Subgroup ↥H)) ∧
      (⁅K, P⁆ : Subgroup ↥H) ≠ ⊥ ∧
      OddOrder.Isaacs.Ch01.fitting ↥H ⊓ Subgroup.centralizer (K : Set ↥H) = ⊥ ∧
      OddOrder.Isaacs.Ch01.fitting ↥H ⊓ Subgroup.normalizer (K : Set ↥H) = ⊥ ∧
      K.subgroupOf (Subgroup.normalizer (K : Set ↥H))
        = OddOrder.Isaacs.Ch01.fitting ↥(Subgroup.normalizer (K : Set ↥H)) ∧
      Subgroup.centralizer (K : Set ↥H) ≤ K := by
    have : Fact p.Prime := ⟨hp⟩
    set V : Subgroup ↥H := OddOrder.Isaacs.Ch01.fitting ↥H with hVdef
    have hVnorm : V.Normal := by rw [hVdef]; infer_instance
    have hVoPi : V = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H := by
      rw [hfit, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]
    -- `F(H/V)` is a `p'`-group (so `V` is a normal Hall `p`-subgroup of the preimage `U` of
    -- `F(H/V)`).  Proved with the denominator kept as a variable to avoid dependent rewriting
    -- through `hVoPi`.
    have hFQ_compl : ∀ (N : Subgroup ↥H) [N.Normal],
        N = OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H →
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p}ᶜ : Set ℕ)
          (OddOrder.Isaacs.Ch01.fitting (↥H ⧸ N)) := by
      intro N _ hN
      subst hN
      set Q : Type _ := ↥H ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H with hQ
      intro q hqF hqπ
      have hq_prime : q.Prime := (Nat.mem_primeFactors.mp hqF).1
      have : Fact q.Prime := ⟨hq_prime⟩
      have hq_dvd : q ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting Q) :=
        (Nat.mem_primeFactors.mp hqF).2.1
      obtain ⟨P⟩ : Nonempty (Sylow q ↥(OddOrder.Isaacs.Ch01.fitting Q)) := inferInstance
      -- `Pbar` = the Sylow-`q` of `F(Q)` pushed into `Q`; it is a nontrivial normal `q`-subgroup.
      set Pbar : Subgroup Q :=
        (P : Subgroup ↥(OddOrder.Isaacs.Ch01.fitting Q)).map
          (OddOrder.Isaacs.Ch01.fitting Q).subtype with hPbar
      have hPbar_pg : IsPGroup q ↥Pbar := P.2.map _
      have hPnorm : (P : Subgroup ↥(OddOrder.Isaacs.Ch01.fitting Q)).Normal :=
        OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
      have : (P : Subgroup ↥(OddOrder.Isaacs.Ch01.fitting Q)).Characteristic :=
        Sylow.characteristic_of_normal P hPnorm
      have : Pbar.Normal := hPbar ▸ inferInstance
      have hPbar_le_op : Pbar ≤ OddOrder.Isaacs.Ch01.opCore q Q :=
        OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hPbar_pg
      have hPbar_ne : Pbar ≠ ⊥ := by
        have hcard_gt : 1 < Nat.card ↥Pbar := by
          rw [hPbar,
            Subgroup.card_map_of_injective (OddOrder.Isaacs.Ch01.fitting Q).subtype_injective,
            P.card_eq_multiplicity]
          exact Nat.one_lt_pow
            (hq_prime.factorization_pos_of_dvd Nat.card_pos.ne' hq_dvd).ne' hq_prime.one_lt
        intro hbot; rw [hbot, Subgroup.card_bot] at hcard_gt; exact lt_irrefl 1 hcard_gt
      -- `O_q(Q) ≤ O_{p}(Q)` only when `q = p`; but `O_p(Q) = O_p(H/O_p H) = ⊥`.
      have hop_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
          (OddOrder.Isaacs.Ch01.opCore q Q) := by
        intro r hr
        obtain ⟨n, hn⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup q Q).exists_card_eq
        rw [hn] at hr
        have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
        have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hrp hq_prime).mp
          (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
        -- `O_q(Q)` is a `q`-group and `q = p` (from `hqπ : q ∈ {p}`), so it is a `{p}`-group
        rw [Set.mem_singleton_iff, hrq]
        exact Set.mem_singleton_iff.mp hqπ
      have hoPi_bot : OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) Q = ⊥ :=
        OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot ({p} : Set ℕ)
      exact hPbar_ne (le_bot_iff.mp ((hPbar_le_op.trans
        (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore hop_pi)).trans_eq hoPi_bot))
    have hp_ndvd : ¬ p ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) := by
      intro hdvd
      have := hFQ_compl V hVoPi p
        (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
      simp at this
    -- `U := preimage of F(↥H/V)` in `↥H`: characteristic (hence `R`-invariant), and contains `V`.
    have hVchar : V.Characteristic := by rw [hVdef]; infer_instance
    set U : Subgroup ↥H :=
      (OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)).comap (QuotientGroup.mk' V) with hUdef
    have hUchar : U.Characteristic := Subgroup.Characteristic.comap_quotient_mk inferInstance
    have hVU : V ≤ U := by
      rw [hUdef]
      intro v hv
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff v).mpr hv]
      exact one_mem _
    -- `R`-action on `↥U` (restriction of the conjugation action; `U` characteristic ⟹
    -- `R`-invariant).
    set φ : ↥R →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R.subtype with hφ
    have hU_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ U :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
    set φU : ↥R →* MulAut ↥U := hU_inv.restrict with hφU
    -- **`R`-invariant complement `K` to `V` in `U`** (Proposition 1.5(a)): an `R`-invariant Hall
    -- `p'`-subgroup of `U`.  Coprimality from `|U| ∣ |H|` and `hHall`; `U` solvable as a
    -- subgroup of `H`.
    have hCopU : Nat.Coprime (Nat.card ↥R) (Nat.card ↥U) :=
      hHall.symm.coprime_dvd_right (Subgroup.card_subgroup_dvd_card U)
    obtain ⟨K', hK'_hall, hK'_inv⟩ :=
      OddOrder.BG.Ch1.S01.exists_aInvariant_hall (G := ↥U) (φ := φU) hCopU ({p}ᶜ : Set ℕ)
    -- `K := K'` pushed into `↥H`: `R`-invariant, and a complement to `V` in `U` (card bookkeeping).
    set K : Subgroup ↥H := K'.map U.subtype with hKdef
    have hK_le_U : K ≤ U := Subgroup.map_subtype_le K'
    have hK_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ K :=
      isAInvariant_map_subtype_of_restrict hU_inv hK'_inv
    have hKcard : Nat.card ↥K = Nat.card ↥K' :=
      Subgroup.card_map_of_injective U.subtype_injective
    have hK'p' : ¬ p ∣ Nat.card ↥K' := by
      intro hdvd
      have := hK'_hall.1 p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
      simp at this
    obtain ⟨a, hVa⟩ := hVp.exists_card_eq
    -- `|U| = |F(H/V)| · |V|` (the restriction of `mk' V` to `U` has kernel `V`, range `F(H/V)`).
    have hψker : ((QuotientGroup.mk' V).comp U.subtype).ker = V.subgroupOf U := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hψrange : ((QuotientGroup.mk' V).comp U.subtype).range
        = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
      rw [MonoidHom.range_comp, U.range_subtype, hUdef]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) _
    have hUcard : Nat.card ↥U
        = Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) * Nat.card ↥V := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (((QuotientGroup.mk' V).comp U.subtype).ker)]
      congr 1
      · exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange _).trans
          (MulEquiv.subgroupCongr hψrange)).toEquiv
      · rw [hψker]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv
    -- `|K'| = |F(H/V)|`: both are the `p'`-part of `|U| = |F(H/V)| · p^a`.
    have hCop_mFidx : Nat.Coprime (Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V))) K'.index := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hne
      rw [Nat.dvd_gcd_iff] at hq_dvd
      have hqp : q = p := by
        have := hK'_hall.2 q (Nat.mem_primeFactors.mpr
          ⟨hq_prime, hq_dvd.2, Subgroup.index_ne_zero_of_finite⟩)
        simpa using this
      exact hp_ndvd (hqp ▸ hq_dvd.1)
    have hK'm : Nat.card ↥K' = Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) := by
      have hKidx : Nat.card ↥K' * K'.index = Nat.card ↥U := Subgroup.card_mul_index K'
      refine Nat.dvd_antisymm ?_ ?_
      · have h1 : Nat.card ↥K' ∣ Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V)) * Nat.card ↥V :=
          hUcard ▸ Subgroup.card_subgroup_dvd_card K'
        refine Nat.Coprime.dvd_of_dvd_mul_right ?_ h1
        rw [hVa]
        exact Nat.Coprime.pow_right a (hp.coprime_iff_not_dvd.mpr hK'p').symm
      · have h2 : Nat.card ↥(OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V))
            ∣ Nat.card ↥K' * K'.index := by
          rw [hKidx, hUcard]; exact dvd_mul_right _ _
        exact Nat.Coprime.dvd_of_dvd_mul_right hCop_mFidx h2
    -- `IsComplement' (V.subgroupOf U) K'`, hence `V ⊔ K = U` and `V ⊓ K = ⊥` in `↥H`.
    have hVU_card : Nat.card ↥(V.subgroupOf U) = Nat.card ↥V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv
    have hcomplVK : Subgroup.IsComplement' (V.subgroupOf U) K' := by
      refine Subgroup.isComplement'_of_coprime ?_ ?_
      · rw [hVU_card, hK'm, hUcard]; exact mul_comm _ _
      · rw [hVU_card, hVa]
        exact Nat.Coprime.pow_left a (hp.coprime_iff_not_dvd.mpr hK'p')
    have hVK_sup : V ⊔ K = U := by
      have h1 := congrArg (Subgroup.map U.subtype) hcomplVK.sup_eq_top
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVU, ← hKdef,
        ← MonoidHom.range_eq_map, U.range_subtype] at h1
    have hVK_inf : V ⊓ K = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard (by
        rw [hVa, hKcard]
        exact Nat.Coprime.pow_left a (hp.coprime_iff_not_dvd.mpr hK'p'))).eq_bot
    -- `N := N_{↥H}(K)` is `R`-invariant; pick an `R`-invariant Sylow `p`-subgroup `P` of `N`
    -- (Theorem 3.23(a) = `exists_aInvariant_sylow`).
    set N : Subgroup ↥H := Subgroup.normalizer (K : Set ↥H) with hNdef
    have hK_le_N : K ≤ N := Subgroup.le_normalizer
    have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ N := hK_inv.normalizer
    have hCopN : Nat.Coprime (Nat.card ↥R) (Nat.card ↥N) :=
      hHall.symm.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
    obtain ⟨P', hP'_inv⟩ := OddOrder.Isaacs.Ch04.exists_aInvariant_sylow
      (G := ↥N) (φ := hN_inv.restrict) hCopN (Or.inr inferInstance) p
    set P : Subgroup ↥H := (P' : Subgroup ↥N).map N.subtype with hPdef
    have hP_le_N : P ≤ N := Subgroup.map_subtype_le _
    have hP_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ P :=
      isAInvariant_map_subtype_of_restrict hN_inv hP'_inv
    have hPp : IsPGroup p ↥P := P'.2.map _
    -- **(3.12)** Frattini argument: `↥H = U·N = V·N`, i.e. `V ⊔ N = ⊤`.  Conjugates of `K'` are
    -- Hall `{p}ᶜ`-subgroups of `↥U`, hence `U`-conjugate to `K'` (`hall_C`).
    have h312 : V ⊔ N = ⊤ := by
      -- commuting squares: conjugation inside `↥U` vs conjugation in `↥H` after `U.subtype`.
      have hsq : ∀ (g : ↥H) (X : Subgroup ↥U),
          (X.map (MulAut.conjNormal (G := ↥H) (H := U) g).toMonoidHom).map U.subtype
            = (X.map U.subtype).map (MulAut.conj g).toMonoidHom := by
        intro g X
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      have hsq' : ∀ (u : ↥U) (X : Subgroup ↥U),
          (X.map (MulAut.conj u).toMonoidHom).map U.subtype
            = (X.map U.subtype).map (MulAut.conj (u : ↥H)).toMonoidHom := by
        intro u X
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      have hUN : ∀ hh : ↥H, hh ∈ U ⊔ N := by
        intro hh
        have hKh_hall : OddOrder.Isaacs.Ch03.IsHallSubgroup ({p}ᶜ : Set ℕ)
            (K'.map (MulAut.conjNormal (G := ↥H) (H := U) hh).toMonoidHom) :=
          isHallSubgroup_map_of_mulEquiv _ hK'_hall
        obtain ⟨u, hu⟩ := OddOrder.Isaacs.Ch03.hall_C hKh_hall hK'_hall
        have h1 := congrArg (Subgroup.map U.subtype) hu
        rw [hsq', hsq, ← hKdef, Subgroup.map_map] at h1
        have hKK : K.map (MulAut.conj ((u : ↥H) * hh)).toMonoidHom = K := by
          have hcomp : (MulAut.conj ((u : ↥H) * hh)).toMonoidHom
              = (MulAut.conj (u : ↥H)).toMonoidHom.comp (MulAut.conj hh).toMonoidHom := by
            ext x
            simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply]
            group
          rw [hcomp]
          exact h1
        have huh_norm : (u : ↥H) * hh ∈ N := by
          rw [hNdef, Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            have hmem : ((u : ↥H) * hh) * x * ((u : ↥H) * hh)⁻¹
                ∈ K.map (MulAut.conj ((u : ↥H) * hh)).toMonoidHom :=
              ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
            rwa [hKK] at hmem
          · intro hx
            rw [← hKK] at hx
            obtain ⟨y, hy, hyeq⟩ := hx
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq
            have hxy : y = x := by
              have := hyeq
              group at this
              exact mul_left_cancel (mul_right_cancel (mul_right_cancel this))
            exact hxy ▸ hy
        have hdec : hh = (u : ↥H)⁻¹ * ((u : ↥H) * hh) := by group
        rw [hdec]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (U.inv_mem u.2))
          (Subgroup.mem_sup_right huh_norm)
      have hUN_top : U ⊔ N = ⊤ := by
        rw [eq_top_iff]
        exact fun hh _ => hUN hh
      rw [eq_top_iff, ← hUN_top, ← hVK_sup]
      exact sup_le (sup_le le_sup_left (hK_le_N.trans le_sup_right)) le_sup_right
    -- The image of `N` covers the quotient `↥H ⧸ V` (used at (3.13) and (3.15)).
    have hVmap_bot : V.map (QuotientGroup.mk' V) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hv
    have hNmap_top : N.map (QuotientGroup.mk' V) = ⊤ := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' V)) h312
      rwa [Subgroup.map_sup, hVmap_bot, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective V)] at h1
    -- `U` covers `F(H/V)` and so does `K` (`U = V·K` and `V` dies in the quotient).
    have hUmap : U.map (QuotientGroup.mk' V) = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
      rw [hUdef]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) _
    have hKmap : K.map (QuotientGroup.mk' V) = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
      have h1 := congrArg (Subgroup.map (QuotientGroup.mk' V)) hVK_sup
      rwa [Subgroup.map_sup, hVmap_bot, bot_sup_eq, hUmap] at h1
    -- shared ending: `p ∤ |H/V|` makes `H` have `p`-length one ((3.8): `O_{p',p}(H) = O_p(H) = V`),
    -- contradicting `hcounter` via (3.6).  Used at (3.13) and (3.17).
    have hfalse_of_pndvd : ¬ p ∣ Nat.card (↥H ⧸ V) → False := by
      intro hnd
      apply hcounter
      have hcard_eq : Nat.card (↥H ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) ↥H)
          = Nat.card (↥H ⧸ V) :=
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hVoPi.symm).toEquiv
      rw [h36, hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot h38, hcard_eq]
      exact hnd
    -- **(3.13)** `⁅K, P⁆ ≠ ⊥`.  Otherwise the image of `P` in `H/V` centralizes
    -- `F(H/V) = KV/V`, hence lies in it (Prop 1.3); a `p`-group inside the `p'`-group `F(H/V)`
    -- is trivial, so `P ≤ V`.  Then the Sylow `p`-subgroup `P` of `N` dies in the image of `N`,
    -- which is all of `H/V` (3.12); so `p ∤ |H/V|` and `H` has `p`-length one — contradiction.
    have h313 : (⁅K, P⁆ : Subgroup ↥H) ≠ ⊥ := by
      intro hKP
      have hPV : P ≤ V := by
        have hPQ_le : P.map (QuotientGroup.mk' V) ≤ Subgroup.centralizer
            ((OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) : Subgroup (↥H ⧸ V)) : Set (↥H ⧸ V)) := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Subgroup.mem_centralizer_iff]
          rintro _ hfq
          rw [← hKmap] at hfq
          obtain ⟨k, hk, rfl⟩ := hfq
          have hcomm : (x : ↥H) * k = k * x :=
            (Subgroup.mem_centralizer_iff.mp
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKP hk)) x hx
          simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hcomm]
        have hPQ_le_F : P.map (QuotientGroup.mk' V)
            ≤ OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) :=
          hPQ_le.trans OddOrder.GroupTheory.centralizer_fitting_le_fitting
        have hPQ_p : IsPGroup p ↥(P.map (QuotientGroup.mk' V)) := hPp.map _
        obtain ⟨k, hk⟩ := hPQ_p.exists_card_eq
        have hk0 : k = 0 := by
          by_contra hk0
          exact hp_ndvd ((hk ▸ dvd_pow_self p hk0).trans (Subgroup.card_dvd_of_le hPQ_le_F))
        have hPQbot : P.map (QuotientGroup.mk' V) = ⊥ :=
          Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
        rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hPQbot
      -- `p ∤ |H/V|`: the image of the Sylow `P'` of `N` under `↥N ↠ H/V` is trivial.
      apply hfalse_of_pndvd
      intro hdvd
      set ψ : ↥N →* ↥H ⧸ V := (QuotientGroup.mk' V).comp N.subtype with hψ
      have hψsurj : Function.Surjective ψ := by
        rw [← MonoidHom.range_eq_top, hψ, MonoidHom.range_comp, N.range_subtype]
        exact hNmap_top
      have hkerP : (P' : Subgroup ↥N) ≤ ψ.ker := by
        intro x hx
        rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hPV (Subgroup.mem_map_of_mem N.subtype hx)
      have hNcard : Nat.card ↥N = Nat.card (↥H ⧸ V) * Nat.card ↥ψ.ker := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv]
        exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      have hdvd2 : p ^ (Nat.card ↥N).factorization p ∣ Nat.card ↥ψ.ker := by
        rw [← P'.card_eq_multiplicity]
        exact Subgroup.card_dvd_of_le hkerP
      have hcontra : p ^ ((Nat.card ↥N).factorization p + 1) ∣ Nat.card ↥N := by
        rw [pow_succ]
        calc p ^ (Nat.card ↥N).factorization p * p
            ∣ Nat.card ↥ψ.ker * Nat.card (↥H ⧸ V) := mul_dvd_mul hdvd2 hdvd
          _ = Nat.card ↥N := by rw [hNcard, mul_comm]
      exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp hcontra
    -- **(3.14)** `[V,K] = V` and `C_V(K) = ⊥` (hence `V ⊓ N = ⊥`).  Proposition 1.6(d) splits
    -- `V = C_V(K) × [V,K]`; both factors are normal in `↥H` (they are normalized by `V` — abelian
    -- — and by `N`, and `↥H = VN` by (3.12)) and `R`-invariant, so their `G`-lifts are normal in
    -- `G`, and (3.11) kills one of them.  `[V,K] = ⊥` would give `K ≤ C_H(V) = V` ((3.10)), so
    -- `K = ⊥` and `⁅K,P⁆ = ⊥`, contradicting (3.13).
    let : CommGroup ↥V := { (inferInstance : Group ↥V) with mul_comm := fun a b => hVelem.1 a b }
    set φKV : ↥K →* MulAut ↥V := (MulAut.conjNormal (G := ↥H) (H := V)).comp K.subtype with hφKV
    have hφKV_val : ∀ (k : ↥K) (v : ↥V),
        ((φKV k v : ↥V) : ↥H) = (k : ↥H) * v * (k : ↥H)⁻¹ := by
      intro k v
      simp only [hφKV, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
    have hCopKV : Nat.Coprime (Nat.card ↥K) (Nat.card ↥V) := by
      rw [hVa, hKcard]
      exact (Nat.Coprime.pow_left a (hp.coprime_iff_not_dvd.mpr hK'p')).symm
    -- Proposition 1.6(d): `IsComplement' C_V(K) [V,K]` inside `↥V`.
    have hcompl14 : Subgroup.IsComplement' (Subgroup.fixedPointsOfMulAut φKV)
        (OddOrder.Isaacs.Ch04.actionCommutator φKV) :=
      OddOrder.BG.Ch1.S01.fixedPoints_isComplement_actionCommutator_of_abelian hCopKV
    -- bridges to `↥H`: the two factors are `V ⊓ C_{↥H}(K)` and `⁅V, K⁆`.
    have hAC : (OddOrder.Isaacs.Ch04.actionCommutator φKV).map V.subtype = ⁅V, K⁆ :=
      actionCommutator_conjNormal_map_subtype_eq V K
    have hFP : (Subgroup.fixedPointsOfMulAut φKV).map V.subtype
        = V ⊓ Subgroup.centralizer (K : Set ↥H) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨v.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have h1 := congrArg Subtype.val (Subgroup.mem_fixedPointsOfMulAut.mp hv ⟨k, hk⟩)
        rw [hφKV_val] at h1
        exact mul_inv_eq_iff_eq_mul.mp h1
      · rintro ⟨hxV, hxc⟩
        refine ⟨⟨x, hxV⟩, Subgroup.mem_fixedPointsOfMulAut.mpr fun k => ?_, rfl⟩
        apply Subtype.ext
        rw [hφKV_val]
        have h2 := Subgroup.mem_centralizer_iff.mp hxc (k : ↥H) k.2
        rw [h2]
        group
    have hker_subtype : (H.subtype).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
    -- conjugation by elements of `N` preserves `K` and `C_{↥H}(K)`.
    have hconjK : ∀ x : ↥H, x ∈ N → K.map (MulAut.conj x).toMonoidHom = K := by
      intro x hx
      have hx' := Subgroup.mem_normalizer_iff.mp hx
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hx' z).mp hz
      · intro hy
        have h1 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
        exact ⟨x⁻¹ * y * x, (hx' _).mpr (h1.symm ▸ hy), by group⟩
    have hconjC : ∀ x : ↥H, x ∈ N →
        (Subgroup.centralizer (K : Set ↥H)).map (MulAut.conj x).toMonoidHom
          = Subgroup.centralizer (K : Set ↥H) := by
      intro x hx
      have hx' := Subgroup.mem_normalizer_iff.mp hx
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Subgroup.mem_centralizer_iff] at hz ⊢
        intro k hk
        have hk' : x⁻¹ * k * x ∈ K := by
          refine (hx' (x⁻¹ * k * x)).mpr ?_
          have h1 : x * (x⁻¹ * k * x) * x⁻¹ = k := by group
          rwa [h1]
        have hcz := hz _ hk'
        calc k * (x * z * x⁻¹) = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by group
          _ = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by rw [hcz]
          _ = (x * z * x⁻¹) * k := by group
      · intro hy
        refine ⟨x⁻¹ * y * x, ?_, by group⟩
        rw [Subgroup.mem_centralizer_iff] at hy ⊢
        intro k hk
        have hk' : x * k * x⁻¹ ∈ K := (hx' k).mp hk
        have hcy := hy _ hk'
        calc k * (x⁻¹ * y * x) = x⁻¹ * ((x * k * x⁻¹) * y) * x := by group
          _ = x⁻¹ * (y * (x * k * x⁻¹)) * x := by rw [hcy]
          _ = (x⁻¹ * y * x) * k := by group
    -- a subgroup of `V` normalized by all of `N` is normal in `↥H` (by (3.12), `↥H = VN`,
    -- and `V` centralizes subgroups of itself since `V` is abelian).
    have hnormal_of_VN : ∀ (X : Subgroup ↥H), X ≤ V →
        (∀ x : ↥H, x ∈ N → X.map (MulAut.conj x).toMonoidHom = X) → X.Normal := by
      intro X hXV hXN
      constructor
      intro nn hnn g
      have hg : g ∈ (V : Set ↥H) * (N : Set ↥H) := by
        rw [← Subgroup.normal_mul, h312, Subgroup.coe_top]
        trivial
      obtain ⟨v, hv, x, hx, rfl⟩ := hg
      have h1 : x * nn * x⁻¹ ∈ X := by
        rw [← hXN x hx]
        exact ⟨nn, hnn, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      have hcomm : v * (x * nn * x⁻¹) = (x * nn * x⁻¹) * v := by
        simpa using congrArg Subtype.val (hVelem.1 ⟨v, hv⟩ ⟨x * nn * x⁻¹, hXV h1⟩)
      have h2 : (v * x) * nn * (v * x)⁻¹ = v * (x * nn * x⁻¹) * v⁻¹ := by group
      rw [h2, hcomm]
      simpa using h1
    have hBnorm : (⁅V, K⁆ : Subgroup ↥H).Normal := by
      refine hnormal_of_VN _ (Subgroup.commutator_le_left V K) fun x hx => ?_
      rw [Subgroup.map_commutator, Subgroup.characteristic_iff_map_eq.mp hVchar (MulAut.conj x),
        hconjK x hx]
    have hCnorm : (V ⊓ Subgroup.centralizer (K : Set ↥H)).Normal := by
      refine hnormal_of_VN _ inf_le_left fun x hx => ?_
      rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective,
        Subgroup.characteristic_iff_map_eq.mp hVchar (MulAut.conj x), hconjC x hx]
    -- both factors are `R`-invariant (`V` characteristic, `K` `R`-invariant).
    have hV_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ V :=
      OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
    have hB_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (⁅V, K⁆ : Subgroup ↥H) := by
      intro r
      change (⁅V, K⁆ : Subgroup ↥H).map (φ r).toMonoidHom = ⁅V, K⁆
      have h1 : V.map (φ r).toMonoidHom = V := hV_inv r
      have h2 : K.map (φ r).toMonoidHom = K := hK_inv r
      rw [Subgroup.map_commutator, h1, h2]
    have hC_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ
        (V ⊓ Subgroup.centralizer (K : Set ↥H)) := by
      rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
      intro r y hy
      obtain ⟨hyV, hyc⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨hV_inv.smul_mem r hyV, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hyc ⊢
      intro k hk
      have hk' : (φ r)⁻¹ k ∈ K := hK_inv.inv_smul_mem r hk
      calc k * (φ r) y = (φ r) ((φ r)⁻¹ k * y) := by
            rw [map_mul, MulAut.apply_inv_self]
        _ = (φ r) (y * (φ r)⁻¹ k) := by rw [hyc _ hk']
        _ = (φ r) y * k := by rw [map_mul, MulAut.apply_inv_self]
    -- the `G`-lifts are normal in `G` (normal in `↥H` + `R`-invariant + `G = HR`).
    have hBnormG : ((⁅V, K⁆ : Subgroup ↥H).map H.subtype).Normal :=
      normal_map_subtype_of_isAInvariant_conjNormal hcompl.sup_eq_top hB_inv
    have hCnormG : ((V ⊓ Subgroup.centralizer (K : Set ↥H)).map H.subtype).Normal :=
      normal_map_subtype_of_isAInvariant_conjNormal hcompl.sup_eq_top hC_inv
    -- the two factors intersect trivially and generate `V` (image of `IsComplement'`).
    have hCB_inf : (V ⊓ Subgroup.centralizer (K : Set ↥H)) ⊓ (⁅V, K⁆ : Subgroup ↥H) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxC, hxB⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨hxV, hxc⟩ := Subgroup.mem_inf.mp hxC
      have hxFP : (⟨x, hxV⟩ : ↥V) ∈ Subgroup.fixedPointsOfMulAut φKV := by
        have h1 : x ∈ (Subgroup.fixedPointsOfMulAut φKV).map V.subtype := by
          rw [hFP]
          exact Subgroup.mem_inf.mpr ⟨hxV, hxc⟩
        obtain ⟨z, hz, hzx⟩ := h1
        rwa [show z = (⟨x, hxV⟩ : ↥V) from Subtype.ext hzx] at hz
      have hxAC : (⟨x, hxV⟩ : ↥V) ∈ OddOrder.Isaacs.Ch04.actionCommutator φKV := by
        have h1 : x ∈ (OddOrder.Isaacs.Ch04.actionCommutator φKV).map V.subtype := by
          rw [hAC]
          exact hxB
        obtain ⟨z, hz, hzx⟩ := h1
        rwa [show z = (⟨x, hxV⟩ : ↥V) from Subtype.ext hzx] at hz
      have hbot : (⟨x, hxV⟩ : ↥V) ∈ Subgroup.fixedPointsOfMulAut φKV
          ⊓ OddOrder.Isaacs.Ch04.actionCommutator φKV := ⟨hxFP, hxAC⟩
      rw [hcompl14.disjoint.eq_bot, Subgroup.mem_bot] at hbot
      rw [Subgroup.mem_bot]
      simpa using congrArg Subtype.val hbot
    have hCB_sup : (V ⊓ Subgroup.centralizer (K : Set ↥H)) ⊔ (⁅V, K⁆ : Subgroup ↥H) = V := by
      have h2 := congrArg (Subgroup.map V.subtype) hcompl14.sup_eq_top
      rwa [Subgroup.map_sup, hFP, hAC, ← MonoidHom.range_eq_map, V.range_subtype] at h2
    -- **(3.11) dichotomy**: the `C_V(K)` factor dies (else `K = ⊥`, contradicting (3.13)).
    have h314C : V ⊓ Subgroup.centralizer (K : Set ↥H) = ⊥ := by
      have hinfG : ((V ⊓ Subgroup.centralizer (K : Set ↥H)).map H.subtype)
          ⊓ ((⁅V, K⁆ : Subgroup ↥H).map H.subtype) = ⊥ := by
        rw [← Subgroup.map_inf _ _ H.subtype H.subtype_injective, hCB_inf, Subgroup.map_bot]
      rcases h311 _ _ (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hinfG with hc | hb
      · rwa [Subgroup.map_eq_bot_iff, hker_subtype, le_bot_iff] at hc
      · exfalso
        rw [Subgroup.map_eq_bot_iff, hker_subtype, le_bot_iff] at hb
        have hKle : K ≤ Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) :=
          Subgroup.le_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb)
        have hKbot : K = ⊥ := by
          rw [eq_bot_iff]
          intro k hk
          have hkV : k ∈ V ⊓ K := ⟨hCHV ▸ hKle hk, hk⟩
          rwa [hVK_inf] at hkV
        exact h313 (by rw [hKbot, Subgroup.commutator_bot_left])
    -- **(3.14)**: `[V,K] = V`, and `V ⊓ N = ⊥`.
    have h314B : (⁅V, K⁆ : Subgroup ↥H) = V := by
      have h1 := hCB_sup
      rwa [h314C, bot_sup_eq] at h1
    have hVN_inf : V ⊓ N = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨hvV, hvN⟩ := Subgroup.mem_inf.mp hv
      have hvc : v ∈ Subgroup.centralizer (K : Set ↥H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have h1 : v * k * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hvN k).mp hk
        have h2 : v * k * v⁻¹ * k⁻¹ ∈ V := by
          have h3 : k * v⁻¹ * k⁻¹ ∈ V := hVnorm.conj_mem _ (V.inv_mem hvV) k
          have hcomb : v * k * v⁻¹ * k⁻¹ = v * (k * v⁻¹ * k⁻¹) := by group
          rw [hcomb]
          exact V.mul_mem hvV h3
        have h4 : v * k * v⁻¹ * k⁻¹ ∈ V ⊓ K := ⟨h2, K.mul_mem h1 (K.inv_mem hk)⟩
        rw [hVK_inf, Subgroup.mem_bot] at h4
        rw [mul_inv_eq_one] at h4
        exact (mul_inv_eq_iff_eq_mul.mp h4).symm
      have hvmem : v ∈ V ⊓ Subgroup.centralizer (K : Set ↥H) := ⟨hvV, hvc⟩
      rwa [h314C] at hvmem
    -- **(3.15)** `K = F(N)`: by (3.12) and `V ⊓ N = ⊥` the map `mk' V ∘ N.subtype` is an
    -- isomorphism `↥N ≃* ↥H ⧸ V` carrying `K.subgroupOf N` to `F(H/V)`; the Fitting subgroup
    -- transports along isomorphisms.
    set ψN : ↥N →* ↥H ⧸ V := (QuotientGroup.mk' V).comp N.subtype with hψN
    have hψNinj : Function.Injective ψN := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, hψN, MonoidHom.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      have hxVN : (x : ↥H) ∈ V ⊓ N := ⟨hx, x.2⟩
      rw [hVN_inf, Subgroup.mem_bot] at hxVN
      rw [Subgroup.mem_bot]
      exact Subtype.ext hxVN
    have hψNsurj : Function.Surjective ψN := by
      rw [← MonoidHom.range_eq_top, hψN, MonoidHom.range_comp, N.range_subtype]
      exact hNmap_top
    set eN : ↥N ≃* (↥H ⧸ V) := MulEquiv.ofBijective ψN ⟨hψNinj, hψNsurj⟩ with heN
    have heN_hom : eN.toMonoidHom = ψN := by
      ext x
      rfl
    have hKN_fit : K.subgroupOf N = OddOrder.Isaacs.Ch01.fitting ↥N := by
      have h1 : (K.subgroupOf N).map eN.toMonoidHom
          = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := by
        rw [heN_hom, hψN, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hK_le_N]
        exact hKmap
      have h2 : (OddOrder.Isaacs.Ch01.fitting ↥N).map eN.toMonoidHom
          = OddOrder.Isaacs.Ch01.fitting (↥H ⧸ V) := fitting_map_eq_of_mulEquiv eN
      exact Subgroup.map_injective eN.injective (h1.trans h2.symm)
    have h315 : (OddOrder.Isaacs.Ch01.fitting ↥N).map N.subtype = K := by
      rw [← hKN_fit, Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hK_le_N
    -- **(3.16)** `C_{↥H}(K) ≤ K`: a centralizing element lies in `N`, and inside `↥N`
    -- Proposition 1.3 gives `C_N(K) ≤ C_N(F(N)) ≤ F(N) = K`.
    have h316 : Subgroup.centralizer (K : Set ↥H) ≤ K := by
      intro c hc
      have hcN : c ∈ N := Subgroup.centralizer_le_normalizer (K : Set ↥H) hc
      have hcC : (⟨c, hcN⟩ : ↥N) ∈ Subgroup.centralizer
          ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact Subgroup.mem_centralizer_iff.mp hc (k : ↥H) (Subgroup.mem_subgroupOf.mp hk)
      have hcF : (⟨c, hcN⟩ : ↥N) ∈ OddOrder.Isaacs.Ch01.fitting ↥N :=
        OddOrder.GroupTheory.centralizer_fitting_le_fitting (hKN_fit ▸ hcC)
      rw [← hKN_fit] at hcF
      exact Subgroup.mem_subgroupOf.mp hcF
    have hKp_ndvd : ¬ p ∣ Nat.card ↥K := fun h => hK'p' (hKcard ▸ h)
    exact ⟨K, P, hK_inv, hP_inv, hV_inv, hKp_ndvd, hVK_inf, hP_le_N, hPp, hp_ndvd,
      hfalse_of_pndvd, hKmap, h313, h314C, hVN_inf, hKN_fit, h316⟩

end OddOrder.BG.Ch1.S03f


