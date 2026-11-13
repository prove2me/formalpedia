-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:47:35.373924+00:00
-- url     : https://prove2.me/theorems/5f688925-61a1-4b6d-9e01-59c1a9433bf2
-- title:
--   Peterfalvi §13: structural facts of the maximal pair $(S,T)$
-- statement:
--   Formalizes the structural dictionary for the maximal pair $(S,T)$ that feeds the (13.5)–(13.10) counting layer, including $p\ne q$ and normalizer identities.
--
--   Main declarations: `Hypothesis.exists_typePData_U_eq_V` (A type-`P` datum on `T` whose complement is the abstract `V` (and whose kernel is `Q`)).
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/PairStructure.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/PairStructure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section PairStructure

open OddOrder.GroupTheory

/-- Under **Peterfalvi (13.1)**, the prime parameters are distinct: `W₁` and `W₂` are nontrivial
subgroups of the *cyclic* `W` with trivial intersection, so if `p = q` the `q`-element count of
`W` would exceed `φ(q)` (`IsCyclic.card_orderOf_eq_totient`): `W₁^#` supplies `q − 1` elements of
order `q` and `W₂^#` a further one outside `W₁`. -/
theorem Hypothesis.p_ne_q [Finite G] (hyp : Hypothesis (G := G)) : hyp.p ≠ hyp.q := by
  intro hpq
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have : IsCyclic ↥hyp.W := hyp.W_cyclic
  have : Fintype ↥hyp.W := Fintype.ofFinite _
  classical
  set W1' : Subgroup ↥hyp.W := hyp.W1.subgroupOf hyp.W with hW1def
  set W2' : Subgroup ↥hyp.W := hyp.W2.subgroupOf hyp.W with hW2def
  have hc1 : Nat.card ↥W1' = hyp.q := by
    rw [hW1def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1W).toEquiv, ← hyp.q_eq_card_W1]
  have hc2 : Nat.card ↥W2' = hyp.q := by
    rw [hW2def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2W).toEquiv, ← hpq,
      ← hyp.p_eq_card_W2]
  have hinf : W1' ⊓ W2' = ⊥ := by
    ext a
    simp only [Subgroup.mem_inf, Subgroup.mem_bot, Subgroup.mem_subgroupOf, hW1def, hW2def]
    constructor
    · rintro ⟨h1, h2⟩
      have hmem : (a : G) ∈ hyp.W1 ⊓ hyp.W2 := ⟨h1, h2⟩
      rw [hyp.W1_inf_W2_eq_bot, Subgroup.mem_bot] at hmem
      exact OneMemClass.coe_eq_one.mp hmem
    · rintro rfl; exact ⟨one_mem _, one_mem _⟩
  -- Nonidentity elements of an order-`q` subgroup have order `q`.
  have horder : ∀ (V : Subgroup ↥hyp.W), Nat.card ↥V = hyp.q →
      ∀ a : ↥hyp.W, a ∈ V → a ≠ 1 → orderOf a = hyp.q := by
    intro V hV a ha ha1
    have hdvd : orderOf a ∣ hyp.q := by
      have h1 : orderOf (⟨a, ha⟩ : ↥V) ∣ Nat.card ↥V := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk a ha, hV] at h1
    rcases (Nat.dvd_prime hyp.q_prime).mp hdvd with h1 | hq
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact hq
  -- The order-`q` element count of the cyclic `W` is `φ(q) = q − 1`.
  have hqdvd : hyp.q ∣ Fintype.card ↥hyp.W := by
    rw [← Nat.card_eq_fintype_card, ← hc1]
    exact Subgroup.card_subgroup_dvd_card W1'
  have htot := IsCyclic.card_orderOf_eq_totient (α := ↥hyp.W) hqdvd
  -- ... but `W₁^# ∪ {y}` (`y ∈ W₂^#`) already has `q` elements of order `q`.
  obtain ⟨y', hy'⟩ : ∃ y' : ↥W2', y' ≠ 1 := by
    have : Nontrivial ↥W2' := Finite.one_lt_card_iff_nontrivial.mp
      (by rw [hc2]; exact hyp.q_prime.one_lt)
    exact exists_ne 1
  have hy1 : (y' : ↥hyp.W) ≠ 1 := by
    intro h
    exact hy' (OneMemClass.coe_eq_one.mp h)
  have hyW2 : (y' : ↥hyp.W) ∈ W2' := y'.2
  set F : Finset ↥hyp.W :=
    insert (y' : ↥hyp.W) ((Finset.univ.filter (· ∈ W1')).erase 1) with hFdef
  have hynotin : (y' : ↥hyp.W) ∉ (Finset.univ.filter (· ∈ W1')).erase 1 := by
    intro hmem
    have hyW1 : (y' : ↥hyp.W) ∈ W1' := (Finset.mem_filter.mp (Finset.mem_erase.mp hmem).2).2
    have : (y' : ↥hyp.W) ∈ W1' ⊓ W2' := ⟨hyW1, hyW2⟩
    rw [hinf] at this
    exact hy1 this
  have hW1card : (Finset.univ.filter (· ∈ W1')).card = hyp.q := by
    rw [← hc1, Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype]
  have hFcard : F.card = hyp.q := by
    rw [hFdef, Finset.card_insert_of_notMem hynotin,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, W1'.one_mem⟩),
      hW1card]
    have := hyp.q_prime.two_le
    omega
  have hFsub : F ⊆ Finset.univ.filter (fun a => orderOf a = hyp.q) := by
    intro a ha
    rw [hFdef, Finset.mem_insert] at ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | ha
    · exact horder W2' hc2 _ hyW2 hy1
    · obtain ⟨ha1, hamem⟩ := Finset.mem_erase.mp ha
      exact horder W1' hc1 a (Finset.mem_filter.mp hamem).2 ha1
  have hle : hyp.q ≤ hyp.q.totient := by
    calc hyp.q = F.card := hFcard.symm
      _ ≤ (Finset.univ.filter (fun a => orderOf a = hyp.q)).card := Finset.card_le_card hFsub
      _ = hyp.q.totient := htot
  rw [Nat.totient_prime hyp.q_prime] at hle
  have := hyp.q_prime.two_le
  omega

/-- `Q = T_F` is nontrivial: any type-`P` witness on `T` (available from `T_nonI` via
`typePData_of_isTypeNonI`) records `H = T_F` noncyclic, and `⊥` is cyclic. -/
theorem Hypothesis.Q_ne_bot [Finite G] (hyp : Hypothesis (G := G)) : hyp.Q ≠ ⊥ := by
  obtain ⟨tpd⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  intro hbot
  apply tpd.H_noncyclic
  rw [tpd.H_eq, ← hyp.Q_eq_TF, hbot]
  infer_instance

/-- **`N_G(Q) = T`** — the `T`-side mirror of the (8.5.a) normalizer identity: `Q = T_F` is a
nontrivial `T`-normal subgroup of the maximal `T` of the minimal simple `G`, hence
self-normalizing at `T` (`normalizer_eq_self_of_subgroupOf_normal_of_ne_bot`). -/
theorem normalizer_Q_eq_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Subgroup.normalizer (hyp.Q : Set G) = hyp.T := by
  refine OddOrder.BG.Ch4.S16.normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG
    hyp.T_maximal ?_ ?_ hyp.Q_ne_bot
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.T

/-- **`V` is nilpotent** — the `U`-factor of `T`'s reconciled type-`P` datum.  `V` and any type-`P`
complement `tpd0.U` (from `typePData_of_isTypeNonI T_nonI`) both complement `Q = T_F` in `T' = QV`
(`derived_complement` / `Q_inf_V_eq_bot` + `T_deriv_eq_QV`), so Schur–Zassenhaus conjugacy inside
`↥T'` (`IsComplement'.exists_conj_of_coprime`, coprimality from `Q` being Hall in `T`) conjugates
`tpd0.U` onto `V`, transporting `Group.IsNilpotent` (`tpd0.U_nilpotent`).  Structurally the mirror
of the `S16` complement-conjugacy transport `isMulCommutative_typePData_U_of_V`.  Discharges the
`U_nilpotent` field of `reconciled_typePData_T` without matching the full `T`-side type-`P` datum.
-/
theorem Hypothesis.isNilpotent_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : Group.IsNilpotent ↥hyp.V := by
  obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  have hQtpd : tpd0.H = hyp.Q := by rw [tpd0.H_eq, ← hyp.Q_eq_TF]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hU_le : tpd0.U ≤ derivedInG hyp.T := tpd0.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  -- `Q` complements `V` in `T'`.
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  -- `Q` complements `tpd0.U` in `T'` (from `tpd0.derived_complement`, `tpd0.H = Q`).
  have hUcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tpd0.U.subgroupOf (derivedInG hyp.T)) := by
    rw [← hQtpd]; exact tpd0.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    have hcard : Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.Q.subgroupOf (derivedInG hyp.T)).index ∣
        (hyp.Q.subgroupOf hyp.T).index := by
      have htower : hyp.Q.relIndex (derivedInG hyp.T) *
          (derivedInG hyp.T).relIndex hyp.T = hyp.Q.relIndex hyp.T :=
        Subgroup.relIndex_mul_relIndex hyp.Q (derivedInG hyp.T) hyp.T hQ_le hM'_le_T
      change hyp.Q.relIndex (derivedInG hyp.T) ∣ hyp.Q.relIndex hyp.T
      exact ⟨(derivedInG hyp.T).relIndex hyp.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  have hQsolv : Group.IsSolvable ↥hyp.Q := hG.isSolvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : Group.IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      Group.IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  -- Schur–Zassenhaus conjugates `tpd0.U` onto `V` inside `T'`; push nilpotency forward.
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hUcompl hVcompl
  have : Group.IsNilpotent ↥tpd0.U := tpd0.U_nilpotent
  have h1 : Group.IsNilpotent ↥(tpd0.U.subgroupOf (derivedInG hyp.T)) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hU_le).symm
  have := h1
  have h2 : Group.IsNilpotent
      ↥((tpd0.U.subgroupOf (derivedInG hyp.T)).map (MulAut.conj n).toMonoidHom) :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective)
  have h3 : Group.IsNilpotent ↥(hyp.V.subgroupOf (derivedInG hyp.T)) := hn ▸ h2
  have := h3
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hV_le)

set_option backward.isDefEq.respectTransparency false in
/-- **A type-`P` datum on `T` whose complement is the abstract `V` (and whose kernel is `Q`).**
The §13-level producer `typePData_of_isTypeNonI T_nonI` gives *some* `tpd0 : TypePData T`; its
complement `tpd0.U` and the §16-chosen `V` both complement `Q = T_F` in `T' = QV`, so
Schur–Zassenhaus
inside `↥T'` (`IsComplement'.exists_conj_of_coprime`) conjugates `tpd0.U` onto `V` by an element
`g ∈ T'` (hence `g ∈ T`).  Because `g ∈ T`, conjugation by `g` fixes both `T` and its normal
`Q = T_F`, so whole-datum conjugation `tpd0.conj (MulAut.conj g)` — which transports *every* field
of
`TypePData` (including `fitting_eq` and `secondDerived_le_fitting`) — again lands on `T`, with its
`U`-field equal to `V` and its `H`-field equal to `Q`.  This is the honest engine behind the
`fitting_eq`/`secondDerived_le_fitting`/`U_nilpotent` fields of `reconciled_typePData_T`. -/
theorem Hypothesis.exists_typePData_U_eq_V [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ d : TypePData hyp.T, d.U = hyp.V ∧ d.H = hyp.Q := by
  obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
  have hQtpd : tpd0.H = hyp.Q := by rw [tpd0.H_eq, ← hyp.Q_eq_TF]
  have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hU_le : tpd0.U ≤ derivedInG hyp.T := tpd0.U_le
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  -- `Q` complements `V` in `T'` (verbatim from `isNilpotent_V`).
  have hVcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (hyp.V.subgroupOf (derivedInG hyp.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
          (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
        (hyp.V.subgroupOf (derivedInG hyp.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hUcompl : (hyp.Q.subgroupOf (derivedInG hyp.T)).IsComplement'
      (tpd0.U.subgroupOf (derivedInG hyp.T)) := by
    rw [← hQtpd]; exact tpd0.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)))
      ((hyp.Q.subgroupOf (derivedInG hyp.T)).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
    rw [← hyp.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    have hcard : Nat.card ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.Q.subgroupOf (derivedInG hyp.T)).index ∣
        (hyp.Q.subgroupOf hyp.T).index := by
      have htower : hyp.Q.relIndex (derivedInG hyp.T) *
          (derivedInG hyp.T).relIndex hyp.T = hyp.Q.relIndex hyp.T :=
        Subgroup.relIndex_mul_relIndex hyp.Q (derivedInG hyp.T) hyp.T hQ_le hM'_le_T
      change hyp.Q.relIndex (derivedInG hyp.T) ∣ hyp.Q.relIndex hyp.T
      exact ⟨(derivedInG hyp.T).relIndex hyp.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.T_maximal).1)
  have hQsolv : Group.IsSolvable ↥hyp.Q := hG.isSolvable_of_lt_top hyp.Q hQ_lt_top
  have hsolv : Group.IsSolvable ↥(hyp.Q.subgroupOf (derivedInG hyp.T)) ∨
      Group.IsSolvable (↥(derivedInG hyp.T) ⧸ hyp.Q.subgroupOf (derivedInG hyp.T)) :=
    Or.inl (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hUcompl hVcompl
  -- The conjugator, coerced to `G`.
  set g : G := (↑n : G) with hgdef
  have hg_mem_T' : g ∈ derivedInG hyp.T := n.2
  have hg_mem_T : g ∈ hyp.T := hM'_le_T hg_mem_T'
  -- Lift the `subgroupOf`-level conjugacy `hn` to a `G`-level equation `conj g • U = V`.
  have hcomp : (derivedInG hyp.T).subtype.comp (MulAut.conj n).toMonoidHom
      = (MulAut.conj g).toMonoidHom.comp (derivedInG hyp.T).subtype := by
    ext k
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hgdef, Subgroup.coe_mul, Subgroup.coe_inv]
  have hUmap : tpd0.U.map (MulAut.conj g).toMonoidHom = hyp.V := by
    have key := congrArg (Subgroup.map (derivedInG hyp.T).subtype) hn
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hU_le, Subgroup.map_subgroupOf_eq_of_le hV_le] at key
    exact key
  have hUV : (MulAut.conj g) • tpd0.U = hyp.V := by
    rw [pointwise_mulAut_smul_eq_map]; exact hUmap
  -- Conjugation by `g ∈ T` fixes `T` and its normal `Q`.
  have hgT : (MulAut.conj g) • hyp.T = hyp.T := Subgroup.conj_smul_eq_self_of_mem hg_mem_T
  have hgQ : (MulAut.conj g) • hyp.Q = hyp.Q := by
    have hgN : ∀ h, h ∈ hyp.Q ↔ g * h * g⁻¹ ∈ hyp.Q := by
      have := Subgroup.mem_set_normalizer_iff.mp (hT_le_NQ hg_mem_T)
      simpa only [SetLike.mem_coe] using this
    ext x
    rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hgN y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hgN (g⁻¹ * x * g)).mpr ?_, ?_⟩
      · rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x from by group]
      · change MulAut.conj g (g⁻¹ * x * g) = x
        simp only [MulAut.conj_apply]; group
  -- Whole-datum conjugation, cast back to `TypePData T`.  The `.U`/`.H` projections have constant
  -- codomain `Subgroup G`, so they commute with the `▸` cast on the index (proved by `subst` on a
  -- fresh index variable — `hgT` itself has `T` on both sides, so casing it directly fails).
  have hcastU : ∀ {S : Subgroup G} (h : S = hyp.T) (d : TypePData S), (h ▸ d).U = d.U := by
    intro S h d; subst h; rfl
  have hcastH : ∀ {S : Subgroup G} (h : S = hyp.T) (d : TypePData S), (h ▸ d).H = d.H := by
    intro S h d; subst h; rfl
  refine ⟨hgT ▸ tpd0.conj (MulAut.conj g), ?_, ?_⟩
  · rw [hcastU hgT, show (tpd0.conj (MulAut.conj g)).U = (MulAut.conj g) • tpd0.U from rfl, hUV]
  · rw [hcastH hgT, show (tpd0.conj (MulAut.conj g)).H = (MulAut.conj g) • tpd0.H from rfl, hQtpd,
      hgQ]

/-- **`M'` is a Hall subgroup of a type-`P` maximal** (`Coprime |M'| [M:M']`).  A `κ(M)`-Hall `K`
exists (`exists_isHallSubgroup_kappa_ge`, `X := ⊥`), is cyclic (Theorem 14.7 `typeP_duality`:
`K ⊔ K*` cyclic) and complements `M'` (`typeP_derivedInG_isComplement_kappaHall`); then
`coprime_card_derived_kappaHall_of_isComplement'` gives `(|M'|, |K|) = 1` with `|K| = [M : M']`.

This is the coprimality behind the Schur–Zassenhaus conjugacy of complements to `M'` — it is
**ungated** (needs only `IsTypeP M`), so the earlier belief that `p ∤ |T'|` requires
`FieldNormalizerData` (via `W2_card_coprime_Q_card`/`Q_elementaryAbelian`) was too pessimistic: the
`κ`-Hall route supplies it directly.  Used to align a type-`P` datum's `κ`-factor to any given
complement of `M'` (e.g. the abstract `W₂` on `T`, `W2_isComplement_T_deriv`). -/
theorem coprime_card_derivedInG_index_of_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP M) :
    Nat.Coprime (Nat.card ↥(derivedInG M)) ((derivedInG M).subgroupOf M).index := by
  classical
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (bot_le (a := M))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstar
  have hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hKhall hKstar
    have : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcompl :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hKhall
  have hcop :=
    OddOrder.BG.Ch4.S14.coprime_card_derived_kappaHall_of_isComplement' hKhall hcompl
  have h1 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  have h2 : Nat.card ↥(K.subgroupOf M) = ((derivedInG M).subgroupOf M).index :=
    (hcompl.symm.index_eq_card).symm
  rwa [h1, h2] at hcop

/-- **Fact A: `W₂` is a `κ`-Hall of `T`** (ungated).  `W₂` complements `T'`
(`W2_isComplement_T_deriv`); a produced `κ(T)`-Hall `K` (`exists_isHallSubgroup_kappa_ge`, cyclic,
also complementing `T'`) is `T`-conjugate to `W₂` by Schur–Zassenhaus
(`IsComplement'.exists_conj_of_coprime`, coprimality `coprime_card_derivedInG_index_of_isTypeP`);
Hall-ness transfers along the conjugation (`IsHallSubgroup.mulAut_smul`). This discharges the
`hFactA`
residual of `reconciled_typePData_T` with no `FieldNormalizerData`/(14.9) input. -/
theorem Hypothesis.W2_isKappaHall_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.T)
      (hyp.W2.subgroupOf hyp.T) := by
  classical
  have hP := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.T_maximal hyp.T_nonI
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hyp.T_maximal (bot_le (a := hyp.T))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (K : Set G) with hKstar
  have hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hyp.T_maximal hP hKM hKhall hKstar
    have : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcomplK :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hyp.T_maximal hP hKM hKhall
  have : Group.IsSolvable ↥hyp.T := hG.isSolvable_of_mem_maximalSubgroups hyp.T_maximal
  have hNnorm : ((derivedInG hyp.T).subgroupOf hyp.T).Normal := by
    rw [show (derivedInG hyp.T).subgroupOf hyp.T = commutator ↥hyp.T from
      Subgroup.comap_map_eq_self_of_injective hyp.T.subtype_injective (commutator ↥hyp.T)]
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T))
      ((derivedInG hyp.T).subgroupOf hyp.T).index := by
    have hderivM_le : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
    have hcard : Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T) = Nat.card ↥(derivedInG hyp.T) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hderivM_le).toEquiv
    rw [hcard]
    exact coprime_card_derivedInG_index_of_isTypeP hG hyp.T_maximal hP
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance)
    hcomplK hyp.W2_isComplement_T_deriv
  have hHall := hKhall.mulAut_smul (MulAut.conj n)
  rw [pointwise_mulAut_smul_eq_map] at hHall
  rw [show ((MulAut.conj n).toMonoidHom : ↥hyp.T →* ↥hyp.T) = ↑(MulAut.conj n) from rfl] at hn
  rwa [hn] at hHall

/-- **A complement of `M'` in a type-`P` maximal is a `κ(M)`-Hall subgroup** (ungated, generic).
Extracted from the `W₂`/`T` argument (`W2_isKappaHall_T`): a produced `κ(M)`-Hall `K` is cyclic and
complements `M'` (`typeP_derivedInG_isComplement_kappaHall`); Schur–Zassenhaus
(`coprime_card_derivedInG_index_of_isTypeP`) conjugates it onto any given complement `W` of `M'` in
`M`, and Hall-ness transfers along the conjugation (`IsHallSubgroup.mulAut_smul`).  Used for the
`S`-side Fact A (`W₁` κ-Hall of `S`, via the carried `Sdata.M_complement`). -/
theorem isKappaHall_of_isComplement_derivedInG [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M W : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : OddOrder.BG.Ch4.S14.IsTypeP M)
    (hWcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W.subgroupOf M)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (W.subgroupOf M) := by
  classical
  obtain ⟨K, hKM, hKhall, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (bot_le (a := M))
      (fun q hq => by rw [Subgroup.card_bot] at hq; simp at hq)
  set Kstar : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstar
  have hKcyc : IsCyclic ↥K := by
    obtain ⟨_, _, _, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
      OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hKhall hKstar
    have : IsCyclic ↥(K ⊔ Kstar) := hcyc
    exact Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  have hcomplK :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hKhall
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hNnorm : ((derivedInG M).subgroupOf M).Normal := by
    rw [show (derivedInG M).subgroupOf M = commutator ↥M from
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)]
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      ((derivedInG M).subgroupOf M).index := by
    have hderivM_le : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hcard : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hderivM_le).toEquiv
    rw [hcard]
    exact coprime_card_derivedInG_index_of_isTypeP hG hM hP
  obtain ⟨n, -, hn⟩ := Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance)
    hcomplK hWcompl
  have hHall := hKhall.mulAut_smul (MulAut.conj n)
  rw [pointwise_mulAut_smul_eq_map] at hHall
  rw [show ((MulAut.conj n).toMonoidHom : ↥M →* ↥M) = ↑(MulAut.conj n) from rfl] at hn
  rwa [hn] at hHall

/-- **Fact A (`S`-side): `W₁` is a `κ`-Hall of `S`** (ungated).  `W₁` complements `S'`
(the carried `Sdata.M_complement`, reconciled to `W₁` via `Sdata_W1_eq`), so
`isKappaHall_of_isComplement_derivedInG` applies.  The `S`-side companion of `W2_isKappaHall_T`,
used to feed `typeP_duality`/`exists_partner`/`kappaHall_primes_subset_sigma_partner` on `S`. -/
theorem Hypothesis.W1_isKappaHall_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.S)
      (hyp.W1.subgroupOf hyp.S) := by
  have hPS := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  have hW1compl : Subgroup.IsComplement' ((derivedInG hyp.S).subgroupOf hyp.S)
      (hyp.W1.subgroupOf hyp.S) := by
    have h := hyp.Sdata.M_complement
    rwa [hyp.Sdata_W1_eq] at h
  exact isKappaHall_of_isComplement_derivedInG hG hyp.S_maximal hPS hW1compl

/-- **Fact B (`S`-side): `M_σ(S) ⊓ C_G(W₁) = W₂`** (the (8.4.d) centralizer law for `S`, ungated).
`⊆`: `M_σ(S) ≤ S'` (`Msigma_le_derived`), then `S' ⊓ C(W₁) = W₂` is the carried datum
`Sdata.derivedInG_inf_centralizer_W1_eq` (reconciled via `Sdata_W1_eq`/`Sdata_W2_eq`).  `⊇`:
`W₂ = Sdata.W2 ≤ Sdata.H = M_F(S) ≤ M_σ(S)` (the general
`maxNilpotentNormalHall_le_Msigma` inclusion)
and `W₂ ≤ C(W₁)` (`W1_commutes_W2`).  This is the `Kstar = W₂` identification that lets
`typeP_duality`/`typeP_partner_structure` on `S` output Fact B (`W₁ = M_σ(Mstar) ⊓ C(W₂)`) for the
partner. -/
theorem Hypothesis.Msigma_S_inf_centralizer_W1_eq_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) = hyp.W2 := by
  classical
  have hSder : derivedInG hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) = hyp.W2 := by
    have h := hyp.Sdata.derivedInG_inf_centralizer_W1_eq
    rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq] at h
    exact h
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · calc OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G)
        ≤ derivedInG hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) :=
          inf_le_inf_right _ (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hyp.S_maximal)
      _ = hyp.W2 := hSder
  · calc hyp.W2 = hyp.Sdata.W2 := hyp.Sdata_W2_eq.symm
      _ ≤ hyp.Sdata.H := le_trans hyp.Sdata.W2_le inf_le_left
      _ = maxNilpotentNormalHall hyp.S := hyp.Sdata.H_eq
      _ ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S :=
        OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hyp.W1_commutes_W2 x hx y hy

/-- **`opiCoreInG` is conjugation-equivariant** (public form of the S14/S10 private helpers, needed
for the `Msigma` conjugation used in the `S15` pairing carve-out).  `φ • O_π(H) = O_π(φ • H)` via
`oPiCore.map_eq_of_mulEquiv` transported along the conjugation isomorphism `↥H ≃* ↥(φ • H)`. -/
theorem opiCoreInG_conj_smul [Finite G] (π : Set ℕ) (φ : MulAut G) (H : Subgroup G) :
    φ • OddOrder.GroupTheory.opiCoreInG π H
      = OddOrder.GroupTheory.opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (pointwise_mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • OddOrder.GroupTheory.opiCoreInG π H
      = (OddOrder.GroupTheory.opiCoreInG π H).map (φ : G →* G) := pointwise_mulAut_smul_eq_map φ _
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by
        rw [Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥H).map
          ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((OddOrder.Isaacs.Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map
          (φ • H).subtype := by rw [← Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv]

/-- **`M_σ` is conjugation-equivariant** (`M_σ(Mᵍ) = M_σ(M)ᵍ`, public form).  From
`opiCoreInG_conj_smul` and `sigma_conj_smul_eq` (`σ(Mᵍ) = σ(M)`). -/
theorem Msigma_conj_smul_eq [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S10.Msigma (MulAut.conj g • M)
      = MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
  simp only [OddOrder.BG.Ch3.S10.Msigma]
  rw [OddOrder.BG.Ch4.S14.sigma_conj_smul_eq, ← opiCoreInG_conj_smul]

/-- **Fact B (`T`-side): `W₁ = M_σ(T) ⊓ C_G(W₂)`** (the (8.4.d)-dual centralizer law for `T`,
ungated via the type-`P` pairing — Coq `PFsection8` `typeP_cent_compl`/`FTtypeP_pair_witness`).

This is the last residual of `reconciled_typePData_T` (issue 9073); it is genuine §13 pairing
content
proved *without* assuming `(14.9)`/`IsTypeII T`, by descending to `S`'s type-`P` structure:

* Apply `typeP_duality`/`exists_partner`/`typeP_partner_structure` to `S` (`hKS` = Fact A for `S`,
  `hKstarSW2` = Fact B for `S`, `Kstar = W₂`): the partner `Mstar` satisfies Fact B *for* `Mstar`,
  `W₁ = M_σ(Mstar) ⊓ C(W₂)` (`hKeq`), plus `W₂` is a `κ`-Hall of `Mstar` and the pair is
  nonconjugate to `S`.
* `Mstar` is `G`-conjugate to `T`: `theorem88_caseB` at `Mstar` (type-`P`, non-`I`, `≁ S`) leaves
  only `∃g, Mstarᵍ = T`.
* `⊇`: `q ∈ σ(Mstar) = σ(T)` (`kappaHall_primes_subset_sigma_partner` + `sigma_conj_smul_eq`), so
  the
  `q`-group `W₁ ≤ T` lands in the normal Hall `σ(T)`-subgroup `M_σ(T)`
  (`sigma_subgroup_le_Msigma_of_isHall`), and `W₁ ≤ C(W₂)` (`W1_commutes_W2`).
* `⊆`/cardinality: a fix-`W` correction (`exists_conj_eq_of_isHall_subgroupOf`, matching the two
  `κ`-Halls `W₂` of `T`, `Mstar`) gives `n` with `Tⁿ = Mstar`, `W₂ⁿ = W₂`, whence
  `(M_σ(T) ⊓ C(W₂))ⁿ = M_σ(Mstar) ⊓ C(W₂) = W₁`, so `|M_σ(T) ⊓ C(W₂)| = |W₁|`; with `⊇` and
  `eq_of_le_of_card_ge` this forces equality. -/
theorem Hypothesis.W1_eq_Msigma_T_inf_centralizer_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    hyp.W1 = OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) := by
  classical
  -- `S`-side data.
  have hPS := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
  have hW1S : hyp.W1 ≤ hyp.S :=
    (by rw [hyp.W_eq_join]; exact le_sup_left : hyp.W1 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_left)
  have hW2T : hyp.W2 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hKS := hyp.W1_isKappaHall_S hG
  set KstarS : Subgroup G :=
    OddOrder.BG.Ch3.S10.Msigma hyp.S ⊓ Subgroup.centralizer (hyp.W1 : Set G) with hKstarSdef
  have hKstarSW2 : KstarS = hyp.W2 := by
    rw [hKstarSdef]; exact hyp.Msigma_S_inf_centralizer_W1_eq_W2 hG
  have : Group.IsSolvable ↥hyp.S := hG.isSolvable_of_mem_maximalSubgroups hyp.S_maximal
  obtain ⟨US, hUS'⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥hyp.S)
    ((OddOrder.BG.Ch4.S14.kappa hyp.S ∪ OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ)
  have hU_S : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa hyp.S ∪ OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ)
      ((US.map hyp.S.subtype).subgroupOf hyp.S) := by
    have hUSeq : (US.map hyp.S.subtype).subgroupOf hyp.S = US :=
      Subgroup.comap_map_eq_self_of_injective hyp.S.subtype_injective US
    rw [hUSeq]; exact hUS'
  -- Partner `Mstar` of `S` (Theorem 14.7), with Fact B *for* `Mstar`.
  obtain ⟨Mstar, hMstarne, hmem, hpart⟩ :=
    OddOrder.BG.Ch4.S14.exists_partner hG (OddOrder.BG.Ch4.S14.dummySigmaDecomposition G)
      hyp.S_maximal hPS hW1S hKS hKstarSdef hU_S
  obtain ⟨hMstarmax, hMstarP, hKstarleMstar, hKstar_hall, hKeq⟩ :=
    OddOrder.BG.Ch4.S14.typeP_partner_structure hG hyp.S_maximal hPS hW1S hKS hKstarSdef hU_S
      hmem hMstarne hpart
  rw [hKstarSW2] at hKeq hKstarleMstar hKstar_hall
  -- `hKeq : W₁ = M_σ(Mstar) ⊓ C(W₂)`; `hKstar_hall : W₂ κ-Hall of Mstar`; `W₂ ≤ Mstar`.
  have hncSMstar : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup hyp.S Mstar :=
    OddOrder.BG.Ch4.S14.typeP_family_pairwise_nonconjugate hG hyp.S_maximal hPS hW1S hKS
      hKstarSdef hU_S (Or.inl rfl) hmem (Ne.symm hMstarne)
  have hMstarNotI : ¬ OddOrder.GroupTheory.IsTypeI Mstar := by
    intro hI
    exact absurd ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarmax).1.mp hI)
      (Set.nonempty_iff_ne_empty.mp hMstarP)
  -- `Mstar` is `G`-conjugate to `T`.
  obtain ⟨g, hg⟩ : ∃ g : G, MulAut.conj g • Mstar = hyp.T := by
    rcases hyp.theorem88_caseB Mstar hMstarmax with hI | hS | hT
    · exact absurd hI hMstarNotI
    · exact absurd
        (OddOrder.BG.Ch4.S14.IsConjugateSubgroup.symm
          (hS : OddOrder.BG.Ch4.S14.IsConjugateSubgroup Mstar hyp.S)) hncSMstar
    · exact hT
  -- `q ∈ σ(T)`, hence `W₁ ≤ M_σ(T)` (normal Hall `σ`-subgroup contains every `σ`-subgroup).
  have hqK : hyp.q ∣ Nat.card ↥hyp.W1 := ⟨1, by rw [mul_one]; exact hyp.q_eq_card_W1.symm⟩
  have hqMstar : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma Mstar :=
    OddOrder.BG.Ch4.S14.kappaHall_primes_subset_sigma_partner hG hyp.S_maximal hPS hW1S hKS
      hKstarSdef hU_S hpart hyp.q_prime hqK
  have hqT : hyp.q ∈ OddOrder.BG.Ch3.S10.sigma hyp.T := by
    rw [← hg, OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]; exact hqMstar
  have hW1T : hyp.W1 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_left : hyp.W1 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hW1piT : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
      (OddOrder.BG.Ch3.S10.sigma hyp.T) hyp.W1 := by
    intro r hr
    have hpf : (Nat.card ↥hyp.W1).primeFactors = {hyp.q} := by
      rw [← hyp.q_eq_card_W1, Nat.Prime.primeFactors hyp.q_prime]
    rw [hpf, Finset.mem_singleton] at hr
    rw [hr]; exact hqT
  have hW1MsigmaT : hyp.W1 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hyp.T_maximal) hW1T hW1piT
  have hSupset : hyp.W1 ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set
      G) :=
    le_inf hW1MsigmaT (by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hyp.W1_commutes_W2 x hx y hy).symm.eq)
  -- fix-`W` correction: a conjugator `n` with `Tⁿ = Mstar` and `W₂ⁿ = W₂`.
  have hg0 : MulAut.conj g⁻¹ • hyp.T = Mstar := by
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hW2hallT := hyp.W2_isKappaHall_T hG
  have hconjW2hall := OddOrder.BG.Ch4.S14.isHall_kappa_subgroupOf_conj g⁻¹ hg0 hW2T hW2hallT
  have hconjW2le : MulAut.conj g⁻¹ • hyp.W2 ≤ Mstar := by
    rw [← hg0]; exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hW2T
  have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstarmax
  obtain ⟨w, hwMstar, hw⟩ := OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf
    inferInstance hconjW2le hKstarleMstar hconjW2hall hKstar_hall
  set n : G := w * g⁻¹ with hn_def
  have hnW2 : MulAut.conj n • hyp.W2 = hyp.W2 := by
    rw [hn_def, map_mul, mul_smul]; exact hw
  have hnT : MulAut.conj n • hyp.T = Mstar := by
    rw [hn_def, map_mul, mul_smul, hg0]
    exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hwMstar)
  -- `(M_σ(T) ⊓ C(W₂))ⁿ = M_σ(Mstar) ⊓ C(W₂) = W₁`.
  have hconj_eq : MulAut.conj n •
      (OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G)) = hyp.W1 := by
    rw [Subgroup.smul_inf, centralizer_pointwise_smul, ← coe_pointwise_smul, hnW2,
      ← Msigma_conj_smul_eq, hnT]
    exact hKeq.symm
  -- cardinality: `|M_σ(T) ⊓ C(W₂)| = |W₁|`, and with `⊇`, equality.
  have hcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓
      Subgroup.centralizer (hyp.W2 : Set G)) = Nat.card ↥hyp.W1 := by
    rw [← hconj_eq, Subgroup.pointwise_smul_def]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective).toEquiv
  exact Subgroup.eq_of_le_of_card_ge hSupset (le_of_eq hcard)

/-- **`reconciled_typePData_T` の 2 residual を pairing facts から** (Fact A ∧ Fact B → 両 field, 実証明).
`W₂` が `T` の `κ`-Hall (**Fact A**) かつ `W₁ = M_σ(T) ⊓ C(W₂)` (**Fact B**) — `typeP_partner_structure`
(`S14`) が `S` の partner に対して供給する 2 つの (8.4.d)-dual pairing facts — があれば、既存の一般
type-`P` 機構 (`typeP_kstar_in_mf` / `typeP_derivedInG_inf_centralizer_kappaElement_eq`, いずれも
`M := T`, `K := W₂`, `K* := W₁`) が `reconciled_typePData_T` の両 field を discharge する:
`W₁ ≤ Q ⊓ T''` (`W2_le` field) と `∀ x ∈ W₂#, T' ⊓ C(x) = W₁` (`centralizer_W1` field)。

これは gated-endpoint skeleton (issue 9073): 2 つの残 obligation を **精密な pairing 2 facts**
(κ-Hall + Kstar 同定) に還元し、その **十分性を実証明で verify** したもの。Fact A + Fact B は
`typeP_partner_structure` を `S` に適用 (κ-Hall `W₁`, `Kstar = M_σ(S)⊓C(W₁) = W₂`) すれば
partner `Mstar = T` に対し供給される。 -/
theorem Hypothesis.reconciled_residuals_of_pairing_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hFactA : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa hyp.T)
      (hyp.W2.subgroupOf hyp.T))
    (hFactB : hyp.W1 = OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G)) :
    hyp.W1 ≤ hyp.Q ⊓ secondDerivedInAmbient hyp.T ∧
      (∀ x ∈ hyp.W2, x ≠ 1 →
        derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) = hyp.W1) := by
  have hW2T : hyp.W2 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  have hP := OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.T_maximal hyp.T_nonI
  refine ⟨?_, ?_⟩
  · -- `W2_le`: `W₁ = K* ≤ M_F(T) ⊓ T''` from `typeP_kstar_in_mf` (Corollary 15.6).
    have hk := OddOrder.BG.Ch4.S15.typeP_kstar_in_mf hG hyp.T_maximal hP hW2T hFactA hFactB
    rw [hyp.Q_eq_TF]
    exact le_inf hk.2.2.1 hk.2.2.2.1
  · -- `centralizer_W1`: `T' ⊓ C(x) = K* = W₁` for `x ∈ W₂#` (Theorem A(5) + Dedekind).
    exact OddOrder.BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq
      hG hyp.T_maximal hP hW2T hFactA hFactB

/-- **T-side type-`P` structure reconciled to the abstract `V`/`W₂`** (the honest replacement for
the withdrawn `Tdata` spine carrier; HUB tick² 2026-06-30). `T` is type non-I (`T_nonI`), hence
type-`P`,
and the §16-chosen complement `V` (κ-Hall-invariant) / cyclic factor `W₂` form a type-`P`
decomposition of `T`: there is a `TypePData T` with `.U = V`, `.W1 = W₂`, and `.W2 = W₁` (the dual
cyclic factor `C_{T'}(W₂#)` of `T`'s type-`P` structure is exactly the shared `W₁`).

This is the genuine §13 reconciliation — **TRUE**, and the right §13-level statement: it asserts
only
the *general* type-`P` structure of `T` (available from `T_nonI` at §13), reconciled to the abstract
`V`/`W₂`.  (The sharper `IsTypeP2 T` is *equivalent* to the (14.9) conclusion `IsTypeII T` by the BG
type dictionary `proposition_type_classification` — `IsTypeII M ↔ IsTypeP2 M` — but is not needed
for
the reconciliation itself, so this stays a clean §13 obligation.)  It lives **off the FT spine**:
the `V`-side helpers cite this obligation, keeping `section16TypePStructure_of_isMinimalSimpleOdd`
sorry-free.  Gated on §13; introduced sorried and since proved.  (Relocated from `S15_SAndT`
for the (13.9)/(13.10)
counting layer — the type-V exclusion of `Q_sharp_isTISubset` and the `|T|` decomposition read
it.) -/
theorem reconciled_typePData_T [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∃ data : TypePData hyp.T, data.U = hyp.V ∧ data.W1 = hyp.W2 ∧ data.W2 = hyp.W1 := by
  -- `W₂, W₁ ≤ W` from the (13.1) join `W = W₁ ⊔ W₂`, and `W ≤ T` from `W = S ⊓ T`.
  have hW2W : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
  have hW1W : hyp.W1 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_left
  have hWT : hyp.W ≤ hyp.T := by rw [hyp.W_eq_inter]; exact inf_le_right
  have hWcyc : IsCyclic ↥hyp.W := hyp.W_cyclic
  -- Cyclic factors: a subgroup of the cyclic `W` is cyclic (transport along `subgroupOfEquivOfLe`).
  have hW2cyc : IsCyclic ↥hyp.W2 :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hW2W).surjective
  have hW1cyc : IsCyclic ↥hyp.W1 :=
    isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hW1W).surjective
  -- **(8.4.d)-dual pairing residuals** for the `W2_le`/`centralizer_W1` fields. These are exactly
  -- the
  -- two facts `typeP_partner_structure` (applied to `S`) supplies for its partner `T`: `W₂` a
  -- `κ`-Hall
  -- of `T` (**Fact A**) and `W₁ = M_σ(T) ⊓ C(W₂)` (**Fact B**).  Their *sufficiency* is verified by
  -- `reconciled_residuals_of_pairing_facts` (via `typeP_kstar_in_mf` /
  -- `typeP_derivedInG_inf_centralizer_kappaElement_eq`); the two residuals are honestly gated on
  -- the
  -- §13 `typeP_partner` port (issue 9073) whose remaining step wires `typeP_partner_structure`'s
  -- inputs
  -- (S-side κ-Hall + Z-family covering) from the abstract `Hypothesis`.
  -- **Fact A** (`W₂` κ-Hall of `T`) is now proven ungated (`W2_isKappaHall_T`, via the produced
  -- κ-Hall + Schur–Zassenhaus).  **Fact B** (`W₁ = M_σ(T) ⊓ C(W₂)`) remains the sole residual — the
  -- reverse cyclic-factor identification, supplied by `typeP_partner_structure` applied to `S`.
  have hFactA := hyp.W2_isKappaHall_T hG
  have hFactB : hyp.W1 =
      OddOrder.BG.Ch3.S10.Msigma hyp.T ⊓ Subgroup.centralizer (hyp.W2 : Set G) :=
    hyp.W1_eq_Msigma_T_inf_centralizer_W2 hG
  obtain ⟨hW2le_pf, hCentW1_pf⟩ := hyp.reconciled_residuals_of_pairing_facts hG hFactA hFactB
  refine ⟨{
    H := hyp.Q
    U := hyp.V
    W1 := hyp.W2
    W2 := hyp.W1
    W := hyp.W
    H_eq := hyp.Q_eq_TF
    H_le := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
    U_le := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
    W1_le := hW2W.trans hWT
    -- **Precise residual (`W2_le`, goal `hyp.W1 ≤ hyp.Q ⊓ secondDerivedInAmbient hyp.T`).**
    -- This is the T-side dual of the *carried* S-side field `Sdata.W2_le` (`W₂ ≤ P ⊓ S''`).  Both
    -- halves are `IsTypeP2 hyp.T` (≡ `IsTypeII hyp.T`, BG (14.9))-gated, which is unavailable at
    -- §13 (`IsTypeII hyp.T` lives in `S16` = import-downstream; see `T_typeII`):
    --   • `hyp.W1 ≤ hyp.Q`: needs `hyp.q ∣ Nat.card ↥hyp.Q`; every route (`card_Q_eq`,
    --     `exists_sylow_coe_eq_Q`, `pgroup_le_of_normal_coprime_index` dualizing `W2_le_P`)
    -- requires
    --     `IsTypeII hyp.T` — `q ∣ |Q|` is provably NOT derivable from `hG`+`hyp` alone.  The S-side
    --     `W2_le_P` instead consumes the type-uniform `|P| = p^q` theorem `card_P_eq`.
    --   • `hyp.W1 ≤ secondDerivedInAmbient hyp.T`: needs the intrinsic identification
    --     `hyp.W1 = tpd.W2 = C_{T'}(W₂#)` for a type-`P` datum `tpd` whose `.W1 = W₂`.  The datum
    --     `d` from `exists_typePData_U_eq_V` only pins `d.U = V`, `d.H = Q` (the Schur–Zassenhaus
    --     conjugator controls the *complement*, not the cyclic factors), so `d.W1`/`d.W2` need not
    -- be
    --     the abstract `W₂`/`W₁`.  The alignment is the `typeP_pair` content (Coq PFsection8
    --     `FTtypeP_pair_witness`/`of_typeP_pair`: the shared `W = S ⊓ T` forces T's swapped
    --     decomposition `xdefW : W₂ \x W₁ = W`, whose (8.4.d) component gives `W₁ ⊆ H ⊓ T''`) —
    --     unported to Lean, and equivalent to supplying `IsTypeP2 hyp.T`.
    -- Discharged from the pairing residuals `hFactA`/`hFactB` via the verified reduction
    -- `reconciled_residuals_of_pairing_facts` (`typeP_kstar_in_mf`: `K* ≤ M_F ⊓ M''`).  See the
    -- preamble; the residual is now the precise Fact A + Fact B (`typeP_partner_structure` inputs).
    W2_le := hW2le_pf
    W_eq := by rw [hyp.W_eq_join, sup_comm]
    W_cyclic := hyp.W_cyclic
    W1_nontrivial := by
      intro h; have hp := hyp.p_prime.one_lt
      rw [hyp.p_eq_card_W2, h, Subgroup.card_bot] at hp; exact absurd hp (by norm_num)
    W2_nontrivial := by
      intro h; have hq := hyp.q_prime.one_lt
      rw [hyp.q_eq_card_W1, h, Subgroup.card_bot] at hq; exact absurd hq (by norm_num)
    W1_cyclic := hW2cyc
    W2_cyclic := hW1cyc
    -- `T = T' ⋊ W₂`: the honest field `W2_isComplement_T_deriv` (ungated, threaded from the §16
    -- `typeP_derivedInG_isComplement_kappaHall`).  No longer `sorry`.
    M_complement := hyp.W2_isComplement_T_deriv
    W1_normalizes_U := hyp.W2_normalizes_V
    U_nilpotent := hyp.isNilpotent_V hG
    -- `V` complements `Q = T_F` in `T'`: disjointness is the honest field `Q_inf_V_eq_bot`
    -- (ungated, threaded from the §16 `exists_kappaHall_invariant_complement_to_MF`); the join
    -- `Q ⊔ V = T'` is `T_deriv_eq_QV`.  No longer `sorry`.
    derived_complement := by
      have hQ_le : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
      have hV_le : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
      have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
      have hT_le_NQ : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
        rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
      have hQn_normal : (hyp.Q.subgroupOf (derivedInG hyp.T)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
      refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
      · rw [disjoint_iff]
        ext ⟨x, hx⟩
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
          OneMemClass.coe_one]
        refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
        have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) := ⟨hxQ, hxV⟩
        rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
      · have hsup : (hyp.Q.subgroupOf (derivedInG hyp.T)) ⊔
            (hyp.V.subgroupOf (derivedInG hyp.T)) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.T_deriv_eq_QV.symm,
              Subgroup.subgroupOf_self]
        have hmul := Subgroup.normal_mul (hyp.Q.subgroupOf (derivedInG hyp.T))
          (hyp.V.subgroupOf (derivedInG hyp.T))
        rw [hsup, Subgroup.coe_top] at hmul
        exact hmul.symm
    H_noncyclic := by
      -- `H := Q = maxNilpotentNormalHall T` is the *intrinsic* Fitting Hall (choice-independent),
      -- so `¬ IsCyclic ↥Q` is read off any type-`P` datum on `T`.  The §13-level producer
      -- `typePData_of_isTypeNonI T_nonI` supplies one (no `T_typeII`/(14.9) needed, keeping this a
      -- clean §13 obligation): its `H_noncyclic` is `¬ IsCyclic` of the same subgroup `Q`.
      obtain ⟨tpd0⟩ := OddOrder.GroupTheory.typePData_of_isTypeNonI hyp.T_nonI
      have hHeq : tpd0.H = hyp.Q := by rw [tpd0.H_eq, hyp.Q_eq_TF]
      exact hHeq ▸ tpd0.H_noncyclic
    -- `T`-side (8.5.a) Fitting containment/identity, transported from *any* type-`P` datum on `T`
    -- whose complement is `V` and whose kernel is `Q` (`exists_typePData_U_eq_V`, honest
    -- whole-datum
    -- conjugation via `TypePData.conj`). No longer gated: these are genuine consequences of
    -- `T_nonI`.
    secondDerived_le_fitting := by
      obtain ⟨d, hU, hH⟩ := hyp.exists_typePData_U_eq_V hG
      have := d.secondDerived_le_fitting; rwa [hH, hU] at this
    fitting_eq := by
      obtain ⟨d, hU, hH⟩ := hyp.exists_typePData_U_eq_V hG
      have := d.fitting_eq; rwa [hH, hU] at this
    -- **Precise residual (`centralizer_W1`, goal after instantiation `W1 := hyp.W2`,
    -- `W2 := hyp.W1`,
    -- `M := hyp.T`):
    -- `∀ x ∈ hyp.W2, x ≠ 1 → derivedInG hyp.T ⊓ Subgroup.centralizer ({x}) = hyp.W1`.**
    -- This is the dual cyclic-factor law `C_{T'}(W₂#) = W₁` (Coq (8.4.d) `{in W1^#, C_M'[·] = W2}`
    -- with the swapped `xdefW`).  It is the T-side reflection of the *carried* S-side field
    -- `Sdata.centralizer_W1` (`∀ x ∈ W₁#, S' ⊓ C(x) = W₂`; see its use in
    -- `normalizer_U_inf_W2_eq_bot_of_data`, which crucially also cites the carried `Sdata_W2_eq`).
    -- The ungated general-type-`P` centralizer law `typeP_centralizer_kappaElement_eq`
    -- (`M ⊓ C_G(k) = K ⊔ K*` for `k ∈ K#`, only `IsTypeP M`) would apply to `T` with `K := W₂`,
    -- but ONLY once `W₂` is known to be a κ-Hall of `T` and `K* = M_σ(T) ⊓ C(W₂) = W₁` — precisely
    -- the `typeP_pair` reconciliation (≡ `IsTypeP2 hyp.T`), which the abstract `Hypothesis` does
    -- not
    -- carry (no `Tdata`).  Discharged from `hFactA`/`hFactB` via the verified reduction
    -- `reconciled_residuals_of_pairing_facts` (`typeP_derivedInG_inf_centralizer_kappaElement_eq`).
    centralizer_W1 := hCentW1_pf
    normalizer_V := by
      -- The `W`-exceptional-set normalizer `N_G(X) = W` is symmetric in `W₁`/`W₂`, so it is read
      -- off
      -- the S-side carrier `Sdata.normalizer_V` (same fact as `base_W_normalizer_V`, inlined since
      -- S15
      -- is upstream of S16).  The exceptional set `W − (W₂ ∪ W₁) = W − (W₁ ∪ W₂)` is `union_comm`.
      have hWeq : hyp.Sdata.W = hyp.W := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hyp.W_eq_join.symm
      intro X hX hXsub
      rw [← hWeq]
      refine hyp.Sdata.normalizer_V X hX ?_
      rw [hWeq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, Set.union_comm]
      exact hXsub
  }, rfl, rfl, rfl⟩

/-- **`Q^#` is a TI-subset of `G` with normalizer `T`** — the `T`-side mirror of
`H_sharp_isTISubset`, feeding the (13.10.2)/(13.10.3) `Q`-orbit counting.  For `T` of type
II/III/IV the TI property is the `TypePNontrivialCore` field of the type datum (Peterfalvi
(8.6.a)), with the bound pinned to `T` by `normalizer_Q_eq_T`; type V is excluded by `|V| ≠ 1`
(a type-V witness has `U = ⊥`, and `|V| = |tpd.U|` for the reconciled datum by the
witness-independence `card_U_eq_index`). -/
theorem Q_sharp_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    IsTISubset (sharpSubgroup hyp.Q) hyp.T := by
  classical
  have hQnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
  have hcore : ∀ tpd : TypePData hyp.T, TypePNontrivialCore hyp.T tpd →
      IsTISubset (sharpSubgroup hyp.Q) hyp.T := by
    intro tpd hcore
    have hTI := hcore.2.2
    rw [← hyp.Q_eq_TF] at hTI
    rwa [hQnorm] at hTI
  rcases hyp.T_nonI with h | h | h | h
  · exact hcore h.some.typeP h.some.common
  · exact hcore h.some.typeP h.some.common
  · exact hcore h.some.typeP h.some.common
  · -- Type V: excluded by `v·d = |V| ≠ 1`.
    exfalso
    obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
    have vdata := h.some
    have hcardU : Nat.card ↥tpd.U = Nat.card ↥vdata.typeP.U := by
      rw [tpd.card_U_eq_index, vdata.typeP.card_U_eq_index]
    rw [hU, vdata.U_eq_bot, Subgroup.card_bot, hyp.card_V_eq_vd] at hcardU
    exact hvd hcardU

/-- **(13.2.a)-on-`T`, router form**: `T` is of type II, III or IV — the `T_nonI` classification
minus type V, which is excluded by `|V| = v·d ≠ 1` (a type-V witness has `U = ⊥`, and `|V| =
|tpd.U|` for the reconciled datum by the witness-independence `card_U_eq_index`; the same
exclusion as `Q_sharp_isTISubset`).  This is what the §9 machinery's `TypesIIIIIIVSetup.type_alt`
consumes — the finer (13.2.a) "II or III" (type-IV exclusion, Pf (11.9.b,c) on `T`) is not needed
for the router. -/
theorem Hypothesis.T_typeII_or_III_or_IV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    IsTypeII hyp.T ∨ IsTypeIII hyp.T ∨ IsTypeIV hyp.T := by
  rcases hyp.T_nonI with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    obtain ⟨tpd, hU', -, -⟩ := reconciled_typePData_T hG hyp
    have vdata := h.some
    have hcardU : Nat.card ↥tpd.U = Nat.card ↥vdata.typeP.U := by
      rw [tpd.card_U_eq_index, vdata.typeP.card_U_eq_index]
    rw [hU', vdata.U_eq_bot, Subgroup.card_bot, hyp.card_V_eq_vd] at hcardU
    exact hvd hcardU

end PairStructure

end OddOrder.Peterfalvi.S15


