-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Lemma95
-- name    : OddOrder_BG_Ch2_Uniqueness_S09_Lemma95
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:39:50.088397+00:00
-- url     : https://prove2.me/theorems/e3a92711-fb7b-4cc4-8dd0-91bf69516911
-- title:
--   BG §9: Lemma 9.5, chief-factor data for Corollary 4.19
-- statement:
--   The later part of the formalization of Lemma 9.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §9. It packages the data needed to apply BG Corollary 4.19 to a local chief factor and builds chief-series layers from it, in several variants (ambient $q$-core, absorption, nilpotent).
--
--   Main declarations: `Cor419ChiefFactorData` (Data needed to apply BG Corollary 4.19 to one local chief factor `U/V`); `cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG`; `cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG_absorption` (Choose the chief-factor prime and package Corollary 4.19 data from the ambient `q`-core of `K`); `cor419ChiefFactorData_chiefSeriesInside_of_nilpotent` (Nilpotent version of the chief-series Corollary 4.19 data package).
--
--   The bundle also proves 38 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S09_Lemma95.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S09_Lemma95.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_ChiefSeriesStabilizer

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- If a subgroup centralizes every chief factor in `chiefSeriesInside K`, it
stabilizes that chief series. This is the exact shape needed to feed the Lemma
1.9 bridge after Corollary 4.19 gives chief-factor centralization. -/
private theorem chiefSeries_stabilizer_of_le_chiefFactorCentralizer
    {M : Type*} [Group M] [Finite M] {K D E : Subgroup M} [K.Normal]
    (hDE : D ≤ E)
    (hcent : ∀ i, E ≤ chiefFactorCentralizer
      (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))) :
    ∀ i, ⁅chiefSeriesInside K i, D⁆ ≤ chiefSeriesInside K (i + 1) := by
  intro i
  exact chiefFactorCentralizer.commutator_le_of_le ((hDE).trans (hcent i))

/-- Corollary 4.19 output plus Lemma 1.9 input, already composed: if `D` is
coprime to `K`, lies in a subgroup `E`, and `E` centralizes every chief factor
of `K`, then `D` centralizes `K`. -/
private theorem le_centralizer_of_le_chiefFactorCentralizer_chain
    {M : Type*} [Group M] [Finite M] {K D E : Subgroup M} [K.Normal]
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥K))
    (hsolv : Group.IsSolvable ↥D ∨ Group.IsSolvable ↥K)
    (hDE : D ≤ E)
    (hcent : ∀ i, E ≤ chiefFactorCentralizer
      (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))) :
    D ≤ Subgroup.centralizer (K : Set M) :=
  coprime_chiefSeries_stabilizer_le_centralizer hcop hsolv
    (chiefSeries_stabilizer_of_le_chiefFactorCentralizer hDE hcent)

/-- A centralizer conclusion proved in the local group `↥H` lifts back to the
ambient group. This is the final direction needed after applying Corollary 4.19
inside `L ∩ M`. -/
private theorem le_centralizer_of_subgroupOf_le_centralizer
    {H K P0 : Subgroup G} (hP0H : P0 ≤ H) (hKH : K ≤ H)
    (hlocal : P0.subgroupOf H ≤
      Subgroup.centralizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H)) :
    P0 ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hxH : x ∈ H := hP0H hx
  have hkH : k ∈ H := hKH hk
  have hxlocal : (⟨x, hxH⟩ : ↥H) ∈ P0.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hklocal : (⟨k, hkH⟩ : ↥H) ∈ K.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hk
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp (hlocal hxlocal)
      (⟨k, hkH⟩ : ↥H) hklocal)

/-- Data needed to apply BG Corollary 4.19 to one local chief factor `U/V`.
The prime and the rank-two normal `p`-subgroup are factor-specific; this is the
shape produced later from the `D ∩ L` rank bound in Lemma 9.5. -/
private structure Cor419ChiefFactorData (M : Type*) [Group M] [Finite M]
    (U V : Subgroup M) [V.Normal] where
  q : ℕ
  q_prime : q.Prime
  q_odd : Odd q
  R : Subgroup M
  R_normal : R.Normal
  R_pgroup : IsPGroup q ↥R
  R_rank : pRank ↥R q ≤ 2
  Ubar_pgroup : IsPGroup q ↥(U.map (QuotientGroup.mk' V))
  U_le_sup : U ≤ R ⊔ V

/-- A chief factor of a finite solvable group is a `q`-group for some prime `q`.
This isolates the prime-selection part needed when Lemma 9.5 feeds a local chief
factor into BG Corollary 4.19. -/
private theorem exists_prime_isPGroup_chiefFactor_quotient
    {M : Type*} [Group M] [Finite M] [Group.IsSolvable M]
    {U V : Subgroup M} (hChief : IsChiefFactor U V) :
    haveI : V.Normal := hChief.normal_bot
    ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(U.map (QuotientGroup.mk' V)) := by
  have : V.Normal := hChief.normal_bot
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
    hChief.isMinimalNormal_map_quotient
  obtain ⟨q, hq, hElem⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hMin
  exact ⟨q, hq, hElem.isPGroup⟩

/-- In an odd-order ambient group, the prime attached to a nontrivial chief-factor
`q`-group quotient is odd. -/
private theorem odd_prime_of_chiefFactor_quotient_isPGroup
    {M : Type*} [Group M] [Finite M] (hoddM : Odd (Nat.card M))
    {q : ℕ} (hq : q.Prime) {U V : Subgroup M} (hChief : IsChiefFactor U V)
    (hUbar_pgroup :
      haveI : V.Normal := hChief.normal_bot
      IsPGroup q ↥(U.map (QuotientGroup.mk' V))) :
    Odd q := by
  have : V.Normal := hChief.normal_bot
  have : Fact q.Prime := ⟨hq⟩
  have hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
    hChief.isMinimalNormal_map_quotient
  have hUbar_ne : U.map (QuotientGroup.mk' V) ≠ ⊥ := hMin.2.1
  have hcard_ne_one : Nat.card ↥(U.map (QuotientGroup.mk' V)) ≠ 1 := by
    intro hcard
    exact hUbar_ne (Subgroup.eq_bot_of_card_eq _ hcard)
  have hq_dvd_Ubar : q ∣ Nat.card ↥(U.map (QuotientGroup.mk' V)) := by
    rcases hUbar_pgroup.card_eq_or_dvd with hcard | hdvd
    · exact False.elim (hcard_ne_one hcard)
    · exact hdvd
  have hq_dvd_quot : q ∣ Nat.card (M ⧸ V) :=
    hq_dvd_Ubar.trans (Subgroup.card_subgroup_dvd_card (U.map (QuotientGroup.mk' V)))
  exact hoddM.of_dvd_nat (hq_dvd_quot.trans (Subgroup.card_quotient_dvd_card V))

/-- The ambient `q`-core of a rank-two normal subgroup has `q`-rank at most two.
This is the rank input needed when Lemma 9.5 uses `O_q(D ∩ L)` as the Corollary
4.19 subgroup for a `q`-primary chief factor. -/
private theorem pRank_opiCoreInG_singleton_le_two_of_rank_le_two
    {M : Type*} [Group M] [Finite M] {q : ℕ} [Fact q.Prime] {K : Subgroup M}
    (hK_rank : rank ↥K ≤ 2) :
    pRank ↥(opiCoreInG ({q} : Set ℕ) K) q ≤ 2 := by
  exact (pRank_le_rank
      (G := ↥(opiCoreInG ({q} : Set ℕ) K)) q).trans
    ((rank_le_of_injective
      (f := Subgroup.inclusion (opiCoreInG_le ({q} : Set ℕ) K))
      (Subgroup.inclusion_injective (opiCoreInG_le ({q} : Set ℕ) K))).trans hK_rank)

/-- A finite subgroup that is both a `p`-group and a `q`-group for distinct
prime numbers is trivial. -/
private theorem eq_bot_of_isPGroup_of_isPGroup_ne
    {M : Type*} [Group M] [Finite M] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) {H : Subgroup M} (hp : IsPGroup p ↥H) (hq : IsPGroup q ↥H) :
    H = ⊥ := by
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥H) :=
    IsPGroup.coprime_card_of_ne p q hpq H H hp hq
  exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl)

/-- If the image of `P` in `M/V` is trivial, then `P ≤ V`. -/
private theorem le_of_map_quotient_eq_bot
    {M : Type*} [Group M] {V P : Subgroup M} [V.Normal]
    (h : P.map (QuotientGroup.mk' V) = ⊥) : P ≤ V := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  exact h

/-- In a finite nilpotent normal subgroup, a `q`-primary chief-series layer is
absorbed by `O_q(K)` modulo the next layer. -/
private theorem chiefSeriesInside_le_opiCoreInG_sup_of_nilpotent
    {M : Type*} [Group M] [Finite M] {q : ℕ} [Fact q.Prime]
    {K : Subgroup M} [K.Normal] (hKnilp : Group.IsNilpotent ↥K) (i : ℕ)
    (hUbar_pgroup :
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1))))) :
    chiefSeriesInside K i ≤
      opiCoreInG ({q} : Set ℕ) K ⊔ chiefSeriesInside K (i + 1) := by
  classical
  let U : Subgroup M := chiefSeriesInside K i
  let V : Subgroup M := chiefSeriesInside K (i + 1)
  let X : Subgroup M := opiCoreInG ({q} : Set ℕ) K ⊔ V
  have hU_le_K : U ≤ K := by
    simpa [U] using chiefSeriesInside_le K i
  have hU_nilp : Group.IsNilpotent ↥U := by
    have : Group.IsNilpotent ↥K := hKnilp
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hU_le_K)
  change U ≤ X
  refine S08.le_of_sylow_le_of_nilpotent hU_nilp ?_
  intro r
  have hrFact : Fact (Nat.Prime (r : ℕ)) :=
    ⟨Nat.prime_of_mem_primeFactors r.2⟩
  let S : Sylow (r : ℕ) ↥U := default
  let Sm : Subgroup M := (S : Subgroup ↥U).map U.subtype
  have hSm_le_U : Sm ≤ U := by
    simpa [Sm] using Subgroup.map_subtype_le (S : Subgroup ↥U)
  have hSm_le_K : Sm ≤ K := hSm_le_U.trans hU_le_K
  by_cases hrq : (r : ℕ) = q
  · have hSm_q : IsPGroup q ↥Sm := by
      simpa [S, Sm, hrq] using ((S : Sylow (r : ℕ) ↥U).isPGroup'.map U.subtype)
    have hSm_le_O : Sm ≤ opiCoreInG ({q} : Set ℕ) K :=
      S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hKnilp hSm_le_K hSm_q
    have hSm_le_X : Sm ≤ X := hSm_le_O.trans le_sup_left
    simpa [S, Sm, X] using hSm_le_X
  · have hSm_r : IsPGroup (r : ℕ) ↥Sm := by
      simpa [S, Sm] using ((S : Sylow (r : ℕ) ↥U).isPGroup'.map U.subtype)
    have hSmq_r : IsPGroup (r : ℕ) ↥(Sm.map (QuotientGroup.mk' V)) :=
      hSm_r.map (QuotientGroup.mk' V)
    have hSmq_le_Ubar :
        Sm.map (QuotientGroup.mk' V) ≤ U.map (QuotientGroup.mk' V) :=
      Subgroup.map_mono hSm_le_U
    have hSmq_q : IsPGroup q ↥(Sm.map (QuotientGroup.mk' V)) := by
      simpa [U, V] using hUbar_pgroup.to_le hSmq_le_Ubar
    have hSmq_bot : Sm.map (QuotientGroup.mk' V) = ⊥ :=
      eq_bot_of_isPGroup_of_isPGroup_ne hrq hSmq_r hSmq_q
    have hSm_le_V : Sm ≤ V := le_of_map_quotient_eq_bot hSmq_bot
    have hSm_le_X : Sm ≤ X := hSm_le_V.trans le_sup_right
    simpa [S, Sm, X] using hSm_le_X

/-- Package one chief-series layer using the ambient `q`-core of `K` as the
rank-two normal `q`-subgroup required by BG Corollary 4.19.  The only remaining
mathematical input is the nilpotent/Hall-style absorption `U ≤ O_q(K) V`, which
is kept explicit here. -/
private def cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG
    {M : Type*} [Group M] [Finite M] {q : ℕ} (hq_prime : q.Prime) (hq_odd : Odd q)
    {K : Subgroup M} [K.Normal] (hK_rank : rank ↥K ≤ 2) (i : ℕ)
    (hUbar_pgroup :
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1)))))
    (hU_le_sup :
      chiefSeriesInside K i ≤ opiCoreInG ({q} : Set ℕ) K ⊔ chiefSeriesInside K (i + 1)) :
    Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  refine
    { q := q
      q_prime := hq_prime
      q_odd := hq_odd
      R := opiCoreInG ({q} : Set ℕ) K
      R_normal := opiCoreInG_normal ({q} : Set ℕ)
      R_pgroup := isPGroup_opiCoreInG_singleton K
      R_rank := pRank_opiCoreInG_singleton_le_two_of_rank_le_two hK_rank
      Ubar_pgroup := hUbar_pgroup
      U_le_sup := hU_le_sup }

/-- Choose the chief-factor prime and package Corollary 4.19 data from the
ambient `q`-core of `K`.  After the rank and oddness bridges, the only remaining
input is the nilpotent absorption statement `U ≤ O_q(K) V`. -/
private noncomputable def cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG_absorption
    {M : Type*} [Group M] [Finite M] [Group.IsSolvable M] (hoddM : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hK_rank : rank ↥K ≤ 2) (i : ℕ)
    (hU_ne : chiefSeriesInside K i ≠ ⊥)
    (habsorb : ∀ q : ℕ, q.Prime →
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1)))) →
      chiefSeriesInside K i ≤ opiCoreInG ({q} : Set ℕ) K ⊔ chiefSeriesInside K (i + 1)) :
    Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  classical
  have hChief : IsChiefFactor (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
    isChiefFactor_chiefSeriesInside hU_ne
  let ex := exists_prime_isPGroup_chiefFactor_quotient hChief
  let q : ℕ := Classical.choose ex
  have hq : q.Prime := (Classical.choose_spec ex).1
  have hUbar_pgroup :
      IsPGroup q ↥((chiefSeriesInside K i).map
        (QuotientGroup.mk' (chiefSeriesInside K (i + 1)))) :=
    (Classical.choose_spec ex).2
  exact cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG
    hq (odd_prime_of_chiefFactor_quotient_isPGroup hoddM hq hChief hUbar_pgroup)
    hK_rank i hUbar_pgroup (habsorb q hq hUbar_pgroup)

/-- Nilpotent version of the chief-series Corollary 4.19 data package. -/
private noncomputable def cor419ChiefFactorData_chiefSeriesInside_of_nilpotent
    {M : Type*} [Group M] [Finite M] [Group.IsSolvable M] (hoddM : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal] (hKnilp : Group.IsNilpotent ↥K)
    (hK_rank : rank ↥K ≤ 2) :
    ∀ i, chiefSeriesInside K i ≠ ⊥ →
      Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  intro i hU_ne
  exact cor419ChiefFactorData_chiefSeriesInside_of_opiCoreInG_absorption
    hoddM hK_rank i hU_ne
    (fun q hq hUbar => by
      have : Fact q.Prime := ⟨hq⟩
      exact chiefSeriesInside_le_opiCoreInG_sup_of_nilpotent (q := q) hKnilp i hUbar)

/-- Turn per-factor BG Corollary 4.19 data into the exact chief-factor
centralizer chain input consumed by the Lemma 1.9 bridge.  Trivial zero layers
of `chiefSeriesInside` are handled without Corollary 4.19 data. -/
private theorem local_derived_le_chiefFactorCentralizer_chain_of_cor419Data
    {M : Type*} [Group M] [Finite M] (hoddM : Odd (Nat.card M))
    {K : Subgroup M} [K.Normal]
    (hdata : ∀ i, chiefSeriesInside K i ≠ ⊥ →
      Cor419ChiefFactorData M (chiefSeriesInside K i) (chiefSeriesInside K (i + 1))) :
    ∀ i, derivedInG (⊤ : Subgroup M) ≤
      chiefFactorCentralizer (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) := by
  intro i
  by_cases hU0 : chiefSeriesInside K i = ⊥
  · rw [chiefFactorCentralizer.le_iff_commutator_le, hU0, Subgroup.commutator_bot_left]
    exact bot_le
  · let d := hdata i hU0
    have hChief : IsChiefFactor (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
      isChiefFactor_chiefSeriesInside hU0
    have : Fact d.q.Prime := ⟨d.q_prime⟩
    have : d.R.Normal := d.R_normal
    have hcomm : _root_.commutator M ≤
        chiefFactorCentralizer (chiefSeriesInside K i) (chiefSeriesInside K (i + 1)) :=
      OddOrder.BG.Ch1.S04.commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup
        (G := M) hoddM d.q_odd hChief d.Ubar_pgroup d.R_pgroup d.R_rank d.U_le_sup
    rw [derivedInG_eq_commutator (G := M) (⊤ : Subgroup M)]
    simpa [_root_.commutator] using hcomm

/-- Local Corollary 4.19 output plus the S09 bridge package: if `P₀ ≤ H'`
and the local derived subgroup of `H` centralizes every chief factor of `K`,
then `P₀` centralizes `K` back in the ambient group. -/
private theorem le_centralizer_of_local_derived_chiefFactorCentralizer_chain
    [Finite G] {H K P0 : Subgroup G} [((K.subgroupOf H : Subgroup ↥H)).Normal]
    (hP0D : P0 ≤ derivedInG H) (hKH : K ≤ H)
    (hcop : (Nat.card ↥(P0.subgroupOf H)).Coprime
      (Nat.card ↥(K.subgroupOf H)))
    (hsolv : Group.IsSolvable ↥(P0.subgroupOf H) ∨ Group.IsSolvable ↥(K.subgroupOf H))
    (hcent : ∀ i, derivedInG (⊤ : Subgroup ↥H) ≤
      chiefFactorCentralizer
        (chiefSeriesInside (K.subgroupOf H) i)
        (chiefSeriesInside (K.subgroupOf H) (i + 1))) :
    P0 ≤ Subgroup.centralizer (K : Set G) := by
  have hP0_local :
      P0.subgroupOf H ≤ derivedInG (⊤ : Subgroup ↥H) :=
    subgroupOf_le_derivedInG_top_of_le_derivedInG hP0D
  have hlocal :
      P0.subgroupOf H ≤
        Subgroup.centralizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    le_centralizer_of_le_chiefFactorCentralizer_chain
      (K := K.subgroupOf H) (D := P0.subgroupOf H)
      (E := derivedInG (⊤ : Subgroup ↥H)) hcop hsolv hP0_local hcent
  exact le_centralizer_of_subgroupOf_le_centralizer
    (hP0D.trans (derivedInG_le_self H)) hKH hlocal

/-- Local BG Corollary 4.19 data plus the S09 bridge package, already composed:
if `P₀ ≤ H'` and every nonzero chief layer of `K` carries Corollary 4.19 data,
then `P₀` centralizes `K` in the ambient group. -/
private theorem le_centralizer_of_local_cor419Data_chain
    [Finite G] {H K P0 : Subgroup G} [((K.subgroupOf H : Subgroup ↥H)).Normal]
    (hoddH : Odd (Nat.card ↥H)) (hP0D : P0 ≤ derivedInG H) (hKH : K ≤ H)
    (hcop : (Nat.card ↥(P0.subgroupOf H)).Coprime
      (Nat.card ↥(K.subgroupOf H)))
    (hsolv : Group.IsSolvable ↥(P0.subgroupOf H) ∨ Group.IsSolvable ↥(K.subgroupOf H))
    (hdata : ∀ i, chiefSeriesInside (K.subgroupOf H) i ≠ ⊥ →
      Cor419ChiefFactorData (↥H)
        (chiefSeriesInside (K.subgroupOf H) i)
        (chiefSeriesInside (K.subgroupOf H) (i + 1))) :
    P0 ≤ Subgroup.centralizer (K : Set G) :=
  le_centralizer_of_local_derived_chiefFactorCentralizer_chain
    hP0D hKH hcop hsolv
    (local_derived_le_chiefFactorCentralizer_chain_of_cor419Data hoddH hdata)

/-- Odd order passes from the ambient group to a subgroup. -/
private theorem odd_card_subgroup_of_odd [Finite G] (hoddG : Odd (Nat.card G))
    (H : Subgroup G) : Odd (Nat.card ↥H) :=
  hoddG.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)

/-- If `D` is normalized by `M` and contained in `M`, then `D ∩ L` is normal
inside `L ∩ M`.  This is the local normality needed before applying chief-series
arguments to `D ∩ L` in BG Lemma 9.5. -/
private theorem inf_subgroupOf_inf_normal_of_le_normalizer
    {D L M : Subgroup G} (hDM : D ≤ M)
    (hMnormD : M ≤ Subgroup.normalizer (D : Set G)) :
    (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))).Normal := by
  have hK_le_H : (D ⊓ L : Subgroup G) ≤ L ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans hDM)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_H).mpr ?_
  intro x hxH
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [Subgroup.mem_inf] at hk ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hMnormD hxH.2) k).mp hk.1
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxH.1) k).mp hk.2
  · intro hk
    rw [Subgroup.mem_inf] at hk ⊢
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hMnormD hxH.2) k).mpr hk.1
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hxH.1) k).mpr hk.2

/-- Lemma 9.5's `D ∩ L` Corollary 4.19 consumption step, specialized to the
local group `L ∩ M`.  Once `(9.10)` gives `P₀ ≤ (L ∩ M).derived` and Corollary
4.19 data is available for every nonzero chief layer of `D ∩ L`, this proves
that `P₀` centralizes `D ∩ L`. -/
private theorem le_centralizer_inf_of_local_cor419Data_chain
    [Finite G] (hG : IsMinimalSimpleOdd G) {D L M P0 : Subgroup G}
    (hDM : D ≤ M) (hMnormD : M ≤ Subgroup.normalizer (D : Set G))
    (hP0_der : P0 ≤ derivedInG (L ⊓ M))
    (hcop : (Nat.card ↥(P0.subgroupOf (L ⊓ M))).Coprime
      (Nat.card ↥((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M))))
    (hsolv :
      Group.IsSolvable ↥(P0.subgroupOf (L ⊓ M)) ∨
        Group.IsSolvable ↥((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)))
    (hdata :
      letI : (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) :
          Subgroup ↥(L ⊓ M))).Normal :=
        inf_subgroupOf_inf_normal_of_le_normalizer hDM hMnormD
      ∀ i,
      chiefSeriesInside ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)) i ≠ ⊥ →
        Cor419ChiefFactorData (↥(L ⊓ M))
          (chiefSeriesInside ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)) i)
          (chiefSeriesInside ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M)) (i + 1))) :
    P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G) := by
  have hDL_le_LM : (D ⊓ L : Subgroup G) ≤ L ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans hDM)
  have : (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) :
      Subgroup ↥(L ⊓ M))).Normal :=
    inf_subgroupOf_inf_normal_of_le_normalizer hDM hMnormD
  exact le_centralizer_of_local_cor419Data_chain
    (H := L ⊓ M) (K := D ⊓ L) (P0 := P0)
    (odd_card_subgroup_of_odd hG.odd (L ⊓ M)) hP0_der hDL_le_LM hcop hsolv hdata

/-- A `π`-subgroup remains a `π`-subgroup when viewed as a subgroup of an
ambient overgroup. -/
private theorem isPiSubgroup_subgroupOf_of_le [Finite G]
    {π : Set ℕ} {K H : Subgroup G} (hKH : K ≤ H)
    (hKpi : Subgroup.IsPiSubgroup π K) :
    Subgroup.IsPiSubgroup π (K.subgroupOf H) := by
  intro r hr
  exact hKpi r (by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at hr)

/-- Nilpotent/rank version of the local `D ∩ L` Corollary 4.19 consumption
step.  The solvability of the local group supplies the chief-factor prime, and
nilpotence supplies the `O_q(K)` absorption for every chief layer. -/
private theorem le_centralizer_inf_of_local_nilpotent_rank_chain
    [Finite G] (hG : IsMinimalSimpleOdd G) {D L M P0 : Subgroup G}
    [Group.IsSolvable ↥(L ⊓ M)]
    (hDM : D ≤ M) (hMnormD : M ≤ Subgroup.normalizer (D : Set G))
    (hP0_der : P0 ≤ derivedInG (L ⊓ M))
    (hcop : (Nat.card ↥(P0.subgroupOf (L ⊓ M))).Coprime
      (Nat.card ↥((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M))))
    (hKnilp : Group.IsNilpotent
      ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))))
    (hK_rank :
      rank ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))) ≤ 2) :
    P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G) := by
  have hK_solv :
      Group.IsSolvable
        ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))) := by
    have : Group.IsNilpotent
        ↥(((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M))) :=
      hKnilp
    infer_instance
  have : (((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) :
      Subgroup ↥(L ⊓ M))).Normal :=
    inf_subgroupOf_inf_normal_of_le_normalizer hDM hMnormD
  exact le_centralizer_inf_of_local_cor419Data_chain
    (D := D) (L := L) (M := M) (P0 := P0)
    hG hDM hMnormD hP0_der hcop (Or.inr hK_solv)
    (cor419ChiefFactorData_chiefSeriesInside_of_nilpotent
      (M := ↥(L ⊓ M))
      (K := ((D ⊓ L : Subgroup G).subgroupOf (L ⊓ M) : Subgroup ↥(L ⊓ M)))
      (odd_card_subgroup_of_odd hG.odd (L ⊓ M)) hKnilp hK_rank)

/-- Lemma 9.5's concrete local centralizer step for
`D = O_{p'}(F(M))`.  If the local `(9.10)` inclusion puts a `p`-subgroup `P₀`
inside `(L ∩ M)'`, then Corollary 4.19 and Lemma 1.9 force `P₀` to centralize
`O_{p'}(F(M)) ∩ L`. -/
private theorem le_centralizer_inf_opiCoreFitting_of_pSubgroup_local_derived
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M L P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G) (hLM : L ≠ M)
    (hP0p : IsPGroup p ↥P0) (hP0_der : P0 ≤ derivedInG (L ⊓ M)) :
    P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M) ⊓ L : Subgroup G) : Set G) := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  let H : Subgroup G := L ⊓ M
  let K : Subgroup G := D ⊓ L
  have hD_le_F : D ≤ S08.fittingInG M := by
    simpa [D] using opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hDM : D ≤ M := hD_le_F.trans (S08.fittingInG_le M)
  have hM_norm_F : M ≤ Subgroup.normalizer (S08.fittingInG M : Set G) := by
    intro x hxM
    exact S08.mem_normalizer_fittingInG_of_mem hxM
  have hMnormD : M ≤ Subgroup.normalizer (D : Set G) := by
    simpa [D] using le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)ᶜ hM_norm_F
  have hK_le_H : K ≤ H := by
    refine le_inf inf_le_right ?_
    exact inf_le_left.trans hDM
  have hP0H : P0 ≤ H := by
    simpa [H] using hP0_der.trans (derivedInG_le_self (L ⊓ M))
  have hD_nilp : Group.IsNilpotent ↥D := by
    have : Group.IsNilpotent ↥(S08.fittingInG M) := S08.fittingInG_isNilpotent M
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hD_le_F)
  have hK_nilp_ambient : Group.IsNilpotent ↥K := by
    have : Group.IsNilpotent ↥D := hD_nilp
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left)
  have hK_nilp :
      Group.IsNilpotent ↥((K.subgroupOf H : Subgroup ↥H)) := by
    have : Group.IsNilpotent ↥K := hK_nilp_ambient
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK_le_H).symm
  have hK_rank_ambient : rank ↥K ≤ 2 := by
    simpa [D, K] using
      (rank_inf_opiCoreFitting_le_two_of_distinct_maximals
        (G := G) (p := p) hG hM hL hLM)
  have hK_rank : rank ↥(K.subgroupOf H) ≤ 2 :=
    (rank_subgroupOf_le_of_le hK_le_H).trans hK_rank_ambient
  have hP0p_local : IsPGroup p ↥(P0.subgroupOf H) :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe hP0H).symm
  have hP0pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) (P0.subgroupOf H) :=
    isPiSubgroup_singleton_of_isPGroup hP0p_local
  have hDpic : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ D := by
    simpa [D] using isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hKpic_ambient : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    intro r hr
    exact hDpic r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hr)
  have hKpic : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (K.subgroupOf H) :=
    isPiSubgroup_subgroupOf_of_le hK_le_H hKpic_ambient
  have hcop : (Nat.card ↥(P0.subgroupOf H)).Coprime (Nat.card ↥(K.subgroupOf H)) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hP0pi hKpic
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hHsolv : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_right : H ≤ M))
      (Subgroup.inclusion_injective (inf_le_right : H ≤ M))
  simpa [D, H, K] using
    (le_centralizer_inf_of_local_nilpotent_rank_chain
      (D := D) (L := L) (M := M) (P0 := P0)
      hG hDM hMnormD (by simpa [H] using hP0_der) hcop hK_nilp hK_rank)

/-- Lemma 9.5's final contradiction for a fixed cocyclic witness `B` and
maximal subgroup `L`: the local `(9.10)` inclusion and Corollary 4.19 force
`P₀` to centralize the subgroup whose noncentralization selected `B`. -/
private theorem false_of_not_le_centralizer_inf_centralizer_opiCoreFitting_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A B M L P P0 : Subgroup G} {y : G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hBA : B ≤ A) (hyB : y ∈ B)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hM : M ∈ maximalSubgroups G) (hLM : L ≠ M)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hnot_cent : ¬ P0 ≤ Subgroup.centralizer
      (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
          Subgroup.centralizer (B : Set G)) : Set G)) :
    False := by
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hP0_der : P0 ≤ derivedInG (L ⊓ M) :=
    p0_le_derivedInG_inf_of_scn3_witness_maximal
      hG hA hAnot (hBA hyB) hL hPp hAP hPnormA hNPM hP0N
  have hcentDL : P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G) := by
    simpa [D] using
      (le_centralizer_inf_opiCoreFitting_of_pSubgroup_local_derived
        (G := G) (p := p) hG hM hL.1 hLM hP0p hP0_der)
  have hcentDB : P0 ≤ Subgroup.centralizer
      (((D ⊓ Subgroup.centralizer (B : Set G) : Subgroup G)) : Set G) :=
    le_centralizer_inf_centralizer_of_le_centralizer_inf_maximal
      (D := D) hyB hL hcentDL
  exact hnot_cent (by simpa [D] using hcentDB)

/-- Lemma 9.5's `P₀` centralizes `O_{p'}(F(M))` bridge.  Assuming the existing
normalizer package for `P`, and characteristic Sylow-series packages for the
witness maximal subgroups produced by Theorem 9.1, the Prop. 1.16 witness
argument cannot find a noncentralized cocyclic centralizer. -/
private theorem p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G))) :
    P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G) := by
  classical
  by_contra hP0D
  obtain ⟨B, y, L, _hBea, _hBnot, _hBΩ, hBA, _hBnc, _hcyc,
      hnot_cent, hyB, _hy1, _hCGnotM, hL, _hLA, hLM⟩ :=
    exists_nonU_cocyclic_omega1_witness_maximal_ne
      hG hAcomm_set hM hA hAnot hP0D
  exact false_of_not_le_centralizer_inf_centralizer_opiCoreFitting_witness
    hG hA hAnot hBA hyB hL hM.1 hLM hPp hAP hPnormA hNPM hP0p hP0N hnot_cent

/-- If a rank-three abelian subgroup of `F(M)` centralizes a nontrivial `P₀ ≤ M`,
then `N_G(P₀)` is uniquely maximal, with unique maximal subgroup `M`.

This is the high-rank bookkeeping used in BG Lemma 9.5 after `(9.11)`: Lemma 9.4
puts the rank-three witness in `𝒰`, and every maximal subgroup over `N_G(P₀)`
also contains that witness. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_fitting_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime]
    {M U P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hUab : IsMulCommutative U) (hUq : IsPGroup q U) (hUrank : 3 ≤ rank ↥U)
    (hUF : U ≤ S08.fittingInG M)
    (hUcentP0 : U ≤ Subgroup.centralizer (P0 : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let N0 : Subgroup G := Subgroup.normalizer (P0 : Set G)
  have h3Uq : 3 ≤ pRank ↥U q :=
    three_le_pRank_of_isPGroup_of_three_le_rank hUq hUrank
  have h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q :=
    h3Uq.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hUF)
        (Subgroup.inclusion_injective hUF))
  have hUU : IsUniquelyMaximal U :=
    (abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3Fq)
      U hUab hUq hUrank
  have hUM : U ≤ M := hUF.trans (S08.fittingInG_le M)
  have hU_le_N0 : U ≤ N0 :=
    hUcentP0.trans (Subgroup.centralizer_le_normalizer (P0 : Set G))
  have hN0lt : N0 < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hN0top
    have : P0.Normal := Subgroup.normalizer_eq_top_iff.mp hN0top
    rcases hG.simple.eq_bot_or_eq_top_of_normal P0 inferInstance with hP0bot | hP0top
    · exact hP0ne hP0bot
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        rw [← hP0top]
        exact hP0M
      exact (mem_maximalSubgroups.mp hM).lt_top.ne (eq_top_iff.mpr htop_le_M)
  obtain ⟨N, hNco, hN0N⟩ :=
    (eq_top_or_exists_le_coatom N0).resolve_left hN0lt.ne
  have hUN : U ≤ N := hU_le_N0.trans hN0N
  have hN_eq_M : N = M :=
    hUU.eq_of_isCoatom_of_le hNco hUN (mem_maximalSubgroups.mp hM) hUM
  have hN0M : N0 ≤ M := hN0N.trans (le_of_eq hN_eq_M)
  have hN0U : IsUniquelyMaximal N0 :=
    IsUniquelyMaximal.of_unique_maximal hN0lt hM hN0M
      (fun N hNco hN0N => by
        have hUN : U ≤ N := hU_le_N0.trans hN0N
        exact hUU.eq_of_isCoatom_of_le hNco hUN (mem_maximalSubgroups.mp hM) hUM)
  exact ⟨hN0U, hN0M⟩

/-- The same uniquely-maximal normalizer bridge specialized to
`D = O_{p'}(F(M))`. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_opiCoreFitting_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M U P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hUab : IsMulCommutative U) (hUq : IsPGroup q U) (hUrank : 3 ≤ rank ↥U)
    (hUD : U ≤ opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M))
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have hDcentP0 : D ≤ Subgroup.centralizer (P0 : Set G) := by
    simpa [D] using (Subgroup.le_centralizer_iff.mp hP0centD)
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_fitting_witness
    hG hM hUab hUq hUrank
    (hUD.trans (by simpa [D] using opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    (hUD.trans hDcentP0) hP0M hP0ne

/-- High `q`-rank version of the `(9.12)` singleton package. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_pRank_opiCoreFitting
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (h3Dq : 3 ≤ pRank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) q)
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  obtain ⟨U, hUmax, hUrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := D) (by simpa [D] using h3Dq)
  have hUea : U.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hUmax
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_rank_three_opiCoreFitting_witness
    hG hM (IsMulCommutative.of_comm hUea.comm) hUea.isPGroup hUrank
    (by simpa [D] using S08.isMaxElemAbelianIn_le hUmax)
    hP0centD hP0M hP0ne

/-- Rank-three `D = O_{p'}(F(M))` singleton form of the normalizer-control bridge. -/
private theorem normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_rank_opiCoreFitting
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    (hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G))
    (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  obtain ⟨q, hq, h3Dq⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥D) (n := 3) (by norm_num)
      (by simpa [D] using h3D)
  have : Fact q.Prime := ⟨hq⟩
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_pRank_opiCoreFitting
    (G := G) (p := p) (q := q) hG hM (by simpa [D] using h3Dq)
    hP0centD hP0M hP0ne

/-- Lemma 9.5 `(9.12)` high-rank singleton package.  Under the normalizer data for
`P` and `P₀`, if `rank O_{p'}(F(M)) ≥ 3`, then `N_G(P₀)` itself lies in `𝒰` and
its unique maximal subgroup is `M`. -/
private theorem normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p ↥P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0p : IsPGroup p ↥P0)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hP0ne : P0 ≠ ⊥)
    (h3D : 3 ≤ rank
      ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)))
    :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) ≤ M := by
  have hP0M : P0 ≤ M :=
    (hP0N.trans (derivedInG_le_self (Subgroup.normalizer (P : Set G)))).trans hNPM
  have hP0centD : P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G) :=
    p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package
      hG hAcomm_set hM hA hAnot hPp hAP hPnormA hNPM hP0p hP0N
  exact normalizer_isUniquelyMaximal_and_le_maximal_of_three_le_rank_opiCoreFitting
    hG hM.1 h3D hP0centD hP0M hP0ne

/-- Low-rank `(9.12)` maximality core: once the low-rank argument has shown
`M ≤ N_G(P₀)`, the nontriviality of `P₀ ≤ M` makes `N_G(P₀)` proper, so maximality
of `M` forces `N_G(P₀) = M` and hence `N_G(P₀) ∈ 𝒰`. -/
private theorem normalizer_isUniquelyMaximal_and_eq_maximal_of_maximal_le_normalizer
    [Finite G] (hG : IsMinimalSimpleOdd G) {M P0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP0M : P0 ≤ M) (hP0ne : P0 ≠ ⊥)
    (hMnormP0 : M ≤ Subgroup.normalizer (P0 : Set G)) :
    IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
      Subgroup.normalizer (P0 : Set G) = M := by
  classical
  let N0 : Subgroup G := Subgroup.normalizer (P0 : Set G)
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hN0lt : N0 < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hN0top
    have : P0.Normal := Subgroup.normalizer_eq_top_iff.mp hN0top
    rcases hG.simple.eq_bot_or_eq_top_of_normal P0 inferInstance with hP0bot | hP0top
    · exact hP0ne hP0bot
    · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        rw [← hP0top]
        exact hP0M
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  have hN0leM : N0 ≤ M :=
    (isCoatom_iff_ge_of_le.mp hMco).2 N0 hN0lt.ne hMnormP0
  have hN0eqM : N0 = M := le_antisymm hN0leM hMnormP0
  have hN0U : IsUniquelyMaximal N0 := by
    refine IsUniquelyMaximal.of_unique_maximal hN0lt hM (le_of_eq hN0eqM) ?_
    intro N hNco hN0N
    have hMN : M ≤ N := (le_of_eq hN0eqM.symm).trans hN0N
    have hNleM : N ≤ M :=
      (isCoatom_iff_ge_of_le.mp hMco).2 N hNco.lt_top.ne hMN
    exact le_antisymm hNleM hMN
  exact ⟨by simpa [N0] using hN0U, by simpa [N0] using hN0eqM⟩

/-- BG Lemma 9.5 (9.9)→`P₀ ≠ 1`: for a Sylow `p`-subgroup `P` of the minimal simple odd group `G`
(with `p ∣ |G|`), `P₀ = ⁅P, N_G(P)⁆ ≠ 1`.  If `P₀ = 1` then `N_G(P) ≤ C_G(P)`, so Burnside
(Theorem 1.18) gives a normal `p`-complement `N`; simplicity forces `N = ⊥` (⇒ `G` a `p`-group,
hence solvable — impossible) or `N = ⊤` (⇒ `P = ⊥`, so `p ∤ |G|`). -/
private theorem commutator_normalizer_ne_bot_of_isSylow [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hp_dvd : p ∣ Nat.card G) :
    ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ ≠ ⊥ := by
  classical
  intro h
  have hNC : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h
  obtain ⟨N, hNnorm, hNcompl⟩ :=
    OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer P hNC
  rcases hG.simple.eq_bot_or_eq_top_of_normal N hNnorm with hNbot | hNtop
  · -- `N = ⊥` ⇒ `P = ⊤` ⇒ `G` is a `p`-group ⇒ solvable, contradicting `hG`.
    have hPtop : (P : Subgroup G) = ⊤ :=
      Subgroup.isComplement'_bot_left.mp (hNbot ▸ hNcompl P)
    have hGp : IsPGroup p G :=
      (hPtop ▸ P.isPGroup' : IsPGroup p ↥(⊤ : Subgroup G)).of_equiv Subgroup.topEquiv
    have := hGp.isNilpotent
    exact hG.notSolvable inferInstance
  · -- `N = ⊤` ⇒ `P = ⊥` ⇒ `p ∤ |G|`, contradicting `hp_dvd`.
    have hPbot : (P : Subgroup G) = ⊥ :=
      Subgroup.isComplement'_top_left.mp (hNtop ▸ hNcompl P)
    have hcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
      P.card_eq_multiplicity
    rw [hPbot, Subgroup.card_bot] at hcard
    have hfact0 : (Nat.card G).factorization p = 0 :=
      (Nat.pow_eq_one.mp hcard.symm).resolve_left (Fact.out : p.Prime).ne_one
    exact ((Fact.out : p.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd).ne' hfact0

/-- In a finite nilpotent group `N`, the `q`-rank for `q ≠ p` is realized inside the `p'`-core
`O_{p'}(N)` (the `q`-Sylow is normal, a `{r ≠ p}`-group, hence lies in `O_{p'}(N)`). -/
private theorem pRank_le_pRank_oPiCore_compl_of_nilpotent
    {N : Type*} [Group N] [Finite N] [Group.IsNilpotent N] {p q : ℕ} [Fact q.Prime] (hqp : q ≠ p) :
    pRank N q ≤ pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} N) q := by
  classical
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow q N))
  have hiff : Group.IsNilpotent N ↔
      ∀ (p' : ℕ) (_hp : Fact p'.Prime) (P : Sylow p' N), (↑P : Subgroup N).Normal :=
    (Group.isNilpotent_of_finite_tfae (G := N)).out 0 3
  have hSnorm : (S : Subgroup N).Normal := hiff.mp inferInstance q inferInstance S
  have hSpi : Ch03.Subgroup.IsPiGroup {r : ℕ | r ≠ p} (S : Subgroup N) := by
    intro r hr
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    rw [hk, Nat.mem_primeFactors] at hr
    have hrq : r = q :=
      (Nat.prime_dvd_prime_iff_eq hr.1 (Fact.out : q.Prime)).mp (hr.1.dvd_of_dvd_pow hr.2.1)
    change r ≠ p
    rw [hrq]; exact hqp
  have hScore : (S : Subgroup N) ≤ Ch03.oPiCore {r : ℕ | r ≠ p} N := hSpi.le_oPiCore
  calc pRank N q = pRank ↥(S : Subgroup N) q := (pRank_sylow_eq S).symm
    _ ≤ pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} N) q :=
        pRank_le_of_injective (Subgroup.inclusion_injective hScore)

/-- If `r_p(F(M)) ≤ 2` and the `p'`-core `O_{p'}(F(M))` has rank ≤ 2, then `F(M)` itself has
rank ≤ 2 (for `q ≠ p`, `F(M)`'s `q`-rank lives in `O_{p'}(F(M))` since `F(M)` is nilpotent). -/
private theorem rank_fitting_subtype_le_two_of_low_rank
    [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (hp' : rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ≤ 2) :
    rank ↥(Ch01.fitting ↥M) ≤ 2 := by
  classical
  have : Group.IsNilpotent ↥(S08.fittingInG M) := S08.fittingInG_isNilpotent M
  have hcompl : (({p} : Set ℕ)ᶜ) = {r : ℕ | r ≠ p} := by
    ext r; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  refine (rank_le_of_injective
    (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype
      M.subtype_injective).toMonoidHom)
    (Subgroup.equivMapOfInjective _ _ M.subtype_injective).injective).trans ?_
  rw [rank_le_iff]
  intro q hq
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqp : q = p
  · subst hqp; exact hp
  · have h1 : pRank ↥(S08.fittingInG M) q ≤
        pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} ↥(S08.fittingInG M)) q :=
      pRank_le_pRank_oPiCore_compl_of_nilpotent hqp
    have h2 : pRank ↥(Ch03.oPiCore {r : ℕ | r ≠ p} ↥(S08.fittingInG M)) q ≤
        pRank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) q := by
      rw [← hcompl]
      exact pRank_le_of_injective
        (f := (Subgroup.equivMapOfInjective (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥(S08.fittingInG M))
          (S08.fittingInG M).subtype (S08.fittingInG M).subtype_injective).toMonoidHom)
        (Subgroup.equivMapOfInjective _ _ (S08.fittingInG M).subtype_injective).injective
    exact (h1.trans h2).trans ((pRank_le_rank q).trans hp')

/-- BG Lemma 9.5 low-rank, the `M'' ≤ F(M')` step (BG L2615 "By Theorem 4.20, M''⊆F"): a maximal
`M` of the minimal simple odd `G` with `r_p(F(M)) ≤ 2` and `rank O_{p'}(F(M)) ≤ 2` (so
`rank F(M) ≤ 2`) satisfies `M' ≤ F(M)` in `G`-coordinates. -/
private theorem derivedInG_le_fittingInG_of_low_rank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hAM : A ≤ M) (hAne : A ≠ ⊥)
    (hp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (hp' : rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ≤ 2) :
    derivedInG M ≤ S08.fittingInG M := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have : Nontrivial ↥M :=
    (Subgroup.nontrivial_iff_ne_bot M).mpr fun hM0 => hAne (le_bot_iff.mp (hM0 ▸ hAM))
  have hoddM : Odd (Nat.card ↥M) := by
    rcases Nat.even_or_odd (Nat.card ↥M) with he | ho
    · exact absurd (he.two_dvd.trans (Subgroup.card_subgroup_dvd_card M))
        (by have := hG.odd; rw [Nat.odd_iff] at this; omega)
    · exact ho
  have hderiv : commutator ↥M ≤ Ch01.fitting ↥M :=
    OddOrder.BG.Ch1.S05.derived_le_fitting_of_rank_fitting_le_two hoddM
      (rank_fitting_subtype_le_two_of_low_rank hp hp')
  exact Subgroup.map_mono hderiv

/-- If `g` normalizes `K`, then conjugation by `g` fixes `K` setwise. -/
private theorem map_conj_eq_self_of_mem_normalizer {g : G} {K : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj g).toMonoidHom = K := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  · intro hy
    exact ⟨g⁻¹ * y * g, (Subgroup.mem_normalizer_iff''.mp hg y).mp hy, by group⟩

/-- `N_G(H)` normalizes the commutator `⁅H, N_G(H)⁆`: conjugation by an element of
`N_G(H)` fixes both `H` and `N_G(H)`, hence fixes their commutator. -/
private theorem normalizer_le_normalizer_commutator_normalizer (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer
        ((⁅H, Subgroup.normalizer (H : Set G)⁆ : Subgroup G) : Set G) := by
  intro g hg
  have key : (⁅H, Subgroup.normalizer (H : Set G)⁆).map (MulAut.conj g).toMonoidHom
      = ⁅H, Subgroup.normalizer (H : Set G)⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_self_of_mem_normalizer hg,
      map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg)]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : (MulAut.conj g) h ∈
        (⁅H, Subgroup.normalizer (H : Set G)⁆).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    rw [key] at hmem
    simpa [MulAut.conj_apply] using hmem
  · intro hh
    have hmem : (MulAut.conj g) h ∈ ⁅H, Subgroup.normalizer (H : Set G)⁆ := by
      simpa [MulAut.conj_apply] using hh
    rw [← key, Subgroup.mem_map] at hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    have hzh : z = h := (MulAut.conj g).injective (by
      simpa [MulEquiv.coe_toMonoidHom] using hzeq)
    rwa [hzh] at hz

/-- A finite nilpotent group is generated by its `p`-core and its `p'`-core. -/
private theorem top_le_oPiCore_singleton_sup_compl_of_isNilpotent
    {K : Type*} [Group K] [Finite K] [Group.IsNilpotent K] (p : ℕ) :
    (⊤ : Subgroup K) ≤
      Ch03.oPiCore ({p} : Set ℕ) K ⊔ Ch03.oPiCore (({p} : Set ℕ)ᶜ) K := by
  classical
  have hfit : Ch01.fitting K = ⊤ := by
    refine top_le_iff.mp ?_
    have : Group.IsNilpotent ↥(⊤ : Subgroup K) := Group.isNilpotent_top.mpr inferInstance
    exact Ch01.nilpotent_normal_le_fitting
  rw [← hfit, Ch01.fitting_eq_iSup_primeFactors]
  refine iSup_le fun q => ?_
  obtain ⟨qval, hq_mem⟩ := q
  have : Fact qval.Prime := ⟨(Nat.mem_primeFactors.mp hq_mem).1⟩
  rw [show (Ch01.opCore qval K) = Ch03.oPiCore ({qval} : Set ℕ) K from
      (Ch04.oPiCore_singleton_eq_opCore qval).symm]
  by_cases hqeq : qval = p
  · exact le_sup_of_le_left
      (Ch03.oPiCore_mono (Set.singleton_subset_iff.mpr (Set.mem_singleton_iff.mpr hqeq)) K)
  · exact le_sup_of_le_right
      (Ch03.oPiCore_mono
        (Set.singleton_subset_iff.mpr (Set.mem_compl_singleton_iff.mpr hqeq)) K)

/-- `F(M) ≤ O_p(F(M)) ⊔ O_{p'}(F(M))` in the ambient group: `F(M)` is nilpotent, so it
is generated by its `p`-core and `p'`-core. -/
private theorem fittingInG_le_opiCoreInG_sup_compl [Finite G] (p : ℕ) (M : Subgroup G) :
    S08.fittingInG M ≤ opiCoreInG ({p} : Set ℕ) (S08.fittingInG M)
      ⊔ opiCoreInG (({p} : Set ℕ)ᶜ) (S08.fittingInG M) := by
  classical
  have : Group.IsNilpotent ↥(S08.fittingInG M) := S08.fittingInG_isNilpotent M
  have hmap := Subgroup.map_mono (f := (S08.fittingInG M).subtype)
    (top_le_oPiCore_singleton_sup_compl_of_isNilpotent (K := ↥(S08.fittingInG M)) p)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap

/-- **BG Lemma 9.5** (mmd L2559): `p` prime, `A ∈ SCN₃(p)` ⇒ `A ∈ 𝒰`。

Proof gate: mmd L2579 uses Thm 7.6 and Thm 7.4; L2605 uses Cor 4.19; L2615 uses
Thm 4.20. The `SCN₃(p)` input is the right interface, so no §5 narrow or Thm 4.16
assumption should be introduced here. -/
theorem scn3_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ S07.scn3Global p G) :
    IsUniquelyMaximal A := by
  classical
  by_contra hAnot
  -- abelian + `p`-group data for `A`
  have hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val
      (isMulCommutative_iff.mp (isMulCommutative_of_mem_scn3Global hA) ⟨x, hx⟩ ⟨y, hy⟩)
  have hAp : IsPGroup p ↥A := isPGroup_of_mem_scn3Global hA
  have hAne : A ≠ ⊥ := ne_bot_of_mem_scn3Global hA
  have h3pRankA : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp (three_le_rank_of_mem_scn3Global hA)
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx; rw [Subgroup.mem_centralizer_iff]; intro y hy; exact (hAcomm_set y hy x hx)
  -- `p ∣ |G|`
  have hp_dvd : p ∣ Nat.card G := by
    have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    have hk1 : k ≠ 0 := by
      rintro rfl; rw [pow_zero] at hk; exact (Finite.one_lt_card (α := ↥A)).ne' hk
    exact (hk ▸ dvd_pow_self p hk1 : p ∣ Nat.card ↥A).trans (Subgroup.card_subgroup_dvd_card A)
  -- the Sylow `p`-subgroup `P` of `G` containing `A` (from `A ∈ SCN₃`), and `P₀ = ⁅P, N_G(P)⁆`
  obtain ⟨PG, hAPG, hSCN⟩ := S07.exists_sylow_of_mem_scn3Global hA
  set P : Subgroup G := (PG : Subgroup G) with hPdef
  have hPp : IsPGroup p ↥P := PG.isPGroup'
  have hAP : A ≤ P := hAPG
  have hPnormA : P ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAPG).mp hSCN.1.isNormal
  set P0 : Subgroup G := ⁅P, Subgroup.normalizer (P : Set G)⁆ with hP0def
  have hP0_le_P : P0 ≤ P := by
    rw [hP0def, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have hbab : b * a⁻¹ * b⁻¹ ∈ P := ((Subgroup.mem_normalizer_iff.mp hb) a⁻¹).mp (P.inv_mem ha)
    have heq : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [heq]
    exact P.mul_mem ha hbab
  have hP0p : IsPGroup p ↥P0 := by
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    obtain ⟨j, _, hj⟩ :=
      (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (hk ▸ Subgroup.card_dvd_of_le hP0_le_P)
    exact IsPGroup.of_card hj
  have hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)) := by
    rw [hP0def, derivedInG_eq_commutator]
    exact Subgroup.commutator_mono Subgroup.le_normalizer le_rfl
  have hP0ne : P0 ≠ ⊥ := commutator_normalizer_ne_bot_of_isSylow hG PG hp_dvd
  -- key `(9.6)→(9.12)`: every maximal `M'` over `C_G(A)` is the unique maximal over `N_G(P₀)`
  have key : ∀ M' : Subgroup G,
      M' ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) →
        IsUniquelyMaximal (Subgroup.normalizer (P0 : Set G)) ∧
          Subgroup.normalizer (P0 : Set G) ≤ M' := by
    intro M' hM'
    have hNPM' : Subgroup.normalizer (P : Set G) ≤ M' :=
      (normalizer_scn3_pSubgroup_le_maximal_of_not_scn3 hG hM' hA hAnot hPp hAP hPnormA).2
    have hP0M' : P0 ≤ M' := hP0_le_P.trans (Subgroup.le_normalizer.trans hNPM')
    by_cases h3D : 3 ≤ rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M'))
    · exact normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package
        hG hAcomm_set hM' hA hAnot hPp hAP hPnormA hNPM' hP0p hP0N hP0ne h3D
    · -- low rank `(9.12)` (BG L2615-2619): `r(F(M')) ≤ 2` ⟹ by Thm 4.20 `M'' ≤ F(M')`, so
      -- `M' = O_{p'}(F(M'))·N_{M'}(P)`; `(9.11)` puts `O_{p'}(F(M'))` in `C_G(P₀)` and
      -- `N_{M'}(P) ≤ N_G(P) ≤ N_G(P₀)`, whence `P₀ ⊴ M'`, i.e. `M' ≤ N_G(P₀)`.
      -- (§9 Phase B sub-assembly 2) the Frattini decomposition:
      -- `derived_le_fitting_of_rank_fitting_le_two`
      -- (Thm 4.20a) applies since `r_p(F)≤2` (here) + `r(O_{p'}(F))≤2` (¬h3D) ⟹ `rank F(M')≤2`
      -- (full).
      have hMN0 : M' ≤ Subgroup.normalizer (P0 : Set G) := by
        -- `(9.6)`: `r_p(F(M')) ≤ 2`, and `¬ h3D` gives `rank O_{p'}(F(M')) ≤ 2`.
        have hpr : pRank ↥(S08.fittingInG M') p ≤ 2 :=
          pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM'.1 hA hAnot
        have hpr' : rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M')) ≤ 2 := by omega
        have hAM' : A ≤ M' := hA_le_C.trans hM'.2
        have hPM' : (P : Subgroup G) ≤ M' := Subgroup.le_normalizer.trans hNPM'
        -- Theorem 4.20(a) inside `↥M'`: `M'' ≤ F(M')`, i.e. `commutator ↥M' ≤ fitting ↥M'`.
        have hderiv : derivedInG M' ≤ S08.fittingInG M' :=
          derivedInG_le_fittingInG_of_low_rank hG hM'.1 hAM' hAne hpr hpr'
        have hcomm_le : commutator ↥M' ≤ Ch01.fitting ↥M' :=
          (Subgroup.map_le_map_iff_of_injective M'.subtype_injective).mp hderiv
        -- `P` as a Sylow `p`-subgroup of `↥M'`, and `FP = F(M') ⊔ P ⊴ M'`.
        let PM' : Sylow p ↥M' := PG.subtype hPM'
        have hPM'coe : (PM' : Subgroup ↥M') = (P : Subgroup G).subgroupOf M' :=
          PG.coe_subtype hPM'
        set FP : Subgroup ↥M' := Ch01.fitting ↥M' ⊔ (P : Subgroup G).subgroupOf M' with hFPdef
        have hcomm_FP : commutator ↥M' ≤ FP := by
          rw [hFPdef]; exact hcomm_le.trans le_sup_left
        have hFPnorm : FP.Normal :=
          Subgroup.Normal.of_commutator_le (G := ↥M') (H := FP) hcomm_FP
        have hPM'_le_FP : (PM' : Subgroup ↥M') ≤ FP := by rw [hPM'coe]; exact le_sup_right
        -- Frattini argument in `↥M'`: `N_{M'}(P) ⊔ FP = ⊤`.
        have hFrat : Subgroup.normalizer ((PM' : Subgroup ↥M') : Set ↥M') ⊔ FP = ⊤ :=
          Sylow.normalizer_sup_eq_top' PM' hPM'_le_FP
        -- `N_G(P) ≤ N_G(P₀)` (conjugation preserves `P₀ = ⁅P, N_G(P)⁆`), hence `P ≤ N_G(P₀)`.
        have hNP_NP0 : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
            Subgroup.normalizer (P0 : Set G) :=
          normalizer_le_normalizer_commutator_normalizer (P : Subgroup G)
        have hP_NP0 : (P : Subgroup G) ≤ Subgroup.normalizer (P0 : Set G) :=
          Subgroup.le_normalizer.trans hNP_NP0
        -- `O_p(F(M')) ≤ P`: a normal `p`-subgroup of `↥M'` lies in the Sylow `P`.
        have hOp_le_P : opiCoreInG ({p} : Set ℕ) (S08.fittingInG M') ≤ (P : Subgroup G) := by
          set Op : Subgroup G := opiCoreInG ({p} : Set ℕ) (S08.fittingInG M') with hOpdef
          have hOp_le_M' : Op ≤ M' := (opiCoreInG_le _ _).trans (S08.fittingInG_le M')
          have hM'_norm_F : M' ≤ Subgroup.normalizer ((S08.fittingInG M') : Set G) :=
            fun x hx => S08.mem_normalizer_fittingInG_of_mem hx
          have hM'_norm_Op : M' ≤ Subgroup.normalizer (Op : Set G) :=
            le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ) hM'_norm_F
          have hOpnorm : (Op.subgroupOf M').Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hOp_le_M').mpr hM'_norm_Op
          have hOpp : IsPGroup p ↥(Op.subgroupOf M') :=
            (isPGroup_opiCoreInG_singleton (S08.fittingInG M')).comap_of_injective
              M'.subtype M'.subtype_injective
          have hsub : Op.subgroupOf M' ≤ (P : Subgroup G).subgroupOf M' := by
            rw [← hPM'coe]
            exact (Ch01.normal_pgroup_le_opCore hOpp).trans (Ch01.opCore_le PM')
          intro x hx
          have hxM' : x ∈ M' := hOp_le_M' hx
          have hmem : (⟨x, hxM'⟩ : ↥M') ∈ (P : Subgroup G).subgroupOf M' :=
            hsub (Subgroup.mem_subgroupOf.mpr hx)
          exact Subgroup.mem_subgroupOf.mp hmem
        -- `F(M') ≤ N_G(P₀)`: `O_p(F) ≤ P ≤ N_G(P₀)` and `O_{p'}(F) ≤ C_G(P₀) ≤ N_G(P₀)`.
        have hFle : S08.fittingInG M' ≤ Subgroup.normalizer (P0 : Set G) := by
          refine (fittingInG_le_opiCoreInG_sup_compl p M').trans (sup_le ?_ ?_)
          · exact hOp_le_P.trans hP_NP0
          · have h911 := p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package
              hG hAcomm_set hM' hA hAnot hPp hAP hPnormA hNPM' hP0p hP0N
            exact (Subgroup.le_centralizer_iff.mp h911).trans
              (Subgroup.centralizer_le_normalizer _)
        -- transport the Frattini decomposition back to `G` and bound by `N_G(P₀)`.
        calc M' = (⊤ : Subgroup ↥M').map M'.subtype := by
                rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
          _ ≤ (Subgroup.normalizer ((PM' : Subgroup ↥M') : Set ↥M') ⊔ FP).map M'.subtype :=
                Subgroup.map_mono hFrat.ge
          _ = (Subgroup.normalizer ((PM' : Subgroup ↥M') : Set ↥M')).map M'.subtype
                ⊔ FP.map M'.subtype := Subgroup.map_sup _ _ _
          _ ≤ Subgroup.normalizer (P0 : Set G) := by
                refine sup_le ?_ ?_
                · rw [hPM'coe]
                  refine (Subgroup.le_normalizer_map M'.subtype).trans ?_
                  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPM']
                  exact hNP_NP0
                · rw [hFPdef, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
                    inf_eq_left.mpr hPM']
                  exact sup_le hFle hP_NP0
      obtain ⟨hU, hEq⟩ :=
        normalizer_isUniquelyMaximal_and_eq_maximal_of_maximal_le_normalizer
          hG hM'.1 hP0M' hP0ne hMN0
      exact ⟨hU, le_of_eq hEq⟩
  obtain ⟨M, hM⟩ := exists_maximalSubgroupsContaining_centralizer_of_mem_scn3Global hG hA
  obtain ⟨hUniq, hN0M⟩ := key M hM
  -- final contradiction: `Ω₁(A) ∉ 𝒰` ⟹ Theorem 9.1 gives `x` with `C_G(x) ⊄ M`, so a maximal
  -- `M* ⊇ C_G(x)` lies in `𝓜(C_G(A))` and `M* ≠ M`; but `(9.12)` forces `M = M*`.
  set W : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set with hWdef
  have hWA : W ≤ A := fun x hx => OddOrder.GroupTheory.omega1OfAbelian_le hx
  have hWnot : ¬ IsUniquelyMaximal W :=
    not_isUniquelyMaximal_of_le_scn3_counterexample hG hAcomm_set hA hWA hAnot
  have hWea : W.IsElementaryAbelian p :=
    OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian (hH := hAcomm_set)
  have hWnc : ¬ IsCyclic ↥W :=
    not_isCyclic_omega1OfAbelian_of_three_le_pRank hAcomm_set h3pRankA
  have hWleM : W ≤ M := hWA.trans (hA_le_C.trans hM.2)
  have hncase := mt (noncyclic_isUniquelyMaximal_of_centralizer_le hG hM.1 hWea hWleM hWnc) hWnot
  rw [not_or] at hncase
  have hfirst := hncase.1
  push Not at hfirst
  obtain ⟨x, hxW, hx1, hxnotM⟩ := hfirst
  -- `Z(G) = ⊥`, hence `C_G(x) < ⊤`
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (Group.isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hCxlt : Subgroup.centralizer ({x} : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hCtop
    have hxZ : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [hCtop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg x (Set.mem_singleton x)).symm
    rw [hZbot, Subgroup.mem_bot] at hxZ
    exact hx1 hxZ
  obtain ⟨Mstar, hMstarCo, hCMstar⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer ({x} : Set G))).resolve_left hCxlt.ne
  have hMstarA : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) :=
    maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton (hWA hxW)
      ⟨hMstarCo, hCMstar⟩
  obtain ⟨_, hN0Mstar⟩ := key Mstar hMstarA
  have hMM : M = Mstar :=
    hUniq.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hM.1) hN0M hMstarCo hN0Mstar
  exact hxnotM (hMM ▸ hCMstar)

/-- A local `SCN₃(P)` subgroup of a Sylow subgroup, viewed in `G`, is a global
`SCN₃(p)` subgroup. -/
private theorem scn3Global_of_scn3_sylow [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {A : Subgroup ↥(P : Subgroup G)}
    (hA : IsSCN₃ p A) :
    A.map (P : Subgroup G).subtype ∈ S07.scn3Global p G := by
  classical
  have hAP : A.map (P : Subgroup G).subtype ≤ (P : Subgroup G) :=
    Subgroup.map_subtype_le A
  refine ⟨P, hAP, ?_⟩
  have htarget :
      (A.map (P : Subgroup G).subtype).subgroupOf (P : Subgroup G) = A := by
    apply (Subgroup.map_subtype_inj (H := (P : Subgroup G))).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hAP]
  rwa [htarget]

/-- If `K` has rank at least two, then `C_G(K)` is proper. -/
theorem centralizer_lt_top_of_two_le_rank [Finite G] (hG : IsMinimalSimpleOdd G)
    {K : Subgroup G} (hr : 2 ≤ rank ↥K) :
    Subgroup.centralizer (K : Set G) < ⊤ := by
  classical
  have hZbot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exact absurd (Group.isSolvable_of_comm fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm) hG.notSolvable
  have hKne : K ≠ ⊥ := by
    obtain ⟨p, hp, A, _hAea, hAK, hAnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank K hr
    intro hKbot
    have hA_bot : A = ⊥ := le_bot_iff.mp (hAK.trans (le_of_eq hKbot))
    have : Nontrivial ↥A := Nontrivial.of_not_isCyclic hAnc
    exact ((Subgroup.nontrivial_iff_ne_bot A).mp inferInstance) hA_bot
  rw [lt_top_iff_ne_top]
  intro hCtop
  have hKleZ : K ≤ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp hCtop
  have hKbot : K = ⊥ := by
    exact le_bot_iff.mp (hKleZ.trans (le_of_eq hZbot))
  exact hKne hKbot

/-- Proper form of BG Theorem 9.6 for the branch `r(K) ≥ 3`. -/
theorem isUniquelyMaximal_of_three_le_rank_of_lt_top [Finite G]
    (hG : IsMinimalSimpleOdd G) {K : Subgroup G} (hKlt : K < ⊤)
    (hr3 : 3 ≤ rank ↥K) :
    IsUniquelyMaximal K := by
  classical
  obtain ⟨p, hp, hpRankK⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥K) (n := 3) (by norm_num) hr3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨B₀, hB₀ea, hB₀log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank
      (G := ↥K) (p := p) (n := 3) (by norm_num) hpRankK
  let B : Subgroup G := B₀.map K.subtype
  have hBea : B.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map K.subtype_injective hB₀ea
  have hBK : B ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hBlog : 3 ≤ Nat.log p (Nat.card B) := by
    rw [show B = B₀.map K.subtype from rfl,
      Subgroup.card_map_of_injective K.subtype_injective]
    exact hB₀log
  have hBnc : ¬ IsCyclic ↥B :=
    not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hBea (by omega)
  have hBp : IsPGroup p B := hBea.isPGroup
  have hp_dvd_B : p ∣ Nat.card B := by
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have hn_zero : n = 0 := by omega
      rw [hn_zero, pow_zero] at hn
      rw [hn] at hBlog
      norm_num at hBlog
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  have hp_odd : Odd p :=
    hG.odd.of_dvd_nat (hp_dvd_B.trans (Subgroup.card_subgroup_dvd_card B))
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  have h3P : 3 ≤ pRank ↥(P : Subgroup G) p := by
    let Bsub : Subgroup ↥(P : Subgroup G) := B.subgroupOf (P : Subgroup G)
    have hBsub_ea : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBP).symm hBea
    have hBsub_log : 3 ≤ Nat.log p (Nat.card Bsub) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv]
      exact hBlog
    exact hBsub_log.trans (le_pRank Bsub hBsub_ea)
  obtain ⟨A₀, hA₀scn⟩ :=
    OddOrder.BG.Ch1.S05.scn3_nonempty_of_three_le_pRank
      (R := ↥(P : Subgroup G)) hp_odd P.isPGroup' h3P
  let A : Subgroup G := A₀.map (P : Subgroup G).subtype
  have hAglobal : A ∈ S07.scn3Global p G := by
    change A₀.map (P : Subgroup G).subtype ∈ S07.scn3Global p G
    exact scn3Global_of_scn3_sylow P hA₀scn
  have hAU : IsUniquelyMaximal A :=
    scn3_isUniquelyMaximal hG hAglobal
  have hAab : IsMulCommutative A := by
    have : IsMulCommutative A₀ := hA₀scn.isSCN.isMulCommutative
    change IsMulCommutative (A₀.map (P : Subgroup G).subtype)
    infer_instance
  have hAp : IsPGroup p A := by
    change IsPGroup p (A₀.map (P : Subgroup G).subtype)
    exact (P.isPGroup'.to_subgroup A₀).map (P : Subgroup G).subtype
  have hmA : 3 ≤ rank ↥A := by
    have h3pRankA : 3 ≤ pRank ↥A p := by
      have hmono :
          pRank A₀ p ≤ pRank ↥(A₀.map (P : Subgroup G).subtype) p :=
        pRank_le_of_injective
          (f := (Subgroup.equivMapOfInjective A₀ (P : Subgroup G).subtype
            (P : Subgroup G).subtype_injective).toMonoidHom)
          (Subgroup.equivMapOfInjective A₀ (P : Subgroup G).subtype
            (P : Subgroup G).subtype_injective).injective
      exact hA₀scn.le_pRank.trans hmono
    exact h3pRankA.trans (pRank_le_rank (G := ↥A) p)
  have hB_le_CB : B ≤ Subgroup.centralizer (B : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (congrArg Subtype.val (hBea.comm ⟨b, hb⟩ ⟨c, hc⟩)).symm
  have hrB : 3 ≤ pRank ↥(Subgroup.centralizer (B : Set G)) p := by
    let Bsub : Subgroup ↥(Subgroup.centralizer (B : Set G)) :=
      B.subgroupOf (Subgroup.centralizer (B : Set G))
    have hBsub_ea : Bsub.IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hB_le_CB).symm hBea
    have hBsub_log : 3 ≤ Nat.log p (Nat.card Bsub) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_CB).toEquiv]
      exact hBlog
    exact hBsub_log.trans (le_pRank Bsub hBsub_ea)
  have hBU : IsUniquelyMaximal B :=
    isUniquelyMaximal_of_abelian_rank_three hG hAab hAp hBp hBnc hAU hmA hrB
  exact hBU.of_le_of_lt_top hBK hKlt

end OddOrder.BG.Ch2.S09


