-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_ChiefSeriesStabilizer
-- name    : OddOrder_BG_Ch2_Uniqueness_S09_ChiefSeriesStabilizer
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:36:36.070195+00:00
-- url     : https://prove2.me/theorems/6aa7ee74-9356-49bc-857c-d5594aef33b4
-- title:
--   BG §9: chief-series stabilizer lemmas (support for Lemma 9.5)
-- statement:
--   Support material for Lemma 9.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §9, split off from the Lemma 9.5 file. It applies BG Lemma 1.9 to chief series: a coprime subgroup stabilizing every term of a chief series centralizes the relevant sections, with related conjugation-transitivity and $H$-invariant bookkeeping steps.
--
--   The main declaration: `coprime_chiefSeries_stabilizer_le_centralizer`.
--
--   The bundle also proves 55 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S09_ChiefSeriesStabilizer.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S09_ChiefSeriesStabilizer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowPGroups
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Transitivity
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_FittingOfMaximal
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_AInvariantPiSubgroups
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelianFamily
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Theorem91
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Corollaries

namespace OddOrder.BG.Ch2.S09

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The Theorem 7.6 → Theorem 7.4 propagation step used in BG Lemma 9.5.

If `A ∈ SCN₃(p)`, `A ≤ R`, and `R` is a proper `p`-subgroup, then for every `q ≠ p`
`O_{p'}(C_G(R))` acts transitively on `ℋ_G^*(R;q)`. This is the formal version of the
line "By Theorems 7.6 and 7.4" in the normalizer part of Lemma 9.5. -/
private theorem conjTransitiveOn_hInvariantStar_of_scn3Global_intermediate [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A R : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R) (hRlt : R < ⊤)
    {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) :
    S07.ConjTransitiveOn (opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)))
      (hInvariantStar ⊤ R {q}) := by
  classical
  have hA0 := hA
  obtain ⟨P, hAP, hAscn3⟩ := hA0
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hAscn2 : IsSCN_n p 2 (A.subgroupOf (P : Subgroup G)) :=
    IsSCN_n.mono (by norm_num) hAscn3
  have hHyp : S07.Hypothesis71 A := S07.hypothesis71_of_scn2 hG hAab hAp P hAP hAscn2
  have hπ : S07.primesOf A = ({p} : Set ℕ) := primesOf_eq_singleton_of_mem_scn3Global hA
  have hqA : q ∈ (S07.primesOf A)ᶜ := by
    rw [hπ]
    simpa [Set.mem_singleton_iff] using hqp
  have hRpi : Subgroup.IsPiSubgroup (S07.primesOf A) R := by
    rw [hπ]
    exact isPiSubgroup_singleton_of_isPGroup hRp
  have hAsub : Subgroup.IsSubnormal (A.subgroupOf R) :=
    subgroupOf_isSubnormal_of_isPGroup hRp
  have htransA : S07.ConjTransitiveOn (S07.kSubgroup A) (hInvariantStar ⊤ A {q}) := by
    have hT := S07.thompsonTransitivity hG (prime_dvd_card_of_mem_scn3Global hA) hA hqp
    simpa [S07.kSubgroup, hπ] using hT
  have hprop := S07.transitivity_propagates hG hHyp hqA R hRlt hRpi hAR hAsub htransA
  simpa [hπ] using hprop.2.1

/-- A conjugation-transitivity bookkeeping step for BG Lemma 9.5.

If `x` normalizes `R`, transitivity gives `k ∈ K` with `Q^k = Q^x`. Once both `K` and
`N_G(Q)` lie in `M`, this forces `x ∈ M`. -/
private theorem mem_of_mem_normalizer_of_conjTransitiveOn
    {K M R Q : Subgroup G} {q : ℕ} [Fact q.Prime] {x : G}
    (hxR : x ∈ Subgroup.normalizer (R : Set G))
    (hQ : Q ∈ hInvariantStar ⊤ R {q})
    (htrans : S07.ConjTransitiveOn K (hInvariantStar ⊤ R {q}))
    (hKleM : K ≤ M) (hNQleM : Subgroup.normalizer (Q : Set G) ≤ M) :
    x ∈ M := by
  classical
  have hxR_eq : MulAut.conj x • R = R :=
    conj_smul_eq_self_of_mem_normalizer hxR
  have hxQ : MulAut.conj x • Q ∈ hInvariantStar ⊤ R {q} :=
    conj_smul_mem_hInvariantStar_top_of_normalizer hQ hxR_eq
  obtain ⟨k, hkK, hkQ⟩ := htrans Q hQ (MulAut.conj x • Q) hxQ
  have hknorm : k⁻¹ * x ∈ Subgroup.normalizer (Q : Set G) := by
    apply mem_normalizer_of_conj_smul_eq_self
    calc MulAut.conj (k⁻¹ * x) • Q
        = MulAut.conj k⁻¹ • MulAut.conj x • Q := by
            rw [smul_smul, ← map_mul]
      _ = MulAut.conj k⁻¹ • MulAut.conj k • Q := by rw [← hkQ]
      _ = Q := by
            rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hkM : k ∈ M := hKleM hkK
  have hknormM : k⁻¹ * x ∈ M := hNQleM hknorm
  have hprod : k * (k⁻¹ * x) ∈ M := M.mul_mem hkM hknormM
  simpa [mul_assoc] using hprod

/-- BG Lemma 9.5's normalizer step after the `Q` and `(9.8)` witnesses have been supplied.

This packages the final use of Theorems 7.6 and 7.4: the transitivity bridge puts a
normalizer element of `R` in the fixed maximal subgroup `M`, provided `Q ∈ ℋ_G^*(R;q)` and
`N_G(Q) ≤ M` are already known. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate [Finite G]
    (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R Q : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p)
    (hQ : Q ∈ hInvariantStar ⊤ R {q})
    (hNQleM : Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have htrans :
      S07.ConjTransitiveOn
        (opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)))
        (hInvariantStar ⊤ R {q}) :=
    conjTransitiveOn_hInvariantStar_of_scn3Global_intermediate hG hA hRp hAR hRlt hqp
  have hKleM :
      opiCoreInG ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G)) ≤ M := by
    exact (opiCoreInG_le ({p} : Set ℕ)ᶜ (Subgroup.centralizer (R : Set G))).trans
      ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAR)).trans hM.2)
  intro x hxR
  exact mem_of_mem_normalizer_of_conjTransitiveOn hxR hQ htrans hKleM hNQleM

/-- BG Lemma 9.5's L2573-L2589 normalizer step, with the `Q` package as input.

The low-rank and high-rank cases both produce a `Q ∈ ℋ_G^*(R;q)` with `N_G(Q) ≤ M`;
this helper consumes that uniform package and applies the Theorems 7.6/7.4 transitivity
bridge. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p)
    (hQpack :
      ∃ Q : Subgroup G,
        Q ∈ hInvariantStar ⊤ R {q} ∧
          opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, _hcoreQ, hNQleM⟩ := hQpack
  exact normalizer_le_maximal_of_scn3Global_intermediate
    hG hM hA hRp hAR hRlt hqp hQ hNQleM

/-- The `Q`-choice in BG Lemma 9.5.

If `R ≤ M`, then `R` normalizes `O_q(M)`, so `O_q(M)` lies in `ℋ_G(R;q)` and can be
extended to a maximal member of `ℋ_G^*(R;q)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_of_le [Finite G]
    {q : ℕ} [Fact q.Prime] {M R : Subgroup G} (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧ opiCoreInG ({q} : Set ℕ) M ≤ Q := by
  classical
  have hcore : opiCoreInG ({q} : Set ℕ) M ∈ hInvariant ⊤ R {q} := by
    refine ⟨le_top, ?_, isPiSubgroup_opiCoreInG ({q} : Set ℕ) M⟩
    exact hRM.trans (le_normalizer_opiCoreInG ({q} : Set ℕ) M)
  exact exists_le_hInvariantStar hcore

/-- A member of `ℋ_G^*(R;q)` containing a Sylow `q`-subgroup is that Sylow subgroup. -/
private theorem hInvariantStar_eq_sylow_of_sylow_le [Finite G]
    {q : ℕ} [Fact q.Prime] (P : Sylow q G) {R Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar ⊤ R {q}) (hPQ : (P : Subgroup G) ≤ Q) :
    Q = (P : Subgroup G) := by
  have hQp : IsPGroup q Q :=
    isPGroup_of_isPiSubgroup_singleton (hInvariantStar_isPiSubgroup hQ)
  exact P.is_maximal' hQp hPQ

/-- If a subgroup is the ambient image of a Sylow `q`-subgroup of `M` and its ambient
normalizer is contained in `M`, then it is a Sylow `q`-subgroup of `G`.

This is the Sylow-normalizer bookkeeping in BG (9.7). -/
private theorem exists_sylow_eq_of_sylow_subgroupOf_and_normalizer_le [Finite G]
    {q : ℕ} [Fact q.Prime] {M O : Subgroup G} (PM : Sylow q ↥M)
    (hPMO : (PM : Subgroup ↥M).map M.subtype = O)
    (hNOM : Subgroup.normalizer (O : Set G) ≤ M) :
    ∃ P : Sylow q G, (P : Subgroup G) = O := by
  classical
  have hOp : IsPGroup q O := by
    rw [← hPMO]
    exact PM.isPGroup'.map M.subtype
  obtain ⟨S, hOS⟩ := hOp.exists_le_sylow
  have hSO : (S : Subgroup G) = O := by
    by_contra hS_ne_O
    have hOltS : O < (S : Subgroup G) :=
      lt_of_le_of_ne hOS (fun h => hS_ne_O h.symm)
    have hOltSN : O < (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) :=
      S08.lt_inf_normalizer_of_isPGroup_lt S.isPGroup' hOltS
    have hSN_le_M : (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) ≤ M :=
      inf_le_right.trans hNOM
    let K : Subgroup ↥M :=
      ((S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)).subgroupOf M
    have hKp : IsPGroup q K := (S.isPGroup'.to_inf_left).comap_subtype
    have hPM_le_K : (PM : Subgroup ↥M) ≤ K := by
      intro x hx
      have hxO : (x : G) ∈ O := by
        rw [← hPMO]
        exact ⟨x, hx, rfl⟩
      change (x : G) ∈ (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)
      exact (le_inf hOS Subgroup.le_normalizer) hxO
    have hK_eq_PM : K = (PM : Subgroup ↥M) := PM.is_maximal' hKp hPM_le_K
    have hSN_eq_O : (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G) = O := by
      calc
        (S : Subgroup G) ⊓ Subgroup.normalizer (O : Set G)
            = K.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hSN_le_M).symm
        _ = (PM : Subgroup ↥M).map M.subtype := by rw [hK_eq_PM]
        _ = O := hPMO
    exact (ne_of_lt hOltSN) hSN_eq_O.symm
  exact ⟨S, hSO⟩

/-- The `(9.7)` side of BG Lemma 9.5's `(9.8)` step, abstracted from the source of the
Sylow fact.

If the core `O_q(M)` is a Sylow `q`-subgroup of `G` and its normalizer lies in `M`, then
the `Q` chosen above has `N_G(Q) ≤ M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_sylow
    [Finite G] {q : ℕ} [Fact q.Prime] {M R : Subgroup G} (P : Sylow q G)
    (hPcore : (P : Subgroup G) = opiCoreInG ({q} : Set ℕ) M) (hRM : R ≤ M)
    (hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, hcoreQ⟩ := exists_hInvariantStar_containing_opiCoreInG_of_le (q := q) hRM
  have hPQ : (P : Subgroup G) ≤ Q := (le_of_eq hPcore).trans hcoreQ
  have hQeq : Q = (P : Subgroup G) := hInvariantStar_eq_sylow_of_sylow_le P hQ hPQ
  refine ⟨Q, hQ, hcoreQ, ?_⟩
  rw [hQeq]
  exact hNPM

/-- Low-rank `(9.7)` package once Theorem 4.20(c) has identified `O_q(M)` as the
ambient image of a Sylow `q`-subgroup of `M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hOqne : opiCoreInG ({q} : Set ℕ) M ≠ ⊥) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  have hNcoreM : Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M : Set G) ≤ M :=
    normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot hG hM hOqne
  obtain ⟨P, hPcore⟩ :=
    exists_sylow_eq_of_sylow_subgroupOf_and_normalizer_le PM hPMcore hNcoreM
  have hNPM : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
    rw [hPcore]
    exact hNcoreM
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_sylow
    P hPcore hRM hNPM

/-- If a local Sylow `q`-subgroup maps onto `O_q(M)` and `q ∈ π(M)`, then
`O_q(M)` is nontrivial. -/
private theorem opiCoreInG_singleton_ne_bot_of_local_sylow_eq_of_mem_primeFactors
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G} (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    opiCoreInG ({q} : Set ℕ) M ≠ ⊥ := by
  classical
  have hq_dvd_M : q ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hqM).2.1
  have hPMne : (PM : Subgroup ↥M) ≠ ⊥ :=
    OddOrder.Isaacs.Ch07.Sylow.ne_bot_of_dvd_card hq_dvd_M PM
  intro hOqbot
  have hPMmap_bot : (PM : Subgroup ↥M).map M.subtype = ⊥ := by
    rw [hPMcore, hOqbot]
  have hPMbot : (PM : Subgroup ↥M) = ⊥ := by
    apply (Subgroup.map_subtype_inj (H := M)).mp
    simpa [Subgroup.map_bot] using hPMmap_bot
  exact hPMne hPMbot

/-- Low-rank `(9.7)` package when Theorem 4.20(c) has supplied only the local Sylow
equality; nontriviality follows from `q ∈ π(M)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow
    hG hM PM hPMcore
    (opiCoreInG_singleton_ne_bot_of_local_sylow_eq_of_mem_primeFactors PM hPMcore hqM)
    hRM

/-- Convert the local `O_q(M)` notation used by the §4 endpoint into the ambient
`opiCoreInG` notation used in §9. -/
private theorem local_sylow_map_eq_opiCoreInG_of_eq_opCore
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G} (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M) :
    (PM : Subgroup ↥M).map M.subtype = opiCoreInG ({q} : Set ℕ) M := by
  rw [hPMcore, opiCoreInG, OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) q]

/-- Low-rank `(9.7)` package with the natural §4-shaped input
`(P_M : Subgroup M) = O_q(M)`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMcore : (PM : Subgroup ↥M) = Ch01.opCore q ↥M)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_sylow_eq
    hG hM PM (local_sylow_map_eq_opiCoreInG_of_eq_opCore PM hPMcore) hqM hRM

/-- Low-rank `(9.7)` package when §4 has supplied a normal local Sylow subgroup. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_normal_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (PM : Sylow q ↥M)
    (hPMnorm : (PM : Subgroup ↥M).Normal)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  exact exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_local_opCore
    hG hM PM (Ch01.Sylow.eq_opCore_of_normal PM hPMnorm) hqM hRM

/-- A rank-three `q`-subgroup is nontrivial. -/
private theorem ne_bot_of_isPGroup_of_three_le_rank [Finite G]
    {q : ℕ} [Fact q.Prime] {B : Subgroup G} (hBq : IsPGroup q B)
    (hBrank : 3 ≤ rank ↥B) :
    B ≠ ⊥ := by
  have h3pRankB : 3 ≤ pRank ↥B q :=
    three_le_pRank_of_isPGroup_of_three_le_rank hBq hBrank
  have hq_dvd_B : q ∣ Nat.card B :=
    (Nat.mem_primeFactors.mp
      (mem_primeFactors_card_of_pos_pRank (H := ↥B) (p := q) (by omega))).2.1
  intro hBbot
  rw [hBbot, Subgroup.card_bot] at hq_dvd_B
  exact (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hq_dvd_B)

/-- If a uniquely maximal subgroup `B` lies in both a fixed maximal subgroup `M` and a
nontrivial `q`-subgroup `Q`, then the normalizer of `Q` lies in `M`.

This is the uniqueness bookkeeping behind BG Lemma 9.5's high-rank `(9.8)` step. -/
private theorem normalizer_le_maximal_of_isUniquelyMaximal_le [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M B Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hBU : IsUniquelyMaximal B)
    (hBM : B ≤ M) (hBQ : B ≤ Q) (hQne : Q ≠ ⊥)
    (hQpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Q) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  have hQlt : Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hQtop
    have hQp : IsPGroup q Q := isPGroup_of_isPiSubgroup_singleton hQpi
    have hGp : IsPGroup q G :=
      (hQtop ▸ hQp : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
        Subgroup.topEquiv.surjective
    have : Group.IsNilpotent G := hGp.isNilpotent
    exact hG.notSolvable inferInstance
  obtain ⟨N, hNco, hQN⟩ := (eq_top_or_exists_le_coatom Q).resolve_left hQlt.ne
  have hN_eq_M : N = M :=
    hBU.eq_of_isCoatom_of_le hNco (hBQ.trans hQN) (mem_maximalSubgroups.mp hM) hBM
  have hQM : Q ≤ M := hQN.trans (le_of_eq hN_eq_M)
  obtain ⟨L, hL, hNQleL⟩ :=
    S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal hG hM hQne hQM
  have hB_le_L : B ≤ L := hBQ.trans (Subgroup.le_normalizer.trans hNQleL)
  have hL_eq_M : L = M :=
    hBU.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hL) hB_le_L
      (mem_maximalSubgroups.mp hM) hBM
  exact hNQleL.trans (le_of_eq hL_eq_M)

/-- High-rank `(9.8)` bookkeeping once a rank-three subgroup inside `O_q(M)` has been
chosen.

Lemma 9.4 makes the rank-three subgroup uniquely maximal; uniqueness then forces the
normalizer of the chosen `Q ∈ ℋ_G^*(R;q)` into the fixed maximal subgroup `M`. -/
private theorem normalizer_hInvariantStar_le_maximal_of_rank_three_opiCoreInG_witness
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q)
    (hQ : Q ∈ hInvariantStar ⊤ R {q}) (hOqQ : opiCoreInG ({q} : Set ℕ) M ≤ Q)
    (hwit :
      ∃ B : Subgroup G,
        IsMulCommutative B ∧ IsPGroup q B ∧ 3 ≤ rank ↥B ∧
          B ≤ opiCoreInG ({q} : Set ℕ) M) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨B, hBab, hBq, hBrank, hBcore⟩ := hwit
  have hBU : IsUniquelyMaximal B :=
    (abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3Fq) B hBab hBq hBrank
  have hBM : B ≤ M := hBcore.trans (opiCoreInG_le ({q} : Set ℕ) M)
  have hBQ : B ≤ Q := hBcore.trans hOqQ
  have hBne : B ≠ ⊥ := ne_bot_of_isPGroup_of_three_le_rank hBq hBrank
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    exact hBne (le_bot_iff.mp (hBQ.trans (le_of_eq hQbot)))
  exact normalizer_le_maximal_of_isUniquelyMaximal_le hG hM hBU hBM hBQ hQne
    (hInvariantStar_isPiSubgroup hQ)

/-- A high `q`-rank Fitting subgroup supplies a rank-three abelian `q`-subgroup inside
`O_q(M)`.

The point is that the elementary abelian witness in `F(M)` lies in `O_q(F(M))` by
nilpotence, and `O_q(F(M)) ≤ O_q(M)`. -/
private theorem exists_rank_three_abelian_le_opiCoreInG_of_three_le_pRank_fittingInG
    [Finite G] {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q) :
    ∃ B : Subgroup G,
      IsMulCommutative B ∧ IsPGroup q B ∧ 3 ≤ rank ↥B ∧
        B ≤ opiCoreInG ({q} : Set ℕ) M := by
  classical
  obtain ⟨B, hBmax, hBrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank
      (H := S08.fittingInG M) h3Fq
  have hBea : B.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hBmax
  have hBab : IsMulCommutative B := IsMulCommutative.of_comm hBea.comm
  have hBq : IsPGroup q B := hBea.isPGroup
  have hBF : B ≤ S08.fittingInG M := S08.isMaxElemAbelianIn_le hBmax
  have hBOF : B ≤ opiCoreInG ({q} : Set ℕ) (S08.fittingInG M) :=
    S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (S08.fittingInG_isNilpotent M) hBF hBq
  have hBOM : B ≤ opiCoreInG ({q} : Set ℕ) M :=
    hBOF.trans (S08.opiCoreInG_fittingInG_le_opiCoreInG ({q} : Set ℕ) M)
  exact ⟨B, hBab, hBq, hBrank, hBOM⟩

/-- The high-rank side of BG Lemma 9.5's `(9.8)` package.

If `r_q(F(M)) ≥ 3`, the `Q ∈ ℋ_G^*(R;q)` chosen to contain `O_q(M)` has
`N_G(Q) ≤ M`. -/
private theorem exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_high_pRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M R : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q)
    (hRM : R ≤ M) :
    ∃ Q : Subgroup G,
      Q ∈ hInvariantStar ⊤ R {q} ∧
        opiCoreInG ({q} : Set ℕ) M ≤ Q ∧ Subgroup.normalizer (Q : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, hcoreQ⟩ := exists_hInvariantStar_containing_opiCoreInG_of_le (q := q) hRM
  refine ⟨Q, hQ, hcoreQ, ?_⟩
  exact normalizer_hInvariantStar_le_maximal_of_rank_three_opiCoreInG_witness
    hG hM h3Fq hQ hcoreQ
    (exists_rank_three_abelian_le_opiCoreInG_of_three_le_pRank_fittingInG h3Fq)

/-- Low-rank normalizer step when §4 has supplied a normal local Sylow subgroup. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_normal_local_sylow
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M) (PM : Sylow q ↥M)
    (hPMnorm : (PM : Subgroup ↥M).Normal)
    (hqM : q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_normal_local_sylow
      hG hM.1 PM hPMnorm hqM hRM)

/-- Low-rank normalizer step when §4 supplies a positive-length characteristic
Sylow series for the local maximal subgroup. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_characteristicSylowSeries
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors)
    (hterminal_ne :
      ∀ i : Fin S.length, i.succ = Fin.last S.length → (S.step i).q ≠ p) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  obtain ⟨i, hi, PM, hPMnorm⟩ :=
    OddOrder.BG.Ch1.S04.CharacteristicSylowSeries.exists_normal_sylow_of_length_pos S hpos
  have : Fact (S.step i).q.Prime := (S.step i).q_prime
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_normal_local_sylow
    hG hM hA hRp hAR hRlt (hterminal_ne i hi) hRM PM hPMnorm (hterminal_mem i hi)

/-- In the low-rank Lemma 9.5 branch, the terminal normal local Sylow label
cannot be the ambient `SCN₃` prime. -/
private theorem normal_sylow_label_ne_of_scn3Global_of_pRank_fittingInG_le_two
    [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {A M : Subgroup G}
    (hA : A ∈ S07.scn3Global p G) (hAM : A ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (PM : Sylow q ↥M) (hPMnorm : (PM : Subgroup ↥M).Normal) :
    q ≠ p := by
  classical
  intro hqp
  subst q
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  have h3A : 3 ≤ pRank ↥A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank hAp hArank
  let AM : Subgroup ↥M := A.subgroupOf M
  have hAMp : IsPGroup p AM :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  obtain ⟨P, hAMP⟩ := hAMp.exists_le_sylow
  have : Unique (Sylow p ↥M) := Sylow.unique_of_normal PM hPMnorm
  have hAM_PM : AM ≤ (PM : Subgroup ↥M) := by
    have hP_eq : P = PM := Subsingleton.elim P PM
    rwa [← hP_eq]
  have hA_PM_map : A ≤ (PM : Subgroup ↥M).map M.subtype := by
    calc
      A = AM.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hAM).symm
      _ ≤ (PM : Subgroup ↥M).map M.subtype := Subgroup.map_mono hAM_PM
  have hPMcore : (PM : Subgroup ↥M) = Ch01.opCore p ↥M :=
    Ch01.Sylow.eq_opCore_of_normal PM hPMnorm
  have hPMfit : (PM : Subgroup ↥M).map M.subtype ≤ S08.fittingInG M := by
    rw [hPMcore, ← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) p]
    change opiCoreInG ({p} : Set ℕ) M ≤ S08.fittingInG M
    exact S08.opiCoreInG_singleton_le_fittingInG M
  have hAF : A ≤ S08.fittingInG M := hA_PM_map.trans hPMfit
  have h3F : 3 ≤ pRank ↥(S08.fittingInG M) p :=
    h3A.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hAF)
        (Subgroup.inclusion_injective hAF))
  omega

/-- **BG Theorem 4.20(c) package bridge for §9.** A maximal subgroup `M` of the minimal simple
odd group `G` with `r(F(M)) ≤ 2` carries a characteristic Sylow series package: `M` is solvable
(`hG.isSolvable_of_mem_maximalSubgroups`), of odd order (`|M| ∣ |G|`), nontrivial, and
`rank F(↥M) = rank (fittingInG M) ≤ 2` (the two Fitting subgroups are isomorphic via
`M.subtype`).  This is how the low-rank branch of the Lemma 9.5 normalizer step obtains its
`(9.7)` Sylow data internally — replacing the (unfulfillable, since `r(F(M))` may be `≥ 3`)
external package hypothesis. -/
private theorem exists_characteristicSylowSeriesPackage_of_maximal_of_rank_fittingInG_le_two
    [Finite G] (hG : IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) [Nontrivial ↥M]
    (hrank : rank ↥(S08.fittingInG M) ≤ 2) :
    Nonempty (OddOrder.BG.Ch1.S04.CharacteristicSylowSeriesPackage ↥M) := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hodd : Odd (Nat.card ↥M) := by
    rcases Nat.even_or_odd (Nat.card ↥M) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := he.two_dvd.trans (Subgroup.card_subgroup_dvd_card M)
      have := hG.odd; rw [Nat.odd_iff] at this; omega
    · exact ho
  have hrankF : rank ↥(Ch01.fitting ↥M) ≤ 2 := by
    refine le_trans (OddOrder.GroupTheory.rank_le_of_injective
      (f := (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype
        M.subtype_injective).toMonoidHom) ?_) hrank
    exact (Subgroup.equivMapOfInjective (Ch01.fitting ↥M) M.subtype M.subtype_injective).injective
  exact ⟨(OddOrder.BG.Ch1.S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two
    hodd hrankF).some⟩

/-- Low-rank normalizer step when §4 supplies a positive-length characteristic
Sylow series and Lemma 9.5 has already established `r_p(F(M)) ≤ 2`. -/
private theorem normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_lowRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2)
    (S : OddOrder.BG.Ch1.S04.CharacteristicSylowSeries ↥M) (hpos : 0 < S.length)
    (hterminal_mem :
      ∀ i : Fin S.length,
        i.succ = Fin.last S.length → (S.step i).q ∈ (Nat.card ↥M).primeFactors) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  have hAM : A ≤ M := hA_le_C.trans hM.2
  refine normalizer_le_maximal_of_scn3Global_intermediate_of_characteristicSylowSeries
    hG hM hA hRp hAR hRlt hRM S hpos hterminal_mem ?_
  intro i hi
  obtain ⟨PM, hPMnorm⟩ :=
    OddOrder.BG.Ch1.S04.CharacteristicSylowSeries.exists_normal_sylow_of_terminal_step S i hi
  have : Fact (S.step i).q.Prime := (S.step i).q_prime
  exact normal_sylow_label_ne_of_scn3Global_of_pRank_fittingInG_le_two
    hA hAM hFp PM hPMnorm

/-- High-rank version of the BG Lemma 9.5 normalizer step, using Lemma 9.4 through the
rank-three witness inside `O_q(M)`. -/
private theorem normalizer_le_maximal_of_scn3Global_intermediate_of_high_pRank
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hqp : q ≠ p) (hRM : R ≤ M)
    (h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  exact normalizer_le_maximal_of_scn3Global_intermediate_of_exists_hInvariantStar
    hG hM hA hRp hAR hRlt hqp
    (exists_hInvariantStar_containing_opiCoreInG_with_normalizer_le_of_high_pRank
      hG hM.1 h3Fq hRM)

/-- If the overall rank is at least three but the fixed `p`-rank is at most two,
then some other prime has rank at least three. -/
private theorem exists_pRank_ge_three_ne_of_rank_ge_three_of_pRank_le_two
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hrank : 3 ≤ rank H) (hp : pRank H p ≤ 2) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 3 ≤ pRank H q := by
  obtain ⟨q, hq, h3q⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := H) (n := 3) (by norm_num) hrank
  refine ⟨q, hq, ?_, h3q⟩
  intro hqp
  subst q
  omega

/-- BG Lemma 9.5 rank-case normalizer adapter.

The low-rank branch consumes the §4 characteristic Sylow series package, while the
high-rank branch chooses a prime `q ≠ p` with `r_q(F(M)) ≥ 3` and applies Lemma 9.4. -/
private theorem normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M R : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hRp : IsPGroup p R) (hAR : A ≤ R)
    (hRlt : R < ⊤) (hRM : R ≤ M)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  by_cases hrank : rank ↥(S08.fittingInG M) ≤ 2
  · -- low rank: build the §4.20(c) characteristic Sylow series of `M` internally via L2
    have hAM : A ≤ M := hAR.trans hRM
    have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr fun hM0 =>
      ne_bot_of_mem_scn3Global hA (le_bot_iff.mp (hM0 ▸ hAM))
    obtain ⟨pkg⟩ :=
      exists_characteristicSylowSeriesPackage_of_maximal_of_rank_fittingInG_le_two hG hM.1 hrank
    exact normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_lowRank
      hG hM hA hRp hAR hRlt hRM hFp pkg.series pkg.length_pos pkg.terminal_mem
  · have h3rank : 3 ≤ rank ↥(S08.fittingInG M) := by omega
    obtain ⟨q, hq, hqp, h3Fq⟩ :=
      exists_pRank_ge_three_ne_of_rank_ge_three_of_pRank_le_two
        (H := ↥(S08.fittingInG M)) (p := p) h3rank hFp
    have : Fact q.Prime := ⟨hq⟩
    exact normalizer_le_maximal_of_scn3Global_intermediate_of_high_pRank
      hG hM hA hRp hAR hRlt hqp hRM h3Fq

/-- BG Lemma 9.5 normalizer step specialized to `R = A`.

After the rank-case normalizer adapter has been supplied with the §4 characteristic
Sylow series package, the first application gives `N_G(A) ≤ M`. -/
private theorem normalizer_scn3_self_le_maximal_of_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G)
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2) :
    Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab ⟨y, hy⟩ ⟨x, hx⟩)
  have hAM : A ≤ M := hA_le_C.trans hM.2
  have hAlt : A < ⊤ :=
    lt_of_le_of_lt hA_le_C (centralizer_lt_top_of_mem_scn3Global hG hA)
  exact normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
    hG hM hA (isPGroup_of_mem_scn3Global hA) le_rfl hAlt hAM hFp

/-- BG Lemma 9.5 normalizer step specialized to a `p`-subgroup of `N_G(A)`.

The `R = A` instance first puts every chosen `P ≤ N_G(A)` inside `M`; the rank-case
adapter can then be applied with `R = P` to obtain `N_G(P) ≤ M`. -/
private theorem normalizer_scn3_sylowNormalizer_le_maximal_of_rankCases
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hFp : pRank ↥(S08.fittingInG M) p ≤ 2) :
    P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  have hNAleM : Subgroup.normalizer (A : Set G) ≤ M :=
    normalizer_scn3_self_le_maximal_of_rankCases hG hM hA hFp
  have hPM : P ≤ M := hPnormA.trans hNAleM
  have hMlt : M < ⊤ := (mem_maximalSubgroups.mp hM.1).lt_top
  have hPlt : P < ⊤ := lt_of_le_of_lt hPM hMlt
  exact ⟨hPM,
    normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases
      hG hM hA hPp hAP hPlt hPM hFp⟩

/-- If an `SCN₃(p)` subgroup is a counterexample to uniqueness, then every maximal
subgroup has `pRank F(M) ≤ 2`.

This is the first reduction in BG Lemma 9.5: otherwise Lemma 9.4 would put the
rank-three abelian `p`-subgroup `A` itself in `𝒰`. -/
theorem pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA : A ∈ S07.scn3Global p G)
    (hAnot : ¬ IsUniquelyMaximal A) :
    pRank ↥(S08.fittingInG M) p ≤ 2 := by
  classical
  by_contra hnot
  have h3F : 3 ≤ pRank ↥(S08.fittingInG M) p := by omega
  have hAab : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hAp : IsPGroup p A := isPGroup_of_mem_scn3Global hA
  have hArank : 3 ≤ rank ↥A := three_le_rank_of_mem_scn3Global hA
  exact hAnot
    ((abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3F) A hAab hAp hArank)

/-- Counterexample version of the `R = P` normalizer step in BG Lemma 9.5.

Once `P` is a `p`-subgroup between `A` and `N_G(A)`, the rank cut `(9.6)` and the
`R = A` instance put `P` inside `M`, and the rank-case adapter gives `N_G(P) ≤ M`. -/
theorem normalizer_scn3_pSubgroup_le_maximal_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M P : Subgroup G}
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G)) :
    P ≤ M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  have hFp : pRank ↥(S08.fittingInG M) p ≤ 2 :=
    pRank_fittingInG_le_two_of_not_scn3_isUniquelyMaximal hG hM.1 hA hAnot
  exact normalizer_scn3_sylowNormalizer_le_maximal_of_rankCases
    hG hM hA hPp hAP hPnormA hFp

/-- BG Lemma 9.5's Proposition 1.16 extraction step.

If `P0` does not centralize `D`, and a noncyclic abelian subgroup `A` normalizes `D`
coprimely, then among the cocyclic centralizers generating `D` there is one not centralized
by `P0`. This is the formal version of the line "Take `B ⊆ Ω₁(A)` such that
`Ω₁(A)/B` is cyclic and `P₀` does not centralize `C_D(B)`." -/
private theorem exists_cocyclic_not_le_centralizer_inf_centralizer_of_not_le_centralizer
    [Finite G] {A D P0 : Subgroup G} [IsMulCommutative ↥A]
    (hAD : A ≤ Subgroup.normalizer D)
    (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥D))
    (hAnc : ¬ IsCyclic ↥A)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer (D : Set G)) :
    ∃ B : Subgroup G,
      B ≤ A ∧ (∃ a ∈ A, B ⊔ Subgroup.zpowers a = A) ∧
        ¬ P0 ≤ Subgroup.centralizer
          ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  by_contra hnone
  have hAll :
      ∀ B : Subgroup G,
        B ≤ A → (∃ a ∈ A, B ⊔ Subgroup.zpowers a = A) →
          P0 ≤ Subgroup.centralizer
            ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
    intro B hBA hcyc
    by_contra hnot
    exact hnone ⟨B, hBA, hcyc, hnot⟩
  have hDinv : Ch03.IsAInvariant (S07.conjAction A) D :=
    S07.isAInvariant_conjAction_iff.mpr hAD
  have htop :=
    OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic
      hDinv.restrict hCop hAnc
  exact hP0D (by
    intro x hxP0
    rw [Subgroup.mem_centralizer_iff]
    intro d hdD
    let CxD : Subgroup ↥D :=
      (D ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D
    have hclosure_le :
        OddOrder.BG.Ch1.S01.cocyclicFixedByClosure hDinv.restrict ≤ CxD := by
      rw [OddOrder.BG.Ch1.S01.cocyclicFixedByClosure, Subgroup.closure_le]
      rintro z ⟨Yb, ⟨a, hcycYb⟩, hfix⟩
      change (z : G) ∈ D ⊓ Subgroup.centralizer ({x} : Set G)
      set Y : Subgroup G := Yb.map A.subtype with hYdef
      have hYleA : Y ≤ A := by
        rw [hYdef]
        exact Subgroup.map_subtype_le Yb
      have hYcyc : ∃ a' ∈ A, Y ⊔ Subgroup.zpowers a' = A := by
        refine ⟨(a : G), a.2, ?_⟩
        have hzp : Subgroup.zpowers (a : G) = (Subgroup.zpowers a).map A.subtype :=
          (MonoidHom.map_zpowers A.subtype a).symm
        rw [hYdef, hzp, ← Subgroup.map_sup, hcycYb, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      have hzY : (z : G) ∈ D ⊓ Subgroup.centralizer (Y : Set G) := by
        refine ⟨z.2, ?_⟩
        change (z : G) ∈ Subgroup.centralizer (Y : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hyY
        rw [hYdef, Subgroup.coe_map, Set.mem_image] at hyY
        obtain ⟨yb, hyb, rfl⟩ := hyY
        have hval := congrArg (fun w : ↥D => (w : G)) (hfix yb hyb)
        change ((hDinv.restrict yb) z : G) = (z : G) at hval
        rw [Ch03.IsAInvariant.restrict_apply_val] at hval
        simp only [S07.conjAction, MonoidHom.comp_apply, Subgroup.coe_subtype,
          MulAut.conj_apply] at hval
        exact mul_inv_eq_iff_eq_mul.mp hval
      refine ⟨z.2, ?_⟩
      change (z : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hx_cent := (hAll Y hYleA hYcyc) hxP0
      exact (Subgroup.mem_centralizer_iff.mp hx_cent (z : G) hzY).symm
    have hdCx : (⟨d, hdD⟩ : ↥D) ∈ CxD := by
      apply hclosure_le
      rw [htop]
      exact Subgroup.mem_top _
    have hdc : d ∈ Subgroup.centralizer ({x} : Set G) := by
      simpa [CxD, Subgroup.mem_subgroupOf] using hdCx
    exact (Subgroup.mem_centralizer_iff.mp hdc x (Set.mem_singleton x)).symm)

/-- A cocyclic subgroup `Y` (`Y ⊔ ⟨b⟩ = B`) of an elementary abelian `p`-group `B`
of rank at least three is noncyclic. -/
private theorem not_isCyclic_of_cocyclic_elementary_rank_three [Finite G] {p : ℕ}
    (hp2 : 2 ≤ p) {B Y : Subgroup G}
    (hB_ea : B.IsElementaryAbelian p) (hlog : 3 ≤ Nat.log p (Nat.card ↥B))
    (hYB : Y ≤ B) {b : G} (hb : b ∈ B) (hsup : Y ⊔ Subgroup.zpowers b = B) :
    ¬ IsCyclic ↥Y := by
  classical
  have : IsMulCommutative ↥B := IsMulCommutative.of_comm hB_ea.1
  set Y' : Subgroup ↥B := Y.subgroupOf B with hY'
  set K : Subgroup ↥B := (Subgroup.zpowers b).subgroupOf B with hK
  have : Y'.Normal := Subgroup.normal_of_isMulCommutative _
  have hzple : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
  have hsup' : Y' ⊔ K = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_sup, hY', hK, Subgroup.map_subgroupOf_eq_of_le hYB,
      Subgroup.map_subgroupOf_eq_of_le hzple, hsup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hKle : Nat.card ↥K ≤ p := by
    rw [hK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzple).toEquiv, Nat.card_zpowers]
    refine Nat.le_of_dvd (by omega : 0 < p) (orderOf_dvd_of_pow_eq_one ?_)
    have hbp := congrArg Subtype.val (hB_ea.2 (⟨b, hb⟩ : ↥B))
    simpa using hbp
  have hKmap : K.map (QuotientGroup.mk' Y') = ⊤ := by
    have h1 : (Y' ⊔ K).map (QuotientGroup.mk' Y') = ⊤ := by
      rw [hsup', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y')]
    rwa [Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff Y').mpr (le_of_eq (QuotientGroup.ker_mk' Y').symm),
      bot_sup_eq] at h1
  have hquot_le : Nat.card (↥B ⧸ Y') ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective ((QuotientGroup.mk' Y').comp K.subtype) (by
      intro x
      obtain ⟨k, hk, hkx⟩ := hKmap ▸ Subgroup.mem_top x
      exact ⟨⟨k, hk⟩, hkx⟩)
  have hcardB : Nat.card ↥B ≤ Nat.card ↥K * Nat.card ↥Y := by
    have hY'card : Nat.card ↥Y' = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Y', hY'card]
    exact Nat.mul_le_mul_right _ hquot_le
  intro hcyc
  have hY_ea : Y.IsElementaryAbelian p := by
    refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
    · change (x : G) * (y : G) = (y : G) * (x : G)
      exact congrArg (Subtype.val : ↥B → G)
        (hB_ea.1 ⟨(x : G), hYB x.2⟩ ⟨(y : G), hYB y.2⟩)
    · change (x : G) ^ p = 1
      exact congrArg (Subtype.val : ↥B → G)
        (hB_ea.2 (⟨(x : G), hYB x.2⟩ : ↥B))
  have hYle : Nat.card ↥Y ≤ p := by
    have hdvd : Monoid.exponent ↥Y ∣ p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      exact hY_ea.2
    rw [← hcyc.exponent_eq_card]
    exact Nat.le_of_dvd (by omega : 0 < p) hdvd
  have hp3 : p ^ 3 ≤ Nat.card ↥B :=
    (Nat.le_log_iff_pow_le (by omega : 1 < p) Nat.card_pos.ne').mp hlog
  have h1 : Nat.card ↥B ≤ p ^ 2 := by
    rw [pow_two]
    exact le_trans hcardB (Nat.mul_le_mul hKle hYle)
  have h2 : p ^ 2 < p ^ 3 :=
    Nat.pow_lt_pow_right (by omega : 1 < p) (by norm_num)
  omega

/-- If `A` has `pRank ≥ 3`, then its abelian `Ω₁(A)` has logarithmic size at least three. -/
private theorem three_le_log_card_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p) :
    3 ≤ Nat.log p
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) := by
  have hp3_dvd : p ^ 3 ∣
      Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    OddOrder.GroupTheory.pow_dvd_card_omega1OfAbelian_of_pos_le_pRank
      (G := G) (H := A) (p := p) (hH := hAcomm_set) (n := 3) (by norm_num) h3A
  have hp3_le : p ^ 3 ≤
      Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    Nat.le_of_dvd Nat.card_pos hp3_dvd
  exact (Nat.le_log_iff_pow_le (Fact.out : p.Prime).one_lt Nat.card_pos.ne').mpr hp3_le

/-- `Ω₁(A)` is noncyclic when `A` has `pRank ≥ 3`. -/
theorem not_isCyclic_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p) :
    ¬ IsCyclic ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) := by
  exact not_isCyclic_of_isElementaryAbelian_of_two_le_log_card
    (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
      (G := G) (H := A) (p := p) (hH := hAcomm_set))
    (by
      have hlog := three_le_log_card_omega1OfAbelian_of_three_le_pRank
        (G := G) (p := p) hAcomm_set h3A
      omega)

/-- A cocyclic subgroup of `Ω₁(A)` is noncyclic when `pRank A ≥ 3`. -/
private theorem not_isCyclic_of_cocyclic_omega1OfAbelian_of_three_le_pRank [Finite G]
    {p : ℕ} [Fact p.Prime] {A B : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p)
    (hBΩ : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)
    (hsup : B ⊔ Subgroup.zpowers a =
      OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :
    ¬ IsCyclic ↥B := by
  exact not_isCyclic_of_cocyclic_elementary_rank_three
    (G := G) (p := p) (hp2 := (Fact.out : p.Prime).two_le)
    (B := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) (Y := B)
    (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
      (G := G) (H := A) (p := p) (hH := hAcomm_set))
    (three_le_log_card_omega1OfAbelian_of_three_le_pRank
      (G := G) (p := p) hAcomm_set h3A)
    hBΩ ha hsup

/-- BG Lemma 9.5's Prop 1.16 extraction specialized to `Ω₁(A)` under `pRank A ≥ 3`.

The output packages the cocyclic subgroup `B ≤ Ω₁(A)` with the extra facts needed for the
next step of the Lemma 9.5 contradiction: `B ≤ A`, `B` is noncyclic, and `P0` still does
not centralize `D ∩ C_G(B)`. -/
private theorem exists_noncyclic_cocyclic_omega1OfAbelian_not_le_centralizer_inf
    [Finite G] {p : ℕ} [Fact p.Prime] {A D P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3A : 3 ≤ pRank A p)
    (hΩD : OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ≤ Subgroup.normalizer D)
    (hCop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) (Nat.card ↥D))
    (hP0D : ¬ P0 ≤ Subgroup.centralizer (D : Set G)) :
    ∃ B : Subgroup G,
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧ ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a = OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        ((D ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let ΩA : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set
  have hΩea : ΩA.IsElementaryAbelian p := by
    simpa [ΩA] using
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set))
  have : IsMulCommutative ↥ΩA := IsMulCommutative.of_comm hΩea.1
  have hΩAnc : ¬ IsCyclic ↥ΩA := by
    simpa [ΩA] using
      (not_isCyclic_omega1OfAbelian_of_three_le_pRank
        (G := G) (p := p) (A := A) hAcomm_set h3A)
  obtain ⟨B, hBΩ, hcycpack, hnot⟩ :=
    exists_cocyclic_not_le_centralizer_inf_centralizer_of_not_le_centralizer
      (A := ΩA) (D := D) (P0 := P0) (by simpa [ΩA] using hΩD)
      (by simpa [ΩA] using hCop) hΩAnc hP0D
  rcases hcycpack with ⟨a, haΩ, hsup⟩
  have hBΩ_raw : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using hBΩ
  have haΩ_raw : a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using haΩ
  have hsup_raw : B ⊔ Subgroup.zpowers a =
      OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set := by
    simpa [ΩA] using hsup
  refine ⟨B, hBΩ_raw, ?_, ?_, ⟨a, haΩ_raw, hsup_raw⟩, hnot⟩
  · exact hBΩ_raw.trans (OddOrder.GroupTheory.omega1OfAbelian_le (G := G) (H := A)
      (p := p) (hH := hAcomm_set))
  · exact not_isCyclic_of_cocyclic_omega1OfAbelian_of_three_le_pRank
      (G := G) (p := p) (A := A) (B := B) hAcomm_set h3A hBΩ_raw haΩ_raw hsup_raw

/-- Lemma 9.5's Prop. 1.16 extraction with `D = O_{p'}(F(M))`.

For `M ∈ ℳ(C_G(A))` and `A ∈ SCN₃(p)`, the subgroup `Ω₁(A)` normalizes
`O_{p'}(F(M))`: `A ≤ C_G(A) ≤ M`, `M` normalizes `F(M)`, and the ambient
`p'`-core is characteristic in `F(M)`. Since `Ω₁(A)` is a `p`-group and
`O_{p'}(F(M))` is a `p'`-subgroup, the action is coprime. This packages the
exact input needed for the BG L2590--L2613 contradiction block. -/
private theorem exists_cocyclic_omega1_not_le_cent_inf_opiCoreFitting
    [Finite G] {p : ℕ} [Fact p.Prime] {A M P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G)) :
    ∃ B : Subgroup G,
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧ ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a =
          OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
            Subgroup.centralizer (B : Set G)) : Set G) := by
  classical
  let D : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)
  have h3A : 3 ≤ pRank A p :=
    three_le_pRank_of_isPGroup_of_three_le_rank
      (isPGroup_of_mem_scn3Global hA) (three_le_rank_of_mem_scn3Global hA)
  have hAcomm_inst : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_M : A ≤ M := by
    exact (Subgroup.le_centralizer A).trans hM.2
  have hM_norm_F : M ≤ Subgroup.normalizer (S08.fittingInG M : Set G) := by
    intro x hxM
    exact S08.mem_normalizer_fittingInG_of_mem hxM
  have hA_norm_F : A ≤ Subgroup.normalizer (S08.fittingInG M : Set G) :=
    hA_le_M.trans hM_norm_F
  have hOmegaD : OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ≤
      Subgroup.normalizer D := by
    exact (OddOrder.GroupTheory.omega1OfAbelian_le (G := G) (H := A)
      (p := p) (hH := hAcomm_set)).trans
        (le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)ᶜ hA_norm_F)
  have hOmegapi : Subgroup.IsPiSubgroup ({p} : Set ℕ)
      (OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :=
    isPiSubgroup_singleton_of_isPGroup
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set)).isPGroup
  have hDpic : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ D := by
    simpa [D] using
      (isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M))
  have hCop : Nat.Coprime
      (Nat.card ↥(OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set)) (Nat.card ↥D) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hOmegapi hDpic
  simpa [D] using
    (exists_noncyclic_cocyclic_omega1OfAbelian_not_le_centralizer_inf
      (G := G) (p := p) (A := A) (D := D) (P0 := P0)
      hAcomm_set h3A hOmegaD hCop (by simpa [D] using hP0D))

/-- Any subgroup of the abelian `Ω₁(A)` is elementary abelian at the same prime. -/
private theorem isElementaryAbelian_of_le_omega1OfAbelian {p : ℕ} {A B : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hBΩ : B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) :
    B.IsElementaryAbelian p := by
  let Ω : Subgroup G := OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set
  have hΩea : Ω.IsElementaryAbelian p := by
    simpa [Ω] using
      (OddOrder.GroupTheory.omega1OfAbelian_isElementaryAbelian
        (G := G) (H := A) (p := p) (hH := hAcomm_set))
  have hB_sub_ea : (B.subgroupOf Ω).IsElementaryAbelian p :=
    hΩea.to_subgroup (B.subgroupOf Ω)
  exact IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBΩ) hB_sub_ea

/-- BG Lemma 9.5 bridge: the `B` found by the cocyclic `Ω₁(A)` argument is
also outside the uniqueness class whenever the ambient `SCN₃` subgroup `A` is
the chosen counterexample. -/
private theorem exists_nonU_cocyclic_omega1_not_le_cent_inf_opiCoreFitting [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G)) :
    ∃ B : Subgroup G,
      B.IsElementaryAbelian p ∧
      ¬ IsUniquelyMaximal B ∧
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧
      ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a =
          OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
            Subgroup.centralizer (B : Set G)) : Set G) := by
  obtain ⟨B, hBΩ, hBA, hBnc, hcyc, hnot_cent⟩ :=
    exists_cocyclic_omega1_not_le_cent_inf_opiCoreFitting hAcomm_set hM hA hP0D
  have hBea : B.IsElementaryAbelian p :=
    isElementaryAbelian_of_le_omega1OfAbelian hAcomm_set hBΩ
  exact ⟨B, hBea,
    not_isUniquelyMaximal_of_le_scn3_counterexample hG hAcomm_set hA hBA hAnot,
    hBΩ, hBA, hBnc, hcyc, hnot_cent⟩

/-- Lemma 9.5 witness package after Theorem 9.1: from the cocyclic `Ω₁(A)`
witness one also obtains `y ∈ B#` and a maximal subgroup `L` containing
`C_G(y)` with `L ≠ M`. -/
theorem exists_nonU_cocyclic_omega1_witness_maximal_ne [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {A M P0 : Subgroup G}
    (hAcomm_set : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hM : M ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A)
    (hP0D : ¬ P0 ≤ Subgroup.centralizer
      ((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) : Set G)) :
    ∃ B : Subgroup G, ∃ y : G, ∃ L : Subgroup G,
      B.IsElementaryAbelian p ∧
      ¬ IsUniquelyMaximal B ∧
      B ≤ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set ∧
      B ≤ A ∧
      ¬ IsCyclic ↥B ∧
      (∃ a ∈ OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set,
        B ⊔ Subgroup.zpowers a =
          OddOrder.GroupTheory.omega1OfAbelian G A p hAcomm_set) ∧
      ¬ P0 ≤ Subgroup.centralizer
        (((opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M)) ⊓
            Subgroup.centralizer (B : Set G)) : Set G) ∧
      y ∈ B ∧ y ≠ 1 ∧
      ¬ Subgroup.centralizer ({y} : Set G) ≤ M ∧
      L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) ∧
      L ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) ∧
      L ≠ M := by
  obtain ⟨B, hBea, hBnot, hBΩ, hBA, hBnc, hcyc, hnot_cent⟩ :=
    exists_nonU_cocyclic_omega1_not_le_cent_inf_opiCoreFitting hG hAcomm_set hM hA hAnot hP0D
  have hAcomm_inst : IsMulCommutative A := isMulCommutative_of_mem_scn3Global hA
  have hA_le_M : A ≤ M := (Subgroup.le_centralizer A).trans hM.2
  have hBM : B ≤ M := hBA.trans hA_le_M
  obtain ⟨y, L, hyB, hy1, hCGnotM, hL, hLneM⟩ :=
    exists_nontrivial_centralizer_maximal_ne_of_not_isUniquelyMaximal hG hM.1 hBea hBM
      hBnc hBnot
  have hLA : L ∈ maximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) :=
    maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton (hBA hyB) hL
  exact ⟨B, y, L, hBea, hBnot, hBΩ, hBA, hBnc, hcyc, hnot_cent,
    hyB, hy1, hCGnotM, hL, hLA, hLneM⟩

/-- BG Lemma 9.5: reapply the `(9.9)` normalizer package with a maximal subgroup
`L ∈ 𝓜(C_G(y))`, where `y ∈ A`.  The conclusion is for the same `p`-subgroup
`P ≤ N_G(A)`, matching the line `N_G(P) ≤ L` before (9.10). -/
private theorem normalizer_scn3_pSubgroup_le_witness_maximal_of_not_scn3
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A L P : Subgroup G} {y : G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) (hyA : y ∈ A)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G)) :
    P ≤ L ∧ Subgroup.normalizer (P : Set G) ≤ L := by
  exact normalizer_scn3_pSubgroup_le_maximal_of_not_scn3 hG
    (maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton hyA hL)
    hA hAnot hPp hAP hPnormA

/-- Ambient form of the identity `H' = [H,H]`. -/
theorem derivedInG_eq_commutator (H : Subgroup G) :
    derivedInG H = ⁅(H : Subgroup G), H⁆ := by
  exact Subgroup.map_subtype_commutator H

/-- Monotonicity of the ambient derived subgroup. -/
private theorem derivedInG_mono {H K : Subgroup G} (hHK : H ≤ K) :
    derivedInG H ≤ derivedInG K := by
  rw [derivedInG_eq_commutator H, derivedInG_eq_commutator K]
  exact Subgroup.commutator_mono hHK hHK

/-- The ambient derived subgroup is contained in the subgroup it is derived from. -/
theorem derivedInG_le_self (H : Subgroup G) : derivedInG H ≤ H := by
  unfold derivedInG
  exact Subgroup.map_subtype_le _

/-- Mapping the derived subgroup of the top subgroup of `H` back to `G` recovers
the ambient derived subgroup `H'`. -/
private theorem derivedInG_top_map_subtype (H : Subgroup G) :
    (derivedInG (⊤ : Subgroup ↥H)).map H.subtype = derivedInG H := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [derivedInG_eq_commutator (⊤ : Subgroup ↥H), derivedInG_eq_commutator H,
    Subgroup.map_commutator, htop]

/-- If an ambient subgroup `P₀` lies in `H'`, then its restriction to `H` lies
in the derived subgroup of the top subgroup of `↥H`. -/
theorem subgroupOf_le_derivedInG_top_of_le_derivedInG {H P0 : Subgroup G}
    (hP0D : P0 ≤ derivedInG H) :
    P0.subgroupOf H ≤ derivedInG (⊤ : Subgroup ↥H) := by
  have hP0H : P0 ≤ H := hP0D.trans (derivedInG_le_self H)
  rw [← H.map_subtype_le_map_subtype, Subgroup.map_subgroupOf_eq_of_le hP0H,
    derivedInG_top_map_subtype H]
  exact hP0D

/-- The subgroup-theoretic core of BG (9.10): if `P₀ ≤ N_G(P)'` and
`N_G(P) ≤ L ∩ M`, then `P₀ ≤ (L ∩ M)'`. -/
private theorem le_derivedInG_inf_of_le_derivedInG_normalizer {P M L P0 : Subgroup G}
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G)))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hNPL : Subgroup.normalizer (P : Set G) ≤ L) :
    P0 ≤ derivedInG (L ⊓ M) :=
  hP0N.trans (derivedInG_mono (le_inf hNPL hNPM))

/-- BG Lemma 9.5 bridge toward (9.10): after reapplying (9.9) with the witness
maximal subgroup `L`, any `P₀ ≤ N_G(P)'` lies in `(L ∩ M)'`. -/
theorem p0_le_derivedInG_inf_of_scn3_witness_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A M L P P0 : Subgroup G} {y : G}
    (hA : A ∈ S07.scn3Global p G) (hAnot : ¬ IsUniquelyMaximal A) (hyA : y ∈ A)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hPp : IsPGroup p P) (hAP : A ≤ P)
    (hPnormA : P ≤ Subgroup.normalizer (A : Set G))
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P : Set G))) :
    P0 ≤ derivedInG (L ⊓ M) := by
  have hNPL : Subgroup.normalizer (P : Set G) ≤ L :=
    (normalizer_scn3_pSubgroup_le_witness_maximal_of_not_scn3
      hG hA hAnot hyA hL hPp hAP hPnormA).2
  exact le_derivedInG_inf_of_le_derivedInG_normalizer hP0N hNPM hNPL

/-- If `y ∈ B` and `L` contains `C_G(y)`, then `D ∩ C_G(B)` is contained in
`D ∩ L`. This is the subgroup inclusion used to pass from a centralizer of
`D ∩ L` to a centralizer of `D ∩ C_G(B)`. -/
private theorem inf_centralizer_le_inf_of_mem_of_maximalContaining_centralizer_singleton
    {B D L : Subgroup G} {y : G} (hyB : y ∈ B)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G))) :
    D ⊓ Subgroup.centralizer (B : Set G) ≤ D ⊓ L := by
  refine le_inf inf_le_left ?_
  exact inf_le_right.trans
    ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyB)).trans hL.2)

/-- Antitonicity bridge for the final contradiction in BG Lemma 9.5. If `P₀`
centralizes `D ∩ L`, then it centralizes the smaller subgroup `D ∩ C_G(B)`. -/
theorem le_centralizer_inf_centralizer_of_le_centralizer_inf_maximal
    {B D L P0 : Subgroup G} {y : G} (hyB : y ∈ B)
    (hL : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)))
    (hcentDL : P0 ≤ Subgroup.centralizer ((D ⊓ L : Subgroup G) : Set G)) :
    P0 ≤ Subgroup.centralizer
      (((D ⊓ Subgroup.centralizer (B : Set G) : Subgroup G)) : Set G) :=
  hcentDL.trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      (inf_centralizer_le_inf_of_mem_of_maximalContaining_centralizer_singleton
        (D := D) hyB hL)))

/-- Lemma 9.4 rank squeeze in the form used inside BG Lemma 9.5: if `K ≤ F(M)`
and every subgroup of `K` is excluded from `𝒰`, then `K` has rank at most two. -/
private theorem rank_le_two_of_no_uniqueMaximal_subgroups_le_fitting
    [Finite G] (hG : IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKF : K ≤ S08.fittingInG M)
    (hno : ∀ B : Subgroup G, B ≤ K → ¬ IsUniquelyMaximal B) :
    rank ↥K ≤ 2 := by
  classical
  by_contra hnot
  have h3K : 3 ≤ rank ↥K := by omega
  obtain ⟨q, hq, h3Kq⟩ :=
    exists_pRank_ge_of_pos_le_rank (G := ↥K) (n := 3) (by norm_num) h3K
  have : Fact q.Prime := ⟨hq⟩
  have h3Fq : 3 ≤ pRank ↥(S08.fittingInG M) q :=
    h3Kq.trans
      (pRank_le_of_injective (f := Subgroup.inclusion hKF)
        (Subgroup.inclusion_injective hKF))
  obtain ⟨B, hBmax, hBrank⟩ :=
    exists_isMaxElemAbelianIn_rank_three_of_three_le_pRank (H := K) h3Kq
  have hBea : B.IsElementaryAbelian q :=
    S08.isMaxElemAbelianIn_isElementaryAbelian hBmax
  have hBK : B ≤ K := S08.isMaxElemAbelianIn_le hBmax
  have hBU : IsUniquelyMaximal B :=
    (abelian_rank_three_isUniquelyMaximal_of_fitting hG hM h3Fq)
      B (IsMulCommutative.of_comm hBea.comm) hBea.isPGroup hBrank
  exact (hno B hBK) hBU

/-- In the BG Lemma 9.5 contradiction setup, `D ∩ L` has rank at most two.
Here `D` is any subgroup of `F(M)` and `L ≠ M` is another maximal subgroup; the
specialization `D = O_{p'}(F(M))` is used below. -/
private theorem rank_inf_le_two_of_le_fitting_of_distinct_maximals
    [Finite G] (hG : IsMinimalSimpleOdd G) {D M L : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G) (hLM : L ≠ M)
    (hDF : D ≤ S08.fittingInG M) :
    rank ↥(D ⊓ L : Subgroup G) ≤ 2 := by
  refine rank_le_two_of_no_uniqueMaximal_subgroups_le_fitting hG hM
    (K := D ⊓ L) (inf_le_left.trans hDF) ?_
  intro B hB
  exact not_isUniquelyMaximal_of_le_inf_distinct_maximals hM hL
    (hB.trans (le_inf (inf_le_left.trans (hDF.trans (S08.fittingInG_le M))) inf_le_right))
    hLM

/-- Specialization of the Lemma 9.5 rank squeeze to `D = O_{p'}(F(M))`. -/
theorem rank_inf_opiCoreFitting_le_two_of_distinct_maximals
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} {M L : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hL : L ∈ maximalSubgroups G) (hLM : L ≠ M) :
    rank ↥(opiCoreInG ({p} : Set ℕ)ᶜ (S08.fittingInG M) ⊓ L : Subgroup G) ≤ 2 :=
  rank_inf_le_two_of_le_fitting_of_distinct_maximals hG hM hL hLM
    (opiCoreInG_le ({p} : Set ℕ)ᶜ (S08.fittingInG M))

/-- A `subgroupOf` copy has rank no larger than the ambient subgroup it copies. -/
theorem rank_subgroupOf_le_of_le [Finite G] {H K : Subgroup G} (hKH : K ≤ H) :
    rank ↥(K.subgroupOf H) ≤ rank ↥K :=
  rank_le_of_injective (G := ↥K) (H := ↥(K.subgroupOf H))
    (f := (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKH).injective

open OddOrder.Isaacs.Ch03 in
open scoped commutatorElement in
/-- BG Lemma 1.9 applied to a chief series: a coprime subgroup that stabilizes
every chief factor of `K` centralizes `K`. This isolates the Lemma 1.9 part of
BG Lemma 9.5 after Corollary 4.19 supplies the per-factor stabilizer input. -/
theorem coprime_chiefSeries_stabilizer_le_centralizer
    {M : Type*} [Group M] [Finite M] {K : Subgroup M} [K.Normal] {D : Subgroup M}
    (hcop : (Nat.card ↥D).Coprime (Nat.card ↥K))
    (hsolv : Group.IsSolvable ↥D ∨ Group.IsSolvable ↥K)
    (hstab : ∀ i, ⁅chiefSeriesInside K i, D⁆ ≤ chiefSeriesInside K (i + 1)) :
    D ≤ Subgroup.centralizer (K : Set M) := by
  classical
  obtain ⟨N, hN⟩ := chiefSeriesInside_exists_eq_bot K
  set ψ : ↥D →* MulAut ↥K := (MulAut.conjNormal (H := K)).comp D.subtype with hψ
  set s : ℕ → Subgroup ↥K := fun i => (chiefSeriesInside K i).subgroupOf K with hs
  have hψcoe : ∀ (a : ↥D) (g : ↥K),
      ((ψ a) g : M) = (a : M) * (g : M) * (a : M)⁻¹ := by
    intro a g
    rw [hψ]
    simp [MulAut.conjNormal_apply]
  have htrivψ : ∀ a : ↥D, ψ a = 1 := by
    refine OddOrder.BG.Ch1.S01.coprime_stabilizes_chain_trivial
      ψ hcop hsolv s ?_ ?_ (n := N) ?_ ?_ ?_ ?_
    · intro i j hij
      exact Subgroup.comap_mono (chiefSeriesInside_antitone K hij)
    · simp [hs, chiefSeriesInside_zero, Subgroup.subgroupOf_self]
    · simp [hs, hN, Subgroup.bot_subgroupOf]
    · intro i
      exact (inferInstance : (chiefSeriesInside K i).Normal).subgroupOf K
    · intro i
      rw [isAInvariant_iff_smul_mem]
      intro a g hg
      rw [hs, Subgroup.mem_subgroupOf] at hg ⊢
      rw [hψcoe]
      exact (chiefSeriesInside_instNormal K i).conj_mem _ hg _
    · intro i a x hx
      rw [hs, Subgroup.mem_subgroupOf] at hx
      refine ⟨x⁻¹ * ψ a x, ?_, by group⟩
      rw [hs, Subgroup.mem_subgroupOf]
      have hcoe : ((x⁻¹ * ψ a x : ↥K) : M) = ⁅(x : M)⁻¹, (a : M)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hψcoe, commutatorElement_def]
        group
      rw [hcoe]
      exact hstab i (Subgroup.commutator_mem_commutator
        (Subgroup.inv_mem _ hx) (SetLike.coe_mem a))
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := DFunLike.congr_fun (htrivψ ⟨x, hx⟩) ⟨k, hk⟩
  have h2 : (x : M) * k * x⁻¹ = k := by
    have := congrArg Subtype.val h1
    rwa [hψcoe] at this
  have h3 : x * k = k * x := by
    have := congrArg (· * x) h2
    simpa [mul_assoc] using this
  exact h3.symm

end OddOrder.BG.Ch2.S09


