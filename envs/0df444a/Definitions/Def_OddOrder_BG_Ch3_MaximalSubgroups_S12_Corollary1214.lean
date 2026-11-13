-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1214
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary1214
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:15:13.141406+00:00
-- url     : https://prove2.me/theorems/8e98b8d1-ef51-4037-a4c5-be4cf43d3e85
-- title:
--   BG §12: Corollary 12.14, $\mathcal{M}(C_G(X))=\{M\}$ for central $\mathcal{E}_p^1$ subgroups
-- statement:
--   Formalizes Corollary 12.14 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: if $p\in\sigma(M)$, $X\in\mathcal{E}_p^1(M)$, and $p\in\beta(M)$ or $X\subseteq M_{\sigma'}$, then $\mathcal{M}(C_G(X))=\{M\}$. It is a downstream leaf because the proof uses Theorem 12.13.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary1214.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary1214.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Proposition1215

namespace OddOrder.BG.Ch3.S12.Cor1214

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **統一エンジン**: 非真の `C_G(X)` を覆う uniquely-maximal `U` が極大 `M` に入るなら
`ℳ(C_G(X)) = {M}`。`IsUniquelyMaximal.of_le_of_lt_top` で `C_G(X)` 自身を uniquely-maximal 化し、
その unique maximal が `M` と一致することを `eq_of_isCoatom_of_le` で示す。 -/
private theorem eq_singleton_of_uniquelyMaximal_le [Finite G]
    {Y U M : Subgroup G} (hU : IsUniquelyMaximal U)
    (hUC : U ≤ Y) (hUM : U ≤ M) (hM : IsCoatom M)
    (hClt : Y < ⊤) :
    maximalSubgroupsContaining Y = {M} := by
  classical
  have hCU : IsUniquelyMaximal Y :=
    hU.of_le_of_lt_top hUC hClt
  obtain ⟨hM₀co, hCM₀⟩ := hCU.uniqueMaximalSubgroup_spec
  have hUM₀ : U ≤ hCU.uniqueMaximalSubgroup := hUC.trans hCM₀
  have hMeq : M = hCU.uniqueMaximalSubgroup :=
    hU.eq_of_isCoatom_of_le hM hUM hM₀co hUM₀
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨?_, ?_⟩
  · rw [mem_maximalSubgroupsContaining]
    exact ⟨hM, hCM₀.trans hMeq.ge⟩
  · intro N hN
    rw [mem_maximalSubgroupsContaining] at hN
    exact hU.eq_of_isCoatom_of_le hN.1 (hUC.trans hN.2) hM hUM

/-- Bridge: the `↥S`-level centralizer of `L.subgroupOf S` is the `subgroupOf`-image of the
ambient `C_G(L) ⊓ S`. (Replicated from `S10_LocalLemmas.centralizer_subgroupOf_inf_eq`.) -/
private theorem centralizer_subgroupOf_inf_eq {S L : Subgroup G} (hLS : L ≤ S) :
    Subgroup.centralizer ((L.subgroupOf S : Subgroup ↥S) : Set ↥S)
      = (Subgroup.centralizer (L : Set G) ⊓ S).subgroupOf S := by
  ext m
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc
    refine ⟨fun h hh => ?_, m.2⟩
    simpa using congrArg Subtype.val (hc ⟨h, hLS hh⟩ (Subgroup.mem_subgroupOf.mpr hh))
  · intro hc h hh
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hc.1 (h : G) (Subgroup.mem_subgroupOf.mp hh)

/-- `derivedInG H = ⁅H, H⁆`. (Replicated from `S10_BetaRadicalCore.derivedInG_eq_commutator`.) -/
private theorem derivedInG_eq_commutator (H : Subgroup G) : derivedInG H = ⁅H, H⁆ := by
  rw [derivedInG, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

/-- A finite `p`-group has zero `q`-rank for `q ≠ p`. (Replicated from the private helper in
`S09_Theorem91`.) -/
private theorem pRank_eq_zero_of_isPGroup_of_ne_prime {H : Type*} [Group H] [Finite H]
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) (hH : IsPGroup p H) :
    pRank H q = 0 := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  apply le_antisymm ?_ (Nat.zero_le _)
  rw [pRank_le_iff]
  intro E hE
  obtain ⟨a, ha⟩ := (hH.to_subgroup E).exists_card_eq
  obtain ⟨b, hb⟩ := hE.isPGroup.exists_card_eq
  have hcard_one : Nat.card E = 1 := by
    by_contra hne
    have hbpos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · exact absurd (by simpa [hb0] using hb) hne
      · exact hb0
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp
      (hq.dvd_of_dvd_pow (ha ▸ hb ▸ dvd_pow_self q hbpos.ne')))
  simp [hcard_one]

/-- **BG Corollary 12.14, faithful form** (mmd L3399–3401): `p ∈ σ(M)`, `X ∈ ℰ_p¹(M)`,
`p ∈ β(M)` または `X ⊆ M_σ'` なら `ℳ(C_G(X)) = {M}` かつ、`M_σ` の *ある* Sylow `p`-部分群
`S₀ ⊇ X` について `ℳ(S₀) = {M}`。原典の `ℳ(C_G(X)) = ℳ(P) = {M}` の両 conjunct を供給する
(統一エンジンの witness `U` が全ケースで `U ≤ S₀` を満たすことを利用; issue 8002)。 -/
theorem maximalContaining_centralizer_and_someSylow_eq_singleton [Finite G]
    (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ S10.sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXM : X ≤ M)
    (hcase : p ∈ S10.beta M ∨ X ≤ derivedInG (S10.Msigma M)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
      ∃ S₀ : Subgroup G, X ≤ S₀ ∧ S₀ ≤ S10.Msigma M ∧ IsPGroup p ↥S₀ ∧
        (∀ T : Subgroup G, T ≤ S10.Msigma M → IsPGroup p ↥T → S₀ ≤ T → S₀ = T) ∧
        maximalSubgroupsContaining S₀ = {M} := by
  classical
  -- `|X| = p`, `X ≠ ⊥`, `X` is a `p`-group.
  have hXEA : X.IsElementaryAbelian p := (mem_elemAbelianOfRank.mp hX).1
  have hXcard : Nat.card ↥X = p := by
    have := (mem_elemAbelianOfRank.mp hX).2; simpa using this
  have hXpg : IsPGroup p ↥X := hXEA.isPGroup
  have hXne : X ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hXcard
    exact (Fact.out : p.Prime).one_lt.ne' hXcard.symm
  -- **Setup**: a Sylow `p`-subgroup `S` of `G` with `X ≤ S ≤ M` (since `p ∈ σ(M)`).
  have hXsubOf_pg : IsPGroup p ↥(X.subgroupOf M) :=
    hXpg.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  obtain ⟨PM, hXPM⟩ := hXsubOf_pg.exists_le_sylow
  obtain ⟨S, hS⟩ := S10.isSylow_sylowMap_of_mem_sigma hp PM
  have hSM : (S : Subgroup G) ≤ M := by rw [hS]; exact Subgroup.map_subtype_le _
  have hXS : X ≤ (S : Subgroup G) := by
    rw [hS, ← Subgroup.map_subgroupOf_eq_of_le hXM]
    exact Subgroup.map_mono hXPM
  -- **`C_G(X) < ⊤`**: else `X ≤ Z(G) = ⊥`, contradicting `X ≠ ⊥`.
  have hcenter_bot : Subgroup.center G = ⊥ := by
    rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with h | h
    · exact h
    · exfalso
      refine hG.notSolvable (Group.isSolvable_of_comm fun a b => ?_)
      exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  have hClt : Subgroup.centralizer (X : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hXcenter : X ≤ Subgroup.center G :=
      SetLike.coe_subset_coe.mp (Subgroup.centralizer_eq_top_iff_subset.mp htop)
    rw [hcenter_bot, le_bot_iff] at hXcenter
    exact hXne hXcenter
  -- `S ≤ M_σ` (hoisted out of the rank case split: needed for the exposed Sylow `S₀`).
  have hp_prime : p.Prime := Fact.out
  have hSpi : Ch03.Subgroup.IsPiGroup (S10.sigma M) (S : Subgroup G) := by
    intro s hs
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hsd := (Nat.mem_primeFactors.mp hs).2.1
    rw [hn] at hsd
    rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hs) hp_prime).mp
      ((Nat.prime_of_mem_primeFactors hs).dvd_of_dvd_pow hsd)]
  have hSMσ : (S : Subgroup G) ≤ S10.Msigma M :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM) hSM hSpi
  -- **Reduce to: a uniquely-maximal `U ≤ C_G(X)` with `U ≤ S` and `U ≤ M`.** The same witness
  -- supplies both `ℳ(C_G(X)) = {M}` (via `U ≤ C_G(X)`) and `ℳ(S) = {M}` (via `U ≤ S`).
  suffices hU : ∃ U : Subgroup G, IsUniquelyMaximal U ∧
      U ≤ Subgroup.centralizer (X : Set G) ∧ U ≤ (S : Subgroup G) ∧ U ≤ M by
    obtain ⟨U, hUmax, hUC, hUS, hUM⟩ := hU
    have hcoat : IsCoatom M := mem_maximalSubgroups.mp hM
    have hS₀lt : (S : Subgroup G) < ⊤ := lt_of_le_of_lt hSM hcoat.lt_top
    refine ⟨eq_singleton_of_uniquelyMaximal_le hUmax hUC hUM hcoat hClt,
      (S : Subgroup G), hXS, hSMσ, S.isPGroup', ?_,
      eq_singleton_of_uniquelyMaximal_le hUmax hUS hUM hcoat hS₀lt⟩
    -- `S` is a Sylow `p`-subgroup of `G` inside `M_σ`, hence maximal among `p`-subgroups of `M_σ`.
    intro T _hTMσ hTpg hST
    exact (S.3 hTpg hST).symm
  -- **Case split** on `r(C_P(X))` where `C_P(X) = C_G(X) ⊓ S`.
  set CPX : Subgroup G := Subgroup.centralizer (X : Set G) ⊓ (S : Subgroup G) with hCPX
  rcases Nat.lt_or_ge (pRank ↥CPX p) 3 with hlt | hge
  · -- `r(C_P(X)) ≤ 2`: `P = S` is nonabelian with `X ≤ Z(P)`; Theorem 12.13.
    have hle : pRank ↥CPX p ≤ 2 := by omega
    have hp_prime : p.Prime := Fact.out
    have hp_dvd_M : p ∣ Nat.card ↥M :=
      (Nat.mem_primeFactors.mp ((S10.mem_sigma_iff M p).mp hp).1).2.1
    have hp_odd : Odd p :=
      hG.odd.of_dvd_nat (dvd_trans hp_dvd_M (Subgroup.card_subgroup_dvd_card M))
    -- `X` realized as an order-`p` subgroup of `↥S`.
    have hX'card : Nat.card ↥(X.subgroupOf (S : Subgroup G)) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXS).toEquiv]; exact hXcard
    -- Bridge: `r(C_{↥S}(X')) ≤ 2` from `hle` (`= r(C_G(X) ⊓ S)`).
    have hrank2' : pRank ↥(Subgroup.centralizer
        ((X.subgroupOf (S : Subgroup G) : Subgroup ↥(S : Subgroup G)) :
          Set ↥(S : Subgroup G))) p ≤ 2 := by
      rw [centralizer_subgroupOf_inf_eq hXS]
      exact le_trans
        (pRank_le_of_injective
          (f := (Subgroup.subgroupOfEquivOfLe
            (inf_le_right : Subgroup.centralizer (X : Set G) ⊓ (S : Subgroup G)
              ≤ (S : Subgroup G))).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe _).injective)
        hle
    -- **Step 1**: `p ∉ idealPrime G` (`= p ∉ β(G)`).
    have hnotideal : ¬ S10.idealPrime p G := by
      rcases Nat.lt_or_ge (pRank ↥(S : Subgroup G) p) 3 with hSlt | hSge
      · intro hideal
        have h3G : 3 ≤ pRank G p := hideal.1
        rw [← pRank_sylow_eq S] at h3G
        omega
      · have hnarrow : IsNarrow p ↥(S : Subgroup G) :=
          (Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two
            hp_odd S.isPGroup' hSge).mpr ⟨X.subgroupOf (S : Subgroup G), hX'card, hrank2'⟩
        obtain ⟨A, hAcard, hAmax⟩ :=
          (Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
            hp_odd S.isPGroup' hSge).mp hnarrow
        intro hideal
        exact hideal.2 S ⟨A, hAcard, hAmax⟩
    -- **Step 2**: `p ∉ β(M)` (`β(M)` requires `idealPrime`).
    have hpβ : p ∉ S10.beta M := fun h => hnotideal h.2
    -- **Step 3**: the `p ∈ β(M)` disjunct of `hcase` dies, leaving `X ⊆ M_σ'`.
    have hXMσ' : X ≤ derivedInG (S10.Msigma M) := hcase.resolve_left hpβ
    have hpπ : p ∈ (Nat.card ↥M).primeFactors := ((S10.mem_sigma_iff M p).mp hp).1
    -- (`hSMσ : S ≤ M_σ` is hoisted above the rank case split.)
    -- **Step 4**: `X ⊆ S'` (`= P'`). Lemma 10.8(c): `M_σ` has a normal `p`-complement `K`;
    -- `S` is a Sylow `p` of `↥M_σ`. Project `↥M_σ ↠ ↥M_σ ⧸ K`: `commutator ↥M_σ ≤ ⁅S,S⁆ ⊔ K`,
    -- then Dedekind (`K ⊓ S = ⊥`) gives `(commutator ↥M_σ) ⊓ S ≤ ⁅S,S⁆`.
    have hXP' : X ≤ derivedInG (S : Subgroup G) := by
      obtain ⟨K, hKnormal, hKcompl⟩ :=
        (S10.derived_msigma_hasNormalPComplement_of_not_mem_beta hG hM hpπ hpβ).2
      have : K.Normal := hKnormal
      obtain ⟨S'', hS''eq⟩ := S10.exists_sylow_subgroupOf_of_le S hSMσ
      set Ssub : Subgroup ↥(S10.Msigma M) := (S'' : Subgroup ↥(S10.Msigma M)) with hSsubdef
      have hcompl := hKcompl S''
      have hqS : Ssub.map (QuotientGroup.mk' K) = ⊤ := by
        have hKmap : K.map (QuotientGroup.mk' K) = ⊥ := by
          rw [eq_bot_iff, Subgroup.map_le_iff_le_comap]
          exact le_of_eq (QuotientGroup.ker_mk' K).symm
        have hsup : K ⊔ Ssub = ⊤ := hcompl.sup_eq_top
        have := congrArg (Subgroup.map (QuotientGroup.mk' K)) hsup
        rwa [Subgroup.map_sup, hKmap, bot_sup_eq,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] at this
      have hcomm_map : (commutator ↥(S10.Msigma M)).map (QuotientGroup.mk' K)
          = (⁅Ssub, Ssub⁆).map (QuotientGroup.mk' K) := by
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_commutator, hqS,
          Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
      have hkey : commutator ↥(S10.Msigma M) ≤ ⁅Ssub, Ssub⁆ ⊔ K := by
        calc commutator ↥(S10.Msigma M)
            ≤ ((commutator ↥(S10.Msigma M)).map (QuotientGroup.mk' K)).comap
                (QuotientGroup.mk' K) := Subgroup.le_comap_map _ _
          _ = ((⁅Ssub, Ssub⁆).map (QuotientGroup.mk' K)).comap (QuotientGroup.mk' K) := by
                rw [hcomm_map]
          _ = ⁅Ssub, Ssub⁆ ⊔ (QuotientGroup.mk' K).ker := Subgroup.comap_map_eq _ _
          _ = ⁅Ssub, Ssub⁆ ⊔ K := by rw [QuotientGroup.ker_mk']
      have hX'comm : X.subgroupOf (S10.Msigma M) ≤ commutator ↥(S10.Msigma M) := by
        calc X.subgroupOf (S10.Msigma M)
            ≤ (derivedInG (S10.Msigma M)).subgroupOf (S10.Msigma M) :=
              Subgroup.comap_mono hXMσ'
          _ = commutator ↥(S10.Msigma M) := by
              rw [derivedInG, Subgroup.subgroupOf,
                Subgroup.comap_map_eq_self_of_injective (S10.Msigma M).subtype_injective]
      have hX'S'' : X.subgroupOf (S10.Msigma M) ≤ Ssub := by
        rw [hS''eq]; exact Subgroup.comap_mono hXS
      -- Manual Dedekind (`K ⊴ M_σ`): `x ∈ ⁅S,S⁆ ⊔ K` and `x ∈ S` force the `K`-part trivial.
      have hSK : K ⊓ Ssub = ⊥ := by
        rw [hSsubdef]; exact disjoint_iff.mp hcompl.disjoint
      have hX'comm2 : X.subgroupOf (S10.Msigma M) ≤ ⁅Ssub, Ssub⁆ := by
        intro x hx
        have hxSsub : x ∈ Ssub := hX'S'' hx
        have hxsup : x ∈ ⁅Ssub, Ssub⁆ ⊔ K := hkey (hX'comm hx)
        obtain ⟨c, hc, k, hk, hck⟩ :=
          (Subgroup.mem_sup_of_normal_right (s := ⁅Ssub, Ssub⁆) (t := K)).mp hxsup
        have hcomm_self : ⁅Ssub, Ssub⁆ ≤ Ssub := Subgroup.commutator_le.mpr fun a ha b hb => by
          rw [commutatorElement_def]
          exact Ssub.mul_mem (Ssub.mul_mem (Ssub.mul_mem ha hb) (Ssub.inv_mem ha)) (Ssub.inv_mem hb)
        have hcSsub : c ∈ Ssub := hcomm_self hc
        have hkSsub : k ∈ Ssub := by
          have hkeq : k = c⁻¹ * x := by rw [← hck]; group
          rw [hkeq]; exact Ssub.mul_mem (Ssub.inv_mem hcSsub) hxSsub
        have hk1 : k = 1 := by
          have hmem : k ∈ K ⊓ Ssub := Subgroup.mem_inf.mpr ⟨hk, hkSsub⟩
          rw [hSK, Subgroup.mem_bot] at hmem; exact hmem
        rw [← hck, hk1, mul_one]; exact hc
      have hS''map : Ssub.map (S10.Msigma M).subtype = (S : Subgroup G) := by
        rw [hS''eq, Subgroup.map_subgroupOf_eq_of_le hSMσ]
      calc X = (X.subgroupOf (S10.Msigma M)).map (S10.Msigma M).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le (hXS.trans hSMσ)).symm
        _ ≤ (⁅Ssub, Ssub⁆).map (S10.Msigma M).subtype := Subgroup.map_mono hX'comm2
        _ = ⁅(S : Subgroup G), (S : Subgroup G)⁆ := by rw [Subgroup.map_commutator, hS''map]
        _ = derivedInG (S : Subgroup G) := (derivedInG_eq_commutator _).symm
    -- **Step 5**: `rank S ≤ 2`. If `r(S) ≥ 3`, `S` is narrow (Cor 5.4), and Theorem 5.3(d)
    -- gives `X' ⊓ S' = ⊥`, contradicting `1 ⊂ X ⊆ S' = P'`.
    have hrankS_p : pRank ↥(S : Subgroup G) p ≤ 2 := by
      by_contra hcon
      have hSge : 3 ≤ pRank ↥(S : Subgroup G) p := by omega
      have hnarrow : IsNarrow p ↥(S : Subgroup G) :=
        (Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two hp_odd S.isPGroup' hSge).mpr
          ⟨X.subgroupOf (S : Subgroup G), hX'card, hrank2'⟩
      obtain ⟨-, hXcommbot, -, -⟩ :=
        Ch1.S05.narrow_centralizer_decomp hp_odd S.isPGroup' hSge hnarrow
          (X.subgroupOf (S : Subgroup G)) hX'card hrank2'
      have hX'comm_S : X.subgroupOf (S : Subgroup G) ≤ commutator ↥(S : Subgroup G) := by
        calc X.subgroupOf (S : Subgroup G)
            ≤ (derivedInG (S : Subgroup G)).subgroupOf (S : Subgroup G) := Subgroup.comap_mono hXP'
          _ = commutator ↥(S : Subgroup G) := by
              rw [derivedInG, Subgroup.subgroupOf,
                Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective]
      rw [inf_eq_left.mpr hX'comm_S] at hXcommbot
      rw [hXcommbot, Subgroup.card_bot] at hX'card
      exact (Fact.out : p.Prime).one_lt.ne' hX'card.symm
    have hrankS : rank ↥(S : Subgroup G) ≤ 2 := by
      rw [rank_le_iff]
      intro q hq
      by_cases hqp : q = p
      · subst q; exact hrankS_p
      · rw [pRank_eq_zero_of_isPGroup_of_ne_prime hq hqp S.isPGroup']; exact Nat.zero_le _
    -- **Step 6**: Corollary 10.7(b). `S` is abelian (impossible: `X ⊆ S' = ⊥`) or a central
    -- product `P₁ * P₂` with `P₁` extraspecial. The witness is `P₁`: nonabelian, `X ≤ C_G(P₁)`.
    rcases (S10.sylow_structure hG S).2.1 hrankS with hSab | ⟨P₁, P₂, hP₁S, hP₂S, hP₁es, hP₁card,
      hP₂cyc, hOmega, hcp⟩
    · -- abelian case: `S' = ⊥`, contradicting `1 ⊂ X ⊆ S'`.
      exfalso
      have hcommbot : ⁅(S : Subgroup G), (S : Subgroup G)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact congrArg Subtype.val (hSab.is_comm.comm (⟨b, hb⟩ : ↥(S : Subgroup G)) ⟨a, ha⟩)
      have hXbot : X = ⊥ :=
        le_bot_iff.mp (hXP'.trans (by rw [derivedInG_eq_commutator, hcommbot]))
      exact hXne hXbot
    · -- central-product case: witness `P₁` (`P₁ ≤ S`, so it also feeds `ℳ(S) = {M}`).
      refine ⟨P₁, ?_, ?_, hP₁S, hP₁S.trans hSM⟩
      · -- `IsUniquelyMaximal P₁` (Theorem 12.13: `P₁` is a nonabelian `p`-group).
        have hP₁nab : ¬ IsMulCommutative ↥(P₁ : Subgroup G) := by
          intro hcomm
          have hctop : Subgroup.center ↥(P₁ : Subgroup G) = ⊤ := Subgroup.center_eq_top
          have h1 : Nat.card ↥(Subgroup.center ↥(P₁ : Subgroup G)) = p ^ 3 := by
            rw [hctop, Nat.card_congr Subgroup.topEquiv.toEquiv]; exact hP₁card
          have hp1lt : p < p ^ 3 := by
            calc p = p ^ 1 := (pow_one p).symm
              _ < p ^ 3 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
          exact absurd (hP₁es.isExtraspecial.center_card.symm.trans h1) hp1lt.ne
        exact nonabelian_pgroup_isUniquelyMaximal hG hP₁es.isExtraspecial.isPGroup hP₁nab
      · -- `P₁ ≤ C_G(X)`: `X ⊆ S' = ⁅S,S⁆ ⊆ C_G(P₁)` (central product + extraspecial).
        have hcent : derivedInG (S : Subgroup G) ≤ Subgroup.centralizer (P₁ : Set G) := by
          rw [derivedInG_eq_commutator]
          -- `⁅P₁,P₁⁆ = Z(P₁) ≤ C_G(P₁)` (extraspecial: derived = centre).
          have hP₁cc : ⁅(P₁ : Subgroup G), (P₁ : Subgroup G)⁆ ≤ Subgroup.centralizer (P₁ : Set G) :=
              by
            rw [← derivedInG_eq_commutator, derivedInG, hP₁es.isExtraspecial.commutator_eq_center]
            intro y hy
            obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
            rw [Subgroup.mem_centralizer_iff]
            intro g hg
            exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
          -- `↑S = ↑P₁ * ↑P₂`.
          have hP₁norm : (P₁ : Subgroup G) ≤ Subgroup.normalizer (P₂ : Set G) :=
            le_trans hcp.le_centralizer_right (Subgroup.centralizer_le_normalizer _)
          have hScoe : (↑(S : Subgroup G) : Set G)
              = (↑(P₁ : Subgroup G) : Set G) * ↑(P₂ : Subgroup G) := by
            rw [hcp.sup_eq]; exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hP₁norm
          -- `P₂` centralizes `S` (`P₂` commutes with `P₁` and is abelian).
          let := hP₂cyc.commGroup
          have hP₂cS : ∀ c ∈ (P₂ : Subgroup G), ∀ s ∈ (S : Subgroup G), c * s = s * c := by
            intro c hc s hs
            rw [← SetLike.mem_coe, hScoe] at hs
            obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Set.mem_mul.mp hs
            have hcs₁ : c * s₁ = s₁ * c := (hcp.commute_of_mem hs₁ hc).symm
            have hcs₂ : c * s₂ = s₂ * c :=
              congrArg Subtype.val (mul_comm (⟨c, hc⟩ : ↥(P₂ : Subgroup G)) ⟨s₂, hs₂⟩)
            calc c * (s₁ * s₂) = c * s₁ * s₂ := by rw [mul_assoc]
              _ = s₁ * c * s₂ := by rw [hcs₁]
              _ = s₁ * (c * s₂) := by rw [mul_assoc]
              _ = s₁ * (s₂ * c) := by rw [hcs₂]
              _ = s₁ * s₂ * c := by rw [mul_assoc]
          -- `⁅u*c, v⁆ = ⁅u,v⁆` (`c` commutes with `v`); `⁅u, w*d⁆ = ⁅u,w⁆` (`d` commutes with `u`).
          have keyA : ∀ u v c : G, c * v = v * c → ⁅u * c, v⁆ = ⁅u, v⁆ := by
            intro u v c hcv
            rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
              show u * c * v = u * (c * v) by group, hcv]
            group
          have keyB : ∀ u w d : G, d * u = u * d → ⁅u, w * d⁆ = ⁅u, w⁆ := by
            intro u w d hdu
            rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
              show u * (w * d) * u⁻¹ = u * w * (d * u⁻¹) by group,
              show d * u⁻¹ = u⁻¹ * d from (Commute.inv_right hdu).eq]
            group
          -- `⁅S,S⁆ ≤ ⁅P₁,P₁⁆`: factor and drop the central `P₂`-parts.
          have hSSP₁ : ⁅(S : Subgroup G), (S : Subgroup G)⁆
              ≤ ⁅(P₁ : Subgroup G), (P₁ : Subgroup G)⁆ := by
            rw [Subgroup.commutator_le]
            intro a ha b hb
            have ha' := ha; have hb' := hb
            rw [← SetLike.mem_coe, hScoe] at ha'
            rw [← SetLike.mem_coe, hScoe] at hb'
            obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Set.mem_mul.mp ha'
            obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hb'
            rw [keyA a₁ (b₁ * b₂) a₂ (hP₂cS a₂ ha₂ (b₁ * b₂) hb),
              keyB a₁ b₁ b₂ (hP₂cS b₂ hb₂ a₁ (hP₁S ha₁))]
            exact Subgroup.commutator_mem_commutator ha₁ hb₁
          exact le_trans hSSP₁ hP₁cc
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp (hcent (hXP' hx)) a ha).symm
  · -- `r(C_P(X)) ≥ 3`: `C_P(X) = C_G(X) ⊓ S` itself is uniquely maximal by the Uniqueness Theorem
    -- (`CPX ≤ S` via `inf_le_right`, so it also feeds `ℳ(S) = {M}`).
    refine ⟨CPX, ?_, inf_le_left, inf_le_right, inf_le_right.trans hSM⟩
    have hrank3 : 3 ≤ rank ↥CPX := le_trans hge (pRank_le_rank p)
    have hrank2 : 2 ≤ rank ↥CPX := by omega
    have hCPXlt : CPX < ⊤ :=
      lt_of_le_of_lt (inf_le_right.trans hSM) (mem_maximalSubgroups.mp hM).lt_top
    exact OddOrder.BG.Ch2.S09.uniquenessTheorem hG hCPXlt hrank2 (Or.inl hrank3)

/-- **BG Corollary 12.14** (mmd L3399): `p ∈ σ(M)`, `X ∈ ℰ_p¹(M)`, `p ∈ β(M)` または
`X ⊆ M_σ'` なら `ℳ(C_G(X)) = {M}`。`…and_someSylow…` の第 1 projection。 -/
theorem maximalContaining_centralizer_eq_singleton [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ S10.sigma M)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXM : X ≤ M)
    (hcase : p ∈ S10.beta M ∨ X ≤ derivedInG (S10.Msigma M)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
  (maximalContaining_centralizer_and_someSylow_eq_singleton hG hM hp hX hXM hcase).1

end OddOrder.BG.Ch3.S12.Cor1214


