-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04g_Thm418Core
-- name    : OddOrder_BG_Ch1_Preliminary_S04g_Thm418Core
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:13:08.3717+00:00
-- url     : https://prove2.me/theorems/ae2ebe01-e42a-4d86-96d0-af6bb1ee43de
-- title:
--   BG §4H: Theorem 4.18, rank-2 solvable structure (core proof)
-- statement:
--   Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, Chapter I §4, Theorem 4.18 (printed p. 43). This leaf gives the reduction to $O_{p'}(G)=1$ and the assembly of Theorem 4.18(a)-(e), with direct corollaries on rank and the Fitting subgroup.
--
--   The bundle consists of lemmas, including `conjNormal_ker` (the kernel of `MulAut.conjNormal` is the centralizer), `isPGroup_commutator_quotient_conjNormal_ker_of_pRank_le_two` (Lemma 4.17 in quotient-action form) and `card_quotient_oPiPrimePiCore` (a third-isomorphism cardinality statement).
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04g_Thm418Core.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04g_Thm418Core.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04f_Blackburn
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLength
import Definitions.Def_OddOrder_GroupTheory_OpResidual
import Definitions.Def_OddOrder_Mathlib_Subgroup

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped commutatorElement

section Thm418

variable {G : Type*} [Group G] [Finite G]

/-- `{q | q ∉ ({p} : Set ℕ)} = {r | r ≠ p}` — `oPiPrimePiCore` の内部表現と
Thm 5.6 語彙の橋。S05 (Thm 5.6 narrow core) でも使う。 -/
theorem compl_singleton_eq {p : ℕ} :
    {q : ℕ | q ∉ ({p} : Set ℕ)} = {r : ℕ | r ≠ p} := by
  ext q
  simp [Set.mem_singleton_iff]

/-- π-glue: `p`-部分群は `{p}`-群。 -/
theorem isPiGroup_singleton_of_isPGroup {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPGroup p ↥H) : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := by
  intro q hq
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  rw [hk, Nat.mem_primeFactors] at hq
  have hq_eq : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq.1 (Fact.out : p.Prime)).mp
      (hq.1.dvd_of_dvd_pow hq.2.1)
  simp [hq_eq]

/-- π-glue: `{p}`-群は `p`-部分群。 -/
theorem isPGroup_of_isPiGroup_singleton {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H) : IsPGroup p ↥H := by
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card ↥H).primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_
  intro q hq hq_dvd
  have hmem : q ∈ (Nat.card ↥H).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, Nat.card_pos.ne'⟩
  exact Set.mem_singleton_iff.mp (hH q hmem)

/-- `p ∉ π` なら `p ∤ |O_π(G)|`。 -/
theorem not_dvd_card_oPiCore {p : ℕ} [Fact p.Prime] {π : Set ℕ}
    (hp_notin : p ∉ π) : ¬ p ∣ Nat.card ↥(Ch03.oPiCore π G) := by
  intro hdvd
  have hmem : p ∈ (Nat.card ↥(Ch03.oPiCore π G)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
  exact hp_notin (Ch03.oPiCore.isPiGroup π p hmem)

omit [Finite G] in
/-- **`MulAut.conjNormal` の核は中心化群**。S05 (Thm 5.6 narrow core) でも使う。 -/
theorem conjNormal_ker {N : Subgroup G} [N.Normal] :
    (MulAut.conjNormal (G := G) (H := N)).ker = Subgroup.centralizer (N : Set G) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h n hn
    have happ := congrArg (fun e : MulAut ↥N => ((e ⟨n, hn⟩ : ↥N) : G)) h
    simp only [MulAut.one_apply, MulAut.conjNormal_apply] at happ
    -- happ : a * n * a⁻¹ = n
    calc n * a = (a * n * a⁻¹) * a := by rw [happ]
      _ = a * n := by group
  · intro h
    ext n
    simp only [MulAut.one_apply, MulAut.conjNormal_apply]
    have hcomm := h (n : G) n.2
    calc a * (n : G) * a⁻¹ = ((n : G) * a) * a⁻¹ := by rw [← hcomm]
      _ = (n : G) := by group

/-- If a subgroup has `p`-group conjugation image on a minimal normal `p`-subgroup,
then it centralizes that subgroup. This is the fixed-point argument used in BG
Corollary 4.19: a nontrivial fixed-point subgroup is normal, hence all of the
chief factor. -/
theorem le_centralizer_of_isPGroup_conjNormal_image_minimalNormal
    {D N : Subgroup G} [D.Normal] [N.Normal] (hMin : Ch02.IsMinimalNormal N)
    {p : ℕ} [Fact p.Prime] (hN_pg : IsPGroup p ↥N)
    (hD_pg : IsPGroup p ↥(D.map (MulAut.conjNormal (H := N)))) :
    D ≤ Subgroup.centralizer (N : Set G) := by
  classical
  set α : G →* MulAut ↥N := MulAut.conjNormal with hα_def
  have hD_pgPrime : IsPGroup p ↥(D.map α) := by
    rw [hα_def]
    exact hD_pg
  have hN_nontriv : Nontrivial ↥N := by
    rcases Subgroup.bot_or_nontrivial N with h | h
    · exact absurd h hMin.2.1
    · exact h
  have hfix_ne : Subgroup.fixedPointsOfMulAut (D.map α).subtype ≠ ⊥ :=
    Ch04.fixedPoints_ne_bot_of_pgroup_action_pgroup hN_pg hD_pgPrime _
  set W : Subgroup G :=
    (Subgroup.fixedPointsOfMulAut (D.map α).subtype).map N.subtype with hW_def
  have hW_mem : ∀ x : G, x ∈ W ↔ x ∈ N ∧ ∀ d ∈ D, d * x * d⁻¹ = x := by
    intro x
    constructor
    · rintro ⟨⟨n, hn⟩, hfix, rfl⟩
      refine ⟨hn, fun d hd => ?_⟩
      have h1 := Subgroup.mem_fixedPointsOfMulAut.mp hfix
        ⟨α d, Subgroup.mem_map.mpr ⟨d, hd, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      calc d * (N.subtype ⟨n, hn⟩) * d⁻¹
          = (((α d) ⟨n, hn⟩ : ↥N) : G) :=
            (MulAut.conjNormal_apply d (⟨n, hn⟩ : ↥N)).symm
        _ = N.subtype ⟨n, hn⟩ := h2
    · rintro ⟨hxN, hxfix⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_fixedPointsOfMulAut]
      intro a
      obtain ⟨d, hd, ha⟩ := a.2
      have h3 : a.1 ⟨x, hxN⟩ = (⟨x, hxN⟩ : ↥N) := by
        rw [← ha]
        apply Subtype.ext
        calc (((α d) ⟨x, hxN⟩ : ↥N) : G)
            = d * x * d⁻¹ := MulAut.conjNormal_apply d (⟨x, hxN⟩ : ↥N)
          _ = x := hxfix d hd
      exact h3
  have hW_le : W ≤ N := by
    intro x hx
    exact ((hW_mem x).mp hx).1
  have hW_ne : W ≠ ⊥ := by
    intro h
    apply hfix_ne
    rw [hW_def, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at h
    exact h
  have hW_norm : W.Normal := by
    constructor
    intro n hn g
    obtain ⟨hnN, hnfix⟩ := (hW_mem n).mp hn
    refine (hW_mem _).mpr ⟨(inferInstance : N.Normal).conj_mem n hnN g, fun d hd => ?_⟩
    have hdPrime : g⁻¹ * d * g ∈ D := by
      simpa using (inferInstance : D.Normal).conj_mem d hd g⁻¹
    have hfix := hnfix _ hdPrime
    calc d * (g * n * g⁻¹) * d⁻¹
        = g * ((g⁻¹ * d * g) * n * (g⁻¹ * d * g)⁻¹) * g⁻¹ := by group
      _ = g * n * g⁻¹ := by rw [hfix]
  rcases hMin.2.2 W (inferInstance : W.Normal) hW_le with hW_bot | hW_top
  · exact absurd hW_bot hW_ne
  · intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnW : n ∈ W := by rw [hW_top]; exact hn
    have hfix := ((hW_mem n).mp hnW).2 d hd
    calc n * d = (d * n * d⁻¹) * d := by rw [hfix]
      _ = d * n := by group

/-- Corollary 4.19 fixed-point endpoint for an arbitrary chief factor: if the
image of `D` acting by conjugation on the quotient chief factor `U/V` is a
`p`-group, then `D` centralizes `U/V`. -/
theorem le_chiefFactorCentralizer_of_isPGroup_conjNormal_image_chiefFactor
    {p : ℕ} [Fact p.Prime] {D U V : Subgroup G} [D.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal] (hChief : IsChiefFactor U V)
    (hUbar_pg : IsPGroup p ↥(U.map (QuotientGroup.mk' V)))
    (hDbar_pg : IsPGroup p
      ↥((D.map (QuotientGroup.mk' V)).map
        (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V))))) :
    D ≤ chiefFactorCentralizer U V := by
  have hDbar_normal : (D.map (QuotientGroup.mk' V)).Normal :=
    (inferInstance : D.Normal).map _ (QuotientGroup.mk'_surjective V)
  have hMin : Ch02.IsMinimalNormal (U.map (QuotientGroup.mk' V)) :=
    hChief.isMinimalNormal_map_quotient
  have hcent :
      D.map (QuotientGroup.mk' V) ≤
        Subgroup.centralizer
          ((U.map (QuotientGroup.mk' V) : Subgroup (G ⧸ V)) : Set (G ⧸ V)) :=
    le_centralizer_of_isPGroup_conjNormal_image_minimalNormal
      (G := G ⧸ V) (D := D.map (QuotientGroup.mk' V))
      (N := U.map (QuotientGroup.mk' V)) hMin hUbar_pg hDbar_pg
  exact chiefFactorCentralizer.le_of_map_le_centralizer hcent

omit [Finite G] in
/-- If a homomorphism `φ` kills `K`, then a `p`-group derived subgroup in
`G/K` gives a `p`-group image of `G'` under `φ`. This packages the quotient
map calculation used in Corollary 4.19 and the §5 rank/narrow variants. -/
theorem isPGroup_commutator_map_of_quotient_commutator_isPGroup
    {A : Type*} [Group A] {p : ℕ} {K : Subgroup G} [K.Normal] (φ : G →* A)
    (hK : K ≤ φ.ker) (hQ : IsPGroup p ↥(_root_.commutator (G ⧸ K))) :
    IsPGroup p ↥((_root_.commutator G).map φ) := by
  let φbar : G ⧸ K →* A :=
    QuotientGroup.lift K φ (fun k hk => MonoidHom.mem_ker.mp (hK hk))
  have hcomp : φbar.comp (QuotientGroup.mk' K) = φ := by
    ext g
    rfl
  have hmapK : (_root_.commutator G).map (QuotientGroup.mk' K) =
      _root_.commutator (G ⧸ K) := by
    rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
  have hmap : (_root_.commutator G).map φ =
      (_root_.commutator (G ⧸ K)).map φbar := by
    rw [← hcomp, ← hmapK, Subgroup.map_map]
  rw [hmap]
  exact hQ.map φbar

omit [Finite G] in
/-- Lemma 4.17 in the quotient-action form used by Corollary 4.19: if a
normal `p`-subgroup has `p`-rank at most two, then the derived subgroup of the
quotient by its conjugation kernel is a `p`-group. -/
theorem isPGroup_commutator_quotient_conjNormal_ker_of_pRank_le_two
    [Finite G] (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R : Subgroup G} [R.Normal] (hR_pg : IsPGroup p ↥R)
    (hR_rank : pRank ↥R p ≤ 2) :
    IsPGroup p (_root_.commutator (G ⧸ (MulAut.conjNormal (H := R)).ker)) := by
  let ψ : G →* MulAut ↥R := MulAut.conjNormal
  change IsPGroup p (_root_.commutator (G ⧸ ψ.ker))
  have hquot_dvd : Nat.card (G ⧸ ψ.ker) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card ψ.ker
    simpa [Subgroup.index] using this
  have hquot_odd : Odd (Nat.card (G ⧸ ψ.ker)) := by
    rcases Nat.even_or_odd (Nat.card (G ⧸ ψ.ker)) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  exact isPGroup_commutator_of_mulAut_odd_of_pRank_le_two hp_odd hR_pg hR_rank
    (QuotientGroup.kerLift_injective ψ) hquot_odd

/-- Corollary 4.19 action-image bridge, modulo the lower factor: if a normal
`p`-subgroup `R` has `p`-rank at most two and the top `U` of a chief factor is
contained in `R ⊔ V`, then the image of `G'` acting on `U/V` is a `p`-group. -/
theorem isPGroup_commutator_chiefFactor_conjNormal_image_of_pRank_le_two_of_le_sup
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R U V : Subgroup G} [R.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal]
    (hR_pg : IsPGroup p ↥R) (hR_rank : pRank ↥R p ≤ 2) (hU_le_RV : U ≤ R ⊔ V) :
    IsPGroup p ↥(((_root_.commutator G).map (QuotientGroup.mk' V)).map
      (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))) := by
  let q : G →* G ⧸ V := QuotientGroup.mk' V
  let N : Subgroup (G ⧸ V) := U.map q
  let φ : G →* MulAut ↥N := (MulAut.conjNormal (H := N)).comp q
  let K : Subgroup G := (MulAut.conjNormal (H := R)).ker
  have hK_le : K ≤ φ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    ext x
    obtain ⟨u, huU, hxu⟩ := x.2
    obtain ⟨r, hrR, v, hvV, hru⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := R) (t := V)).mp (hU_le_RV huU)
    have hg_fix_r : g * r * g⁻¹ = r := by
      have happ := congrArg
        (fun e : MulAut ↥R => ((e ⟨r, hrR⟩ : ↥R) : G)) hg
      simpa only [MulAut.one_apply, MulAut.conjNormal_apply] using happ
    have hqv : q v = 1 := by
      change (QuotientGroup.mk' V) v = 1
      exact (QuotientGroup.eq_one_iff v).mpr hvV
    have hq_u : q u = q r := by
      rw [← hru, map_mul, hqv, mul_one]
    change ((MulAut.conjNormal (H := N) (q g)) x : G ⧸ V) = (x : G ⧸ V)
    rw [MulAut.conjNormal_apply, ← hxu]
    calc q g * q u * (q g)⁻¹ = q g * q r * (q g)⁻¹ := by rw [hq_u]
      _ = q (g * r * g⁻¹) := by simp [q, map_mul]
      _ = q r := by rw [hg_fix_r]
      _ = q u := hq_u.symm
  have hQ : IsPGroup p ↥(_root_.commutator (G ⧸ K)) := by
    dsimp [K]
    exact isPGroup_commutator_quotient_conjNormal_ker_of_pRank_le_two
      hodd hp_odd hR_pg hR_rank
  have himg : IsPGroup p ↥((_root_.commutator G).map φ) :=
    isPGroup_commutator_map_of_quotient_commutator_isPGroup
      (K := K) φ hK_le hQ
  change IsPGroup p ↥(((_root_.commutator G).map q).map
    (MulAut.conjNormal (H := N)))
  rw [Subgroup.map_map]
  exact himg

/-- Corollary 4.19 centralizer bridge modulo the lower factor: under the
rank-two normal `p`-subgroup hypothesis, `G'` centralizes every `p`-chief factor
whose top lies in `R ⊔ V`. -/
theorem commutator_le_chiefFactorCentralizer_of_pRank_le_two_of_le_sup
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    {R U V : Subgroup G} [R.Normal] [V.Normal]
    [(U.map (QuotientGroup.mk' V)).Normal]
    (hChief : IsChiefFactor U V)
    (hUbar_pg : IsPGroup p ↥(U.map (QuotientGroup.mk' V)))
    (hR_pg : IsPGroup p ↥R) (hR_rank : pRank ↥R p ≤ 2) (hU_le_RV : U ≤ R ⊔ V) :
    _root_.commutator G ≤ chiefFactorCentralizer U V := by
  have hDbar_pg : IsPGroup p ↥(((_root_.commutator G).map (QuotientGroup.mk' V)).map
      (MulAut.conjNormal (H := U.map (QuotientGroup.mk' V)))) :=
    isPGroup_commutator_chiefFactor_conjNormal_image_of_pRank_le_two_of_le_sup
      hodd hp_odd hR_pg hR_rank hU_le_RV
  exact le_chiefFactorCentralizer_of_isPGroup_conjNormal_image_chiefFactor
    (D := _root_.commutator G) hChief hUbar_pg hDbar_pg

/-- **`p'`-核による商で `p`-rank は増えない**: `N ⊴ G` with `p ∤ |N|` のとき
`r_p(G/N) ≤ r_p(G)`。商の elementary abelian `p`-部分群 `B` は、その逆像の
Sylow `p`-部分群 `P` と同型 (`p`-元は `p'`-核と交わらない) なので `G` 内で実現される。 -/
theorem pRank_quotient_le_of_coprime {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card ↥N) :
    pRank (G ⧸ N) p ≤ pRank G p := by
  classical
  rw [pRank_le_iff]
  intro B hB
  -- the preimage `H` of `B`
  set H : Subgroup G := B.comap (QuotientGroup.mk' N) with hH_def
  have hNH : N ≤ H := by
    intro x hx
    change QuotientGroup.mk' N x ∈ B
    have hx1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact B.one_mem
  -- the restriction of `mk'` to `H` has range `B` and kernel of card `|N|`
  set g : ↥H →* G ⧸ N := (QuotientGroup.mk' N).comp H.subtype with hg_def
  have hg_mem : ∀ x : ↥H, g x ∈ B := fun x => x.2
  have hg_ker_card : Nat.card g.ker = Nat.card ↥N := by
    have hker_eq : g.ker = N.subgroupOf H := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hg_def]
      exact QuotientGroup.eq_one_iff (x : G)
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  -- |H| = |N| * |B|
  have hH_card : Nat.card ↥H = Nat.card ↥N * Nat.card ↥B := by
    have h1 : Nat.card g.ker * g.ker.index = Nat.card ↥H := Subgroup.card_mul_index g.ker
    have h2 : g.ker.index = Nat.card g.range := by
      calc g.ker.index = Nat.card (↥H ⧸ g.ker) := rfl
        _ = Nat.card g.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv
    have h3 : g.range = B := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact hg_mem x
      · intro b hb
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective b
        exact ⟨⟨x, hb⟩, rfl⟩
    rw [← h1, h2, h3, hg_ker_card]
  -- `B` is a `p`-group of order `p ^ m`
  have hB_pg : IsPGroup p ↥B := fun b => ⟨1, by
    rw [pow_one]
    exact hB.pow_eq_one b⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB_pg
  -- a Sylow `p`-subgroup of `H` has order `p ^ m`
  let P : Sylow p ↥H := default
  have hP_card : Nat.card ↥(P : Subgroup ↥H) = p ^ m := by
    rw [P.card_eq_multiplicity, hH_card, hm]
    congr 1
    rw [Nat.factorization_mul Nat.card_pos.ne'
        (pow_pos (Fact.out : p.Prime).pos m).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN,
      Nat.factorization_pow_self (Fact.out : p.Prime)]
    exact Nat.zero_add m
  -- the composite `P → G ⧸ N` is injective into `B`
  set f : ↥(P : Subgroup ↥H) →* G ⧸ N := g.comp (P : Subgroup ↥H).subtype with hf_def
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : ((x : ↥H) : G) ∈ N := (QuotientGroup.eq_one_iff ((x : ↥H) : G)).mp hx
    obtain ⟨k, hk⟩ := P.2 x
    have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf x ∣ Nat.card ↥N := by
      have he1 : orderOf ((x : ↥H) : G) = orderOf x :=
        orderOf_injective (H.subtype.comp (P : Subgroup ↥H).subtype)
          (H.subtype_injective.comp (Subgroup.subtype_injective _)) x
      have he2 : orderOf (N.subtype ⟨((x : ↥H) : G), hxN⟩) =
          orderOf (⟨((x : ↥H) : G), hxN⟩ : ↥N) :=
        orderOf_injective N.subtype N.subtype_injective _
      have he3 : orderOf ((x : ↥H) : G) = orderOf (⟨((x : ↥H) : G), hxN⟩ : ↥N) := he2
      calc orderOf x = orderOf (⟨((x : ↥H) : G), hxN⟩ : ↥N) := by
            rw [← he1]
            exact he3
        _ ∣ Nat.card ↥N := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (p ^ k) (Nat.card ↥N) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN)
    have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.mp h3
  -- realize `B` inside `G`: the image of `P` under the subtype tower
  set E : Subgroup G := ((P : Subgroup ↥H).map H.subtype) with hE_def
  have hE_card : Nat.card ↥E = p ^ m := by
    rw [hE_def, ← hP_card]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv).symm
  -- `E` is elementary abelian: it is isomorphic to a subgroup of `B`
  have hE_elem : E.IsElementaryAbelian p := by
    have hf_mem : ∀ x, f x ∈ B := fun x => hg_mem _
    set f' : ↥(P : Subgroup ↥H) →* ↥B := f.codRestrict B hf_mem with hf'_def
    have hf'_inj : Function.Injective f' := by
      intro x y hxy
      apply hf_inj
      exact congrArg Subtype.val hxy
    have hP_elem : OddOrder.GroupTheory.IsElementaryAbelian p ↥(P : Subgroup ↥H) := by
      have hrange_elem : (f'.range).IsElementaryAbelian p := hB.to_subgroup f'.range
      exact OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (MonoidHom.ofInjective hf'_inj).symm hrange_elem
    rw [hE_def]
    exact Subgroup.IsElementaryAbelian.map H.subtype_injective hP_elem
  -- conclude
  calc Nat.log p (Nat.card ↥B) = Nat.log p (Nat.card ↥E) := by rw [hm, hE_card]
    _ ≤ pRank G p := le_pRank E hE_elem

/-- **Thm 4.18 core** (`O_{p'}(G) = 1` の場合): `G' ≤ O_p(G)`, `p` 以外の素因子は
`p` 以下, `G/O_p(G)` は `p'`-群。

`R = O_p(G)`, `C = C_G(R)`: Hall–Higman 1.2.3 (= **G** Thm 6.3.2) で `C ≤ R`;
Lemma 4.17 で `(G/C)'` は `p`-群; `C` も `p`-群なので `G'` の引き戻しが normal
`p`-部分群となり `O_p(G)` に入る。素因子評価は Lemma 4.13。 -/
private theorem core418 {p : ℕ} [Fact p.Prime] [Group.IsSolvable G]
    (hp : Odd p) (hodd : Odd (Nat.card G)) (hrank : pRank G p ≤ 2)
    (hredu : Ch03.oPiCore {r : ℕ | r ≠ p} G = ⊥) :
    _root_.commutator G ≤ Ch03.oPiCore ({p} : Set ℕ) G ∧
      (∀ q ∈ (Nat.card G).primeFactors, q ≤ p) ∧
      ¬ p ∣ Nat.card (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) := by
  classical
  have hprime : p.Prime := Fact.out
  set R : Subgroup G := Ch03.oPiCore ({p} : Set ℕ) G with hR_def
  have hR_normal : R.Normal := by rw [hR_def]; infer_instance
  -- `R` is a `p`-group of rank ≤ 2
  have hR_pg : IsPGroup p ↥R :=
    isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  have hR_rank : pRank ↥R p ≤ 2 :=
    le_trans (pRank_le_of_injective (f := R.subtype) R.subtype_injective) hrank
  -- Hall–Higman 1.2.3: `C := C_G(R) ≤ R`
  have hCR : Subgroup.centralizer (R : Set G) ≤ R := by
    refine Ch03.hall_higman_1_2_3 ({p} : Set ℕ) ?_
    rw [show {q : ℕ | q ∉ ({p} : Set ℕ)} = {r : ℕ | r ≠ p} from compl_singleton_eq]
    exact hredu
  have hC_pg : IsPGroup p ↥(Subgroup.centralizer (R : Set G)) := hR_pg.to_le hCR
  -- the conjugation action of `G` on `R`, with kernel `C`
  set ψ : G →* MulAut ↥R := MulAut.conjNormal with hψ_def
  have hker : ψ.ker = Subgroup.centralizer (R : Set G) := by
    rw [hψ_def]
    exact conjNormal_ker
  have hker_pg : IsPGroup p ↥ψ.ker := by
    rw [hker]
    exact hC_pg
  -- the quotient `G ⧸ ker ψ` acts faithfully; it is odd
  have hquot_dvd : Nat.card (G ⧸ ψ.ker) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card ψ.ker
    simpa [Subgroup.index] using this
  have hquot_odd : Odd (Nat.card (G ⧸ ψ.ker)) := by
    rcases Nat.even_or_odd (Nat.card (G ⧸ ψ.ker)) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  -- Lemma 4.17: `(G ⧸ C)'` is a `p`-group
  have hA' : IsPGroup p (_root_.commutator (G ⧸ ψ.ker)) :=
    isPGroup_commutator_of_mulAut_odd_of_pRank_le_two hp hR_pg hR_rank
      (QuotientGroup.kerLift_injective ψ) hquot_odd
  -- pull back: `G' ≤ W := comap mk' ((G ⧸ C)')`, a normal `p`-subgroup, hence `≤ R`
  have hG'R : _root_.commutator G ≤ R := by
    have hW_pg : IsPGroup p
        ↥((_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker)) := by
      refine IsPGroup.comap_of_ker_isPGroup hA' _ ?_
      rw [QuotientGroup.ker_mk']
      exact hker_pg
    have hW_norm :
        ((_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker)).Normal :=
      Subgroup.Normal.comap inferInstance _
    have hW_le_R :
        (_root_.commutator (G ⧸ ψ.ker)).comap (QuotientGroup.mk' ψ.ker) ≤ R :=
      Ch03.Subgroup.IsPiGroup.le_oPiCore (isPiGroup_singleton_of_isPGroup hW_pg)
    refine le_trans ?_ hW_le_R
    have hmap : (_root_.commutator G).map (QuotientGroup.mk' ψ.ker) =
        _root_.commutator (G ⧸ ψ.ker) := by
      rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective ψ.ker)]
    rw [← hmap]
    exact Subgroup.le_comap_map _ _
  refine ⟨hG'R, ?_, ?_⟩
  · -- every prime factor `q ≠ p` of `|G|` satisfies `q < p` (Lemma 4.13)
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq_prime, hq_dvd, -⟩ := hq
    rcases eq_or_ne q p with rfl | hq_ne
    · exact le_rfl
    · have hSCN : ∀ B : Subgroup ↥R, ¬ OddOrder.GroupTheory.IsSCN₃ p B := by
        intro B hB
        have h3 : 3 ≤ pRank ↥B p := hB.le_pRank
        have hle : pRank ↥B p ≤ pRank ↥R p :=
          pRank_le_of_injective (f := B.subtype) B.subtype_injective
        omega
      have hq_dvd_quot : q ∣ Nat.card (G ⧸ ψ.ker) := by
        have hmul : Nat.card ↥ψ.ker * Nat.card (G ⧸ ψ.ker) = Nat.card G := by
          have := Subgroup.card_mul_index ψ.ker
          simpa [Subgroup.index] using this
        rcases (Nat.Prime.dvd_mul hq_prime).mp (hmul ▸ hq_dvd) with h | h
        · exfalso
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker_pg
          rw [hk] at h
          exact hq_ne ((Nat.prime_dvd_prime_iff_eq hq_prime hprime).mp
            (hq_prime.dvd_of_dvd_pow h))
        · exact h
      have hq_dvd_aut : q ∣ Nat.card (MulAut ↥R) := by
        have h1 : Nat.card (G ⧸ ψ.ker) = Nat.card (QuotientGroup.kerLift ψ).range :=
          Nat.card_congr (MonoidHom.ofInjective (QuotientGroup.kerLift_injective ψ)).toEquiv
        rw [h1] at hq_dvd_quot
        exact dvd_trans hq_dvd_quot
          (Subgroup.card_subgroup_dvd_card (QuotientGroup.kerLift ψ).range)
      exact le_of_lt (dvd_prime_sq_sub_one_and_lt_of_prime_dvd_aut_of_scn3_empty
        hp hR_pg hSCN hq_prime hq_ne hq_dvd_aut).2
  · -- `G ⧸ R` is a `p'`-group: an order-`p` element of the abelian quotient pulls back
    intro hp_dvd
    have hcomm_quot : ∀ x y : G ⧸ R, x * y = y * x := by
      intro x y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hrw : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [hrw]
      exact hG'R (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
        (Subgroup.mem_top _))
    obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
    have hx_ne : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx_ord
      exact hprime.one_lt.ne' hx_ord.symm
    have hS_pg : IsPGroup p (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hx_ord, pow_one]
    have hS_norm : (Subgroup.zpowers x).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hgn : g * n * g⁻¹ = n := by
        rw [hcomm_quot g n]
        group
      rwa [hgn]
    have hP_pg : IsPGroup p
        ↥((Subgroup.zpowers x).comap (QuotientGroup.mk' R)) := by
      refine IsPGroup.comap_of_ker_isPGroup hS_pg _ ?_
      rw [QuotientGroup.ker_mk']
      exact hR_pg
    have hP_norm :
        ((Subgroup.zpowers x).comap (QuotientGroup.mk' R)).Normal :=
      Subgroup.Normal.comap hS_norm _
    have hP_le : (Subgroup.zpowers x).comap (QuotientGroup.mk' R) ≤ R :=
      Ch03.Subgroup.IsPiGroup.le_oPiCore (isPiGroup_singleton_of_isPGroup hP_pg)
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective R x
    have ha_mem : a ∈ (Subgroup.zpowers x).comap (QuotientGroup.mk' R) := by
      rw [Subgroup.mem_comap, ha]
      exact Subgroup.mem_zpowers x
    have hx_one : x = 1 := by
      rw [← ha]
      exact (QuotientGroup.eq_one_iff a).mpr (hP_le ha_mem)
    exact hx_ne hx_one

omit [Finite G] in
/-- **第三同型 (card 版)**: `|G ⧸ O_{p',p}(G)| = |Ḡ ⧸ O_p(Ḡ)|` (`Ḡ = G/O_{p'}(G)`)。
`hasPLengthOne p G` を `Ḡ`-側の `¬ p ∣ |Ḡ/O_p(Ḡ)|` へ移送する橋 (Thm 4.18 (e) /
Thm 5.6 narrow core で使用)。`O_{p'}(G)` は `oPiPrimePiCore` の内部表現
`{q | q ∉ ({p} : Set ℕ)}` 形で書く。 -/
theorem card_quotient_oPiPrimePiCore {p : ℕ} :
    Nat.card (G ⧸ Ch03.oPiPrimePiCore {p} G) =
      Nat.card ((G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G) ⧸
        Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G)) := by
  classical
  set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
  have hN_norm : N.Normal := by rw [hN_def]; infer_instance
  have hOpp : Ch03.oPiPrimePiCore {p} G =
      (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N)).comap (QuotientGroup.mk' N) := by
    rw [Ch03.oPiPrimePiCore]
  have hOpp_norm : (Ch03.oPiPrimePiCore {p} G).Normal := inferInstance
  have hN_le_Opp : N ≤ Ch03.oPiPrimePiCore {p} G := by
    rw [hOpp]
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact Subgroup.one_mem _
  have hmap_Opp : (Ch03.oPiPrimePiCore {p} G).map (QuotientGroup.mk' N) =
      Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N) := by
    rw [hOpp]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  have : ((Ch03.oPiPrimePiCore {p} G).map (QuotientGroup.mk' N)).Normal := by
    rw [hmap_Opp]
    infer_instance
  have e := QuotientGroup.quotientQuotientEquivQuotient N
    (Ch03.oPiPrimePiCore {p} G) hN_le_Opp
  rw [← Nat.card_congr e.toEquiv, hmap_Opp]

/-- **Thm 4.18 / Thm 5.6 共通 assembly**: `Ḡ = G/O_{p'}(G)` 上の core data
((c)′ `Ḡ' ≤ O_p(Ḡ)`, (a)′ `p` が `|Ḡ|` の最大素因子, (e)′ `Ḡ/O_p(Ḡ)` が `p'`-群) から
結論 5 連 (a)-(e) を組み立てる。Thm 4.18 (`r_p(G) ≤ 2`, core = Lemma 4.17 経由) と
BG §5 Thm 5.6 (`S` narrow, `r(S) ≥ 3` + `p`-length one, core = Thm 5.5 経由;
`S05_NarrowPGroups`) の両分岐がここに合流する。solvability・rank 仮定は不要。 -/
theorem structure_of_quotient_commutator_le_opCore
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime]
    (hG'bar : _root_.commutator (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G) ≤
      Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G))
    (hlargest : ∀ q ∈ (Nat.card
      (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G)).primeFactors, q ≤ p)
    (hp'quot : ¬ p ∣ Nat.card ((G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G) ⧸
      Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G))) :
    (∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p) ∧
    ((p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) →
      Ch05.HasNormalPComplement p G) ∧
    Ch05.HasNormalPComplement p ↥(_root_.commutator G) ∧
    (∀ K : Subgroup ↥(_root_.commutator G), Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(_root_.commutator G)) ∧
    ((∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x) ∧ hasPLengthOne p G) := by
  classical
  have hprime : p.Prime := Fact.out
  -- the `p'`-residual quotient `Ḡ = G ⧸ N` (`oPiPrimePiCore` の内部表現の集合形を使う)
  set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
  have hN_norm : N.Normal := by rw [hN_def]; infer_instance
  have hN_p' : ¬ p ∣ Nat.card ↥N :=
    not_dvd_card_oPiCore (by simp)
  -- the two forms of `O_{p'}(G)` agree
  have hN_eq : Ch03.oPiCore {r : ℕ | r ≠ p} G = N := by
    rw [hN_def, compl_singleton_eq]
  have hquot_dvd_G : Nat.card (G ⧸ N) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card N
    simpa [Subgroup.index] using this
  -- `O_{p',p}(G)` is the preimage of `R̄ = O_p(Ḡ)` (definitional with this `N`)
  have hOpp : Ch03.oPiPrimePiCore {p} G =
      (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N)).comap (QuotientGroup.mk' N) := by
    rw [Ch03.oPiPrimePiCore]
  have hOpp_norm : (Ch03.oPiPrimePiCore {p} G).Normal := inferInstance
  -- `G' ≤ O_{p',p}(G)`
  have hmap_comm : (_root_.commutator G).map (QuotientGroup.mk' N) =
      _root_.commutator (G ⧸ N) := by
    rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hG'_le : _root_.commutator G ≤ Ch03.oPiPrimePiCore {p} G := by
    rw [hOpp]
    intro x hx
    rw [Subgroup.mem_comap]
    have hmem : (QuotientGroup.mk' N) x ∈
        (_root_.commutator G).map (QuotientGroup.mk' N) := ⟨x, hx, rfl⟩
    rw [hmap_comm] at hmem
    exact hG'bar hmem
  -- (e)
  have he_comm : ∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hrw : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hrw]
    exact hG'_le (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _))
  have he_pl : hasPLengthOne p G := by
    rw [hasPLengthOne, card_quotient_oPiPrimePiCore (G := G) (p := p)]
    exact hp'quot
  -- (a)
  have ha : ∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p := by
    have hcards : Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G) = Nat.card (G ⧸ N) := by
      rw [hN_eq]
    rw [hcards]
    exact hlargest
  -- (c): the normal `p`-complement `N'' = N ∩ G'` of `G'`
  set N'' : Subgroup ↥(_root_.commutator G) :=
    N.subgroupOf (_root_.commutator G) with hN''_def
  have hN''_norm : N''.Normal := by
    rw [hN''_def]
    exact hN_norm.subgroupOf _
  have hN''_card_dvd : Nat.card ↥N'' ∣ Nat.card ↥N := by
    have h1 : Nat.card ↥N'' = Nat.card ↥(N ⊓ _root_.commutator G) := by
      rw [hN''_def]
      have h2 := Subgroup.subgroupOf_map_subtype N (_root_.commutator G)
      calc Nat.card ↥(N.subgroupOf (_root_.commutator G))
          = Nat.card ↥((N.subgroupOf (_root_.commutator G)).map
              (_root_.commutator G).subtype) :=
            Nat.card_congr (Subgroup.equivMapOfInjective _ _
              (_root_.commutator G).subtype_injective).toEquiv
        _ = Nat.card ↥(N ⊓ _root_.commutator G) := by rw [h2]
    rw [h1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hN''_p' : ¬ p ∣ Nat.card ↥N'' := fun h => hN_p' (dvd_trans h hN''_card_dvd)
  -- the index of `N''` in `G'` is a power of `p`
  set g'' : ↥(_root_.commutator G) →* (G ⧸ N) :=
    (QuotientGroup.mk' N).comp (_root_.commutator G).subtype with hg''_def
  have hker'' : g''.ker = N'' := by
    ext x
    rw [MonoidHom.mem_ker, hN''_def, Subgroup.mem_subgroupOf, hg''_def]
    exact QuotientGroup.eq_one_iff (x : G)
  have hrange_pg : IsPGroup p ↥g''.range := by
    have hrange_le : g''.range ≤ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N) := by
      rintro _ ⟨x, rfl⟩
      refine hG'bar ?_
      have hmem : (g'' x : G ⧸ N) ∈ (_root_.commutator G).map (QuotientGroup.mk' N) :=
        ⟨(x : G), x.2, rfl⟩
      rwa [hmap_comm] at hmem
    exact (isPGroup_of_isPiGroup_singleton
      (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))).to_le hrange_le
  have hidx_eq : N''.index = Nat.card g''.range := by
    rw [← hker'']
    calc g''.ker.index = Nat.card (↥(_root_.commutator G) ⧸ g''.ker) := rfl
      _ = Nat.card g''.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange g'').toEquiv
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hrange_pg
  have hj_idx : N''.index = p ^ j := by rw [hidx_eq, hj]
  have hc : Ch05.HasNormalPComplement p ↥(_root_.commutator G) := by
    refine ⟨N'', hN''_norm, ?_⟩
    intro P
    have hP_card : Nat.card ↥(P : Subgroup ↥(_root_.commutator G)) = p ^ j := by
      rw [P.card_eq_multiplicity]
      congr 1
      have h1 : Nat.card ↥N'' * N''.index = Nat.card ↥(_root_.commutator G) :=
        Subgroup.card_mul_index N''
      rw [← h1, hj_idx,
        Nat.factorization_mul Nat.card_pos.ne' (pow_pos hprime.pos j).ne',
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hN''_p',
        Nat.factorization_pow_self hprime]
      exact Nat.zero_add j
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hP_card, ← hj_idx]
      exact Subgroup.card_mul_index N''
    · rw [hP_card]
      exact Nat.Coprime.pow_right j
        ((hprime.coprime_iff_not_dvd.mpr hN''_p').symm)
  -- (d): a `p'`-subgroup of `G'` lies in `N'' ≤ O_{p'}(G')`
  have hd : ∀ K : Subgroup ↥(_root_.commutator G),
      Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(_root_.commutator G) := by
    intro K hK
    have hK_p' : ¬ p ∣ Nat.card ↥K := by
      intro h
      exact (hK p (Nat.mem_primeFactors.mpr ⟨hprime, h, Nat.card_pos.ne'⟩)) rfl
    have hK_le_N'' : K ≤ N'' := by
      intro k hk
      rw [← hker'', MonoidHom.mem_ker]
      have h1 : orderOf (g'' k) ∣ Nat.card ↥K := by
        have h2 : orderOf (g'' k) ∣ orderOf k := orderOf_map_dvd g'' k
        have h3 : orderOf k ∣ Nat.card ↥K := by
          have h4 : orderOf (K.subtype ⟨k, hk⟩) = orderOf (⟨k, hk⟩ : ↥K) :=
            orderOf_injective K.subtype K.subtype_injective _
          have h4' : orderOf k = orderOf (⟨k, hk⟩ : ↥K) := h4
          rw [h4']
          exact orderOf_dvd_natCard _
        exact dvd_trans h2 h3
      have h5 : orderOf (g'' k) ∣ p ^ j := by
        have h6 : g'' k ∈ g''.range := ⟨k, rfl⟩
        have h7 : orderOf (g''.range.subtype ⟨g'' k, h6⟩) =
            orderOf (⟨g'' k, h6⟩ : ↥g''.range) :=
          orderOf_injective g''.range.subtype g''.range.subtype_injective _
        have h7' : orderOf (g'' k) = orderOf (⟨g'' k, h6⟩ : ↥g''.range) := h7
        rw [h7', ← hj]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (Nat.card ↥K) (p ^ j) :=
        Nat.Coprime.pow_right j ((hprime.coprime_iff_not_dvd.mpr hK_p').symm)
      have h8 : orderOf (g'' k) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop h1 h5
      exact orderOf_eq_one_iff.mp h8
    refine le_trans hK_le_N'' ?_
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    intro hq_eq
    rw [hq_eq] at hq
    exact hN''_p' hq.2.1
  -- (b): when `p` is forced to be the only prime of `Ḡ`, the core `N` is a complement
  have hb : (p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) →
      Ch05.HasNormalPComplement p G := by
    intro hcase
    have hall_p : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card (G ⧸ N) → q = p := by
      intro q hq hq_dvd
      have h1 : q ≤ p := hlargest q
        (Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, Nat.card_pos.ne'⟩)
      have hq_dvd_G : q ∣ Nat.card G := dvd_trans hq_dvd hquot_dvd_G
      have h2 : q ≠ 2 := by
        intro h2
        rw [h2] at hq_dvd_G
        rw [Nat.odd_iff] at hodd
        omega
      rcases hcase with rfl | hmin
      · have := hq.two_le
        omega
      · have h3 := hmin q (Nat.mem_primeFactors.mpr ⟨hq, hq_dvd_G, Nat.card_pos.ne'⟩)
        omega
    have hk := Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_pos (α := G ⧸ N)).ne' hall_p
    refine ⟨N, hN_norm, ?_⟩
    intro P
    have hP_card : Nat.card ↥(P : Subgroup G) =
        p ^ (Nat.card (G ⧸ N)).primeFactorsList.length := by
      rw [P.card_eq_multiplicity]
      congr 1
      have h1 : Nat.card ↥N * Nat.card (G ⧸ N) = Nat.card G := by
        have := Subgroup.card_mul_index N
        simpa [Subgroup.index] using this
      have hfact : (Nat.card (G ⧸ N)).factorization p =
          (Nat.card (G ⧸ N)).primeFactorsList.length := by
        conv_lhs => rw [hk]
        exact Nat.factorization_pow_self hprime
      rw [← h1, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN_p', hfact]
      exact Nat.zero_add _
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hP_card, ← hk]
      have := Subgroup.card_mul_index N
      simpa [Subgroup.index] using this
    · rw [hP_card]
      exact Nat.Coprime.pow_right _
        ((hprime.coprime_iff_not_dvd.mpr hN_p').symm)
  exact ⟨ha, hb, hc, hd, he_comm, he_pl⟩

/-- **BG Theorem 4.18** (mmd L1734-1752): `G` solvable odd, `p ∣ |G|`, `r_p(G) ≤ 2`。
すると:

* (a) `p` は `|G/O_{p'}(G)|` の最大素因子;
* (b) `p = 3` または `p` が `|G|` の最小素因子なら、`G` は normal `p`-complement を持つ;
* (c) `G'` は normal `p`-complement を持つ;
* (d) `G'` の任意の `p'`-subgroup は `O_{p'}(G')` に含まれる;
* (e) `G/O_{p',p}(G)` は abelian `p'`-群。

結論の語彙は §5 Thm 5.6 (`narrow_sylow_solvable_structure`) と一致させている。
証明 = `core418` (`O_{p'} = 1` の場合; Hall–Higman + Lemma 4.17 + Lemma 4.13) を
商 `Ḡ = G/O_{p'}(G)` に適用し、`structure_of_quotient_commutator_le_opCore` で引き戻す。 -/
theorem solvable_structure_of_pRank_le_two [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (hrank : pRank G p ≤ 2) :
    (∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p) ∧
    ((p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) →
      Ch05.HasNormalPComplement p G) ∧
    Ch05.HasNormalPComplement p ↥(_root_.commutator G) ∧
    (∀ K : Subgroup ↥(_root_.commutator G), Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(_root_.commutator G)) ∧
    ((∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x) ∧ hasPLengthOne p G) := by
  classical
  have hp_odd : Odd p := by
    rcases Nat.even_or_odd p with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hp_mem
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  -- the `p'`-residual quotient `Ḡ = G ⧸ N`
  set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
  have hN_norm : N.Normal := by rw [hN_def]; infer_instance
  have hN_p' : ¬ p ∣ Nat.card ↥N :=
    not_dvd_card_oPiCore (by simp)
  have hquot_dvd_G : Nat.card (G ⧸ N) ∣ Nat.card G := by
    have := Subgroup.index_dvd_card N
    simpa [Subgroup.index] using this
  have hodd_bar : Odd (Nat.card (G ⧸ N)) := by
    rcases Nat.even_or_odd (Nat.card (G ⧸ N)) with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hquot_dvd_G
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  have hrank_bar : pRank (G ⧸ N) p ≤ 2 :=
    le_trans (pRank_quotient_le_of_coprime hN_p') hrank
  have hredu_bar : Ch03.oPiCore {r : ℕ | r ≠ p} (G ⧸ N) = ⊥ := by
    rw [show {r : ℕ | r ≠ p} = {q : ℕ | q ∉ ({p} : Set ℕ)} from compl_singleton_eq.symm]
    exact Ch03.oPiCore_quotient_self_eq_bot _
  obtain ⟨hG'bar, hlargest, hp'quot⟩ := core418 hp_odd hodd_bar hrank_bar hredu_bar
  exact structure_of_quotient_commutator_le_opCore hodd hG'bar hlargest hp'quot

/-- If `K` is normal in `G`, then `F(K)` has rank at most `F(G)`.

This is the rank form of the BG Theorem 4.20(c) induction line `F(K) <= F(G)`. -/
theorem rank_fitting_le_of_normal_subgroup {K : Subgroup G} [K.Normal] :
    OddOrder.GroupTheory.rank ↥(Ch01.fitting ↥K) ≤
      OddOrder.GroupTheory.rank ↥(Ch01.fitting G) := by
  classical
  let f : ↥(Ch01.fitting ↥K) →* ↥(Ch01.fitting G) :=
    { toFun := fun x =>
        ⟨(x.1 : G),
          Ch01.fitting_map_subtype_le_fitting (M := K) ⟨x.1, x.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        rfl
      map_mul' := by
        intro _ _
        apply Subtype.ext
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Ch01.fitting G) => (z : G)) hxy
  exact OddOrder.GroupTheory.rank_le_of_injective (G := ↥(Ch01.fitting G)) hf

/-- If `K` is normal in `G` and `F(G)` has rank at most two, then so does `F(K)`. -/
theorem rank_fitting_le_two_of_normal_subgroup {K : Subgroup G} [K.Normal]
    (hrF : OddOrder.GroupTheory.rank ↥(Ch01.fitting G) ≤ 2) :
    OddOrder.GroupTheory.rank ↥(Ch01.fitting ↥K) ≤ 2 :=
  (rank_fitting_le_of_normal_subgroup (G := G) (K := K)).trans hrF

/-- If a Sylow `p`-subgroup lies in `F(G)`, then its `p`-rank is bounded by the
rank of `F(G)`. -/
theorem pRank_sylow_le_two_of_le_fitting {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hPfit : (P : Subgroup G) ≤ Ch01.fitting G)
    (hrF : OddOrder.GroupTheory.rank ↥(Ch01.fitting G) ≤ 2) :
    pRank ↥(P : Subgroup G) p ≤ 2 := by
  have hP_le_F : pRank ↥(P : Subgroup G) p ≤ pRank ↥(Ch01.fitting G) p :=
    OddOrder.GroupTheory.pRank_le_of_injective
      (G := ↥(Ch01.fitting G)) (H := ↥(P : Subgroup G))
      (f := Subgroup.inclusion hPfit) (Subgroup.inclusion_injective hPfit)
  exact hP_le_F.trans ((OddOrder.GroupTheory.rank_le_iff.mp hrF) p (Fact.out : p.Prime))

/-- If some Sylow `p`-subgroup lies in `F(G)` and `F(G)` has rank at most two, then
`r_p(G) ≤ 2`. -/
theorem pRank_le_two_of_sylow_le_fitting {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hPfit : (P : Subgroup G) ≤ Ch01.fitting G)
    (hrF : OddOrder.GroupTheory.rank ↥(Ch01.fitting G) ≤ 2) :
    pRank G p ≤ 2 :=
  (OddOrder.GroupTheory.pRank_le_pRank_sylow P).trans
    (pRank_sylow_le_two_of_le_fitting P hPfit hrF)

end Thm418

end OddOrder.BG.Ch1.S04


