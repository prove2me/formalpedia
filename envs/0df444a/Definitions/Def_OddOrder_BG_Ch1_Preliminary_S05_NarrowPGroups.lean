-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowPGroups
-- name    : OddOrder_BG_Ch1_Preliminary_S05_NarrowPGroups
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:29:08.1512+00:00
-- url     : https://prove2.me/theorems/30f2bb98-5e3b-40cb-b0ce-55c510191b9a
-- title:
--   BG §5: Narrow $p$-groups
-- statement:
--   Formalizes Chapter I §5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* on narrow $p$-groups (rank at least 3, 'nearly as well behaved as rank at most 2'): Lemmas 5.1, 5.2, Theorems 5.3, 5.5, 5.6, 5.7 and Corollary 5.4. The core is Theorem 5.3 (for $r(R)\ge 3$, $R$ is narrow iff $\mathcal{E}^2(R)\cap\mathcal{E}^*(R)\ne\emptyset$) and Theorem 5.5 (structure of a solvable odd automorphism group of a narrow $R$).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S05_NarrowPGroups.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowAutomorphisms

namespace OddOrder.BG.Ch1.S05

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped IsMulCommutative commutatorElement

variable {R : Type*} [Group R]

section Thm56

variable {G : Type*} [Group G] [Finite G]

/-- **Thm 5.6 narrow core** (`O_{p'}(G) = 1`, `r(S) ≥ 3` の場合): `G' ≤ O_p(G)` と
最大素因子評価。`p`-length one から `p ∤ |G/O_p(G)|` なので `R = O_p(G)` が唯一の
Sylow `p`-部分群、ゆえに `S = R` で `R` は narrow of rank ≥ 3。Hall–Higman 1.2.3 で
`C := C_G(R) ≤ R`; **Thm 5.5(a)** で `(G/C)/O_p(G/C)` が abelian、すなわち `(G/C)'` が
`p`-群 (Thm 4.18 core での Lemma 4.17 の代替) → `G' ≤ O_p(G)`; **Thm 5.5(b)** で
`q ≠ p` 素因子は `q ∣ p - 1 < p` (Lemma 4.13 の代替)。組み立ては `core418` と同型。 -/
private theorem core56 {p : ℕ} [Fact p.Prime] [Group.IsSolvable G]
    (hp : Odd p) (hodd : Odd (Nat.card G)) (S : Sylow p G)
    (hSnarrow : IsNarrow p ↥S) (h3 : 3 ≤ pRank ↥(S : Subgroup G) p)
    (hredu : Ch03.oPiCore {r : ℕ | r ≠ p} G = ⊥)
    (hpOp : ¬ p ∣ Nat.card (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) :
    _root_.commutator G ≤ Ch03.oPiCore ({p} : Set ℕ) G ∧
      ∀ q ∈ (Nat.card G).primeFactors, q ≤ p := by
  classical
  have hprime : p.Prime := Fact.out
  set R : Subgroup G := Ch03.oPiCore ({p} : Set ℕ) G with hR_def
  have hR_normal : R.Normal := by rw [hR_def]; infer_instance
  have hR_pg : IsPGroup p ↥R :=
    S04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  -- `R` is a normal Sylow `p`-subgroup (`p ∤ |G/R|`), hence the unique one: `S = R`
  have hR_idx : ¬ p ∣ R.index := by
    simpa [Subgroup.index] using hpOp
  have hSR : (S : Subgroup G) = R := by
    have hnorm : ((hR_pg.toSylow hR_idx) : Subgroup G).Normal := by
      rw [hR_pg.toSylow_coe hR_idx]
      exact hR_normal
    have := Sylow.unique_of_normal (hR_pg.toSylow hR_idx) hnorm
    have h1 : S = hR_pg.toSylow hR_idx := Subsingleton.elim _ _
    rw [h1]
    exact hR_pg.toSylow_coe hR_idx
  -- transport narrowness and rank from `S` to `R`
  have eSR : ↥(S : Subgroup G) ≃* ↥R := MulEquiv.subgroupCongr hSR
  have hR_narrow : IsNarrow p ↥R := IsNarrow.of_mulEquiv eSR hSnarrow
  have hR_rank3 : 3 ≤ pRank ↥R p :=
    le_trans h3 (pRank_le_of_injective (f := eSR.toMonoidHom) eSR.injective)
  -- Hall–Higman 1.2.3: `C := C_G(R) ≤ R`
  have hCR : Subgroup.centralizer (R : Set G) ≤ R := by
    refine Ch03.hall_higman_1_2_3 ({p} : Set ℕ) ?_
    rw [show {q : ℕ | q ∉ ({p} : Set ℕ)} = {r : ℕ | r ≠ p} from S04.compl_singleton_eq]
    exact hredu
  have hC_pg : IsPGroup p ↥(Subgroup.centralizer (R : Set G)) := hR_pg.to_le hCR
  -- the conjugation action of `G` on `R`, with kernel `C`
  set ψ : G →* MulAut ↥R := MulAut.conjNormal with hψ_def
  have hker : ψ.ker = Subgroup.centralizer (R : Set G) := by
    rw [hψ_def]
    exact S04.conjNormal_ker
  have hker_pg : IsPGroup p ↥ψ.ker := by
    rw [hker]
    exact hC_pg
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
  -- Theorem 5.5 for `A := G ⧸ C` acting faithfully on the narrow `R` of rank ≥ 3
  obtain ⟨hcomm, -, hb, -⟩ := solvableAut_of_narrow hp hR_pg hR_narrow
    (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ) hquot_odd
  -- 5.5(a): `(G ⧸ C)'` is a `p`-group (the Lemma 4.17 substitute)
  have hA' : IsPGroup p (_root_.commutator (G ⧸ ψ.ker)) := by
    have hle : _root_.commutator (G ⧸ ψ.ker) ≤ Ch01.opCore p (G ⧸ ψ.ker) := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro x _ y _
      have h1 : QuotientGroup.mk' (Ch01.opCore p (G ⧸ ψ.ker)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm _ _
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact (Ch01.opCore_isPGroup p _).to_le hle
  -- pull back: `G' ≤ R` (identical to the Thm 4.18 core assembly)
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
      Ch03.Subgroup.IsPiGroup.le_oPiCore (S04.isPiGroup_singleton_of_isPGroup hW_pg)
    refine le_trans ?_ hW_le_R
    have hmap : (_root_.commutator G).map (QuotientGroup.mk' ψ.ker) =
        _root_.commutator (G ⧸ ψ.ker) := by
      rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective ψ.ker)]
    rw [← hmap]
    exact Subgroup.le_comap_map _ _
  refine ⟨hG'R, ?_⟩
  -- 5.5(b): a prime `q ≠ p` dividing `|G|` divides `p - 1` (the Lemma 4.13 substitute)
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hq_prime, hq_dvd, -⟩ := hq
  rcases eq_or_ne q p with rfl | hq_ne
  · exact le_rfl
  · have hq_dvd_quot : q ∣ Nat.card (G ⧸ ψ.ker) := by
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
    have : Fact q.Prime := ⟨hq_prime⟩
    obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' q hq_dvd_quot
    have hα_cop : Nat.Coprime (orderOf α) p := by
      rw [hα]
      exact (Nat.coprime_primes hq_prime hprime).mpr hq_ne
    have hα_dvd := hb hR_rank3 α hα_cop
    rw [hα] at hα_dvd
    have hp3 : 3 ≤ p := by
      have h2 := hprime.two_le
      rcases hp with ⟨k, hk⟩
      omega
    have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hα_dvd
    omega

end Thm56

/-- **BG Theorem 5.6**: `G` solvable odd, `p ∈ π(G)`, `S` を narrow Sylow `p`-subgroup と
する。`r(S) ≥ 3` なら、さらに `G` が `p`-length one (`hasPLengthOne`) と仮定する。すると:

* (a) `p` は `|G/O_{p'}(G)|` の最大素因子;
* (b) `p = 3` または `p` が `|G|` の最小素因子なら、`G` は normal `p`-complement を持つ;
* (c) `G'` は normal `p`-complement を持つ;
* (d) `G'` の任意の `p'`-subgroup は `O_{p'}(G')` に含まれる;
* (e) `G/O_{p',p}(G)` は abelian `p'`-群 (`p'` 部は `hasPLengthOne p G`)。

mmd L1945-1953。`r(S)≤2` で Thm 4.18, `r(S)≥3` で Thm 5.5 + Thm 4.18 の方法。 -/
theorem narrow_sylow_solvable_structure {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime] (hp_mem : p ∣ Nat.card G)
    (S : Sylow p G) (hSnarrow : IsNarrow p ↥S)
    (hpl : 3 ≤ pRank ↥S p → hasPLengthOne p G) :
    (∀ q ∈ (Nat.card (G ⧸ Ch03.oPiCore {r | r ≠ p} G)).primeFactors, q ≤ p) ∧
    ((p = 3 ∨ ∀ q ∈ (Nat.card G).primeFactors, p ≤ q) → Ch05.HasNormalPComplement p G) ∧
    Ch05.HasNormalPComplement p ↥(commutator G) ∧
    (∀ K : Subgroup ↥(commutator G), Subgroup.IsPiSubgroup {r | r ≠ p} K →
      K ≤ Ch03.oPiCore {r | r ≠ p} ↥(commutator G)) ∧
    ((∀ x y : G ⧸ Ch03.oPiPrimePiCore {p} G, x * y = y * x) ∧ hasPLengthOne p G) := by
  classical
  by_cases hrank : pRank ↥(S : Subgroup G) p ≤ 2
  · -- `r(S) ≤ 2`: the Sylow-rank bridge gives `r_p(G) ≤ 2`; conclude by Theorem 4.18
    exact S04.solvable_structure_of_pRank_le_two hodd hp_mem
      (le_trans (pRank_le_pRank_sylow S) hrank)
  · -- `r(S) ≥ 3`: `p`-length one holds; run the Thm 5.5 narrow core on `Ḡ = G/O_{p'}(G)`
    have h3 : 3 ≤ pRank ↥(S : Subgroup G) p := by omega
    have hpl' : hasPLengthOne p G := hpl h3
    have hp_odd : Odd p := by
      rcases Nat.even_or_odd p with he | ho
      · exfalso
        have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hp_mem
        rw [Nat.odd_iff] at hodd
        omega
      · exact ho
    set N : Subgroup G := Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G with hN_def
    have hN_norm : N.Normal := by rw [hN_def]; infer_instance
    have hN_p' : ¬ p ∣ Nat.card ↥N := S04.not_dvd_card_oPiCore (by simp)
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
    -- the image Sylow `S̄ = SN/N` of `Ḡ`, isomorphic to `S` (`p ∤ |N|`)
    set Sbar : Sylow p (G ⧸ N) := S.mapSurjective (QuotientGroup.mk'_surjective N)
      with hSbar_def
    have hinj : Function.Injective
        ((QuotientGroup.mk' N).subgroupMap (S : Subgroup G)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxN : (x : G) ∈ N := by
        have h1 : QuotientGroup.mk' N (x : G) = 1 := congrArg Subtype.val hx
        exact (QuotientGroup.eq_one_iff _).mp h1
      obtain ⟨k, hk⟩ := S.2 x
      have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf x ∣ Nat.card ↥N := by
        have he1 : orderOf ((S : Subgroup G).subtype x) = orderOf x :=
          orderOf_injective (S : Subgroup G).subtype
            (Subgroup.subtype_injective _) x
        have he2 : orderOf (N.subtype ⟨(x : G), hxN⟩) =
            orderOf (⟨(x : G), hxN⟩ : ↥N) :=
          orderOf_injective N.subtype N.subtype_injective _
        have he3 : orderOf ((x : G)) = orderOf (⟨(x : G), hxN⟩ : ↥N) := he2
        calc orderOf x = orderOf (⟨(x : G), hxN⟩ : ↥N) := by
              rw [← he1]
              exact he3
          _ ∣ Nat.card ↥N := orderOf_dvd_natCard _
      have hcop : Nat.Coprime (p ^ k) (Nat.card ↥N) :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN_p')
      have h3' : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
      exact orderOf_eq_one_iff.mp h3'
    have hSbar_coe : (Sbar : Subgroup (G ⧸ N)) =
        (S : Subgroup G).map (QuotientGroup.mk' N) := rfl
    have e : ↥(S : Subgroup G) ≃* ↥(Sbar : Subgroup (G ⧸ N)) :=
      (MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap (S : Subgroup G))
        ⟨hinj, (QuotientGroup.mk' N).subgroupMap_surjective (S : Subgroup G)⟩).trans
        (MulEquiv.subgroupCongr hSbar_coe.symm)
    have hSbar_narrow : IsNarrow p ↥(Sbar : Subgroup (G ⧸ N)) :=
      IsNarrow.of_mulEquiv e hSnarrow
    have h3bar : 3 ≤ pRank ↥(Sbar : Subgroup (G ⧸ N)) p :=
      le_trans h3 (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    have hredu_bar : Ch03.oPiCore {r : ℕ | r ≠ p} (G ⧸ N) = ⊥ := by
      rw [show {r : ℕ | r ≠ p} = {q : ℕ | q ∉ ({p} : Set ℕ)} from
        S04.compl_singleton_eq.symm]
      exact Ch03.oPiCore_quotient_self_eq_bot _
    -- `p`-length one transports to `p ∤ |Ḡ/O_p(Ḡ)|` by the third isomorphism theorem
    have hpOp_bar : ¬ p ∣ Nat.card ((G ⧸ N) ⧸ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ N)) := by
      rw [hasPLengthOne, S04.card_quotient_oPiPrimePiCore (G := G) (p := p)] at hpl'
      exact hpl'
    obtain ⟨hG'bar, hlargest⟩ :=
      core56 hp_odd hodd_bar Sbar hSbar_narrow h3bar hredu_bar hpOp_bar
    exact S04.structure_of_quotient_commutator_le_opCore hodd hG'bar hlargest hpOp_bar

section Thm57

variable {G : Type*} [Group G] [Finite G]

/-- Prop 1.2 (`G* = G`) 用 glue: `F(⊤)` の subtype 像は `F(G)`。
`≤` は Isaacs Cor 1.28(b) (`fitting_map_subtype_le_fitting`)、`≥` は `F(G)` が
`↥⊤` 内で冪零正規 (`subgroupOf` 経由) であることから。 -/
private theorem fitting_top_map_subtype_eq :
    (Ch01.fitting ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = Ch01.fitting G := by
  apply le_antisymm
  · exact Ch01.fitting_map_subtype_le_fitting
  · have h1 : ((Ch01.fitting G).subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype =
        Ch01.fitting G := Subgroup.map_subgroupOf_eq_of_le le_top
    rw [← h1]
    apply Subgroup.map_mono
    have : ((Ch01.fitting G).subgroupOf (⊤ : Subgroup G)).Normal :=
      (Ch01.fitting.normal G).subgroupOf _
    have : Group.IsNilpotent ↥((Ch01.fitting G).subgroupOf (⊤ : Subgroup G)) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_top).symm
    exact Ch01.nilpotent_normal_le_fitting

/-- **`F(G)` 内の `q`-部分群は `O_q(G)` に入る**: `F(G)` は冪零なのでその Sylow `q` は
正規 (`Sylow.normal_of_isNilpotent`) かつ特性的、その `G`-像は正規 `q`-部分群で
Problem 1B.2 (`normal_pgroup_le_opCore`) から `O_q(G)` に入る。

Thm 5.7 で 2 回使う: `E ≤ O_p(G)` と「`U` の Sylow `q` ≤ `O_q(G)`」。 -/
private theorem le_opCore_of_isPGroup_of_le_fitting {q : ℕ} [Fact q.Prime]
    {W : Subgroup G} (hW : IsPGroup q ↥W) (hWF : W ≤ Ch01.fitting G) :
    W ≤ Ch01.opCore q G := by
  classical
  have hW'_pg : IsPGroup q ↥(W.subgroupOf (Ch01.fitting G)) :=
    hW.of_injective (Subgroup.subgroupOfEquivOfLe hWF).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWF).injective
  obtain ⟨P, hWP⟩ := hW'_pg.exists_le_sylow
  have hPnorm : P.Normal := Ch01.Sylow.normal_of_isNilpotent P
  have : (P : Subgroup ↥(Ch01.fitting G)).Characteristic :=
    Sylow.characteristic_of_normal P hPnorm
  have : ((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype).Normal :=
    inferInstance
  have hPmap_pg :
      IsPGroup q ↥((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype) :=
    P.2.map _
  calc W = (W.subgroupOf (Ch01.fitting G)).map (Ch01.fitting G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWF).symm
    _ ≤ (P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype :=
        Subgroup.map_mono hWP
    _ ≤ Ch01.opCore q G := Ch01.normal_pgroup_le_opCore hPmap_pg

/-- **BG Theorem 5.7**: `G` solvable odd, `p ∈ π(G)`, `E` を `F(G)` の elem-ab `p`-subgroup と
し、`r(C_{F(G)}(E)) ≤ 2` を仮定 (`r` = 全素数にわたる rank; BG §4 p.33)。すると
`G' ⊆ F(G)`。

mmd L1955-1967。Prop 1.2 (chief factor 還元, `S01`) + 各 chief factor `U/V ⊆ F(G)` で:
`U/V` は `q`-chief factor、`R = O_q(G)` が narrow (`r(R) ≥ 3` なら `q = p` が強制され
`EZ ∈ ℰ²(R) ∩ ℰ*(R)` を構成して Thm 5.3) ⇒ Thm 5.5(a) で `G'` が `U/V` に `q`-群の
自己同型を誘導 ⇒ 固定点論法 (Isaacs Lem 4.32) + `U/V` の `G`-既約性で `G' ⊆ C_G(U/V)`。 -/
theorem derived_le_fitting_of_centralizer_rank_le_two
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {p : ℕ} [Fact p.Prime]
    (E : Subgroup G) (hE : E.IsElementaryAbelian p) (hEF : E ≤ Ch01.fitting G)
    (hrank : OddOrder.GroupTheory.rank
      ↥(Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G) ≤ 2) :
    commutator G ≤ Ch01.fitting G := by
  classical
  -- Prop 1.2 (G* = G): it suffices that `G'` centralizes every chief factor inside `F(G)`
  rw [← fitting_top_map_subtype_eq]
  refine S01.chiefFactorCentralizer_subset_le_fitting_of_isSolvable le_top ?_
  intro U V hVn hChief hU_le
  have := hVn
  rw [fitting_top_map_subtype_eq] at hU_le
  -- ## Setup: `Ū ≤ Ĝ = G/V` is a minimal normal elementary abelian `q`-group
  set Ubar : Subgroup (G ⧸ V) := U.map (QuotientGroup.mk' V) with hUbar_def
  have hMin : Ch02.IsMinimalNormal Ubar :=
    S01.isMinimalNormal_map_quotient_of_isChiefFactor hChief
  obtain ⟨-, -, q, hq_prime, hUbar_elem⟩ :=
    S01.isMinimalNormal_le_fitting_and_isElementaryAbelian hMin
  have : Fact q.Prime := ⟨hq_prime⟩
  have hUbar_norm : Ubar.Normal := hMin.1
  have hUbar_ne : Ubar ≠ ⊥ := hMin.2.1
  have hUbar_pg : IsPGroup q ↥Ubar := hUbar_elem.isPGroup
  -- `q` is odd (it divides `|G|`)
  have hq_dvd_G : q ∣ Nat.card G := by
    have h1 : q ∣ Nat.card ↥Ubar := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUbar_pg
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exact absurd (Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])) hUbar_ne
      · rw [hk]
        exact dvd_pow_self q hkpos.ne'
    have h2 : Nat.card ↥Ubar ∣ Nat.card (G ⧸ V) := Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card (G ⧸ V) ∣ Nat.card G := by
      have := Subgroup.index_dvd_card V
      simpa [Subgroup.index] using this
    exact h1.trans (h2.trans h3)
  have hq_odd : Odd q := by
    rcases Nat.even_or_odd q with he | ho
    · exfalso
      have h2 : (2 : ℕ) ∣ Nat.card G := dvd_trans he.two_dvd hq_dvd_G
      rw [Nat.odd_iff] at hodd
      omega
    · exact ho
  -- `R := O_q(G)`
  set R : Subgroup G := Ch01.opCore q G with hR_def
  have hR_norm : R.Normal := Ch01.opCore.normal q G
  have hR_pg : IsPGroup q ↥R := Ch01.opCore_isPGroup q G
  have hR_le_F : R ≤ Ch01.fitting G := Ch01.opCore_le_fitting ⟨q, hq_prime⟩ G
  -- ## `Ū` is covered by `U ⊓ R` (BG "we may assume `U ⊆ O_q(G)`"): a Sylow `q`-subgroup
  -- of `U` surjects onto the `q`-group `Ū`, and it lies in `O_q(G)` since `U ≤ F(G)`
  have hUbar_sub : ∀ z : G ⧸ V, z ∈ Ubar →
      ∃ w, w ∈ U ⊓ R ∧ QuotientGroup.mk' V w = z := by
    intro z hz
    have hf_surj : Function.Surjective ((QuotientGroup.mk' V).subgroupMap U) :=
      (QuotientGroup.mk' V).subgroupMap_surjective U
    obtain ⟨Q⟩ : Nonempty (Sylow q ↥U) := Sylow.nonempty
    have htop_pg : IsPGroup q ↥(⊤ : Subgroup ↥(U.map (QuotientGroup.mk' V))) := by
      refine hUbar_pg.of_injective Subgroup.topEquiv.toMonoidHom ?_
      exact Subgroup.topEquiv.injective
    have hQbar_top : ((Q.mapSurjective hf_surj :
        Sylow q ↥(U.map (QuotientGroup.mk' V))) :
          Subgroup ↥(U.map (QuotientGroup.mk' V))) = ⊤ :=
      ((Q.mapSurjective hf_surj).3 htop_pg le_top).symm
    have hz' : (⟨z, hz⟩ : ↥(U.map (QuotientGroup.mk' V))) ∈
        ((Q.mapSurjective hf_surj : Sylow q ↥(U.map (QuotientGroup.mk' V))) :
          Subgroup ↥(U.map (QuotientGroup.mk' V))) := by
      rw [hQbar_top]
      trivial
    obtain ⟨x, hxQ, hx_eq⟩ := hz'
    refine ⟨(x : G), ⟨x.2, ?_⟩, ?_⟩
    · have hQU_pg : IsPGroup q ↥((Q : Subgroup ↥U).map U.subtype) := Q.2.map _
      have hQU_le : (Q : Subgroup ↥U).map U.subtype ≤ Ch01.fitting G :=
        le_trans (Subgroup.map_subtype_le _) hU_le
      exact le_opCore_of_isPGroup_of_le_fitting hQU_pg hQU_le ⟨x, hxQ, rfl⟩
    · exact congrArg Subtype.val hx_eq
  -- ## `R` is narrow
  -- generic squeeze: any subgroup of `C_G(E) ⊓ F(G)` has `r`-rank ≤ 2 for every prime `r`
  have hsq : ∀ (r : ℕ), r.Prime → ∀ X : Subgroup G,
      X ≤ Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G → pRank ↥X r ≤ 2 := by
    intro r hr X hX
    have : Fact r.Prime := ⟨hr⟩
    calc pRank ↥X r
        ≤ pRank ↥(Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G) r :=
          pRank_le_of_injective (f := Subgroup.inclusion hX) (Subgroup.inclusion_injective hX)
      _ ≤ OddOrder.GroupTheory.rank ↥(Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G) :=
          pRank_le_rank r
      _ ≤ 2 := hrank
  have hE_self : E ≤ Subgroup.centralizer (E : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro e' he'
    exact congrArg Subtype.val (hE.comm ⟨e', he'⟩ ⟨e, he⟩)
  have hR_narrow : IsNarrow q ↥R := by
    by_cases hrk : pRank ↥R q ≤ 2
    · exact isNarrow_of_pRank_le_two hrk
    have h3R : 3 ≤ pRank ↥R q := by omega
    -- `q = p`: otherwise `R` centralizes `E` and the squeeze contradicts `r(R) ≥ 3`
    have hq_eq_p : q = p := by
      by_contra hq_ne
      have hE_Op : E ≤ Ch01.opCore p G :=
        le_opCore_of_isPGroup_of_le_fitting hE.isPGroup hEF
      have hinf_bot : R ⊓ Ch01.opCore p G = ⊥ := by
        have hinf_pg_q : IsPGroup q ↥(R ⊓ Ch01.opCore p G) := hR_pg.to_le inf_le_left
        have hinf_pg_p : IsPGroup p ↥(R ⊓ Ch01.opCore p G) :=
          (Ch01.opCore_isPGroup p G).to_le inf_le_right
        obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hinf_pg_q
        obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hinf_pg_p
        rw [← Subgroup.card_eq_one]
        rcases Nat.eq_zero_or_pos a with ha0 | hapos
        · rw [ha, ha0, pow_zero]
        · exfalso
          have hq_dvd_pb : q ∣ p ^ b := by
            rw [← hb, ha]
            exact dvd_pow_self q hapos.ne'
          exact hq_ne ((Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
            (hq_prime.dvd_of_dvd_pow hq_dvd_pb))
      have hcomm_bot : ⁅R, Ch01.opCore p G⁆ = ⊥ := by
        rw [eq_bot_iff, ← hinf_bot]
        exact le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
      have hR_le_centE : R ≤ Subgroup.centralizer (E : Set G) := by
        refine le_trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot)
          (Subgroup.centralizer_le ?_)
        exact fun x hx => hE_Op hx
      have := hsq q hq_prime R (le_inf hR_le_centE hR_le_F)
      omega
    subst hq_eq_p
    -- `E ≤ R = O_q(G)` and the interior of `R`: `Z = Ω₁(Z(R))`, `E' = E`-in-`R`
    have hE_R : E ≤ R := le_opCore_of_isPGroup_of_le_fitting hE.isPGroup hEF
    have hR_nontriv : Nontrivial ↥R := by
      rcases subsingleton_or_nontrivial ↥R with hsub | h
      · exfalso
        have hle2 : pRank ↥R q ≤ 2 := by
          rw [pRank_le_iff]
          intro A hA
          have : Subsingleton ↥A := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
          have hcard1 : Nat.card ↥A = 1 := Nat.card_eq_one_iff_unique.mpr ⟨‹_›, ⟨1⟩⟩
          rw [hcard1]
          simp
        omega
      · exact h
    set Z : Subgroup ↥R := omega1Center ↥R q with hZ_def
    have hZ_elem : Z.IsElementaryAbelian q := omega1Center_isElementaryAbelian
    have hZ_ne : Z ≠ ⊥ := by
      have := hR_pg.center_nontrivial
      have hdvd : q ∣ Nat.card ↥(Subgroup.center ↥R) := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR_pg.to_subgroup (Subgroup.center ↥R))
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · exfalso
          have hlt := Finite.one_lt_card (α := ↥(Subgroup.center ↥R))
          rw [hk, h0, pow_zero] at hlt
          omega
        · rw [hk]
          exact dvd_pow_self q hpos.ne'
      obtain ⟨z, hz_ord⟩ := exists_prime_orderOf_dvd_card' q hdvd
      intro hbot
      have hzZ : (z : ↥R) ∈ Z := by
        refine mem_omega1Center.mpr ⟨z.2, ?_⟩
        rw [← hz_ord]
        calc (z : ↥R) ^ orderOf z = ((z ^ orderOf z : ↥(Subgroup.center ↥R)) : ↥R) := rfl
          _ = 1 := by rw [pow_orderOf_eq_one z]; rfl
      rw [hbot] at hzZ
      have hz1 : z = 1 := Subtype.ext (Subgroup.mem_bot.mp hzZ)
      rw [hz1, orderOf_one] at hz_ord
      exact hq_prime.one_lt.ne' hz_ord.symm
    have hE'_not_le : ¬ E.subgroupOf R ≤ Z := by
      intro hle
      have hR_le_centE : R ≤ Subgroup.centralizer (E : Set G) := by
        intro r hr
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have hcen := omega1Center_le_center (hle (Subgroup.mem_subgroupOf.mpr he :
          (⟨e, hE_R he⟩ : ↥R) ∈ E.subgroupOf R))
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨r, hr⟩)).symm
      have := hsq q hq_prime R (le_inf hR_le_centE hR_le_F)
      omega
    -- `EZ := E' ⊔ Z` is elementary abelian of order exactly `q²` and maximal
    have hE'_elem : (E.subgroupOf R).IsElementaryAbelian q :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hE_R).symm hE
    have hZ_cent_top : Subgroup.centralizer (Z : Set ↥R) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr fun z hz => omega1Center_le_center hz
    have hEZ_elem : (E.subgroupOf R ⊔ Z).IsElementaryAbelian q :=
      Subgroup.IsElementaryAbelian.sup_of_le_centralizer hE'_elem hZ_elem
        (by rw [hZ_cent_top]; exact le_top)
    -- log-card squeeze for elementary abelian subgroups of `R` centralizing `E`
    have hlog_le_two : ∀ Y : Subgroup ↥R, Y.IsElementaryAbelian q →
        Y.map R.subtype ≤ Subgroup.centralizer (E : Set G) →
        Nat.log q (Nat.card ↥Y) ≤ 2 := by
      intro Y hY hYc
      have hY_le : Y.map R.subtype ≤ Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G :=
        le_inf hYc (le_trans (Subgroup.map_subtype_le _) hR_le_F)
      have h1 : (Y.map R.subtype).IsElementaryAbelian q :=
        Subgroup.IsElementaryAbelian.map R.subtype_injective hY
      have h2 : ((Y.map R.subtype).subgroupOf
          (Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G)).IsElementaryAbelian q :=
        OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe hY_le).symm h1
      have hcard2 : Nat.card ↥((Y.map R.subtype).subgroupOf
          (Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G)) = Nat.card ↥Y := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY_le).toEquiv]
        exact (Nat.card_congr
          (Subgroup.equivMapOfInjective Y R.subtype R.subtype_injective).toEquiv).symm
      calc Nat.log q (Nat.card ↥Y)
          = Nat.log q (Nat.card ↥((Y.map R.subtype).subgroupOf
              (Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G))) := by rw [hcard2]
        _ ≤ pRank ↥(Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G) q := le_pRank _ h2
        _ ≤ OddOrder.GroupTheory.rank
              ↥(Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G) := pRank_le_rank q
        _ ≤ 2 := hrank
    have hEZ_map_le : (E.subgroupOf R ⊔ Z).map R.subtype ≤
        Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rw [Subgroup.map_subgroupOf_eq_of_le hE_R]
        exact hE_self
      · rintro _ ⟨z, hzZ, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp (omega1Center_le_center hzZ) ⟨e, hE_R he⟩)
    have hEZ_card : Nat.card ↥(E.subgroupOf R ⊔ Z) = q ^ 2 := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hEZ_elem.isPGroup
      have hm_le : m ≤ 2 := by
        have h := hlog_le_two _ hEZ_elem hEZ_map_le
        rwa [hm, Nat.log_pow hq_prime.one_lt] at h
      have hm_ge : 2 ≤ m := by
        have hZ_le : Z ≤ E.subgroupOf R ⊔ Z := le_sup_right
        have hZ_ne_EZ : Z ≠ E.subgroupOf R ⊔ Z := by
          intro h
          exact hE'_not_le (h ▸ le_sup_left)
        obtain ⟨z, hz⟩ := IsPGroup.iff_card.mp (hZ_elem.isPGroup)
        have hlt : Nat.card ↥Z < Nat.card ↥(E.subgroupOf R ⊔ Z) := by
          rcases lt_or_eq_of_le (Subgroup.card_le_of_le hZ_le) with h | h
          · exact h
          · exact absurd (Subgroup.eq_of_le_of_card_ge hZ_le h.ge) hZ_ne_EZ
        have hz_pos : 1 ≤ z := by
          rcases Nat.eq_zero_or_pos z with h0 | h
          · exfalso
            apply hZ_ne
            rw [← Subgroup.card_eq_one, hz, h0, pow_zero]
          · exact h
        rw [hz, hm] at hlt
        have := (Nat.pow_lt_pow_iff_right hq_prime.one_lt).mp hlt
        omega
      have : m = 2 := le_antisymm hm_le hm_ge
      rw [hm, this]
    have hEZ_max : IsMaximalElementaryAbelian q (E.subgroupOf R ⊔ Z) := by
      refine ⟨hEZ_elem, ?_⟩
      intro F hF hleF
      have hF_map_le : F.map R.subtype ≤ Subgroup.centralizer (E : Set G) := by
        rintro _ ⟨f, hfF, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have heF : (⟨e, hE_R he⟩ : ↥R) ∈ F :=
          hleF (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr he))
        exact congrArg Subtype.val (congrArg Subtype.val
          (hF.comm ⟨⟨e, hE_R he⟩, heF⟩ ⟨f, hfF⟩))
      obtain ⟨mF, hmF⟩ := IsPGroup.iff_card.mp hF.isPGroup
      have hmF_le : mF ≤ 2 := by
        have h := hlog_le_two F hF hF_map_le
        rwa [hmF, Nat.log_pow hq_prime.one_lt] at h
      refine (Subgroup.eq_of_le_of_card_ge hleF ?_).symm
      rw [hEZ_card, hmF]
      exact Nat.pow_le_pow_right hq_prime.pos hmF_le
    exact (narrow_iff_exists_maximalElementaryAbelian_card_prime_sq hq_odd hR_pg h3R).mpr
      ⟨E.subgroupOf R ⊔ Z, hEZ_card, hEZ_max⟩
  -- ## Theorem 5.5: `(G ⧸ C_G(R))'` is a `q`-group
  set ψ : G →* MulAut ↥R := MulAut.conjNormal with hψ_def
  have hker : ψ.ker = Subgroup.centralizer (R : Set G) := by
    rw [hψ_def]
    exact S04.conjNormal_ker
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
  obtain ⟨hcomm, -, -, -⟩ := solvableAut_of_narrow hq_odd hR_pg hR_narrow
    (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ) hquot_odd
  have hA' : IsPGroup q (_root_.commutator (G ⧸ ψ.ker)) := by
    have hle : _root_.commutator (G ⧸ ψ.ker) ≤ Ch01.opCore q (G ⧸ ψ.ker) := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro x _ y _
      have h1 : QuotientGroup.mk' (Ch01.opCore q (G ⧸ ψ.ker)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm _ _
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact (Ch01.opCore_isPGroup q _).to_le hle
  -- ## the image of `Ĝ' = D` in `MulAut Ū` is a `q`-group (the action factors through `G ⧸ C_G(R)`)
  set α : (G ⧸ V) →* MulAut ↥Ubar := MulAut.conjNormal with hα_def
  set D : Subgroup (G ⧸ V) := _root_.commutator (G ⧸ V) with hD_def
  set β : G →* MulAut ↥Ubar := α.comp (QuotientGroup.mk' V) with hβ_def
  have hmapV : (_root_.commutator G).map (QuotientGroup.mk' V) = D := by
    rw [hD_def, _root_.commutator, _root_.commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective V)]
  have hker_le : ψ.ker ≤ β.ker := by
    intro c hc
    rw [hker] at hc
    rw [MonoidHom.mem_ker]
    ext u
    obtain ⟨w, ⟨hwU, hwR⟩, hw_eq⟩ := hUbar_sub (u : G ⧸ V) u.2
    have hcw : c * w * c⁻¹ = w := by
      rw [← Subgroup.mem_centralizer_iff.mp hc w hwR, mul_inv_cancel_right]
    calc (((β c) u : ↥Ubar) : G ⧸ V)
        = (QuotientGroup.mk' V c) * (u : G ⧸ V) * (QuotientGroup.mk' V c)⁻¹ :=
          MulAut.conjNormal_apply _ _
      _ = (u : G ⧸ V) := by
          rw [← hw_eq, ← map_inv, ← map_mul, ← map_mul, hcw]
      _ = ((1 : MulAut ↥Ubar) u : G ⧸ V) := rfl
  have hD_pg : IsPGroup q ↥(D.map α) := by
    have hmapK : (_root_.commutator G).map (QuotientGroup.mk' ψ.ker) =
        _root_.commutator (G ⧸ ψ.ker) := by
      rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective ψ.ker)]
    set β' : (G ⧸ ψ.ker) →* MulAut ↥Ubar :=
      QuotientGroup.lift ψ.ker β (fun x hx => MonoidHom.mem_ker.mp (hker_le hx))
      with hβ'_def
    have h1 : D.map α = (_root_.commutator G).map β := by
      rw [← hmapV, Subgroup.map_map]
    have h2 : (_root_.commutator G).map β =
        (_root_.commutator (G ⧸ ψ.ker)).map β' := by
      rw [← hmapK, Subgroup.map_map]
      congr 1
    rw [h1, h2]
    exact hA'.map β'
  -- ## fixed points of the `q`-group action on `Ū`: nontrivial, `Ĝ`-normal, hence all of `Ū`
  have hUbar_nontriv : Nontrivial ↥Ubar := by
    rcases Subgroup.bot_or_nontrivial Ubar with h | h
    · exact absurd h hUbar_ne
    · exact h
  have hfix_ne : Subgroup.fixedPointsOfMulAut (D.map α).subtype ≠ ⊥ :=
    Ch04.fixedPoints_ne_bot_of_pgroup_action_pgroup hUbar_pg hD_pg _
  have hD_norm : D.Normal := by
    rw [hD_def, _root_.commutator]
    infer_instance
  set W' : Subgroup (G ⧸ V) :=
    (Subgroup.fixedPointsOfMulAut (D.map α).subtype).map Ubar.subtype with hW'_def
  have hW'_mem : ∀ x : G ⧸ V, x ∈ W' ↔ x ∈ Ubar ∧ ∀ d ∈ D, d * x * d⁻¹ = x := by
    intro x
    constructor
    · rintro ⟨⟨u, hu⟩, hfix, rfl⟩
      refine ⟨hu, fun d hd => ?_⟩
      have h1 := Subgroup.mem_fixedPointsOfMulAut.mp hfix
        ⟨α d, Subgroup.mem_map.mpr ⟨d, hd, rfl⟩⟩
      have h2 := congrArg Subtype.val h1
      calc d * (Ubar.subtype ⟨u, hu⟩) * d⁻¹
          = (((α d) ⟨u, hu⟩ : ↥Ubar) : G ⧸ V) :=
            (MulAut.conjNormal_apply d (⟨u, hu⟩ : ↥Ubar)).symm
        _ = Ubar.subtype ⟨u, hu⟩ := h2
    · rintro ⟨hxU, hxfix⟩
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_fixedPointsOfMulAut]
      intro a
      obtain ⟨d, hd, ha⟩ := a.2
      have h3 : a.1 ⟨x, hxU⟩ = (⟨x, hxU⟩ : ↥Ubar) := by
        rw [← ha]
        apply Subtype.ext
        calc (((α d) ⟨x, hxU⟩ : ↥Ubar) : G ⧸ V)
            = d * x * d⁻¹ := MulAut.conjNormal_apply d (⟨x, hxU⟩ : ↥Ubar)
          _ = x := hxfix d hd
      exact h3
  have hW'_le : W' ≤ Ubar := Subgroup.map_subtype_le _
  have hW'_ne : W' ≠ ⊥ := by
    intro h
    apply hfix_ne
    rw [hW'_def, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at h
    exact h
  have hW'_norm : W'.Normal := by
    constructor
    intro n hn g
    obtain ⟨hnU, hnfix⟩ := (hW'_mem n).mp hn
    refine (hW'_mem _).mpr ⟨hUbar_norm.conj_mem n hnU g, fun d hd => ?_⟩
    have hd' : g⁻¹ * d * g ∈ D := by
      have := hD_norm.conj_mem d hd g⁻¹
      simpa [mul_assoc] using this
    have hfix := hnfix _ hd'
    calc d * (g * n * g⁻¹) * d⁻¹
        = g * ((g⁻¹ * d * g) * n * (g⁻¹ * d * g)⁻¹) * g⁻¹ := by group
      _ = g * n * g⁻¹ := by rw [hfix]
  -- minimality forces `W' = Ū`, so `Ĝ'` centralizes `Ū`
  rcases hMin.2.2 W' hW'_norm hW'_le with h | h
  · exact absurd h hW'_ne
  · have hD_cent : D ≤ Subgroup.centralizer (Ubar : Set (G ⧸ V)) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : u ∈ W' := by rw [h]; exact hu
      have hfix := ((hW'_mem u).mp hu').2 d hd
      calc u * d = (d * u * d⁻¹) * d := by rw [hfix]
        _ = d * u := by group
    refine OddOrder.GroupTheory.chiefFactorCentralizer.le_of_map_le_centralizer ?_
    rw [hmapV]
    exact hD_cent

end Thm57

section Thm420c

open OddOrder.BG.Ch1.S04

variable {G : Type*} [Group G] [Finite G]

/-- **BG Theorem 4.20(a)** for the `r(F(G)) ≤ 2` branch: a finite solvable group of odd order with
`rank F(G) ≤ 2` satisfies `G' ≤ F(G)`, so `G/F(G)` is abelian.

This specializes Theorem 5.7 (`derived_le_fitting_of_centralizer_rank_le_two`) to an arbitrary
elementary abelian `p`-subgroup `E ≤ F(G)` — which exists since `F(G) ≠ 1` — using that the
centralizer-rank hypothesis `r(C_G(E) ⊓ F(G)) ≤ 2` follows from `C_G(E) ⊓ F(G) ≤ F(G)`. (BG proves
4.20(a) via Corollary 4.19 + Proposition 1.2; the repository uses the stronger 5.7, hence the
placement here, downstream of §5.) -/
theorem derived_le_fitting_of_rank_fitting_le_two [Group.IsSolvable G] [Nontrivial G]
    (hodd : Odd (Nat.card G)) (hrank : rank ↥(Ch01.fitting G) ≤ 2) :
    commutator G ≤ Ch01.fitting G := by
  classical
  have hF_ne : Ch01.fitting G ≠ ⊥ := Ch01.fitting_ne_bot_of_isSolvable_nontrivial G
  have : Nontrivial ↥(Ch01.fitting G) := (Subgroup.nontrivial_iff_ne_bot _).mpr hF_ne
  have hcard_ne : Nat.card ↥(Ch01.fitting G) ≠ 1 := (Finite.one_lt_card).ne'
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hcard_ne
  have : Fact p.Prime := ⟨hp_prime⟩
  obtain ⟨x, hx⟩ := Ch01.cauchy (G := ↥(Ch01.fitting G)) hp_dvd
  -- `E = ⟨x⟩ ≤ F(G)` is elementary abelian of order `p`.
  set g : G := (Ch01.fitting G).subtype x with hg
  have hg_mem : g ∈ Ch01.fitting G := by rw [hg]; exact x.2
  have hg_order : orderOf g = p :=
    (orderOf_injective (Ch01.fitting G).subtype (Ch01.fitting G).subtype_injective x).trans hx
  set E : Subgroup G := Subgroup.zpowers g with hE
  have hE_card : Nat.card ↥E = p := by rw [hE, Nat.card_zpowers, hg_order]
  have hE_elem : E.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.of_card_prime hE_card
  have hEF : E ≤ Ch01.fitting G := by rw [hE]; exact Subgroup.zpowers_le.mpr hg_mem
  -- the centralizer-rank hypothesis is automatic from `rank F(G) ≤ 2`.
  have hrank_cent :
      rank ↥(Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G) ≤ 2 :=
    le_trans (rank_le_of_injective
      (Subgroup.inclusion_injective (inf_le_right :
        Subgroup.centralizer (E : Set G) ⊓ Ch01.fitting G ≤ Ch01.fitting G))) hrank
  exact derived_le_fitting_of_centralizer_rank_le_two hodd E hE_elem hEF hrank_cent

/-- **BG Theorem 4.20(c) — minimal-prime step**: a finite solvable group of odd order with
`r(F(G)) ≤ 2` has a normal `p`-complement for the *smallest* prime `p` dividing `|G|`.

This is the engine inside BG's induction for Theorem 4.20(c) (mmd L1786): `F := F(G)`; by
Theorem 4.20(a) (`derived_le_fitting_of_rank_fitting_le_two`) `G' ≤ F`, so `G/F` is abelian.
With `H := (mk' F)⁻¹(O_{p'}(G/F))`, the quotient `G/H ≅ (G/F)/O_{p'}(G/F)` is a `p`-group and
`F` contains a Sylow `p`-subgroup of `H`; Theorem 4.18(b) (via
`solvable_structure_of_pRank_le_two`, minimality of `p` enters through its prime-comparison
side condition) gives a normal `p`-complement of `H`, which combines with the `p`-group `G/H`
into one for `G`.  Exposed standalone (2026-06-11) so that Hall-radical arguments downstream
(BG Theorem 11.7 via `S05b_Thm420Hall`) can iterate it without rebuilding the series. -/
theorem hasNormalPComplement_minFac_of_rank_fitting_le_two
    [Group.IsSolvable G] [Nontrivial G] (hodd : Odd (Nat.card G))
    (hrank : rank ↥(Ch01.fitting G) ≤ 2) :
    Ch05.HasNormalPComplement (Nat.minFac (Nat.card G)) G := by
  classical
  have hcard_ne1 : Nat.card G ≠ 1 := (Finite.one_lt_card).ne'
  have hp_prime : (Nat.minFac (Nat.card G)).Prime := Nat.minFac_prime hcard_ne1
  set p := Nat.minFac (Nat.card G) with hpdef
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp_min : ∀ q ∈ (Nat.card G).primeFactors, p ≤ q := fun q hq =>
    Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
      (Nat.dvd_of_mem_primeFactors hq)
  -- `G/F` is abelian
  have hG' : commutator G ≤ Ch01.fitting G :=
    derived_le_fitting_of_rank_fitting_le_two hodd hrank
  have habel : ∀ x y : G ⧸ Ch01.fitting G, x * y = y * x :=
    isMulCommutative_iff.mp
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hG')
  -- `H = (mk' F)⁻¹(O_{p'}(G/F))`
  set Nbar : Subgroup (G ⧸ Ch01.fitting G) :=
    Ch03.oPiCore {r : ℕ | r ≠ p} (G ⧸ Ch01.fitting G) with hNbar
  set Hsub : Subgroup G :=
    Subgroup.comap (QuotientGroup.mk' (Ch01.fitting G)) Nbar with hHsub
  have hHnorm : Hsub.Normal := by rw [hHsub]; infer_instance
  have hF_le_H : Ch01.fitting G ≤ Hsub := by
    rw [hHsub]
    intro y hy
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
    exact Nbar.one_mem
  have hHmap : Hsub.map (QuotientGroup.mk' (Ch01.fitting G)) = Nbar := by
    rw [hHsub]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  -- `G/H ≅ (G/F)/O_{p'}(G/F)` is a `p`-group
  have houter : IsPGroup p (G ⧸ Hsub) :=
    (isPGroup_quotient_oPiCore_of_comm habel).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hHmap).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient _ _ hF_le_H))
  by_cases hpH : p ∣ Nat.card ↥Hsub
  · -- `p ∣ |H|`: Theorem 4.18(b) gives one for `H`, extended by `houter`
    have hoddH : Odd (Nat.card ↥Hsub) := by
      rcases Nat.even_or_odd (Nat.card ↥Hsub) with he | ho
      · exfalso
        have h2 : (2 : ℕ) ∣ Nat.card G :=
          he.two_dvd.trans (Subgroup.card_subgroup_dvd_card Hsub)
        rw [Nat.odd_iff] at hodd; omega
      · exact ho
    have hpCaseH : p = 3 ∨ ∀ q ∈ (Nat.card ↥Hsub).primeFactors, p ≤ q :=
      Or.inr fun q hq => hp_min q (Nat.primeFactors_mono
        (Subgroup.card_subgroup_dvd_card Hsub) Nat.card_pos.ne' hq)
    have : ((Ch01.fitting G).subgroupOf Hsub).Normal :=
      Subgroup.Normal.subgroupOf inferInstance Hsub
    have : Group.IsNilpotent ↥((Ch01.fitting G).subgroupOf Hsub) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hF_le_H).symm
    -- `p ∤ [H:F]` because `H/F ≅ O_{p'}(G/F)` is a `p'`-group
    have hidx : ¬ p ∣ ((Ch01.fitting G).subgroupOf Hsub).index := by
      have hker : ((QuotientGroup.mk' (Ch01.fitting G)).comp Hsub.subtype).ker
          = (Ch01.fitting G).subgroupOf Hsub := by
        ext h
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hrange : ((QuotientGroup.mk' (Ch01.fitting G)).comp Hsub.subtype).range = Nbar := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, hHmap]
      have hcardq : Nat.card (↥Hsub ⧸ (Ch01.fitting G).subgroupOf Hsub) = Nat.card ↥Nbar := by
        have e : (↥Hsub ⧸ (Ch01.fitting G).subgroupOf Hsub) ≃*
            ↥((QuotientGroup.mk' (Ch01.fitting G)).comp Hsub.subtype).range :=
          (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
            (QuotientGroup.quotientKerEquivRange _)
        rw [Nat.card_congr e.toEquiv, hrange]
      rw [Subgroup.index_eq_card, hcardq, hNbar]
      exact not_dvd_card_oPiCore (by simp)
    obtain ⟨P, hP_le⟩ := exists_sylow_le_fitting_of_nilpotent_normal_index_coprime
      (X := ↥Hsub) (M := (Ch01.fitting G).subgroupOf Hsub) hidx
    have hrH : pRank ↥Hsub p ≤ 2 :=
      pRank_le_two_of_sylow_le_fitting P hP_le (rank_fitting_le_two_of_normal_subgroup hrank)
    exact hasNormalPComplement_of_normal_subgroup_hasNormalPComplement_of_quotient_isPGroup
      ((solvable_structure_of_pRank_le_two hoddH hpH hrH).2.1 hpCaseH) houter
  · -- `p ∤ |H|`: `H` itself is a normal `p`-complement
    exact hasNormalPComplement_of_normal_pPrime_of_quotient_isPGroup hpH houter

/-- **BG Theorem 4.20(c) — existence** (mmd L1764/L1771): a finite solvable group of odd order
with `r(F(G)) ≤ 2` possesses a *characteristic Sylow series* `G = G₀ ⊃ ⋯ ⊃ Gₙ = 1` whose factors
are isomorphic to Sylow subgroups of `G`, packaged as `CharacteristicSylowSeriesPackage G`.

This is the producer the §9 (Lemma 9.5) consumers take as a hypothesis
(`exists_pSubgroup_normalizer_package_of_not_scn3_of_sylowSeriesPackage`, etc.); proving it
discharges those `SP : CharacteristicSylowSeriesPackage ↥M` hypotheses for the
(solvable, `r(F)≤2`) maximal subgroups `M`.

Construction (strong induction on `|G|`, BG's own proof, mmd L1786): `F := F(G)`; by Theorem
4.20(a) (`derived_le_fitting_of_rank_fitting_le_two`) `G' ≤ F`, so `G/F` is abelian.  Let `p` be
the smallest prime divisor of `|G|` and `H := (mk' F)⁻¹(O_{p'}(G/F))`.  Then `G/H ≅
(G/F)/O_{p'}(G/F)` is a `p`-group, and `F` contains a Sylow `p` of `H`.  Theorem 4.18(b) gives a
normal `p`-complement of `H`, which combines with the `p`-group `G/H` into
`Ch05.HasNormalPComplement p G`, complement `K = O_{p'}(G)`.  Since `F(K) ≤ F(G)`, recurse on `K`
(or stop if `K = ⊥`, i.e. `G` is a `p`-group) and lift the resulting series with the attached top
`G/O_{p'}` layer of label `p`.

The induction carries the extra invariant that every step label is a prime divisor of `|G|`,
needed because the lift requires the recursive series to have no `p`-labels (`p ∤ |K|`). -/
theorem exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two
    [Group.IsSolvable G] [Nontrivial G] (hodd : Odd (Nat.card G))
    (hrank : rank ↥(Ch01.fitting G) ≤ 2) :
    Nonempty (CharacteristicSylowSeriesPackage G) := by
  classical
  suffices H : ∀ n : ℕ, ∀ (G : Type _) [Group G] [Finite G] [Group.IsSolvable G] [Nontrivial G],
      Nat.card G = n → Odd (Nat.card G) → rank ↥(Ch01.fitting G) ≤ 2 →
      ∃ S : CharacteristicSylowSeries G, 0 < S.length ∧
        ∀ i : Fin S.length, (S.step i).q ∈ (Nat.card G).primeFactors by
    obtain ⟨S, hpos, hall⟩ := H (Nat.card G) G rfl hodd hrank
    exact ⟨{ series := S, length_pos := hpos, terminal_mem := fun i _ => hall i }⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ _ _ hcard hodd' hrank'
    -- smallest prime divisor `p` of `|G|`
    have hcard_ne1 : Nat.card G ≠ 1 := (Finite.one_lt_card).ne'
    have hp_prime : (Nat.minFac (Nat.card G)).Prime := Nat.minFac_prime hcard_ne1
    set p := Nat.minFac (Nat.card G) with hpdef
    have : Fact p.Prime := ⟨hp_prime⟩
    have hp_dvd : p ∣ Nat.card G := Nat.minFac_dvd _
    have hp_in_piG : p ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, Nat.card_pos.ne'⟩
    -- `G` has a normal `p`-complement (minimal-prime engine, extracted above)
    have hG : Ch05.HasNormalPComplement p G :=
      hasNormalPComplement_minFac_of_rank_fitting_le_two hodd' hrank'
    -- recurse (or stop) on the complement `K = O_{p'}(G)`
    set K : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G with hKdef
    have hKnorm : K.Normal := by rw [hKdef]; infer_instance
    obtain ⟨S, hS_all⟩ :
        ∃ S : CharacteristicSylowSeries ↥K, ∀ j : Fin S.length,
          (S.step j).q ∈ (Nat.card ↥K).primeFactors := by
      by_cases hKbot : K = ⊥
      · have hsub : Subsingleton ↥K := by rw [hKbot]; infer_instance
        have hbotK : (⊤ : Subgroup ↥K) = ⊥ :=
          eq_bot_iff.mpr fun x _ => Subgroup.mem_bot.mpr (Subsingleton.elim x 1)
        refine ⟨⟨0, fun _ => ⊤, rfl, hbotK, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩,
          fun j => j.elim0⟩
      · have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKbot
        have hKodd : Odd (Nat.card ↥K) := by
          rcases Nat.even_or_odd (Nat.card ↥K) with he | ho
          · exfalso
            have h2 : (2 : ℕ) ∣ Nat.card G :=
              he.two_dvd.trans (Subgroup.card_subgroup_dvd_card K)
            rw [Nat.odd_iff] at hodd'; omega
          · exact ho
        have hKrank : rank ↥(Ch01.fitting ↥K) ≤ 2 := rank_fitting_le_two_of_normal_subgroup hrank'
        have hK_lt : Nat.card ↥K < n := by
          have hmul : Nat.card ↥K * K.index = Nat.card G := Subgroup.card_mul_index K
          have hidx_pos : 1 < K.index := by
            rw [hKdef, Subgroup.index_eq_card,
              card_quotient_oPiCore_eq_card_sylow_of_hasNormalPComplement hG (default : Sylow p G)]
            refine lt_of_lt_of_le hp_prime.one_lt (Nat.le_of_dvd Nat.card_pos ?_)
            rw [(default : Sylow p G).card_eq_multiplicity]
            exact dvd_pow_self p (hp_prime.factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd).ne'
          rw [← hcard, ← hmul]
          exact lt_mul_of_one_lt_right Nat.card_pos hidx_pos
        obtain ⟨SK, _, hSK_all⟩ := IH (Nat.card ↥K) hK_lt ↥K rfl hKodd hKrank
        exact ⟨SK, hSK_all⟩
    -- the lifted series avoids `p`-labels (since `p ∤ |K|`)
    have hpq : ∀ i : Fin S.length, (S.step i).q ≠ p := by
      intro i hqi
      exact (not_dvd_card_oPiCore (G := G) (π := {r : ℕ | r ≠ p}) (by simp))
        (hKdef ▸ Nat.dvd_of_mem_primeFactors (hqi ▸ hS_all i))
    refine ⟨CharacteristicSylowSeries.lift_oPiCore_series_of_hasNormalPComplement_ne hG S hpq,
      ?_, ?_⟩
    · simp
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact hp_in_piG
      · intro j
        exact Nat.primeFactors_mono (Subgroup.card_subgroup_dvd_card K) Nat.card_pos.ne' (hS_all j)

end Thm420c

end OddOrder.BG.Ch1.S05


