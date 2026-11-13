-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadical
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadical
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:02:43.33344+00:00
-- url     : https://prove2.me/theorems/05155359-2a92-4a16-9858-3a98a1d07b54
-- title:
--   BG §10: the $\beta$-radical spine, Corollary 10.9 and Proposition 10.10
-- statement:
--   Formalizes Corollary 10.9 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §10 (centralization of $\beta(M)'$-subgroups), the normalizer gates of 10.9(a)(3)/(b), and Proposition 10.10 (factorization of $N_G(P)$). It is the last file of the three-way split of the $\beta$-radical spine.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadical.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S10_BetaRadical.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadicalGlobal

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

/-- **Cor 10.9(a) L1 (W の構成)**: `X` を `M` の `q`-部分群とすると, `XM' = X ⊔ M'` の中に `X` を
含む Hall `{p,q}`-部分群 `W` がある (BG Cor 10.9(a) 第 1 文)。`Y := X ⊔ M'` は可解 (`≤ M`) ゆえ
Hall-D (`Ch03.hall_D`) を `X.subgroupOf Y` (`q`-群 ⊆ `{p,q}`) に適用し, `↥Y` から `G` へ map back。 -/
theorem exists_hall_pq_containing [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact q.Prime]
    {X : Subgroup G} (hXM : X ≤ M) (hXq : IsPGroup q ↥X) :
    ∃ W : Subgroup G, X ≤ W ∧ W ≤ X ⊔ derivedInG M ∧
      Ch03.IsHallSubgroup ({p, q} : Set ℕ) (W.subgroupOf (X ⊔ derivedInG M)) := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set Y : Subgroup G := X ⊔ derivedInG M with hY
  have hYM : Y ≤ M := sup_le hXM (Subgroup.map_subtype_le _)
  have hYsolv : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYM)
  have hXYle : X ≤ Y := le_sup_left
  have hXY_pi : ∀ r ∈ (Nat.card ↥(X.subgroupOf Y)).primeFactors, r ∈ ({p, q} : Set ℕ) := by
    intro r hr
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXYle).toEquiv] at hr
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXq
    rw [hk, Nat.mem_primeFactors] at hr
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr.1 Fact.out).mp (hr.1.dvd_of_dvd_pow hr.2.1)
    exact Set.mem_insert_of_mem _ hrq
  obtain ⟨W₀, hW₀hall, hXW₀⟩ := Ch03.hall_D (G := ↥Y) hXY_pi
  refine ⟨W₀.map Y.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · have hle : (X.subgroupOf Y).map Y.subtype ≤ W₀.map Y.subtype := Subgroup.map_mono hXW₀
    rwa [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
      inf_of_le_right hXYle] at hle
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
    exact hW₀hall

/-- `M` は自身の導来部分群 `M' = derivedInG M` を正規化する。`derivedInG M = (commutator ↥M).map
M.subtype` で `commutator ↥M ◁ ↥M` ゆえ `normalizer(commutator ↥M) =
⊤`、これを `Subgroup.le_normalizer_map`
で押し出すと `range M.subtype = M ≤ normalizer(M')`。Cor 10.9 で `W ⊓ M' ◁ W` (`W ≤ M`) を出すのに使う。 -/
theorem le_normalizer_derivedInG (M : Subgroup G) :
    M ≤ Subgroup.normalizer (derivedInG M) := by
  have h := Subgroup.le_normalizer_map (H := commutator ↥M) M.subtype
  rwa [Subgroup.normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

/-- **Cor 10.9(a) producer (`W` nilpotent)** (mmd L2860-2862, forward-conditional via Theorem 10.6):
under the Corollary 10.9(a) hypotheses there is a Hall `{p,q}`-subgroup `W` of `XM'` containing `X`
that is moreover **nilpotent**. This packages the first two paragraphs of BG's proof:
`W ∩ M'` is nilpotent (`betacompl_subgroup_derived_isNilpotent`); either `X ⊆ M'` (so `W = W ∩ M'`),
or `p < q`, in which case (Lemma 10.8(c)) `W ∩ O_{p'}(M)` is a normal Sylow `q`-subgroup of `W` and
`W/(W ∩ M')` is a `q`-group, so `isNilpotent_of_normalSylowQ_of_nilpotent_qQuotient` applies. -/
theorem exists_nilpotent_hall_pq [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hpβ : p ∉ beta M) (hqβ : q ∉ beta M)
    {X : Subgroup G} (hXM : X ≤ M) (hXq : IsPGroup q ↥X)
    (hcase : X ≤ derivedInG M ∨ p < q) :
    ∃ W : Subgroup G, X ≤ W ∧ W ≤ X ⊔ derivedInG M ∧ Group.IsNilpotent ↥W ∧
      Ch03.IsHallSubgroup ({p, q} : Set ℕ) (W.subgroupOf (X ⊔ derivedInG M)) := by
  obtain ⟨W, hXW, hWY, hWhall⟩ := exists_hall_pq_containing (p := p) hG hM hXM hXq
  set D : Subgroup G := derivedInG M with hD
  set Y : Subgroup G := X ⊔ D with hY
  refine ⟨W, hXW, hWY, ?_, hWhall⟩
  have hDY : D ≤ Y := le_sup_right
  have hXY : X ≤ Y := le_sup_left
  have hYM : Y ≤ M := sup_le hXM (Subgroup.map_subtype_le _)
  have hWM : W ≤ M := hWY.trans hYM
  have hWcard_eq : Nat.card ↥(W.subgroupOf Y) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWY).toEquiv
  -- prime factors of `|W|` are among `{p, q}`.
  have hWpq : ∀ r ∈ (Nat.card ↥W).primeFactors, r = p ∨ r = q := by
    intro r hr
    rw [← hWcard_eq] at hr
    have h := hWhall.1 r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h
  -- `W ∩ M'` is a `β(M)'`-subgroup of `M'`, hence nilpotent (Lemma 10.8(b)).
  have hWDβ : ∀ r ∈ (Nat.card ↥(W ⊓ D)).primeFactors, r ∉ beta M := by
    intro r hr
    have hrW : r ∈ (Nat.card ↥W).primeFactors :=
      Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hr
    rcases hWpq r hrW with rfl | rfl
    · exact hpβ
    · exact hqβ
  have hWDnil : Group.IsNilpotent ↥(W ⊓ D) :=
    betacompl_subgroup_derived_isNilpotent hG hM (inf_le_right : W ⊓ D ≤ D) hWDβ
  rcases hcase with hXD | hpltq
  · -- Case `X ⊆ M'`: then `Y = M'`, `W ≤ M'`, and `W = W ∩ M'` is nilpotent.
    have hYD : Y = D := sup_eq_right.mpr hXD
    have hWD : W ≤ D := hWY.trans hYD.le
    have hWWD : W ⊓ D = W := inf_eq_left.mpr hWD
    exact hWWD ▸ hWDnil
  · -- Case `X ⊄ M'`, so `p < q`.
    by_cases hpπ : p ∈ (Nat.card ↥M).primeFactors
    · -- `p ∈ π(M)`: apply `isNilpotent_of_normalSylowQ_of_nilpotent_qQuotient`.
      -- `N := (W ⊓ M').subgroupOf W` is normal in `↥W` and nilpotent.
      have hWnD : W ≤ Subgroup.normalizer (W ⊓ D) :=
        le_trans (le_inf Subgroup.le_normalizer (hWM.trans (le_normalizer_derivedInG M)))
          (Subgroup.inf_normalizer_le_normalizer_inf)
      have hNnorm : ((W ⊓ D).subgroupOf W).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : W ⊓ D ≤ W)).mpr hWnD
      have := hWDnil
      have hNnil : Group.IsNilpotent ↥((W ⊓ D).subgroupOf W) :=
        Group.nilpotent_of_surjective
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ⊓ D ≤ W)).symm.toMonoidHom
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ⊓ D ≤ W)).symm.surjective
      -- `Y/M'` is a `q`-group (it is covered by the `q`-group `X`).
      have hDYnorm : (D.subgroupOf Y).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).mpr
          (hYM.trans (le_normalizer_derivedInG M))
      have hsup : D.subgroupOf Y ⊔ X.subgroupOf Y = ⊤ := by
        apply Subgroup.map_injective Y.subtype_injective
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDY,
            Subgroup.map_subgroupOf_eq_of_le hXY, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
            sup_comm]
      have hYq : IsPGroup q (↥Y ⧸ D.subgroupOf Y) := by
        have hmap_top : (X.subgroupOf Y).map (QuotientGroup.mk' (D.subgroupOf Y)) = ⊤ := by
          have h := QuotientGroup.comap_map_mk' (D.subgroupOf Y) (X.subgroupOf Y)
          rw [hsup] at h
          exact Subgroup.comap_injective (QuotientGroup.mk'_surjective _)
            (h.trans (Subgroup.comap_top _).symm)
        have h1 : IsPGroup q ↥(X.subgroupOf Y) :=
          hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXY).symm
        have h2 := h1.map (QuotientGroup.mk' (D.subgroupOf Y))
        rw [hmap_top] at h2
        exact h2.of_equiv Subgroup.topEquiv
      -- `W ↪ Y → Y/M'` has kernel `(W ∩ M').subgroupOf W`.
      set f : ↥W →* (↥Y ⧸ D.subgroupOf Y) :=
        (QuotientGroup.mk' (D.subgroupOf Y)).comp (Subgroup.inclusion hWY) with hf
      have hker : f.ker = (W ⊓ D).subgroupOf W := by
        rw [Subgroup.inf_subgroupOf_left, hf, ← MonoidHom.comap_ker,
            QuotientGroup.ker_mk' (D.subgroupOf Y)]
        ext w
        simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      have hWNq : ∀ r ∈ (Nat.card (↥W ⧸ (W ⊓ D).subgroupOf W)).primeFactors, r = q := by
        obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hYq
        have hdvd : Nat.card (↥W ⧸ (W ⊓ D).subgroupOf W) ∣ q ^ n := by
          have hcong : Nat.card (↥W ⧸ (W ⊓ D).subgroupOf W) = Nat.card ↥(f.range) := by
            rw [← hker]
            exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
          rw [hcong, ← hn]
          exact Subgroup.card_subgroup_dvd_card f.range
        intro r hr
        have hrn : r ∈ (q ^ n).primeFactors :=
          Nat.primeFactors_mono hdvd (pow_ne_zero n (Fact.out : q.Prime).pos.ne') hr
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · rw [hn0, pow_zero, Nat.primeFactors_one] at hrn
          exact absurd hrn (Finset.notMem_empty r)
        · rw [Nat.primeFactors_prime_pow hnpos.ne' (Fact.out : q.Prime)] at hrn
          exact Finset.mem_singleton.mp hrn
      -- `Qs := (W ∩ O_{p'}(M)).subgroupOf W` is a normal Sylow `q`-subgroup of `↥W`.
      have hWOpq : IsPGroup q ↥(W ⊓ opiCoreInG {r : ℕ | r ≠ p} M) := by
        apply isPGroup_of_isPiSubgroup_singleton
        intro r hr
        have hrW : r ∈ (Nat.card ↥W).primeFactors :=
          Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_left) Nat.card_pos.ne' hr
        have hrOp : r ∈ (Nat.card ↥(opiCoreInG {r : ℕ | r ≠ p} M)).primeFactors :=
          Nat.primeFactors_mono (Subgroup.card_dvd_of_le inf_le_right) Nat.card_pos.ne' hr
        have hrne : r ≠ p := isPiSubgroup_opiCoreInG ({r : ℕ | r ≠ p}) M r hrOp
        rcases hWpq r hrW with h | h
        · exact absurd h hrne
        · exact Set.mem_singleton_iff.mpr h
      -- a Sylow `q`-subgroup of `↥W` maps into `O_{p'}(M)`, so `W ∩ O_{p'}(M)` is full.
      obtain ⟨QW⟩ := (inferInstance : Nonempty (Sylow q ↥W))
      have hQWg_le_W : ((QW : Subgroup ↥W).map W.subtype) ≤ W := Subgroup.map_subtype_le _
      have hQWg_pg : IsPGroup q ↥((QW : Subgroup ↥W).map W.subtype) :=
        QW.2.of_equiv (Subgroup.equivMapOfInjective _ _ W.subtype_injective)
      have hQWg_le_M : ((QW : Subgroup ↥W).map W.subtype) ≤ M := hQWg_le_W.trans hWM
      have hQWg_M_pg : IsPGroup q ↥(((QW : Subgroup ↥W).map W.subtype).subgroupOf M) :=
        hQWg_pg.of_equiv (Subgroup.subgroupOfEquivOfLe hQWg_le_M).symm
      obtain ⟨QM, hQM_le⟩ := hQWg_M_pg.exists_le_sylow
      have hQM_Op : (QM : Subgroup ↥M) ≤ Ch03.oPiCore {r : ℕ | r ≠ p} ↥M :=
        sylow_le_oPiCore_compl_of_lt_of_not_mem_beta hG hM hpπ hpβ hpltq QM
      have hQWg_Op : ((QW : Subgroup ↥W).map W.subtype) ≤ opiCoreInG {r : ℕ | r ≠ p} M := by
        have h2 := Subgroup.map_mono (hQM_le.trans hQM_Op) (f := M.subtype)
        rwa [Subgroup.map_subgroupOf_eq_of_le hQWg_le_M] at h2
      have hQWg_le_WOp :
          ((QW : Subgroup ↥W).map W.subtype) ≤ W ⊓ opiCoreInG {r : ℕ | r ≠ p} M :=
        le_inf hQWg_le_W hQWg_Op
      have hQWg_card : Nat.card ↥((QW : Subgroup ↥W).map W.subtype) =
          q ^ (Nat.card ↥W).factorization q := by
        rw [Subgroup.card_subtype, Sylow.card_eq_multiplicity QW]
      have hWOp_card : Nat.card ↥((W ⊓ opiCoreInG {r : ℕ | r ≠ p} M).subgroupOf W) =
          q ^ (Nat.card ↥W).factorization q := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : W ⊓ opiCoreInG {r : ℕ | r ≠ p} M ≤ W)).toEquiv]
        refine Nat.dvd_antisymm ?_ ?_
        · obtain ⟨k, hk⟩ := hWOpq.exists_card_eq
          rw [hk]
          have hk_dvd : q ^ k ∣ Nat.card ↥W :=
            hk ▸ Subgroup.card_dvd_of_le (inf_le_left :
              W ⊓ opiCoreInG {r : ℕ | r ≠ p} M ≤ W)
          rw [(Fact.out : q.Prime).pow_dvd_iff_le_factorization Nat.card_pos.ne'] at hk_dvd
          exact pow_dvd_pow q hk_dvd
        · rw [← hQWg_card]
          exact Subgroup.card_dvd_of_le hQWg_le_WOp
      have hWnOp : W ≤ Subgroup.normalizer (W ⊓ opiCoreInG {r : ℕ | r ≠ p} M) :=
        le_trans (le_inf Subgroup.le_normalizer
            (hWM.trans (le_normalizer_opiCoreInG _ M)))
          (Subgroup.inf_normalizer_le_normalizer_inf)
      set Qs : Sylow q ↥W :=
        Sylow.ofCard ((W ⊓ opiCoreInG {r : ℕ | r ≠ p} M).subgroupOf W) hWOp_card with hQs
      have hQsnorm : (Qs : Subgroup ↥W).Normal := by
        rw [hQs, Sylow.coe_ofCard]
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer
          (inf_le_left : W ⊓ opiCoreInG {r : ℕ | r ≠ p} M ≤ W)).mpr hWnOp
      exact isNilpotent_of_normalSylowQ_of_nilpotent_qQuotient hpq hWpq Qs hQsnorm hNnil hWNq
    · -- `p ∉ π(M)`: then `p ∤ |W|`, so `W` is a `q`-group, hence nilpotent.
      have hWq : IsPGroup q ↥W := by
        apply isPGroup_of_isPiSubgroup_singleton
        intro r hr
        rcases hWpq r hr with h | h
        · exact absurd
            (h ▸ Nat.primeFactors_mono (Subgroup.card_dvd_of_le hWM) Nat.card_pos.ne' hr) hpπ
        · exact Set.mem_singleton_iff.mpr h
      exact hWq.isNilpotent

/-- **BG Corollary 10.9 (a)(1)(2)** (mmd L2826): `M ∈ ℳ`, `p, q ∈ β(M)'` distinct, `X` を `M` の
`q`-部分群で `X ⊆ M'` または `p < q` とする。(1) `X` は `M_σ` の Sylow `p`-部分群を中心化する;
(2) `p ∈ α(M)` なら `C_M(X) ∈ 𝒰`。原典 (a)(3)/(b) は
`beta_complement_normalizer_derived_contains_sylow` と
`beta_factorization_of_sylow_normalizer_in_intersection` として別 theorem に露出。 -/
theorem beta_complement_centralizes [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hpβ : p ∉ beta M) (hqβ : q ∉ beta M)
    {X : Subgroup G} (hXM : X ≤ M) (hXq : IsPGroup q ↥X)
    (hcase : X ≤ derivedInG M ∨ p < q) :
    (∃ S : Sylow p ↥(Msigma M),
      X ≤ Subgroup.centralizer
        (((S : Subgroup ↥(Msigma M)).map (Msigma M).subtype : Subgroup G) : Set G)) ∧
    (p ∈ alpha M → IsUniquelyMaximal (Subgroup.centralizer (X : Set G) ⊓ M)) := by
  obtain ⟨W, hXW, hWY, hWnil, hWhall⟩ :=
    exists_nilpotent_hall_pq hG hM hpq hpβ hqβ hXM hXq hcase
  -- **L2**: `W ∩ M_σ` is a Hall `{p,q}`-subgroup of `M_σ` (Hall ∩ normal, transported from
  -- `↥(XM')`).
  have hMσY : Msigma M ≤ X ⊔ derivedInG M := (Msigma_le_derived hG hM).trans le_sup_right
  have hMσYnorm : ((Msigma M).subgroupOf (X ⊔ derivedInG M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMσY).mpr
      ((sup_le hXM (Subgroup.map_subtype_le _)).trans (le_normalizer_opiCoreInG (sigma M) M))
  have hcomp : ((Msigma M).subtype.comp
        (Subgroup.subgroupOfEquivOfLe hMσY : _ →* _))
      = (X ⊔ derivedInG M).subtype.comp
          ((Msigma M).subgroupOf (X ⊔ derivedInG M)).subtype := by
    ext a; rfl
  have hcomapeq : (W.subgroupOf (Msigma M)).comap
        (Subgroup.subgroupOfEquivOfLe hMσY : _ →* _)
      = (W.subgroupOf (X ⊔ derivedInG M)).subgroupOf
          ((Msigma M).subgroupOf (X ⊔ derivedInG M)) := by
    rw [← Subgroup.comap_subtype W (Msigma M), Subgroup.comap_comap, hcomp,
        ← Subgroup.comap_comap]
    rfl
  have hmapeq : ((W.subgroupOf (X ⊔ derivedInG M)).subgroupOf
        ((Msigma M).subgroupOf (X ⊔ derivedInG M))).map
        (Subgroup.subgroupOfEquivOfLe hMσY : _ →* _) = W.subgroupOf (Msigma M) := by
    rw [← hcomapeq, Subgroup.map_comap_eq_self_of_surjective (MulEquiv.surjective _)]
  have hL2 : Ch03.IsHallSubgroup ({p, q} : Set ℕ) (W.subgroupOf (Msigma M)) := by
    rw [← hmapeq]
    exact isHallSubgroup_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hMσY)
      (Ch03.isHallSubgroup_subgroupOf_of_normal hWhall)
  -- **L4**: a Sylow `p`-subgroup of `M_σ` lying inside `W`, centralized by `X`.
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p ↥(W.subgroupOf (Msigma M))))
  have hpidx : ¬ p ∣ (W.subgroupOf (Msigma M)).index := fun hdvd =>
    hL2.2 p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩)
      (Set.mem_insert p {q})
  have hfactp : (Nat.card ↥(Msigma M)).factorization p =
      (Nat.card ↥(W.subgroupOf (Msigma M))).factorization p := by
    have h := Subgroup.card_mul_index (W.subgroupOf (Msigma M))
    have h2 : (Nat.card ↥(W.subgroupOf (Msigma M)) *
        (W.subgroupOf (Msigma M)).index).factorization p
        = (Nat.card ↥(Msigma M)).factorization p := by rw [h]
    rw [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero] at h2
    exact h2.symm
  set PσSub : Subgroup ↥(Msigma M) :=
    (P₀ : Subgroup ↥(W.subgroupOf (Msigma M))).map (W.subgroupOf (Msigma M)).subtype with hPσSub
  have hPσSub_card : Nat.card ↥PσSub = p ^ (Nat.card ↥(Msigma M)).factorization p := by
    rw [hPσSub, Subgroup.card_subtype, Sylow.card_eq_multiplicity P₀, hfactp]
  set Pσ : Sylow p ↥(Msigma M) := Sylow.ofCard PσSub hPσSub_card with hPσ
  have hPσcoe : (Pσ : Subgroup ↥(Msigma M)) = PσSub := Sylow.coe_ofCard _ _
  have hPσG_le_W :
      ((Pσ : Subgroup ↥(Msigma M)).map (Msigma M).subtype : Subgroup G) ≤ W := by
    rw [hPσcoe]
    calc PσSub.map (Msigma M).subtype
        ≤ (W.subgroupOf (Msigma M)).map (Msigma M).subtype :=
          Subgroup.map_mono (hPσSub ▸ Subgroup.map_subtype_le _)
      _ = W ⊓ Msigma M := Subgroup.subgroupOf_map_subtype W (Msigma M)
      _ ≤ W := inf_le_left
  have hPσG_pg : IsPGroup p ↥((Pσ : Subgroup ↥(Msigma M)).map (Msigma M).subtype) :=
    Pσ.2.of_equiv (Subgroup.equivMapOfInjective _ _ (Msigma M).subtype_injective)
  have hcent : X ≤ Subgroup.centralizer
      (((Pσ : Subgroup ↥(Msigma M)).map (Msigma M).subtype : Subgroup G) : Set G) :=
    isPGroup_le_centralizer_of_isNilpotent_ambient hWnil hpq hXW hPσG_le_W hXq hPσG_pg
  refine ⟨⟨Pσ, hcent⟩, ?_⟩
  -- **(a)(2)**: `p ∈ α(M)` ⟹ `P_σ` has `p`-rank ≥ 3, so a rank-2 elem-ab `A ≤ P_σ` is non-maximal
  -- (it sits in a rank-3 one), hence `A ∈ 𝒰` (Uniqueness Theorem), and `C_M(X) ⊇ A` is in `𝒰`.
  intro hpα
  have hpπM : p ∈ (Nat.card ↥M).primeFactors := hpα.1
  have hpRankM : 3 ≤ pRank ↥M p := hpα.2
  have hp_odd : Odd p :=
    hG.odd.of_dvd_nat (dvd_trans (Nat.mem_primeFactors.mp hpπM).2.1
      (Subgroup.card_subgroup_dvd_card M))
  have hpσ : p ∈ sigma M := alpha_subset_sigma hG hM hpα
  have hMσM : Msigma M ≤ M := opiCoreInG_le (sigma M) M
  set PσG : Subgroup G := (Pσ : Subgroup ↥(Msigma M)).map (Msigma M).subtype with hPσGdef
  -- `M_σ` is `σ`-Hall in `M`; with `p ∈ σ`, `|M_σ|` and `|M|` share `p`-part.
  have hMσHallM : Ch03.IsHallSubgroup (sigma M) ((Msigma M).subgroupOf M) :=
    Msigma_subgroupOf_isHall_of_isHall (isHall_Msigma_Malpha hG hM).1
  have hpidxM : ¬ p ∣ ((Msigma M).subgroupOf M).index := fun hdvd =>
    hMσHallM.2 p (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpσ
  have hfactM : (Nat.card ↥(Msigma M)).factorization p = (Nat.card ↥M).factorization p := by
    have hcardeq : Nat.card ↥((Msigma M).subgroupOf M) = Nat.card ↥(Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    have h := Subgroup.card_mul_index ((Msigma M).subgroupOf M)
    rw [hcardeq] at h
    have h2 : (Nat.card ↥(Msigma M) * ((Msigma M).subgroupOf M).index).factorization p
        = (Nat.card ↥M).factorization p := by rw [h]
    rwa [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidxM, add_zero] at h2
  -- `P_σ` (a Sylow `p` of `M_σ`) has the full `p`-part of `M`, so it is a Sylow `p` of `M`.
  have hPσG_le_Mσ : PσG ≤ Msigma M := Subgroup.map_subtype_le _
  have hPσG_le_M : PσG ≤ M := hPσG_le_Mσ.trans hMσM
  have hPσGcard : Nat.card ↥PσG = p ^ (Nat.card ↥M).factorization p := by
    rw [hPσGdef, Subgroup.card_subtype, Sylow.card_eq_multiplicity Pσ, hfactM]
  have hPMcard : Nat.card ↥(PσG.subgroupOf M) = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPσG_le_M).toEquiv, hPσGcard]
  set PM : Sylow p ↥M := Sylow.ofCard (PσG.subgroupOf M) hPMcard with hPMdef
  have hpRankPσG : 3 ≤ pRank ↥PσG p := by
    have e1 : pRank ↥(PσG.subgroupOf M) p = pRank ↥M p := by
      have h := pRank_sylow_eq PM
      rwa [hPMdef, Sylow.coe_ofCard] at h
    have e2 : pRank ↥(PσG.subgroupOf M) p = pRank ↥PσG p :=
      le_antisymm
        (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hPσG_le_M).toMonoidHom)
          (MulEquiv.injective _))
        (pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hPσG_le_M).symm.toMonoidHom)
          (MulEquiv.injective _))
    rw [← e2, e1]; exact hpRankM
  -- extract a rank-3 elem-ab `B ≤ P_σ`, then a rank-2 `A ≤ B`; `A` is non-maximal.
  obtain ⟨B, hB_elem, hB_log⟩ :=
    exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥PσG) (n := 3)
      (by norm_num) hpRankPσG
  set BG : Subgroup G := B.map PσG.subtype with hBGdef
  have hBG_elem : BG.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map PσG.subtype_injective hB_elem
  have hBG_le_PσG : BG ≤ PσG := Subgroup.map_subtype_le _
  have hBG_log : 3 ≤ Nat.log p (Nat.card ↥BG) := by
    rwa [hBGdef, Subgroup.card_map_of_injective PσG.subtype_injective]
  have hBG_nc : ¬ IsCyclic ↥BG :=
    not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hBG_elem (by omega)
  obtain ⟨A₀, hA₀_elem, hA₀_card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      hBG_elem.isPGroup hp_odd hBG_nc
  set A : Subgroup G := A₀.map BG.subtype with hAdef
  have hA_elem : A.IsElementaryAbelian p :=
    Subgroup.IsElementaryAbelian.map BG.subtype_injective hA₀_elem
  have hA_le_BG : A ≤ BG := Subgroup.map_subtype_le _
  have hA_card : Nat.card ↥A = p ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective BG.subtype_injective, hA₀_card]
  have hA2 : A ∈ elemAbelianOfRank G p 2 := mem_elemAbelianOfRank.mpr ⟨hA_elem, hA_card⟩
  -- `A` is not maximal: `B ⊋ A` is a strictly larger elem-ab.
  have hAns : ¬ IsMaximalElementaryAbelian p A := by
    rintro ⟨-, hmax⟩
    have hBA : BG = A := hmax BG hBG_elem hA_le_BG
    have hp3 : p ^ 3 ≤ Nat.card ↥BG :=
      (Nat.le_log_iff_pow_le (Fact.out : p.Prime).one_lt Nat.card_pos.ne').mp hBG_log
    rw [hBA, hA_card] at hp3
    have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num)
    omega
  have hAU : IsUniquelyMaximal A :=
    OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_mem_e2_not_maximal hG hA2 hAns
  -- `A ≤ C_G(X) ⊓ M`, proper, so `C_M(X) ∈ 𝒰` by monotonicity.
  have hPσG_le_cent : PσG ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.le_centralizer_iff.mp hcent
  have hA_le : A ≤ Subgroup.centralizer (X : Set G) ⊓ M :=
    le_inf ((hA_le_BG.trans hBG_le_PσG).trans hPσG_le_cent)
      ((hA_le_BG.trans hBG_le_PσG).trans hPσG_le_M)
  have hCXM_lt : Subgroup.centralizer (X : Set G) ⊓ M < ⊤ :=
    lt_of_le_of_lt inf_le_right (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hM).1)
  exact isUniquelyMaximal_of_le_of_lt_top hAU hA_le hCXM_lt

/-- A `π`-Hall subgroup `H` of `G` contained in `K` is also `π`-Hall in `K` (`H.subgroupOf K`):
`|H ∩ K| = |H|` (`H ≤ K`) so its prime factors stay in `π`, and `[K:H] = H.relIndex K ∣ [G:H]`
is a `π'`-number. Used to descend `M_β` (Hall `β(G)`) to a Hall `β`-subgroup of `M'`. -/
theorem isHallSubgroup_subgroupOf_of_le [Finite G] {π : Set ℕ} {H K : Subgroup G}
    (hH : Ch03.IsHallSubgroup π H) (hHK : H ≤ K) :
    Ch03.IsHallSubgroup π (H.subgroupOf K) := by
  refine ⟨fun r hr => hH.1 r ?_, fun r hr hrπ => hH.2 r ?_ hrπ⟩
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv] at hr
  · rw [Nat.mem_primeFactors] at hr ⊢
    exact ⟨hr.1, hr.2.1.trans (Subgroup.relIndex_dvd_index_of_le hHK),
      Subgroup.index_ne_zero_of_finite⟩

/-- **M'/M_β is nilpotent** (consequence of Lemma 10.8, mmd L3322/L3534, forward-conditional):
`M' = derivedInG M` modulo its Hall `β(M)`-subgroup `M_β` is nilpotent. `M'` has a nilpotent
Hall `β(M)'`-subgroup `W*` (Lemma 10.8(b)) and `M_β` (Hall `β(G)`, normal in `M'`) is a complement,
so `M' = M_β W*` and the quotient `M'/M_β` is a surjective image of the nilpotent `W*`. -/
theorem derivedQuotientMbeta_isNilpotent [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    [((Mbeta M).subgroupOf (derivedInG M)).Normal] :
    Group.IsNilpotent (↥(derivedInG M) ⧸ (Mbeta M).subgroupOf (derivedInG M)) := by
  obtain ⟨Wstar, hWstar_le, hWstar_hall, hWstar_nilp⟩ := (isHall_Mbeta hG hM).2.1
  have hβσ : beta M ⊆ sigma M := fun r hr => alpha_subset_sigma hG hM (beta_subset_alpha M hr)
  have hMβD : Mbeta M ≤ derivedInG M :=
    le_trans (Subgroup.map_mono (Ch03.oPiCore_mono hβσ ↥M)) (Msigma_le_derived hG hM)
  have hWstar'_nilp : Group.IsNilpotent ↥(Wstar.subgroupOf (derivedInG M)) :=
    Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hWstar_le).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hMβHall : Ch03.IsHallSubgroup (beta M) ((Mbeta M).subgroupOf (derivedInG M)) :=
    isHallSubgroup_subgroupOf_of_le (isHall_Mbeta hG hM).1 hMβD
  -- `W* ⊔ M_β = ⊤` in `↥M'` (their indices are coprime: `β'` resp. `β`).
  have hsup : Wstar.subgroupOf (derivedInG M) ⊔ (Mbeta M).subgroupOf (derivedInG M) = ⊤ := by
    apply Ch03.sup_eq_top_of_coprime_index
    apply Nat.coprime_of_dvd
    intro r hr hrW hrMβ
    have hrβ : r ∈ beta M := by
      by_contra hc
      exact hWstar_hall.2 r
        (Nat.mem_primeFactors.mpr ⟨hr, hrW, Subgroup.index_ne_zero_of_finite⟩) hc
    exact hMβHall.2 r
      (Nat.mem_primeFactors.mpr ⟨hr, hrMβ, Subgroup.index_ne_zero_of_finite⟩) hrβ
  -- the surjection `W* ↪ M' → M'/M_β`.
  set f : ↥(Wstar.subgroupOf (derivedInG M)) →*
      (↥(derivedInG M) ⧸ (Mbeta M).subgroupOf (derivedInG M)) :=
    (QuotientGroup.mk' ((Mbeta M).subgroupOf (derivedInG M))).comp
      (Wstar.subgroupOf (derivedInG M)).subtype with hf
  have hmaptop : (Wstar.subgroupOf (derivedInG M)).map
      (QuotientGroup.mk' ((Mbeta M).subgroupOf (derivedInG M))) = ⊤ := by
    have h := QuotientGroup.comap_map_mk' ((Mbeta M).subgroupOf (derivedInG M))
      (Wstar.subgroupOf (derivedInG M))
    rw [sup_comm, hsup] at h
    exact Subgroup.comap_injective (QuotientGroup.mk'_surjective _)
      (h.trans (Subgroup.comap_top _).symm)
  have hrange : f.range = ⊤ := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hmaptop]
  exact Group.nilpotent_of_surjective f (MonoidHom.range_eq_top.mp hrange)

/-- **`N ⊔ Q` is normal when `Γ/N` is nilpotent** (`N` a `q'`-group, `Q` a Sylow `q`-subgroup):
the image `Q̄ = Q.map (mk' N)` is a Sylow `q`-subgroup of the nilpotent `Γ/N`, hence normal, and
`N ⊔ Q = (mk' N)⁻¹(Q̄)` is normal as the preimage of a normal subgroup. Used in Corollary 10.9(a)(3)
with `Γ = ↥M'`, `N = M_β`, `Q = X` to get `M_β X ◁ M'` (the Frattini setup). -/
theorem normal_sup_sylow_of_quotient_nilpotent {Γ : Type*} [Group Γ] [Finite Γ]
    {N : Subgroup Γ} [N.Normal] (hNil : Group.IsNilpotent (Γ ⧸ N)) {q : ℕ} [Fact q.Prime]
    (hNq' : ¬ q ∣ Nat.card ↥N) (Q : Sylow q Γ) :
    (N ⊔ (Q : Subgroup Γ)).Normal := by
  have hQN : (Q : Subgroup Γ) ⊓ N = ⊥ := by
    apply Subgroup.card_eq_one.mp
    by_contra hne
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp
      (hr_prime.dvd_of_dvd_pow (hk ▸ hr_dvd.trans (Subgroup.card_dvd_of_le inf_le_left)))
    exact hNq' (hrq ▸ hr_dvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  -- `mk' N` is injective on `Q`, so `|Q.map (mk' N)| = |Q|`.
  have hg_inj : Function.Injective ((QuotientGroup.mk' N).comp (Q : Subgroup Γ).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      Subgroup.comap_subtype, Subgroup.subgroupOf_eq_bot]
    exact disjoint_iff.mpr (by rw [inf_comm]; exact hQN)
  have hcard : Nat.card ↥((Q : Subgroup Γ).map (QuotientGroup.mk' N)) =
      Nat.card ↥(Q : Subgroup Γ) := by
    have hr : ((QuotientGroup.mk' N).comp (Q : Subgroup Γ).subtype).range =
        (Q : Subgroup Γ).map (QuotientGroup.mk' N) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr]
    exact (Nat.card_congr (MonoidHom.ofInjective hg_inj).toEquiv).symm
  -- so `Q.map (mk' N)` is a Sylow `q`-subgroup of `Γ/N`.
  have hSylcard : Nat.card ↥((Q : Subgroup Γ).map (QuotientGroup.mk' N)) =
      q ^ (Nat.card (Γ ⧸ N)).factorization q := by
    rw [hcard, Sylow.card_eq_multiplicity Q]
    congr 1
    have hsplit : Nat.card Γ = Nat.card (Γ ⧸ N) * Nat.card ↥N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hsplit, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hNq', add_zero]
  set Qbar : Sylow q (Γ ⧸ N) := Sylow.ofCard _ hSylcard with hQbar
  have hQbar_eq : (Q : Subgroup Γ).map (QuotientGroup.mk' N) = (Qbar : Subgroup (Γ ⧸ N)) := by
    rw [hQbar, Sylow.coe_ofCard]
  have hAllNormal : ∀ (r : ℕ), Fact r.Prime → ∀ (R : Sylow r (Γ ⧸ N)),
      (↑R : Subgroup (Γ ⧸ N)).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := Γ ⧸ N)).out 0 3).mp hNil
  have hQbar_norm : (Qbar : Subgroup (Γ ⧸ N)).Normal := hAllNormal q ‹Fact q.Prime› Qbar
  rw [show N ⊔ (Q : Subgroup Γ) =
      ((Q : Subgroup Γ).map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) from
      (QuotientGroup.comap_map_mk' N (Q : Subgroup Γ)).symm, hQbar_eq]
  exact hQbar_norm.comap (QuotientGroup.mk' N)

/-- **BG Corollary 10.9(b)** (mmd L2826): if `H ∈ ℳ - {M}` and `N_G(S) ⊆ H ∩ M` for some
Sylow subgroup `S` of `G`, then `M = (H ∩ M)M_β` and `α(M)=β(M)`.

The product is encoded as subgroup join, matching the existing convention for normal-factor
statements in §12. -/
theorem beta_factorization_of_sylow_normalizer_in_intersection [Finite G]
    (hG : IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G) (hHM : H ≠ M)
    {q : ℕ} [Fact q.Prime] (S : Sylow q G)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ H ⊓ M) :
    M = (H ⊓ M) ⊔ Mbeta M ∧ alpha M = beta M := by
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMc : IsCoatom M := mem_maximalSubgroups.mp hM
  have hM_lt : M < ⊤ := lt_top_iff_ne_top.mpr hMc.1
  set D : Subgroup G := derivedInG M with hD
  have hDM : D ≤ M := Subgroup.map_subtype_le _
  -- `S ⊆ N_G(S) ⊆ H ⊓ M`, so `S ≤ M` and `S ≤ H`.
  have hS_le_HM : (S : Subgroup G) ≤ M ⊓ H :=
    le_inf ((Subgroup.le_normalizer.trans hN).trans inf_le_right)
      ((Subgroup.le_normalizer.trans hN).trans inf_le_left)
  have hS_le_M : (S : Subgroup G) ≤ M := hS_le_HM.trans inf_le_left
  -- `S ≠ 1`: otherwise `N_G(S) = ⊤ ⊄ M`.
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    refine hMc.1 (top_le_iff.mp ((?_ : (⊤ : Subgroup G) ≤ _).trans (hN.trans inf_le_right)))
    rw [hbot]
    intro g _; rw [Subgroup.mem_normalizer_iff]; intro h; simp [Subgroup.mem_bot]
  -- `q ∈ π(M)`.
  have hq_prime : q.Prime := Fact.out
  have hqπ : q ∈ (Nat.card ↥M).primeFactors := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (Subgroup.card_eq_one.mp (by rw [hn, h, pow_zero])) hSne
      · exact h
    exact Nat.mem_primeFactors.mpr ⟨hq_prime,
      (dvd_pow_self q hn0.ne').trans (hn ▸ Subgroup.card_dvd_of_le hS_le_M), Nat.card_pos.ne'⟩
  -- `q ∈ σ(M)`: `S` is a Sylow `q`-subgroup of `M` with `N_G(S) ⊆ M`.
  obtain ⟨QM, hQM⟩ := exists_sylow_subgroupOf_of_le S hS_le_M
  have hQM_map : (QM : Subgroup ↥M).map M.subtype = (S : Subgroup G) := by
    rw [hQM, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS_le_M]
  have hqσ : q ∈ sigma M := by
    rw [mem_sigma_iff]
    exact ⟨hqπ, QM, by rw [hQM_map]; exact hN.trans inf_le_right⟩
  -- `q ∉ α(M)`: else `r(S) ≥ 3` makes `S` uniquely maximal, contradicting `S ≤ M ⊓ H`, `H ≠ M`.
  have hqα : q ∉ alpha M := by
    rw [mem_alpha_iff]
    rintro ⟨-, hr3⟩
    have hrank3 : 3 ≤ rank ↥(S : Subgroup G) :=
      calc (3 : ℕ) ≤ pRank ↥M q := hr3
        _ = pRank ↥(QM : Subgroup ↥M) q := (pRank_sylow_eq QM).symm
        _ ≤ pRank ↥(S : Subgroup G) q := by
            rw [hQM]
            exact pRank_le_of_injective (f := (Subgroup.subgroupOfEquivOfLe hS_le_M).toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hS_le_M).injective
        _ ≤ rank ↥(S : Subgroup G) := pRank_le_rank q
    have hSlt : (S : Subgroup G) < ⊤ := hS_le_M.trans_lt hM_lt
    have hSU : IsUniquelyMaximal (S : Subgroup G) :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_three_le_rank_of_lt_top hG hSlt hrank3
    exact OddOrder.BG.Ch2.S09.not_isUniquelyMaximal_of_le_inf_distinct_maximals
      hM hH hS_le_HM hHM hSU
  have hqβ : q ∉ beta M := fun h => hqα (beta_subset_alpha M h)
  -- `S ⊆ M_σ ⊆ M' = D`.
  have hS_pi : Ch03.Subgroup.IsPiGroup (sigma M) (S : Subgroup G) := by
    intro r hr
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hr_prime := (Nat.mem_primeFactors.mp hr).1
    have hrq : r = q :=
      (Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp
        (hr_prime.dvd_of_dvd_pow (hn ▸ (Nat.mem_primeFactors.mp hr).2.1))
    rw [hrq]; exact hqσ
  have hS_le_Msigma : (S : Subgroup G) ≤ Msigma M :=
    sigma_subgroup_le_Msigma_of_isHall (Msigma_isHall hG hM) hS_le_M hS_pi
  have hS_le_D : (S : Subgroup G) ≤ D := hS_le_Msigma.trans (Msigma_le_derived hG hM)
  -- `S` as a Sylow `q`-subgroup of `↥D = M'`.
  obtain ⟨XD, hXD⟩ := exists_sylow_subgroupOf_of_le S hS_le_D
  have hS_card : Nat.card ↥(S : Subgroup G) = q ^ (Nat.card ↥D).factorization q := by
    have h1 : Nat.card ↥(XD : Subgroup ↥D) = q ^ (Nat.card ↥D).factorization q :=
      XD.card_eq_multiplicity
    rwa [hXD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_D).toEquiv] at h1
  -- `C_M(S) ≤ M ⊓ H`, hence `C_M(S) ∉ 𝒰` (two distinct maximals).
  have hCle : Subgroup.centralizer ((S : Subgroup G) : Set G) ⊓ M ≤ M ⊓ H :=
    le_inf inf_le_right (le_trans inf_le_left
      (le_trans (Subgroup.centralizer_le_normalizer _) (hN.trans inf_le_left)))
  refine ⟨?_, ?_⟩
  · -- `M = (H ⊓ M) ⊔ M_β` via the Frattini argument `M = (M_β·S)·N_M(S) = M_β·N_M(S)`.
    set U : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G) ⊓ M with hU
    have hMβD : Mbeta M ≤ D :=
      le_trans (Subgroup.map_mono (Ch03.oPiCore_mono
        (fun r hr => alpha_subset_sigma hG hM (beta_subset_alpha M hr)) ↥M))
        (Msigma_le_derived hG hM)
    have hMβnorm : ((Mbeta M).subgroupOf D).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMβD).mpr
        (hDM.trans (le_normalizer_opiCoreInG (beta M) M))
    have hNq' : ¬ q ∣ Nat.card ↥((Mbeta M).subgroupOf D) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMβD).toEquiv]
      exact fun hdvd => hqβ (isPiSubgroup_opiCoreInG (beta M) M q
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩))
    have hMβXnorm : ((Mbeta M).subgroupOf D ⊔ (XD : Subgroup ↥D)).Normal :=
      normal_sup_sylow_of_quotient_nilpotent (derivedQuotientMbeta_isNilpotent hG hM) hNq' XD
    set K : Subgroup G := opiCoreInG (beta M ∪ {q}) D with hK
    have hKD : K ≤ D := opiCoreInG_le _ _
    set MβX : Subgroup G := ((Mbeta M).subgroupOf D ⊔ (XD : Subgroup ↥D)).map D.subtype with hMβX
    -- `MβX = M_β ⊔ S` (carrier of the join lifted to `G`).
    have hMβX_eq : MβX = Mbeta M ⊔ (S : Subgroup G) := by
      rw [hMβX, hXD, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMβD,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS_le_D]
    have hMβX_le_D : MβX ≤ D := Subgroup.map_subtype_le _
    have hMβX_pi : Subgroup.IsPiSubgroup (beta M ∪ {q}) MβX := by
      intro r hr
      rw [hMβX, Subgroup.card_map_of_injective D.subtype_injective] at hr
      have hdvd : Nat.card ↥((Mbeta M).subgroupOf D ⊔ (XD : Subgroup ↥D)) ∣
          Nat.card ↥((Mbeta M).subgroupOf D) * Nat.card ↥(XD : Subgroup ↥D) := by
        have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
          ((Mbeta M).subgroupOf D) (XD : Subgroup ↥D)
        rw [show (↑((Mbeta M).subgroupOf D) * ↑(XD : Subgroup ↥D) : Set ↥D)
            = ↑((Mbeta M).subgroupOf D ⊔ (XD : Subgroup ↥D) : Subgroup ↥D) from
            (Subgroup.normal_mul ((Mbeta M).subgroupOf D) (XD : Subgroup ↥D)).symm] at hform
        exact ⟨_, hform.symm⟩
      have hr_prime := Nat.prime_of_mem_primeFactors hr
      rcases (Nat.Prime.dvd_mul hr_prime).mp ((Nat.mem_primeFactors.mp hr).2.1.trans hdvd)
        with h | h
      · exact Or.inl (isPiSubgroup_opiCoreInG (beta M) M r
          (Nat.mem_primeFactors.mpr ⟨hr_prime,
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMβD).toEquiv) ▸ h, Nat.card_pos.ne'⟩))
      · refine Or.inr ?_
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp XD.isPGroup'
        exact (Nat.prime_dvd_prime_iff_eq hr_prime Fact.out).mp (hr_prime.dvd_of_dvd_pow (hk ▸ h))
    have hMβX_le_K : MβX ≤ K := by
      rw [hK, hMβX]
      refine le_opiCoreInG_of_normal_of_isPiSubgroup hMβX_le_D ?_ (hMβX ▸ hMβX_pi)
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
      exact hMβXnorm
    have hS_le_K : (S : Subgroup G) ≤ K := le_trans (hMβX_eq ▸ le_sup_right) hMβX_le_K
    have hKq_card : (Nat.card ↥K).factorization q = (Nat.card ↥D).factorization q := by
      refine le_antisymm
        ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
          (Subgroup.card_dvd_of_le hKD) q) ?_
      have hdvd : q ^ (Nat.card ↥D).factorization q ∣ Nat.card ↥K :=
        hS_card ▸ Subgroup.card_dvd_of_le hS_le_K
      exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
    have hKnorm : (K.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hKD.trans hDM)).mpr
        (le_normalizer_opiCoreInG_of_le_normalizer (beta M ∪ {q}) (le_normalizer_derivedInG M))
    -- **Frattini**: `M = K · N_M(S)`.
    have hSK_card : Nat.card ↥(((S : Subgroup G).subgroupOf M).subgroupOf (K.subgroupOf M)) =
        q ^ (Nat.card ↥(K.subgroupOf M)).factorization q := by
      have hle : (S : Subgroup G).subgroupOf M ≤ K.subgroupOf M :=
        Subgroup.subgroupOf_mono M hS_le_K
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS_le_M).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKD.trans hDM)).toEquiv, hS_card, hKq_card]
    set P : Sylow q ↥(K.subgroupOf M) :=
      Sylow.ofCard (((S : Subgroup G).subgroupOf M).subgroupOf (K.subgroupOf M)) hSK_card with hP
    have hPmap : (P : Subgroup ↥(K.subgroupOf M)).map (K.subgroupOf M).subtype =
        (S : Subgroup G).subgroupOf M := by
      rw [hP, Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (Subgroup.subgroupOf_mono M hS_le_K)]
    have hFrattini := Sylow.normalizer_sup_eq_top P
    rw [hPmap, ← Subgroup.subgroupOf_normalizer_eq hS_le_M] at hFrattini
    have hUeq : (Subgroup.normalizer ((S : Subgroup G) : Set G)).subgroupOf M = U.subgroupOf M := by
      rw [hU, Subgroup.inf_subgroupOf_right]
    rw [hUeq] at hFrattini
    have hKUtop : K.subgroupOf M ⊔ U.subgroupOf M = ⊤ := by rw [sup_comm]; exact hFrattini
    -- **`K = O_{β∪{q}}(M') = M_β X = M_β ⊔ S`**: both are the `{β∪q}`-radical of `M'`.
    -- `MβX ≤ K` (have); for the reverse, compare orders.
    have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hMβ_hall := Mbeta_isHall hG hM
    -- `b = |S| = q ^ (fact_q |M'|)`.
    have hb_eq : Nat.card ↥(XD : Subgroup ↥D) = q ^ (Nat.card ↥D).factorization q :=
      XD.card_eq_multiplicity
    -- `(|M_β|, |S|) = 1` (`M_β` is a `β`-group, `q ∉ β`).
    have hMβ_pf : ∀ r ∈ (Nat.card ↥(Mbeta M)).primeFactors, r ∈ beta M := hMβ_hall.1
    have hcop_ab : Nat.Coprime (Nat.card ↥(Mbeta M)) (Nat.card ↥(XD : Subgroup ↥D)) := by
      rw [hb_eq]
      exact Nat.Coprime.pow_right _
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
        (fun hqdvd =>
          hqβ (hMβ_pf q (Nat.mem_primeFactors.mpr ⟨Fact.out, hqdvd, Nat.card_pos.ne'⟩)))))
    have hMβ'_card : Nat.card ↥((Mbeta M).subgroupOf D) = Nat.card ↥(Mbeta M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMβD).toEquiv
    have hMβX_card : Nat.card ↥MβX =
        Nat.card ↥(Mbeta M) * Nat.card ↥(XD : Subgroup ↥D) := by
      rw [hMβX, Subgroup.card_map_of_injective D.subtype_injective]
      have hform := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
        ((Mbeta M).subgroupOf D) (XD : Subgroup ↥D)
      have hinter : Nat.card ↥((Mbeta M).subgroupOf D ⊓ (XD : Subgroup ↥D)) = 1 :=
        Nat.dvd_one.mp (((hMβ'_card ▸ hcop_ab : Nat.Coprime (Nat.card ↥((Mbeta M).subgroupOf D))
          (Nat.card ↥(XD : Subgroup ↥D))).gcd_eq_one) ▸ Nat.dvd_gcd
          (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
      rw [show (↑((Mbeta M).subgroupOf D) * ↑(XD : Subgroup ↥D) : Set ↥D)
          = ↑((Mbeta M).subgroupOf D ⊔ (XD : Subgroup ↥D)) from
          (Subgroup.normal_mul _ _).symm, hinter, mul_one, hMβ'_card] at hform
      exact hform
    -- For `p ∈ β`: `fact_p |D| = fact_p |M_β|` (`M_β` Hall `β` of `G`, squeeze via `M_β ≤ D ≤ G`).
    have hfacD : ∀ p, p ∈ beta M → p.Prime →
        (Nat.card ↥D).factorization p = (Nat.card ↥(Mbeta M)).factorization p := by
      intro p hpβ' hp_prime
      have hidx : ¬ p ∣ (Mbeta M).index := fun hdvd =>
        hMβ_hall.2 p (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd,
          Subgroup.index_ne_zero_of_finite⟩) hpβ'
      have haG : (Nat.card ↥(Mbeta M)).factorization p = (Nat.card G).factorization p := by
        have h2 : (Nat.card ↥(Mbeta M) * (Mbeta M).index).factorization p =
            (Nat.card G).factorization p := by rw [Subgroup.card_mul_index]
        rwa [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
          Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hidx, add_zero] at h2
      refine le_antisymm ?_ ?_
      · rw [haG]
        exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hG0).mpr
          (Subgroup.card_subgroup_dvd_card D) p
      · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
          (Subgroup.card_dvd_of_le hMβD) p
    -- `|K| ∣ |M_β| · |S|`, so (with `MβX ≤ K`) `K = MβX = M_β ⊔ S`.
    have hKdvd : Nat.card ↥K ∣ Nat.card ↥(Mbeta M) * Nat.card ↥(XD : Subgroup ↥D) := by
      rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')]
      intro p
      rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
      by_cases hp_prime : p.Prime
      · by_cases hpβ' : p ∈ beta M
        · calc (Nat.card ↥K).factorization p
              ≤ (Nat.card ↥D).factorization p :=
                (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
                  (Subgroup.card_dvd_of_le hKD) p
            _ = (Nat.card ↥(Mbeta M)).factorization p := hfacD p hpβ' hp_prime
            _ ≤ _ := Nat.le_add_right _ _
        · by_cases hpq' : p = q
          · subst hpq'
            have hMβq : (Nat.card ↥(Mbeta M)).factorization p = 0 :=
              Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hpβ'
                (hMβ_pf p (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, Nat.card_pos.ne'⟩)))
            have hXDq : (Nat.card ↥(XD : Subgroup ↥D)).factorization p =
                (Nat.card ↥D).factorization p := by
              rw [hb_eq, Nat.Prime.factorization_pow hp_prime, Finsupp.single_eq_same]
            rw [hMβq, hXDq, zero_add, hKq_card]
          · have hpnd : ¬ p ∣ Nat.card ↥K := fun hdvd => by
              rcases isPiSubgroup_opiCoreInG (beta M ∪ {q}) D p
                (Nat.mem_primeFactors.mpr ⟨hp_prime, by rw [← hK]; exact hdvd, Nat.card_pos.ne'⟩)
                with h | h
              · exact hpβ' h
              · exact hpq' (Set.mem_singleton_iff.mp h)
            rw [Nat.factorization_eq_zero_of_not_dvd hpnd]
            exact Nat.zero_le _
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime]
        exact Nat.zero_le _
    have hKeq : K = Mbeta M ⊔ (S : Subgroup G) := by
      rw [← hMβX_eq]
      refine (Subgroup.eq_of_le_of_card_ge hMβX_le_K ?_).symm
      rw [hMβX_card]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero
        (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')) hKdvd
    -- map `hKUtop` up to `G`: `K ⊔ U = M`.
    have hKU : K ⊔ U = M := by
      have h := congrArg (Subgroup.map M.subtype) hKUtop
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hKD.trans hDM),
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right : U ≤ M),
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    -- assemble `M = M_β ⊔ N_M(S) = (H ⊓ M) ⊔ M_β`.
    have hS_le_U : (S : Subgroup G) ≤ U := le_inf Subgroup.le_normalizer hS_le_M
    have hU_le_HM : U ≤ H ⊓ M := inf_le_left.trans hN
    refine le_antisymm ?_ (sup_le inf_le_right (Mbeta_le M))
    calc M = K ⊔ U := hKU.symm
      _ = Mbeta M ⊔ U := by rw [hKeq, sup_assoc, sup_eq_right.mpr hS_le_U]
      _ ≤ Mbeta M ⊔ (H ⊓ M) := sup_le_sup_left hU_le_HM _
      _ = (H ⊓ M) ⊔ Mbeta M := sup_comm _ _
  · -- `α(M) = β(M)`: for `p ∈ α(M) − β(M)` (necessarily `p ≠ q`), Cor 10.9(a)(2) gives
    -- `C_M(S) ∈ 𝒰`, contradicting `C_M(S) ≤ M ⊓ H` (`H ≠ M`).
    refine Set.Subset.antisymm (fun p hp => ?_) (beta_subset_alpha M)
    by_contra hpβ
    have : Fact p.Prime := ⟨(Nat.mem_primeFactors.mp (alpha_subset_primeFactors M hp)).1⟩
    have hpq : p ≠ q := fun h => hqα (h ▸ hp)
    have hU := (beta_complement_centralizes hG hM hpq hpβ hqβ hS_le_M S.isPGroup'
      (Or.inl hS_le_D)).2 hp
    exact OddOrder.BG.Ch2.S09.not_isUniquelyMaximal_of_le_inf_distinct_maximals hM hH hCle hHM hU

/-- **Prop 10.10 prep**: `A ∈ ℰ_p²(G) ∩ ℰ_p^*(G)` satisfies BG Hypothesis 7.1, via Proposition
7.5 case (1): `A = Ω₁(C_G(A))` (from maximality of `A` as elementary abelian — any `p`-torsion
element of `C_G(A)` generates with `A` an elementary abelian group, which collapses to `A`) and
every proper subgroup of `G` has `p`-length one (Theorem 10.6, `proper_hasPLengthOne`). Mirrors
the Hypothesis 7.1 step of `S11_ExceptionalMaximal`. -/
private theorem hypothesis71_of_mem_elemAbelianOfRank_two_of_maximal [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAmax : IsMaximalElementaryAbelian p A) :
    Ch2.S07.Hypothesis71 A := by
  have hAelem : A.IsElementaryAbelian p := hA.1
  have hAcomm : IsMulCommutative ↥A := ⟨⟨fun x y => hAelem.comm x y⟩⟩
  have hAcard : Nat.card ↥A = p ^ 2 := hA.2
  have hpG : p ∣ Nat.card G := by
    have hdvd : Nat.card ↥A ∣ Nat.card G := Subgroup.card_subgroup_dvd_card A
    rw [hAcard] at hdvd
    exact dvd_trans (dvd_pow_self p (by norm_num)) hdvd
  refine Ch2.S07.hypothesis71_of_scn2_or_pLengthOne hG hpG A hAcomm hAelem.isPGroup
    (Or.inl ⟨?_, fun N hN => proper_hasPLengthOne hG N hN⟩)
  -- `(A : Set G) = {x | x ∈ C_G(A) ∧ x ^ p = 1}` (maximality of `A`).
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro hx
    refine ⟨Subgroup.le_centralizer (H := A) hx, ?_⟩
    have hxp1 : (⟨x, hx⟩ : ↥A) ^ p = 1 := hAelem.2 _
    have := congrArg (Subgroup.subtype A) hxp1
    simpa using this
  · rintro ⟨hxc, hxp⟩
    have hgen_comm : ∀ a ∈ (A : Set G) ∪ {x}, ∀ b ∈ (A : Set G) ∪ {x}, a * b = b * a := by
      rintro a (ha | ha) b (hb | hb)
      · have := hAelem.comm ⟨a, ha⟩ ⟨b, hb⟩
        simpa using congrArg (Subgroup.subtype A) this
      · rw [Set.mem_singleton_iff] at hb; subst hb; exact hxc a ha
      · rw [Set.mem_singleton_iff] at ha; subst ha; exact (hxc b hb).symm
      · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
    set B : Subgroup G := Subgroup.closure ((A : Set G) ∪ {x}) with hB_def
    have hBcomm : IsMulCommutative ↥B := Subgroup.isMulCommutative_closure hgen_comm
    have hgen_pow : ∀ w ∈ (A : Set G) ∪ {x}, w ^ p = 1 := by
      rintro w (hw | hw)
      · have := hAelem.2 ⟨w, hw⟩; simpa using congrArg (Subgroup.subtype A) this
      · rw [Set.mem_singleton_iff] at hw; subst hw; exact hxp
    have hBclos_comm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => by
      have := hBcomm.is_comm.comm (⟨a, ha⟩ : ↥B) ⟨b, hb⟩
      simpa using congrArg (Subgroup.subtype B) this
    have hclos_pow : ∀ y ∈ Subgroup.closure ((A : Set G) ∪ {x}), y ^ p = 1 := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz => exact hgen_pow z hz
      | one => simp
      | mul z₁ z₂ hz₁ hz₂ h₁ h₂ =>
          have hc : Commute z₁ z₂ := hBclos_comm z₁ hz₁ z₂ hz₂
          rw [hc.mul_pow, h₁, h₂, mul_one]
      | inv z _ h => rw [inv_pow, h, inv_one]
    have hB_pow : ∀ u : ↥B, u ^ p = 1 := fun u =>
      Subtype.ext (by simpa using hclos_pow (u : G) u.2)
    have hBelem : B.IsElementaryAbelian p := ⟨fun u v => hBcomm.is_comm.comm u v, hB_pow⟩
    have hAleB : A ≤ B := fun z hz => Subgroup.subset_closure (Or.inl hz)
    have hBeqA : B = A := hAmax.2 B hBelem hAleB
    have hxB : x ∈ B := Subgroup.subset_closure (Or.inr (Set.mem_singleton x))
    rw [hBeqA] at hxB
    exact hxB

/-- **Prop 10.10 prep**: conjugation transports membership in `ℋ_⊤(A;π)` along the acting
subgroup as well: `Q ∈ ℋ_⊤(P;π) ⟹ Q^g ∈ ℋ_⊤(P^g;π)`. (The library lemma
`conj_smul_mem_hInvariant_top_of_normalizer` keeps `P` fixed; here both `Q` and `P` move.) -/
private theorem conj_smul_mem_hInvariant_top_conj {P Q : Subgroup G} {π : Set ℕ}
    (hQ : Q ∈ hInvariant ⊤ P π) (g : G) :
    MulAut.conj g • Q ∈ hInvariant ⊤ (MulAut.conj g • P) π := by
  obtain ⟨-, hQnorm, hQpi⟩ := hQ
  refine ⟨le_top, ?_, ?_⟩
  · -- `g•P ≤ N_G(g•Q)`: a `g•P`-element `b = g a g⁻¹` (`a ∈ P ≤ N_G(Q)`) fixes `g•Q`.
    intro b hb
    apply mem_normalizer_of_conj_smul_eq_self
    have ha : g⁻¹ * b * g ∈ P := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hb
      simpa only [map_inv, MulAut.smul_def, MulAut.conj_inv_apply] using hb
    calc MulAut.conj b • MulAut.conj g • Q
        = MulAut.conj (b * g) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj (g * (g⁻¹ * b * g)) • Q := by group
      _ = MulAut.conj g • MulAut.conj (g⁻¹ * b * g) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj g • Q := by
          rw [conj_smul_eq_self_of_mem_setNormalizer (hQnorm ha)]
  · have hcard : Nat.card ↥(MulAut.conj g • Q) = Nat.card ↥Q :=
      (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Q).toEquiv).symm
    intro r hr
    rw [hcard] at hr
    exact hQpi r hr

/-- **Prop 10.10 prep**: conjugation transports membership in `ℋ_⊤^*(A;π)` along the acting
subgroup: `Q ∈ ℋ_⊤^*(P;π) ⟹ Q^g ∈ ℋ_⊤^*(P^g;π)`. Maximality transports along the order
isomorphism `· ↦ ·^g`. -/
private theorem conj_smul_mem_hInvariantStar_top_conj {P Q : Subgroup G} {π : Set ℕ} (g : G)
    (hQ : Q ∈ hInvariantStar ⊤ P π) :
    MulAut.conj g • Q ∈ hInvariantStar ⊤ (MulAut.conj g • P) π := by
  obtain ⟨hQmem, hQmax⟩ := hQ
  refine ⟨conj_smul_mem_hInvariant_top_conj hQmem g, ?_⟩
  intro Q' hQ' hle
  have h1 : MulAut.conj g⁻¹ • Q' ∈ hInvariant ⊤ P π := by
    have h := conj_smul_mem_hInvariant_top_conj hQ' g⁻¹
    rwa [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h
  have h2 : Q ≤ MulAut.conj g⁻¹ • Q' := by
    calc Q = MulAut.conj g⁻¹ • MulAut.conj g • Q := by
          rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ ≤ MulAut.conj g⁻¹ • Q' := by
          rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]; exact hle
  have h3 : MulAut.conj g⁻¹ • Q' = Q := hQmax _ h1 h2
  calc Q' = MulAut.conj g • MulAut.conj g⁻¹ • Q' := by
        rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    _ = MulAut.conj g • Q := by rw [h3]

/-- **Prop 10.10 prep (the §7 core)**: from BG Hypothesis 7.1 and `K`-transitivity on
`ℋ_G^*(A;q)`, every `Q ∈ ℋ_G^*(A;q)` is `ℋ_G^*(P;q)`-maximal for *some* Sylow `p`-subgroup
`P ⊇ A`. Take any Sylow `P₀ ⊇ A` and a maximal `P₀`-invariant `q`-subgroup `Q₀`; by Theorem 7.4
`Q₀ ∈ ℋ_G^*(A;q)`, so transitivity gives `k ∈ K ⊆ C_G(A)` with `Q₀^k = Q`. Then `P := P₀^k` is a
Sylow `p`-subgroup containing `A^k = A` with `Q ∈ ℋ_G^*(P;q)` (conjugation equivariance). -/
private theorem exists_sylow_mem_hInvariantStar [Finite G] (hG : IsMinimalSimpleOdd G)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {A : Subgroup G}
    (hAp : IsPGroup p ↥A) (_hAne : A ≠ ⊥) (hHyp71 : Ch2.S07.Hypothesis71 A)
    (hπ : Ch2.S07.primesOf A = {p}) (hq : q ∈ (Ch2.S07.primesOf A)ᶜ)
    (htrans : Ch2.S07.ConjTransitiveOn (Ch2.S07.kSubgroup A) (hInvariantStar ⊤ A {q}))
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ A {q}) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧ Q ∈ hInvariantStar ⊤ (P : Subgroup G) {q} := by
  classical
  -- A Sylow `p`-subgroup `P₀ ⊇ A`.
  obtain ⟨P₀, hAP₀⟩ := IsPGroup.exists_le_sylow hAp
  -- `↑P₀` is a proper `π(A) = {p}`-subgroup; `A` is subnormal in the nilpotent `p`-group `↑P₀`.
  have hP₀proper : (P₀ : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hGp : IsPGroup p G := (htop ▸ P₀.isPGroup' : IsPGroup p ↥(⊤ : Subgroup G)).of_surjective
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
    have : Group.IsNilpotent G := hGp.isNilpotent
    exact hG.notSolvable inferInstance
  have hP₀pi : Subgroup.IsPiSubgroup (Ch2.S07.primesOf A) (P₀ : Subgroup G) := by
    rw [hπ]; exact isPiSubgroup_singleton_of_isPGroup P₀.isPGroup'
  have : Group.IsNilpotent ↥(P₀ : Subgroup G) := P₀.isPGroup'.isNilpotent
  have hAsub₀ : (A.subgroupOf (P₀ : Subgroup G)).IsSubnormal :=
    Ch02.isSubnormal_of_isNilpotent_finite (A.subgroupOf (P₀ : Subgroup G))
  -- A maximal `P₀`-invariant `q`-subgroup `Q₀` exists (extend `⊥`).
  have hbot : (⊥ : Subgroup G) ∈ hInvariant ⊤ (P₀ : Subgroup G) {q} := by
    rw [mem_hInvariant]
    refine ⟨bot_le, ?_, ?_⟩
    · intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
    · intro r hr
      rw [Subgroup.card_bot] at hr
      simp at hr
  obtain ⟨Q₀, hQ₀star, -⟩ := exists_le_hInvariantStar hbot
  -- Theorem 7.4: `ℋ_G^*(P₀;q) ⊆ ℋ_G^*(A;q)`, so `Q₀ ∈ ℋ_G^*(A;q)`.
  obtain ⟨-, -, hsub, -⟩ := Ch2.S07.transitivity_propagates hG hHyp71 hq (P₀ : Subgroup G)
    hP₀proper hP₀pi hAP₀ hAsub₀ htrans
  have hQ₀A : Q₀ ∈ hInvariantStar ⊤ A {q} := hsub hQ₀star
  -- Transitivity: `k ∈ K ⊆ C_G(A) ⊆ N_G(A)` with `Q₀^k = Q`.
  obtain ⟨k, hkK, hkQ⟩ := htrans Q₀ hQ₀A Q hQ
  have hkc : k ∈ Subgroup.centralizer (A : Set G) := Ch2.S07.kSubgroup_le_centralizer A hkK
  have hkA : MulAut.conj k • A = A :=
    conj_smul_eq_self_of_mem_setNormalizer (Subgroup.centralizer_le_normalizer (A : Set G) hkc)
  -- `P := P₀^k`.
  refine ⟨k • P₀, ?_, ?_⟩
  · rw [Sylow.coe_subgroup_smul, ← hkA]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hAP₀
  · rw [Sylow.coe_subgroup_smul, ← hkQ]
    exact conj_smul_mem_hInvariantStar_top_conj k hQ₀star

/-- **BG Proposition 10.10 (a)(b)(c)** (mmd L2844): `p ≠ q`, `A ∈ ℰ_p²(G)∩ℰ_p*(G)`,
`Q ∈ ℋ_G*(A;q)`, `q ∈ π(C_G(A))`。すると `A ⊆ P` となるある `P ∈ Syl_p(G)` で、
(a) `N_G(P) = O_{p'}(C_G(P))·(N_G(P)∩N_G(Q))`; (b) `P ⊆ N_G(Q)'`;
(c) `Q` が cyclic または `ℰ²(Q)∩ℰ*(Q) ≠ ∅` なら `P` は `Q` を中心化する。 -/
theorem normalizer_factorization [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAmax : IsMaximalElementaryAbelian p A)
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ A {q})
    (hqc : q ∈ (Nat.card ↥(Subgroup.centralizer (A : Set G))).primeFactors) :
    ∃ P : Sylow p G, A ≤ (P : Subgroup G) ∧
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
        ∃ c ∈ opiCoreInG {p}ᶜ (Subgroup.centralizer ((P : Subgroup G) : Set G)),
          ∃ m ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.normalizer (Q : Set G), n = c * m) ∧
      (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer (Q : Set G)) ∧
      ((IsCyclic ↥Q ∨ ∃ B : Subgroup ↥Q, Nat.card ↥B = q ^ 2 ∧ IsMaximalElementaryAbelian q B) →
        (P : Subgroup G) ≤ Subgroup.centralizer (Q : Set G)) := by
  classical
  have hAelem : A.IsElementaryAbelian p := hA.1
  have hAp : IsPGroup p ↥A := hAelem.isPGroup
  have hAcard : Nat.card ↥A = p ^ 2 := hA.2
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : p.Prime).one_lt
    omega
  have hπ : Ch2.S07.primesOf A = {p} := by
    have hpf : (Nat.card ↥A).primeFactors = {p} := by
      rw [hAcard]; exact Nat.primeFactors_prime_pow (by norm_num) Fact.out
    ext r
    change r ∈ (Nat.card ↥A).primeFactors ↔ r ∈ ({p} : Set ℕ)
    rw [hpf, Finset.mem_singleton, Set.mem_singleton_iff]
  have hq : q ∈ (Ch2.S07.primesOf A)ᶜ := by
    rw [hπ]; exact fun h => hpq (Set.mem_singleton_iff.mp h).symm
  -- BG Hypothesis 7.1 and `K`-transitivity on `ℋ_G^*(A;q)` (Theorem 7.3, `m(Z(A)) = 2`).
  have hHyp71 := hypothesis71_of_mem_elemAbelianOfRank_two_of_maximal hG hA hAmax
  have hm : 2 ≤ rank ↥(Subgroup.center ↥A) := by
    have : IsMulCommutative ↥A := ⟨⟨fun x y => hAelem.comm x y⟩⟩
    have hcenter : Subgroup.center ↥A = ⊤ := Subgroup.center_eq_top
    have e : ↥(Subgroup.center ↥A) ≃* ↥A :=
      (MulEquiv.subgroupCongr hcenter).trans Subgroup.topEquiv
    have h2A : 2 ≤ pRank ↥A p := by
      have hlog : Nat.log p (Nat.card ↥A) = 2 := by
        rw [hAcard, Nat.log_pow (Fact.out : p.Prime).one_lt]
      exact hlog ▸ hAelem.log_card_le_pRank
    calc 2 ≤ pRank ↥A p := h2A
      _ ≤ pRank ↥(Subgroup.center ↥A) p :=
          pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective
      _ ≤ rank ↥(Subgroup.center ↥A) := pRank_le_rank p
  have htrans := Ch2.S07.transitive_of_two_le_rank_center_of_dvd hG hHyp71 hq hm hqc
  -- A Sylow `p`-subgroup `P ⊇ A` with `Q ∈ ℋ_G^*(P;q)` (the §7 core, `exists_sylow_…`).
  obtain ⟨P, hAP, hQP⟩ := exists_sylow_mem_hInvariantStar hG hAp hAne hHyp71 hπ hq htrans hQ
  -- Theorem 7.4(d) for `(A, P)` and `Q`: the normalizer factorization and `P ⊓ N_G(P)' ⊆ N_G(Q)'`.
  have hPproper : (P : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hGp : IsPGroup p G := (htop ▸ P.isPGroup' : IsPGroup p ↥(⊤ : Subgroup G)).of_surjective
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
    have : Group.IsNilpotent G := hGp.isNilpotent
    exact hG.notSolvable inferInstance
  have hPpi : Subgroup.IsPiSubgroup (Ch2.S07.primesOf A) (P : Subgroup G) := by
    rw [hπ]; exact isPiSubgroup_singleton_of_isPGroup P.isPGroup'
  have : Group.IsNilpotent ↥(P : Subgroup G) := P.isPGroup'.isNilpotent
  have hAsub : (A.subgroupOf (P : Subgroup G)).IsSubnormal :=
    Ch02.isSubnormal_of_isNilpotent_finite (A.subgroupOf (P : Subgroup G))
  obtain ⟨-, -, -, hd⟩ := Ch2.S07.transitivity_propagates hG hHyp71 hq (P : Subgroup G)
    hPproper hPpi hAP hAsub htrans
  obtain ⟨hd1, hd2⟩ := hd Q hQP
  -- (b)+(c) share `P ≤ N_G(Q)'`: Corollary 10.7 gives `P ≤ N_G(P)'`, so `P ⊓ N_G(P)' = P`.
  have hPderQ : (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer (Q : Set G)) := by
    obtain ⟨V, hV, hPVinf, hPVsup⟩ := exists_sylow_complement_normalizer P
    have hPder : (P : Subgroup G) ≤ derivedInG (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
      ((sylow_structure hG P).1 V hV hPVinf hPVsup).2
    rwa [inf_eq_left.mpr hPder] at hd1
  refine ⟨P, hAP, ?_, hPderQ, ?_⟩
  · -- (a): the factorization `N_G(P) = O_{p'}(C_G(P)) · (N_G(P) ∩ N_G(Q))`.
    intro n hn
    obtain ⟨c, hc, m, hm', hcm⟩ := hd2 n hn
    exact ⟨c, by rwa [hπ] at hc, m, hm', hcm⟩
  · -- (c): under the narrowness hypothesis on `Q`, `P ≤ C_G(Q)` (Theorem 5.5(a)).
    -- `N_G(Q)'` induces a `q`-group of automorphisms on `Q`; the `p`-group `P ≤ N_G(Q)'`
    -- therefore acts trivially, i.e. lies in `C_G(Q)`.
    intro hcase
    rcases eq_or_ne Q ⊥ with hQbot | hQne
    · subst hQbot
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      subst hy
      group
    have hQpg : IsPGroup q ↥Q := isPGroup_of_isPiSubgroup_singleton (hInvariantStar_isPiSubgroup hQ)
    have hq_odd : Odd q := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQpg
      have hn0 : n ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hn
        exact hQne (Subgroup.card_eq_one.mp hn)
      have hqdvd : q ∣ Nat.card G := by
        refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card Q)
        rw [hn]; exact dvd_pow_self q hn0
      exact hG.odd.of_dvd_nat hqdvd
    -- `Q` is narrow.
    have hQnarrow : IsNarrow q ↥Q := by
      rcases hcase with hcyc | ⟨B, hBcard, hBmax⟩
      · refine isNarrow_of_pRank_le_two ?_
        by_contra hcon
        obtain ⟨E, hEea, hEnc⟩ :=
          exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank (by omega : 2 ≤ pRank ↥Q q)
        have : IsCyclic ↥Q := hcyc
        exact hEnc (isCyclic_of_injective E.subtype E.subtype_injective)
      · by_cases h3 : 3 ≤ pRank ↥Q q
        · exact (Ch1.S05.narrow_iff_exists_maximalElementaryAbelian_card_prime_sq
            hq_odd hQpg h3).mpr
            ⟨B, hBcard, hBmax⟩
        · exact isNarrow_of_pRank_le_two (by omega)
    -- `N := N_G(Q)` is a proper (hence solvable) subgroup, since `Q ≠ 1, ⊤` in the simple `G`.
    set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN_def
    have hNlt : N < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      have hQnorm : Q.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff]; exact htop
      rcases hG.simple.eq_bot_or_eq_top_of_normal Q hQnorm with h | h
      · exact hQne h
      · have hGpg : IsPGroup q G := (h ▸ hQpg : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
          (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
        have : Group.IsNilpotent G := hGpg.isNilpotent
        exact hG.notSolvable inferInstance
    have hNsolv : Group.IsSolvable ↥N := hG.isSolvable_of_lt_top N hNlt
    -- The conjugation action `ψ : N → Aut Q` with kernel `C_G(Q) ∩ N`.
    set ψ : ↥N →* MulAut ↥Q := Q.normalizerMonoidHom with hψ_def
    have hψker : ψ.ker = (Subgroup.centralizer (Q : Set G)).subgroupOf N :=
      Q.normalizerMonoidHom_ker
    -- `A := N / ker ψ` acts faithfully, is solvable and odd.
    have : Group.IsSolvable (↥N ⧸ ψ.ker) := inferInstance
    have hA_odd : Odd (Nat.card (↥N ⧸ ψ.ker)) := by
      refine hG.odd.of_dvd_nat (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card N))
      have := Subgroup.card_subgroup_dvd_card ψ.ker
      calc Nat.card (↥N ⧸ ψ.ker) ∣ Nat.card ↥N := by
            simpa [Subgroup.index] using Subgroup.index_dvd_card ψ.ker
        _ ∣ Nat.card ↥N := dvd_rfl
    -- Theorem 5.5(a): `(N / ker)'` is a `q`-group.
    obtain ⟨hcomm, -, -, -⟩ := Ch1.S05.solvableAut_of_narrow hq_odd hQpg hQnarrow
      (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ) hA_odd
    have hA' : IsPGroup q (_root_.commutator (↥N ⧸ ψ.ker)) := by
      have hle : _root_.commutator (↥N ⧸ ψ.ker) ≤ Ch01.opCore q (↥N ⧸ ψ.ker) := by
        rw [_root_.commutator, Subgroup.commutator_le]
        intro x _ y _
        have h1 : QuotientGroup.mk' (Ch01.opCore q (↥N ⧸ ψ.ker)) ⁅x, y⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact hcomm _ _
        exact (QuotientGroup.eq_one_iff _).mp h1
      exact (Ch01.opCore_isPGroup q _).to_le hle
    -- `P ≤ N` and `P.subgroupOf N ≤ commutator ↥N`.
    have hPN : (P : Subgroup G) ≤ N := hPderQ.trans (Subgroup.map_subtype_le _)
    have hPcomm : (P : Subgroup G).subgroupOf N ≤ _root_.commutator ↥N := by
      have key : ((_root_.commutator ↥N).map N.subtype).comap N.subtype = _root_.commutator ↥N :=
        Subgroup.comap_map_eq_self_of_injective N.subtype_injective (_root_.commutator ↥N)
      calc (P : Subgroup G).subgroupOf N
          ≤ (derivedInG N).comap N.subtype := Subgroup.comap_mono hPderQ
        _ = _root_.commutator ↥N := key
    -- The image of `P` in `A` is both a `p`-group and `≤ (N/ker)'` (a `q`-group): hence trivial.
    set PA : Subgroup (↥N ⧸ ψ.ker) :=
      ((P : Subgroup G).subgroupOf N).map (QuotientGroup.mk' ψ.ker) with hPA_def
    have hPsubN_p : IsPGroup p ↥((P : Subgroup G).subgroupOf N) :=
      P.isPGroup'.of_surjective (Subgroup.subgroupOfEquivOfLe hPN).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hPN).symm.surjective
    have hPA_p : IsPGroup p ↥PA := hPsubN_p.map _
    have hPA_q : IsPGroup q ↥PA := by
      refine hA'.to_le ?_
      calc PA ≤ (_root_.commutator ↥N).map (QuotientGroup.mk' ψ.ker) :=
            Subgroup.map_mono hPcomm
        _ ≤ _root_.commutator (↥N ⧸ ψ.ker) := by
            rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator]
            exact Subgroup.commutator_mono le_top le_top
    have hPA_bot : PA = ⊥ := by
      have hcop : Nat.Coprime (Nat.card ↥PA) (Nat.card ↥PA) :=
        IsPGroup.coprime_card_of_ne p q hpq PA PA hPA_p hPA_q
      exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl)
    -- Trivial image means `P ≤ ker ψ = C_G(Q) ∩ N`, hence `P ≤ C_G(Q)`.
    have hPker : (P : Subgroup G).subgroupOf N ≤ ψ.ker := by
      rw [hPA_def, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hPA_bot
      exact hPA_bot
    rw [hψker] at hPker
    intro x hx
    have hxN : x ∈ N := hPN hx
    have : (⟨x, hxN⟩ : ↥N) ∈ (Subgroup.centralizer (Q : Set G)).subgroupOf N :=
      hPker (by rw [Subgroup.mem_subgroupOf]; exact hx)
    rw [Subgroup.mem_subgroupOf] at this
    exact this

end OddOrder.BG.Ch3.S10


