-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TypeVSibley
-- name    : OddOrder_Peterfalvi_S12_TypeVSibley
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:53:20.917217+00:00
-- url     : https://prove2.me/theorems/2e43130c-6693-4cbb-a825-7169d49cefe6
-- title:
--   Peterfalvi (10.10) case (a): type V Sibley coordinates
-- statement:
--   Formalizes the first sentence of the proof of Theorem (10.10) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §10, pp. 58-63): in case (a) of Definition (8.7), coherence follows from a (6.8) Sibley datum for a type V maximal subgroup.
--
--   Main declarations: `hypothesis46CastSet` (Transport a Peterfalvi (4.6) carrier along an equality of support sets); `typeVSibleyDadeHypothesis` (The Peterfalvi (6.8) Sibley datum for a type-V maximal in case (8.7)(a)); `typeVSibleyDadeHypothesis_tau_agree` (Case-(a) `τ`-agreement).
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TypeVSibley.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TypeVSibley.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleBasic
import Definitions.Def_OddOrder_Peterfalvi_S08_YsetInner
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainHypothesis46
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_Peterfalvi_S12_TICyclicSigmaBridge
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence2

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **Type V has `M' = M_F = data.H`** — for *any* `TypePData` witness `data` of the same
`M` (the kernel is the data-independent `maxNilpotentNormalHall M` via `H_eq`).  From
`M' = M_F ⊔ U` (`derivedInG_eq_fitting_sup_U`) and the type-V `U = ⊥`.  Book: the (10.10)
proof opens with "Set `H = M'`". -/
theorem TypeVData.derivedInG_eq_H {M : Subgroup G} (dV : TypeVData M)
    (data : TypePData M) : derivedInG M = data.H := by
  rw [dV.typeP.derivedInG_eq_fitting_sup_U, dV.U_eq_bot, sup_bot_eq, data.H_eq]

/-- **The Sibley support coordinate is the ambient sharp set**:
`sharpImage ((M').subgroupOf M) = (M')^#`.  Mapping `(M').subgroupOf M` back through
`M.subtype` recovers `M'` (as `M' ≤ M`), and `sharpImage`/`sharpSubgroup` both remove the
identity.  Type-V instance of the `S09.FrobeniusFamily.sharpImage_subgroupOf_eq` pattern. -/
theorem sharpImage_subgroupOf_derivedInG (M : Subgroup G) :
    OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)
      = sharpSubgroup (derivedInG M) := by
  rw [OddOrder.Peterfalvi.S08.sharpImage, Subgroup.subgroupOf_map_subtype,
    inf_of_le_left (show derivedInG M ≤ M from Subgroup.map_subtype_le _)]
  rfl

/-- **The set-normalizers of `H` and `H^# = H ∖ {1}` coincide**: conjugation fixes `1`, so
normalizing the punctured set is the same condition as normalizing the subgroup's carrier
set.  Bridges the (8.7)(a) TI bound `N_G(H)` with the sharp-set normalizer that the (8.15)
identification `normalizer_support_eq` computes. -/
theorem normalizer_sharpSubgroup (H : Subgroup G) :
    Subgroup.normalizer (sharpSubgroup H) = Subgroup.normalizer (H : Set G) := by
  have hconj1 : ∀ g x : G, g * x * g⁻¹ = 1 ↔ x = 1 := by
    intro g x
    constructor
    · intro h
      have hx : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [hx, h]
      group
    · rintro rfl
      group
  ext g
  simp only [Subgroup.mem_set_normalizer_iff, sharpSubgroup, Set.mem_sdiff,
    Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · intro h x
    by_cases hx1 : x = 1
    · subst hx1
      simp
    · constructor
      · intro hxH
        exact ((h x).mp ⟨hxH, hx1⟩).1
      · intro hgxH
        exact ((h x).mpr ⟨hgxH, fun he => hx1 ((hconj1 g x).mp he)⟩).1
  · intro h x
    exact and_congr (h x) (not_congr (hconj1 g x).symm)

/-- **`N_G((M')^#) = M`** for a maximal subgroup `M` of a minimal simple odd group carrying
type-`P` data: `(M')^#` is a nonempty (`W₂ ≤ H ≤ M'` nontrivial) `M`-invariant
(`le_normalizer_derivedInG`) subset of `M ∖ {1}`, so the (8.15) normalizer identification
`normalizer_support_eq` applies. -/
theorem normalizer_sharpSubgroup_derivedInG_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M) :
    Subgroup.normalizer (sharpSubgroup (derivedInG M)) = M := by
  refine OddOrder.Peterfalvi.S10.normalizer_support_eq hG hM ?_ ?_ ?_ ?_
  · exact fun x hx => (Subgroup.map_subtype_le _) hx.1
  · exact fun x hx => hx.2
  · obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.W2_nontrivial
    exact ⟨w.1, data.H_le ((inf_le_left : data.H ⊓ _ ≤ data.H) (data.W2_le w.2)),
      fun h => hw1 (Subtype.ext h)⟩
  · intro m x hm
    constructor
    · intro hmx
      have hback := OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M (inv_mem hm)) hmx
      rwa [show m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x from by group] at hback
    · exact OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm)

/-- **Type-V case (a) in the `M`-coordinate**: under the (8.7)(a) TI alternative for a
type-`P` witness `data` (as produced by `TypeVData.alternative_transfer`), the support
`A(M) = (M')^# = H^#` is a TI-subset of `G` relative to `M` itself — the shape the
`SibleyDadeHypothesis.H_sharp_ti` field takes (via `sharpImage_subgroupOf_derivedInG`).
The (8.7)(a) bound `N_G(H)` collapses to `M` by `normalizer_sharpSubgroup_derivedInG_eq`. -/
theorem typePA_isTISubset_of_typeV_TI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (dV : TypeVData M) (data : TypePData M)
    (hTI : IsTISubset (sharpSubgroup data.H)
      (Subgroup.normalizer (data.H : Set G))) :
    IsTISubset (typePA M data) M := by
  have hHeq : derivedInG M = data.H := TypeVData.derivedInG_eq_H dV data
  have hN : Subgroup.normalizer (data.H : Set G) = M := by
    rw [← hHeq, ← normalizer_sharpSubgroup]
    exact normalizer_sharpSubgroup_derivedInG_eq hG hM data
  rw [typePA_eq_sharpSubgroup_derivedInG, hHeq]
  rw [hN] at hTI
  exact hTI

section CastSet

variable [Fintype G] {A B : Set G} {L : Subgroup G} [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- Transport a Peterfalvi (4.6) carrier along an equality of support sets. -/
def hypothesis46CastSet (h : A = B)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A L) :
    OddOrder.Peterfalvi.S06.Hypothesis46 B L := h ▸ h46

@[simp] theorem hypothesis46CastSet_K (h : A = B)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A L) :
    (hypothesis46CastSet h h46).K = h46.K := by subst h; rfl

@[simp] theorem hypothesis46CastSet_W1 (h : A = B)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A L) :
    (hypothesis46CastSet h h46).W1 = h46.W1 := by subst h; rfl

@[simp] theorem hypothesis46CastSet_W2 (h : A = B)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A L) :
    (hypothesis46CastSet h h46).W2 = h46.W2 := by subst h; rfl

end CastSet

/-- **`W₂` lands in the derived subgroup of `M'` in the `↥M`-coordinate**:
`W₂.subgroupOf M ≤ ⁅(M').subgroupOf M, (M').subgroupOf M⁆`.  From the `TypePData` field
`W₂ ≤ H ⊓ M''` and the identification of the `↥M`-commutator of `(M').subgroupOf M` with
the ambient second derived subgroup (`map_commutator` + `map_subtype_commutator`).  This is
the `W₂ ≤ ⁅H, H⁆` side condition of the Sibley (6.8)(c2) `cases` conjunct. -/
theorem TypePData.W2_subgroupOf_le_commutator {M : Subgroup G} (data : TypePData M) :
    data.W2.subgroupOf M
      ≤ ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ := by
  have hmap : Subgroup.map M.subtype
      ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆
        = secondDerivedInAmbient M := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (show derivedInG M ≤ M from Subgroup.map_subtype_le _)]
    exact (Subgroup.map_subtype_commutator (derivedInG M)).symm
  intro x hx
  have hxsd : (x : G) ∈ secondDerivedInAmbient M :=
    (inf_le_right : data.H ⊓ secondDerivedInAmbient M ≤ _)
      (data.W2_le (Subgroup.mem_subgroupOf.mp hx))
  rw [← hmap] at hxsd
  obtain ⟨y, hyC, hyx⟩ := Subgroup.mem_map.mp hxsd
  exact (Subtype.ext hyx : y = x) ▸ hyC

/-- **Type V has nilpotent `(M').subgroupOf M`**: for type V, `M' = M_F` is the maximal
nilpotent normal Hall subgroup (`derivedInG_eq_H` + `H_eq`), whose nilpotency transports
to the `↥M`-coordinate along `subgroupOfEquivOfLe`.  This is the Sibley `H_nilpotent`
field (Peterfalvi (6.8.a)). -/
theorem TypeVData.isNilpotent_derivedInG_subgroupOf [Finite G] {M : Subgroup G}
    (dV : TypeVData M) :
    Group.IsNilpotent ↥((derivedInG M).subgroupOf M) := by
  have hMF : derivedInG M = maxNilpotentNormalHall M :=
    (TypeVData.derivedInG_eq_H dV dV.typeP).trans dV.typeP.H_eq
  have : Group.IsNilpotent ↥(derivedInG M) := by
    rw [hMF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe
      (show derivedInG M ≤ M from Subgroup.map_subtype_le _)).symm

open scoped FiniteInduce in
/-- **The Peterfalvi (6.8) Sibley datum for a type-V maximal in case (8.7)(a)** (the
first sentence of the (10.10) proof).  Assembles a
`SibleyDadeHypothesis G M ((M').subgroupOf M)` from the §10 Hypothesis (10.1):

* the split `M = M' ⋊ W₁` and its side conditions are the `TypePData` fields;
* `H = M'` is nilpotent because type V has `M' = M_F`
  (`TypeVData.isNilpotent_derivedInG_subgroupOf`);
* `H^#` is TI relative to `M` by the (8.7)(a) alternative upgraded through
  `N_G(M') = M` (`typePA_isTISubset_of_typeV_TI`);
* the §4 Dade datum is the (10.1) `dadeData.dade` restricted to `A(M)` and recoordinated
  to `sharpImage` (`hypothesis46CastSet` of `toHypothesis46`) — so the (6.8)(c2) branch
  holds with **the same** `h46` and `h46.dade = dade` is `rfl`;
* its local subgroups vanish by the (2.3) reverse direction
  (`H_eq_bot_of_isTISubset`), as the TI situation forces — no producer measurement
  needed (issue 1021 tick¹⁹).

Feeding this to `S08.sibleySetup_is_coherent` yields the (6.8) coherence for
`S = {Ind_{M'}^M θ | θ ≠ 1}` — the field `S` is definitionally `inducedFamily M`, i.e.
the (10.1) `hyp.Sset`, so the case-(a) output needs no family identification. -/
noncomputable def typeVSibleyDadeHypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (dV : TypeVData M)
    (hTI : IsTISubset (sharpSubgroup hyp.typeP.H)
      (Subgroup.normalizer (hyp.typeP.H : Set G))) :
    OddOrder.Peterfalvi.S08.SibleyDadeHypothesis G M ((derivedInG M).subgroupOf M) :=
  have hodd : Odd (Nat.card G) := hG.odd
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hW2der : hyp.typeP.W2 ≤ derivedInG M :=
    hyp.typeP.W2_le.trans (inf_le_left.trans hyp.typeP.H_le)
  have hW2M : hyp.typeP.W2 ≤ M := hW2der.trans hM'le
  have hset : typePA M hyp.typeP
      = OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M) :=
    (typePA_eq_sharpSubgroup_derivedInG M hyp.typeP).trans
      (sharpImage_subgroupOf_derivedInG M).symm
  let h46 := hypothesis46CastSet hset (hyp.toHypothesis46 hG hodd)
  have hTI_M : IsTISubset
      (OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)) M :=
    hset ▸ typePA_isTISubset_of_typeV_TI hG hyp.maximal dV hyp.typeP hTI
  { W1 := hyp.typeP.W1.subgroupOf M
    H_ne_bot := by
      rw [ne_eq, Subgroup.subgroupOf_eq_bot]
      intro hdisj
      have hbot : derivedInG M = ⊥ := disjoint_self.mp (hdisj.mono_right hM'le)
      exact hyp.typeP.W2_nontrivial (le_bot_iff.mp (hbot ▸ hW2der))
    H_normal := by
      rw [show (derivedInG M).subgroupOf M = commutator ↥M by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
      infer_instance
    H_nilpotent := TypeVData.isNilpotent_derivedInG_subgroupOf dV
    split := hyp.typeP.M_complement
    W1_nontrivial := by
      rw [ne_eq, Subgroup.subgroupOf_eq_bot]
      exact fun hdisj => hyp.typeP.W1_nontrivial
        (disjoint_self.mp (hdisj.mono_right hyp.typeP.W1_le))
    card_L_odd := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
    H_sharp_ti := hTI_M
    dade := h46.dade
    dade_H_eq_bot := fun a => h46.dade.H_eq_bot_of_isTISubset hTI_M a
    S := inducedFamily M
    S_eq := rfl
    cases := Or.inr ⟨h46, rfl,
      by rw [hypothesis46CastSet_K]; rfl,
      by rw [hypothesis46CastSet_W1]; rfl,
      by
        rw [hypothesis46CastSet_W2]
        have hcard : Nat.card ↥((hyp.toHypothesis46 hG hodd).W2)
            = Nat.card ↥hyp.typeP.W2 :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2M).toEquiv
        rw [hcard]
        exact hyp.w2_prime hG,
      by
        rw [hypothesis46CastSet_W2]
        exact TypePData.W2_subgroupOf_le_commutator hyp.typeP,
      by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.W1_le).toEquiv]
        exact typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP⟩ }

section DadeUniqueness

variable [Fintype G] {A : Set G} {L : Subgroup G} [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **(2.5)-uniqueness for the integral character map**: two full Dade data over (possibly
differently packaged) Hypothesis (2.2) data on the same pair `(A, L)`, both with all local
subgroups trivial (the TI situation), give the same integral character map on `A`-supported
functions.  `dadeIntegralCharacterMap` evaluates to the canonical `dadeMap` on the supported
subspace (`dadeIntegralCharacterMap_apply_of_support`), and the canonical maps agree by the
(2.5) uniqueness `dadeMap_unique_of_forall_H_eq_bot`.  This absorbs any packaging difference
(restriction, support-set recoordination) between the two data. -/
theorem dadeIntegralCharacterMap_eq_of_forall_H_eq_bot
    {hyp₁ hyp₂ : OddOrder.Peterfalvi.S04.Hypothesis G A L}
    (D₁ : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp₁)
    (D₂ : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp₂)
    (hH₁ : ∀ a, hyp₁.H a = ⊥) (hH₂ : ∀ a, hyp₂.H a = ⊥)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp₁ D₁ φ
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp₂ D₂ φ := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp₁ D₁ hφ,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp₂ D₂ hφ,
    dadeMap_unique_of_forall_H_eq_bot
      (hyp₁.isDadeMap_dadeMap (k := ℂ)) (hyp₂.isDadeMap_dadeMap (k := ℂ)) hH₁ hH₂]

end DadeUniqueness

open scoped FiniteInduce in
/-- **Case-(a) `τ`-agreement** (Peterfalvi (2.11) + (2.5)): the Sibley–Dade map of
`typeVSibleyDadeHypothesis` agrees with the §10 Dade isometry `hyp.tau` on class functions
supported in `(M')^#`.  `hyp.tau` restricts to the `(M')^#`-datum by (2.11)
(`dadeIntegralCharacterMap_restrict_eq_of_support`), and the restricted datum agrees with the
Sibley `dade` field by the (2.5) uniqueness on the TI pair — both local-subgroup families
vanish (`H_eq_bot_of_isTISubset`), so the packaging difference (the `hypothesis46CastSet`
recoordination) is invisible. -/
theorem typeVSibleyDadeHypothesis_tau_agree [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (dV : TypeVData M)
    (hTI : IsTISubset (sharpSubgroup hyp.typeP.H)
      (Subgroup.normalizer (hyp.typeP.H : Set G)))
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)) M) :
    (typeVSibleyDadeHypothesis hG hyp dV hTI).tau φ = hyp.tau φ := by
  have hset : typePA M hyp.typeP
      = OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M) :=
    (typePA_eq_sharpSubgroup_derivedInG M hyp.typeP).trans
      (sharpImage_subgroupOf_derivedInG M).symm
  have hTI_M : IsTISubset
      (OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)) M :=
    hset ▸ typePA_isTISubset_of_typeV_TI hG hyp.maximal dV hyp.typeP hTI
  have hAsub : OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)
      ⊆ typePA0 M hyp.typeP := by
    rw [← hset]
    exact Set.subset_union_left
  have hnorm' : ∀ (l : ↥M) ⦃a : G⦄,
      a ∈ OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M) →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ OddOrder.Peterfalvi.S08.sharpImage
        ((derivedInG M).subgroupOf M) := by
    intro l a ha
    rw [← hset] at ha ⊢
    exact OddOrder.Peterfalvi.S10.typePA_conj_mem M hyp.typeP l.2 ha
  -- (2.5): the Sibley datum agrees with the (2.11)-restricted `A₀`-datum on the TI pair
  have h25 := dadeIntegralCharacterMap_eq_of_forall_H_eq_bot
    ((typeVSibleyDadeHypothesis hG hyp dV hTI).dade.fullDadeIsometryData)
    ((hyp.dadeData.dade.fullDadeIsometryData).restrict hAsub hnorm')
    (fun a => (typeVSibleyDadeHypothesis hG hyp dV hTI).dade.H_eq_bot_of_isTISubset hTI_M a)
    (fun a => (hyp.dadeData.dade.restrict hAsub hnorm').H_eq_bot_of_isTISubset hTI_M a)
    hφ
  -- (2.11): the restricted datum's map is `hyp.tau` on `A`-supported functions
  have h211 := OddOrder.Peterfalvi.S08.dadeIntegralCharacterMap_restrict_eq_of_support
    hyp.dadeData.dade (hyp.dadeData.dade.fullDadeIsometryData) hAsub hnorm' hφ
  exact h25.trans h211

end OddOrder.Peterfalvi.S12


