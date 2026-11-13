-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_BGInterface
-- name    : OddOrder_Peterfalvi_S10_BGInterface
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:59:38.014698+00:00
-- url     : https://prove2.me/theorems/0043dd72-fe07-4d9e-8598-62b63d1be845
-- title:
--   Peterfalvi §10 and BG §16 interface (shared-notation consumption layer)
-- statement:
--   The interface between Peterfalvi, *Character Theory for the Odd Order Theorem* §10 and BG §16 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. BG §16 states Theorems A–E, Proposition 16.1 and Theorems I–II in BG-internal notation ($M_\sigma$, $\sigma$, $\kappa$, $A(M)$, $A_0(M)$, $\widetilde M$); this file lets the Peterfalvi side consume those results in shared notation. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_BGInterface.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_BGInterface.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TaxonomyOutput

namespace OddOrder.Peterfalvi.S10Interface

open OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-- **Shared-notation Proposition 16.1, `M_F = M_σ` clause** (type I/II).

For a maximal subgroup of Peterfalvi type I or II, Peterfalvi's `M_F`
(`maxNilpotentNormalHall`, definitionally `OddOrder.BG.Ch4.S15.MF`) coincides
with BG's σ-Hall subgroup `M_σ`.  Cites BG Proposition 16.1
(`proposition_type_classification`); unconditional once that is proved. -/
theorem maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M) :
    maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
  (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.2.2.2.mpr
    (hType.imp_right Or.inl)

/-- **Type dictionary (Prop 16.1)**: Peterfalvi type I = BG type `F`.  Used to
translate the BG §14--§16 endpoints (whose conclusions are stated with `S14.IsTypeF`)
into the shared `IsTypeI` predicate that Peterfalvi §10--§13 uses. -/
theorem isTypeI_iff_isTypeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    IsTypeI M ↔ OddOrder.BG.Ch4.S14.IsTypeF M :=
  (OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).1

/-- **The `K`-invariant complement `U` to `M_F` is the `(κ∪σ)'`-Hall** (type-`P₂`).

For a type-`P₂` maximal subgroup `M`, `M_F = M_σ`, and the complement `U` to `M_σ` in
`M'` produced by `exists_kappaHall_invariant_complement_to_MF` shares the order `[M':M_σ]` with the
`(κ∪σ)'`-Hall of `typeP_exists_hall_derived_eq` (which also complements `M_σ` in `M'`).  Since
`IsHallSubgroup` is order-determined, any chosen complement `U` of `M_σ` in `M'` is
the same Hall.  This
discharges the `hUhall` hypothesis of downstream type-`P₂` data constructors for the canonical
invariant complement. -/
theorem isHall_kappaSigmaCompl_of_isTypeP2_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : OddOrder.BG.Ch4.S14.IsTypeP2 M) (hUM : U ≤ M)
    (hUsup : derivedInG M = maxNilpotentNormalHall M ⊔ U)
    (hUinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) := by
  classical
  have hMFeq : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (OddOrder.BG.Ch4.S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hUM' : U ≤ derivedInG M := by
    rw [hUsup]
    exact le_sup_right
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ _
  have hMσnormM' : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M) |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMσM').mpr (hM'M.trans hM_norm_Mσ)
  let U₀ := (OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hM hP2.1).choose
  have hU₀hall : Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U₀.subgroupOf M) :=
    (OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hM hP2.1).choose_spec.1
  have hU₀sup : derivedInG M = U₀ ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
    (OddOrder.BG.Ch4.S16.typeP_exists_hall_derived_eq hG hM hP2.1).choose_spec.2
  have hU₀M' : U₀ ≤ derivedInG M := by
    rw [hU₀sup]
    exact le_sup_left
  have hU₀M : U₀ ≤ M := hU₀M'.trans hM'M
  have hsupU : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊔ U.subgroupOf (derivedInG M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMσM' hUM', ← hMFeq, ← hUsup, Subgroup.subgroupOf_self]
  have hsupU₀ : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊔ U₀.subgroupOf (derivedInG M) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hMσM' hU₀M', sup_comm, ← hU₀sup, Subgroup.subgroupOf_self]
  have hcopU₀ : Nat.Coprime (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) (Nat.card ↥U₀) := by
    refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
      (π := OddOrder.BG.Ch3.S10.sigma M) Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
    · intro p hp
      exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p hp
    · intro p hp hpσ
      exact hU₀hall.1 p (by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀M).toEquiv]) (Or.inr hpσ)
  have hinfU : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊓ U.subgroupOf (derivedInG M) = ⊥ := by
    rw [show
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
          ⊓ U.subgroupOf (derivedInG M)
          = (OddOrder.BG.Ch3.S10.Msigma M ⊓ U).subgroupOf (derivedInG M) from
        (Subgroup.comap_inf _ _ _).symm,
      ← hMFeq, hUinf, Subgroup.bot_subgroupOf]
  have hinfU₀ : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
        ⊓ U₀.subgroupOf (derivedInG M) = ⊥ := by
    rw [show
        (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)
          ⊓ U₀.subgroupOf (derivedInG M)
          = (OddOrder.BG.Ch3.S10.Msigma M ⊓ U₀).subgroupOf (derivedInG M) from
        (Subgroup.comap_inf _ _ _).symm,
      (Subgroup.disjoint_of_coprime_natCard hcopU₀).eq_bot, Subgroup.bot_subgroupOf]
  have hcU := Subgroup.card_mul_card_of_complement_normal hinfU hsupU
  have hcU₀ := Subgroup.card_mul_card_of_complement_normal hinfU₀ hsupU₀
  have hcard : Nat.card ↥(U.subgroupOf (derivedInG M)) = Nat.card ↥(U₀.subgroupOf (derivedInG M)) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hcU.trans hcU₀.symm)
  refine Ch03.isHallSubgroup_of_card_eq (B := U₀.subgroupOf M) hU₀hall ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀M).toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM').toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₀M').toEquiv]
  exact hcard

/-- **Support-set bridge (types I/II)**: Peterfalvi's `A_1(M) = M_s#` coincides with
BG's `\widetilde M = M_σ#` (`sigmaSharp`).  For types I/II, `M_s = M_F = M_σ`
(Proposition 16.1), so both are the `sharpSubgroup` of the same `M_F = M_σ`.

This is a genuine support-set equality — but a special one: the larger support sets
`A(M)`/`A_0(M)` (built from BG's `hatMsigma = {a ∈ M | M_σ ⊓ C(a) ≠ 1}`) are *not*
of this `sharpSubgroup` form, so they have no analogous bridge and would have to go
through the BG §14--§15 structure directly. -/
theorem A1_eq_sigmaSharp_of_typeI_or_II [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M)
    {tau : PeterfalviType} (htau : tau = PeterfalviType.I ∨ tau = PeterfalviType.II) :
    A1 M tau = OddOrder.BG.Ch4.S14.sigmaSharp M := by
  have hmain : mainSubgroup M tau = maxNilpotentNormalHall M := by
    rcases htau with h | h <;> subst h <;> rfl
  change sharpSubgroup (mainSubgroup M tau) = sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)
  rw [hmain, maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hM hType]

end OddOrder.Peterfalvi.S10Interface


