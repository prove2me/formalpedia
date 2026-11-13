-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:30:33.260561+00:00
-- url     : https://prove2.me/theorems/d07179ac-5449-45dc-a7cd-baf7ce892859
-- title:
--   Peterfalvi (14.3): the $T$-side type $P$ data
-- statement:
--   Formalizes Hypothesis (14.3), the type I maximal subgroup $L$ containing a normalizer, and the $T$-side type $P$ Dade integral character map $\tau_T$.
--
--   Main declarations: `LHypothesis` (Peterfalvi (14.3)); `tSideDadeMap` (T-side type-`P` Dade integral character map `τ_T`).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/TSideTypeP.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_OrbitOnIrr
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_Peterfalvi_S16_G0Coprime

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (14.3)**: the type-I maximal subgroup `L` containing `N_G(U)`,
its Fitting kernel `H`, the Dade extension, and the three virtual characters
`beta_S`, `beta_T`, and `beta_L`. -/
structure LHypothesis (hyp : Hypothesis (G := G)) where
  L : Subgroup G
  H : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  normalizer_U_le_L : Subgroup.normalizer (hyp.base.U : Set G) ≤ L
  H_eq_LF : H = maxNilpotentNormalHall L
  typeI_data : OddOrder.Peterfalvi.S15.TypeIOverNormalizerData hyp.base
  typeI_data_L_eq : typeI_data.L = L
  typeI_data_H_eq : typeI_data.H = H
  typeI_complement_card_eq_pq :
    Nat.card ↥typeI_data.frobenius.complement = hyp.base.p * hyp.base.q

/-- **`Q = M_F` is complemented by the intrinsic `U ⊔ W₁` in `T`** (ungated): `T = Q ⋊ (U ⋊ W₁)`.
The semidirect tower `T = T' ⋊ W₁` (`M_complement`) and `T' = M_F ⋊ U` (`derived_complement`,
`Q = M_F`) compose to a complement of the *normal* `Q` by `U ⊔ W₁`.

* **Disjoint** `Q ⊓ (U ⊔ W₁) = ⊥`: an element lies in `Q ≤ T'`, so in `(U ⊔ W₁) ⊓ T'`, which is `U`
  (decompose in the Frobenius complement `U ⋊ W₁`: the `W₁`-part lands in `W₁ ⊓ T' = ⊥`), and then
  in
  `Q ⊓ U = M_F ⊓ U = ⊥` (`derived_complement`).
* **Order** `|Q|·|U ⊔ W₁| = |T|`: `|U ⊔ W₁| = |U|·|W₁|` (Frobenius complement), `|M_F|·|U| = |T'|`
  (`derived_complement`), `|T'|·|W₁| = |T|` (`M_complement`).

This is the iso `↥T ⧸ (Q.subgroupOf T) ≃* ↥(U ⊔ W₁)` powering the quotient Frobenius `T/Q` (via
`isFrobeniusGroup_map_equiv` on `T_typeIII_UW1_frobenius`) feeding
`inertia_inflate_eq_of_frobeniusQuotient`. -/
theorem T_typeIII_Q_isComplement_UW1 [Finite G] (hyp : Hypothesis (G := G))
    (td : OddOrder.GroupTheory.TypeIIIData hyp.base.T) :
    Subgroup.IsComplement' (hyp.base.Q.subgroupOf hyp.base.T)
      ((td.typeP.U ⊔ td.typeP.W1).subgroupOf hyp.base.T) := by
  classical
  have hHeqQ : td.typeP.H = hyp.base.Q := by rw [td.typeP.H_eq, hyp.base.Q_eq_TF]
  have hHle : td.typeP.H ≤ derivedInG hyp.base.T := td.typeP.H_le
  have hUleM' : td.typeP.U ≤ derivedInG hyp.base.T := td.typeP.U_le
  have hM'leM : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQleM : hyp.base.Q ≤ hyp.base.T := hHeqQ ▸ (hHle.trans hM'leM)
  have hW1leM : td.typeP.W1 ≤ hyp.base.T := td.typeP.W1_le
  have hUW1leM : td.typeP.U ⊔ td.typeP.W1 ≤ hyp.base.T := sup_le (hUleM'.trans hM'leM) hW1leM
  -- `W₁ ⊓ T' = ⊥` (from `M_complement`).
  have hW1M' : td.typeP.W1 ⊓ derivedInG hyp.base.T = ⊥ := by
    have hd := td.typeP.M_complement.disjoint; rw [disjoint_iff] at hd
    rw [eq_bot_iff]; intro x hx; rw [Subgroup.mem_inf] at hx
    have hxM : x ∈ hyp.base.T := hM'leM hx.2
    have : (⟨x, hxM⟩ : ↥hyp.base.T) ∈ ((derivedInG hyp.base.T).subgroupOf hyp.base.T) ⊓
        (td.typeP.W1.subgroupOf hyp.base.T) := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_subgroupOf.mpr hx.2, Subgroup.mem_subgroupOf.mpr hx.1⟩
    rw [hd, Subgroup.mem_bot] at this; rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp this
  -- `M_F ⊓ U = ⊥` (from `derived_complement`).
  have hHU : td.typeP.H ⊓ td.typeP.U = ⊥ := by
    have hd := td.typeP.derived_complement.disjoint; rw [disjoint_iff] at hd
    rw [eq_bot_iff]; intro x hx; rw [Subgroup.mem_inf] at hx
    have hxM' : x ∈ derivedInG hyp.base.T := hHle hx.1
    have : (⟨x, hxM'⟩ : ↥(derivedInG hyp.base.T)) ∈
        (td.typeP.H.subgroupOf (derivedInG hyp.base.T)) ⊓
        (td.typeP.U.subgroupOf (derivedInG hyp.base.T)) := by
      rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_subgroupOf.mpr hx.1, Subgroup.mem_subgroupOf.mpr hx.2⟩
    rw [hd, Subgroup.mem_bot] at this; rw [Subgroup.mem_bot]; exact Subtype.ext_iff.mp this
  -- `(U ⊔ W₁) ⊓ T' ≤ U` (Frobenius decomposition).
  have hUW1M'_le_U : (td.typeP.U ⊔ td.typeP.W1) ⊓ derivedInG hyp.base.T ≤ td.typeP.U := by
    intro x hx; obtain ⟨hxUW1, hxM'⟩ := hx
    have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP td.common.1
    obtain ⟨⟨u, w⟩, hgw⟩ := (hfrob.isComplement.existsUnique ⟨x, hxUW1⟩).exists
    have huU : ((u : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ td.typeP.U :=
      Subgroup.mem_subgroupOf.mp u.2
    have hwW1 : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ td.typeP.W1 :=
      Subgroup.mem_subgroupOf.mp w.2
    have hxeq : x = ((u : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) *
        ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) := by
      have := congrArg (Subtype.val) hgw; simpa using this.symm
    have hwM' : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ derivedInG hyp.base.T := by
      have he : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) =
          ((u : ↥(td.typeP.U ⊔ td.typeP.W1)) : G)⁻¹ * x := by rw [hxeq]; group
      rw [he]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (td.typeP.U_le huU)) hxM'
    have hw1 : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) = 1 := by
      have : ((w : ↥(td.typeP.U ⊔ td.typeP.W1)) : G) ∈ td.typeP.W1 ⊓ derivedInG hyp.base.T :=
        ⟨hwW1, hwM'⟩
      rw [hW1M', Subgroup.mem_bot] at this; exact this
    rw [hxeq, hw1, mul_one]; exact huU
  -- Disjointness of the two `subgroupOf T`.
  have hdisj : Disjoint (hyp.base.Q.subgroupOf hyp.base.T)
      ((td.typeP.U ⊔ td.typeP.W1).subgroupOf hyp.base.T) := by
    rw [disjoint_iff, eq_bot_iff]; intro x hx; rw [Subgroup.mem_inf] at hx
    have hxQ : (x : G) ∈ hyp.base.Q := Subgroup.mem_subgroupOf.mp hx.1
    have hxUW1 : (x : G) ∈ td.typeP.U ⊔ td.typeP.W1 := Subgroup.mem_subgroupOf.mp hx.2
    have hxM' : (x : G) ∈ derivedInG hyp.base.T := hHle (hHeqQ ▸ hxQ)
    have hxU : (x : G) ∈ td.typeP.U := hUW1M'_le_U ⟨hxUW1, hxM'⟩
    have hmem : (x : G) ∈ td.typeP.H ⊓ td.typeP.U := ⟨hHeqQ ▸ hxQ, hxU⟩
    rw [hHU, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; exact Subtype.ext hmem
  -- Cardinality `|Q|·|U ⊔ W₁| = |T|`.
  have hcardUW1 : Nat.card ↥(td.typeP.U ⊔ td.typeP.W1) =
      Nat.card ↥td.typeP.U * Nat.card ↥td.typeP.W1 := by
    rw [← (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius td.typeP
        td.common.1).isComplement.card_mul_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv]
  have hcardM' : Nat.card ↥td.typeP.H * Nat.card ↥td.typeP.U =
      Nat.card ↥(derivedInG hyp.base.T) := by
    rw [← td.typeP.derived_complement.card_mul_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleM').toEquiv]
  have hcardM : Nat.card ↥(derivedInG hyp.base.T) * Nat.card ↥td.typeP.W1 =
      Nat.card ↥hyp.base.T := by
    rw [← td.typeP.M_complement.card_mul_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'leM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1leM).toEquiv]
  have hcard : Nat.card ↥(hyp.base.Q.subgroupOf hyp.base.T) *
      Nat.card ↥((td.typeP.U ⊔ td.typeP.W1).subgroupOf hyp.base.T) = Nat.card ↥hyp.base.T := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleM).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUW1leM).toEquiv, hcardUW1, ← hHeqQ,
      ← mul_assoc, hcardM', hcardM]
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

/-- **T-side (8.15) Dade support datum on `A₁(T) = T_σ^#`** (issue 9072 foundation, step 1).
The ungated σ-sharp Dade builder `S10.dadeSupportHypothesisData_of_subset_sigmaSharp` applied at
`X = sigmaSharp T`: `hXσ` is reflexivity, `hXne` follows from `M_σ ≠ ⊥`
(`S10.Msigma_ne_bot`), and `hXiff` is `T`-conjugation invariance of `T_σ^#` via
`sharpSubgroup_conj_mem` (`M_σ ⊴ T`, `le_normalizer_opiCoreInG`). -/
theorem tSideDadeSupport_nonempty [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (OddOrder.Peterfalvi.S10.DadeSupportHypothesisData hyp.base.T
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T)) := by
  have := hyp.base.finiteG
  -- `T ≤ N_G(M_σ(T))` (`M_σ = O_{σ}(T)` is normal in `T`), so `M_σ^#` is `T`-conj-invariant.
  have hTnorm : hyp.base.T ≤ Subgroup.normalizer
      ((OddOrder.BG.Ch3.S10.Msigma hyp.base.T : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma hyp.base.T) hyp.base.T
  refine OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset_sigmaSharp hG
    hyp.base.T_maximal (fun _ h => h) ?_ ?_
  · -- Nonempty: pick a nonidentity element of `M_σ(T) ≠ ⊥`.
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hyp.base.T_maximal)
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    exact ⟨a.1, (Set.mem_sdiff _).mpr
      ⟨SetLike.mem_coe.mpr a.2, fun h => ha1' (Set.mem_singleton_iff.mp h)⟩⟩
  · -- `T`-conjugation invariance of `T_σ^# = sharpSubgroup (M_σ T)`.
    intro m x hm
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (H := OddOrder.BG.Ch3.S10.Msigma hyp.base.T) (hTnorm (inv_mem hm)) h
      have h3 : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
      rwa [h3] at h2
    · exact OddOrder.Peterfalvi.S10.sharpSubgroup_conj_mem
        (H := OddOrder.BG.Ch3.S10.Msigma hyp.base.T) (hTnorm hm) h

open scoped Classical in
/-- **T-side type-`P` Dade integral character map `τ_T`** (issue 9072 foundation, step 2).
The genuine §7 integral character map of the (8.15) support datum
(`tSideDadeSupport_nonempty`), pinned exactly as the type-I `S14.Hypothesis.tau`:
`τ_T = dadeIntegralCharacterMap dadeData.dade (dadeData.dade.fullDadeIsometryData)`.
This is the `tauT` field of the T-side `S07.Hypothesis calT1_set (sigmaSharp T)` package that
`T_typeIII_calT1_coherent`/`T_typeIII_ratio_le`'s `horth` carrier consumes. -/
noncomputable def tSideDadeMap (hyp : Hypothesis (G := G)) [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥hyp.base.T) G :=
  haveI := hyp.base.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (tSideDadeSupport_nonempty hG hyp).some.dade
    ((tSideDadeSupport_nonempty hG hyp).some.dade.fullDadeIsometryData)

end OddOrder.Peterfalvi.S16


