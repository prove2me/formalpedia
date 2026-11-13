-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_StructureSetup
-- name    : OddOrder_Peterfalvi_S10_StructureSetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:03:56.517206+00:00
-- url     : https://prove2.me/theorems/22b1036f-ecb9-480e-b7ff-ceda5f3c3366
-- title:
--   Peterfalvi §8–10: structure setup for the minimal simple group analysis
-- statement:
--   Structure setup for the analysis in Peterfalvi, *Character Theory for the Odd Order Theorem*, split from the minimal-simple-groups basic file. It introduces the data for type $F$ groups (8.1), type I maximal subgroups (8.3) and type $\mathcal{P}$ maximal subgroups (8.4), and the notation $M_s$ and $A_1(M)=M_s^\#$ of (8.10).
--
--   Main declarations: `TypeFData` (Peterfalvi (8.1): data for a group of type `F`); `TypeIData` (Peterfalvi (8.3): data for a maximal subgroup of type I); `TypePData` (Peterfalvi (8.4): data for a maximal subgroup of type `P`); `mainSubgroup` (Peterfalvi (8.10): the notation `M_s`, shared as `mainSubgroup`); and 8 more.
--
--   The bundle also proves 26 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_StructureSetup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_StructureSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeIsometry
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_Hypothesis71
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_NormalCase
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_TwoFamilies
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSelectedEstimate
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TaxonomyOutput
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_Lemma1413
import Definitions.Def_OddOrder_Peterfalvi_S10_BGInterface
import Mathlib.GroupTheory.Nilpotent

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (8.1)**: data for a group of type `F`.

The definition is shared as `OddOrder.GroupTheory.TypeFData`; the proposition
form is `OddOrder.GroupTheory.IsTypeF`. -/
abbrev TypeFData (M : Subgroup G) := OddOrder.GroupTheory.TypeFData M

/-- **Peterfalvi (8.3)**: data for a maximal subgroup of type I. -/
abbrev TypeIData (M : Subgroup G) := OddOrder.GroupTheory.TypeIData M

/-- **Peterfalvi (8.4)**: data for a maximal subgroup of type `P`. -/
abbrev TypePData (M : Subgroup G) := OddOrder.GroupTheory.TypePData M

/-- **Group form of `isZGroup_of_isFrobeniusAction_of_odd`** ([BG] Proposition 3.9 / Huppert
V.8.18): the complement `A` of a finite Frobenius group `G' = N ⋊ A` whose complement has **odd
order** is a Z-group (every Sylow subgroup is cyclic).  This bridges the pair form
`IsFrobeniusGroup` to the action-based `isZGroup_of_isFrobeniusAction_of_odd`, mirroring
`normal_of_card_prime_of_isFrobeniusGroup_of_odd`. -/
theorem isZGroup_of_isFrobeniusGroup_of_odd {G' : Type*} [Group G'] [Finite G']
    {N A : Subgroup G'} (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G' N A)
    (hodd : Odd (Nat.card ↥A)) : _root_.IsZGroup ↥A := by
  let : N.Normal := hFrob.isNormal
  let : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom ↥N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hFrob.ne_bot_kernel
  exact OddOrder.Isaacs.Ch06.isZGroup_of_isFrobeniusAction_of_odd hFrob.toFrobeniusAction hodd

/-- **Peterfalvi (8.2.b), one direction**: when the complement has cyclic Sylow
subgroups, type `F` collapses to a Frobenius group with kernel `M_F`.

The cyclic-Sylow hypothesis is represented by the cardinal/exponent equality
`|U| = exp(U)`, the finite cyclic-complement criterion used in the text. -/
theorem typeF_frobenius_of_card_eq_exponent [Finite G] {M : Subgroup G}
    (data : TypeFData M) (hU : Nat.card ↥data.U = Monoid.exponent data.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.H.subgroupOf M) (data.U.subgroupOf M) := by
  -- The cyclic-Sylow hypothesis `|U| = exp(U) = exp(U₀)` forces `U₀ = U`, so the
  -- Frobenius structure of `H ⊔ U₀` (a field of `TypeFData`) collapses to `M`.
  have hexp : Monoid.exponent ↥data.U0 = Nat.card ↥data.U :=
    data.exponent_eq.trans hU.symm
  have hdvd1 : Nat.card ↥data.U ∣ Nat.card ↥data.U0 := by
    rw [← hexp]; exact Group.exponent_dvd_nat_card
  have hdvd2 : Nat.card ↥data.U0 ∣ Nat.card ↥data.U :=
    Subgroup.card_dvd_of_le data.U0_le
  have hcard : Nat.card ↥data.U0 = Nat.card ↥data.U := Nat.dvd_antisymm hdvd2 hdvd1
  have hU0eq : data.U0 = data.U := Subgroup.eq_of_le_of_card_ge data.U0_le hcard.ge
  -- `H ⊔ U = M`, from the complement `H ⋊ U = M`.
  have hHU : data.H ⊔ data.U = M := by
    have htop : data.H.subgroupOf M ⊔ data.U.subgroupOf M = ⊤ := data.complement.sup_eq_top
    have hmap := congrArg (Subgroup.map M.subtype) htop
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left data.H_le, inf_of_le_left data.U_le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
  -- Transport `frobenius_HU0 : IsFrobeniusGroup (H ⊔ U₀) H U₀` along `U₀ = U` and `H ⊔ U = M`.
  have hfrob := data.frobenius_HU0
  rw [hU0eq, hHU] at hfrob
  exact hfrob

/-- **Peterfalvi (8.2.b), the `⟸` half in its general form**: if the Sylow subgroups of the
complement `U` are cyclic (`IsZGroup ↥U`), then `M` is a Frobenius group with kernel `H = M_F`.

No oddness is needed here: a Z-group has `exp = |·|` (`IsZGroup.exponent_eq_card`), which is
exactly the hypothesis of `typeF_frobenius_of_card_eq_exponent` (the book: *"if the Sylow subgroups
of `U` are cyclic, `exp(U) = |U|`.  Thus, by (a), `|U₀| = |U|`, whence `U₀ = U`"*).  The `⟹` half
does need oddness — see `typeF_frobenius_iff_isZGroup`. -/
theorem typeF_frobenius_of_isZGroup [Finite G] {M : Subgroup G}
    (data : TypeFData M) (hZ : _root_.IsZGroup ↥data.U) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.H.subgroupOf M) (data.U.subgroupOf M) := by
  have := hZ
  exact typeF_frobenius_of_card_eq_exponent data
    (_root_.IsZGroup.exponent_eq_card (G := ↥data.U)).symm

/-- Centralizer of a cyclic subgroup equals the centralizer of a generator. -/
private theorem centralizer_eq_of_generator {W : Subgroup G} (g : G)
    (hg : g ∈ W) (hgen : ∀ w ∈ W, w ∈ Subgroup.zpowers g) :
    Subgroup.centralizer (W : Set G) = Subgroup.centralizer ({g} : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hg)
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hc : Commute g y := (Subgroup.mem_centralizer_iff.mp hy) g rfl
    obtain ⟨n, hn⟩ := hgen w hw
    rw [← hn]
    simpa using (hc.zpow_left n).eq

set_option backward.isDefEq.respectTransparency false in
/-- Lift conjugation transport from `↥M` to `G`: `(K^c).map ι = (K.map ι)^(c : G)`. -/
private theorem map_subtype_conj_smul {M : Subgroup G} (c : ↥M)
    (K : Subgroup ↥M) :
    (MulAut.conj c • K).map M.subtype = MulAut.conj (c : G) • (K.map M.subtype) := by
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def, Subgroup.map_map,
    Subgroup.map_map]
  refine congrArg (fun f => K.map f) ?_
  ext x
  simp [MulAut.conj_apply]

/-- **`|K*| = w₂` carrier bridge** (lane-b W3, BG §14 group theory; axiom-clean).  For a type-`P`
maximal `S` of a minimal simple group of odd order, with κ-Hall factor `K` (cyclic) and any
`TypePData d` on `S`, the dual factor `K* = M_σ(S) ⊓ C_G(K)` has order `|W₂| = w₂`.

This is the group-theoretic translation that pairs with the §11 character reduction (`q > p`,
`w₂ < w₁`) to close `card_kappaHall_lt_of_isTypeIIIorIV`, and with `typeP_duality` to supply the
(8.8) Type-II partner (`exists_typeII_maximal_with_w2_of_typeP`).  Proof: `W₂ = M' ⊓ C(W₁)`
(`centralizer_W1`, `W₁` cyclic) and `W₂ ≤ M_F ≤ M_σ ≤ M'` (`W2_le`, `H_eq`,
`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`) sandwich `M_σ ⊓ C(W₁) = W₂`; `K` and `W₁`
both complement the normal Hall `M'`, hence are `S`-conjugate (Schur–Zassenhaus,
`IsComplement'.exists_conj_of_coprime`); conjugating `M_σ ⊓ C(K)` (with `M_σ` `S`-invariant) onto
`M_σ ⊓ C(W₁) = W₂` gives the equal cardinality.  No character theory. -/
theorem card_Msigma_inf_centralizer_eq_card_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S K : Subgroup G} (hS : S ∈ maximalSubgroups G)
    (hSP : OddOrder.BG.Ch4.S14.IsTypeP S) (hKS : K ≤ S)
    (hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S) (K.subgroupOf S)) [IsCyclic ↥K]
    (d : TypePData S) :
    Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G)) =
      Nat.card ↥d.W2 := by
  classical
  have : IsCyclic ↥d.W1 := d.W1_cyclic
  obtain ⟨g0, hg0gen⟩ := IsCyclic.exists_generator (α := ↥d.W1)
  set g : G := (g0 : G) with hgdef
  have hgW1 : g ∈ d.W1 := g0.2
  have hgne : g ≠ 1 := by
    intro h
    apply d.W1_nontrivial
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨n, hn⟩ := hg0gen ⟨w, hw⟩
    have hg0one : g0 = 1 := Subtype.ext h
    rw [hg0one] at hn
    rw [Subgroup.mem_bot]
    have : (⟨w, hw⟩ : ↥d.W1) = 1 := by rw [← hn]; simp
    exact Subtype.ext_iff.mp this
  have hgenW1 : ∀ w ∈ d.W1, w ∈ Subgroup.zpowers g := by
    intro w hw
    obtain ⟨n, hn⟩ := hg0gen ⟨w, hw⟩
    refine ⟨n, ?_⟩
    have := congrArg (Subgroup.subtype d.W1) hn
    simpa [hgdef] using this
  have hCW1 : Subgroup.centralizer (d.W1 : Set G) = Subgroup.centralizer ({g} : Set G) :=
    centralizer_eq_of_generator g hgW1 hgenW1
  have hW2Msigma : d.W2 ≤ OddOrder.BG.Ch3.S10.Msigma S := by
    refine d.W2_le.trans (le_trans inf_le_left ?_)
    rw [d.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hS
  have hMsigmaM' : OddOrder.BG.Ch3.S10.Msigma S ≤ derivedInG S :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hS
  have hcent : derivedInG S ⊓ Subgroup.centralizer ({g} : Set G) = d.W2 :=
    d.centralizer_W1 g hgW1 hgne
  have hkey : OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (d.W1 : Set G) = d.W2 := by
    rw [hCW1]
    apply le_antisymm
    · calc OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer ({g} : Set G)
          ≤ derivedInG S ⊓ Subgroup.centralizer ({g} : Set G) := inf_le_inf_right _ hMsigmaM'
        _ = d.W2 := hcent
    · rw [le_inf_iff]
      exact ⟨hW2Msigma, by rw [← hcent]; exact inf_le_right⟩
  have hKcompl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (K.subgroupOf S) :=
    OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hS hSP hKS hK
  have hW1compl : Subgroup.IsComplement' ((derivedInG S).subgroupOf S) (d.W1.subgroupOf S) :=
    d.M_complement
  have hNeq : (derivedInG S).subgroupOf S = commutator ↥S :=
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective _
  have hNnormal : ((derivedInG S).subgroupOf S).Normal := by rw [hNeq]; infer_instance
  have : Group.IsSolvable ↥S := hG.isSolvable_of_mem_maximalSubgroups hS
  have : Group.IsSolvable ↥((derivedInG S).subgroupOf S) := inferInstance
  have hcop : Nat.Coprime (Nat.card ↥((derivedInG S).subgroupOf S))
      ((derivedInG S).subgroupOf S).index := by
    rw [hKcompl.symm.index_eq_card]
    exact OddOrder.BG.Ch4.S14.coprime_card_derived_kappaHall_of_isComplement' hK hKcompl
  obtain ⟨n, hnN, hnconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) hW1compl hKcompl
  have hconjG : MulAut.conj (n : G) • d.W1 = K := by
    have h2 : MulAut.conj (n : G) • ((d.W1.subgroupOf S).map S.subtype)
            = (K.subgroupOf S).map S.subtype := by
      rw [← map_subtype_conj_smul]
      exact congrArg (Subgroup.map S.subtype) hnconj
    rwa [Subgroup.map_subgroupOf_eq_of_le d.W1_le,
      Subgroup.map_subgroupOf_eq_of_le hKS] at h2
  set g0G : G := (n : G) with hg0G
  have hg0M : g0G ∈ S := n.2
  have hMsigmaInv : MulAut.conj g0G • OddOrder.BG.Ch3.S10.Msigma S = OddOrder.BG.Ch3.S10.Msigma S :=
      by
    apply conj_smul_eq_self_of_mem_normalizer
    have hsub : S ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma S) := by
      rw [OddOrder.BG.Ch3.S10.Msigma]
      exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma S) S
    exact hsub hg0M
  have hCKconj : Subgroup.centralizer (K : Set G)
      = MulAut.conj g0G • Subgroup.centralizer (d.W1 : Set G) := by
    rw [OddOrder.BG.Ch3.S13.smul_centralizer_subgroup, hconjG]
  have htransport : OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G)
      = MulAut.conj g0G • (OddOrder.BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (d.W1 : Set G)) := by
    rw [Subgroup.smul_inf, hMsigmaInv, ← hCKconj]
  rw [htransport, hkey]
  exact (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g0G) d.W2).toEquiv).symm

/-- **Peterfalvi (8.8)/(8.13) for the given `M`**: a non-type-I (type-`P`) maximal subgroup `M`
admits a Type-II maximal subgroup `S` whose cyclic-factor order `|S : [S,S]|` equals `|W₂|`.

This is the `M`-specific case-(b) datum of Theorem (8.8): the type-`P` maximal `M` participates in
the case-(b) configuration of (8.8), one of whose two distinguished maximal subgroups is of Type II
and shares the cyclic-factor order `w₂ = |W₂|`.  It is the §8 obligation behind both the (9.3) order
relations (`S11.typeIIIorIV_W2_prime`) and the (10.3) prime computation (`S12.Hypothesis.w2_prime`).

**Proof (BG §14 duality + the `|K*| = w₂` bridge)**: `M` is type `P₁` (from
`proposition_type_classification` on the III/IV/V hypothesis), hence κ-nonempty.  Pick a κ-Hall
`K ≤ M` (Hall's theorem in solvable `M`) and set `K* = M_σ(M) ⊓ C(K)`.  `typeP_duality` produces the
nonconjugate partner `M*` with `K*` its κ-Hall and `Z = K ⊔ K*` cyclic, and the disjunction
`IsTypeP2 M ∨ IsTypeP2 M*`; `M` type `P₁` excludes the left disjunct, so `M*` is `P₂` = Type II.
Then `[M* : (M*)'] = |K*|` (`card_kappaHall_eq_derived_index` for `M*`, `K*` cyclic) and
`|K*| = |W₂|` (`card_Msigma_inf_centralizer_eq_card_W2`).  Cites
`proposition_type_classification` (lane-f W1, since proved); axiom-clean. -/
theorem exists_typeII_maximal_with_w2_of_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (data : TypePData M)
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    ∃ S : Subgroup G, S ∈ maximalSubgroups G ∧ IsTypeII S ∧
      ((derivedInG S).subgroupOf S).index = Nat.card ↥data.W2 := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `M` is type `P₁`, hence κ-nonempty (`BG.Ch4.S14.IsTypeP`).
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M := by
    rcases hType with h | h | h
    · exact ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.1.mp (Or.inl h)).1
    · exact ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.1.mp (Or.inr h)).1
    · exact ((OddOrder.BG.Ch4.S16.proposition_type_classification hG hM).2.2.2.1.mp h).1
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M := OddOrder.BG.Ch4.S14.isTypeP_of_isTypeP1 hP1
  -- A κ-Hall `K` of `M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (OddOrder.BG.Ch4.S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' := Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M) (K.subgroupOf M) := by
    rw [hKeq]; exact hK'
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  -- `typeP_duality`: partner `Mstar`, type-`P₂` disjunction, cyclic `Z = K ⊔ K*`.
  obtain ⟨_, _, Mstar, ⟨hMstarMem, hMstarP, _,
      ⟨hKstarMstar, hKstar_hall, _⟩, hcyc, _, hP2disj, _⟩, _⟩ :=
    OddOrder.BG.Ch4.S14.typeP_duality hG hM hP hKM hK hKstardef
  -- `M` not `P₂` ⟹ partner `Mstar` is `P₂` = Type II.
  have hnotP2M : ¬ OddOrder.BG.Ch4.S14.IsTypeP2 M := fun h2 =>
    OddOrder.BG.Ch4.S14.not_isTypeP1_and_isTypeP2 ⟨hP1, h2⟩
  have hP2Mstar : OddOrder.BG.Ch4.S14.IsTypeP2 Mstar := hP2disj.resolve_left hnotP2M
  have hMstarII : IsTypeII Mstar :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG hMstarMem).2.1.mpr hP2Mstar
  -- `K` and `K*` cyclic (subgroups of cyclic `Z = K ⊔ K*`).
  have : IsCyclic ↥(K ⊔ Kstar) := hcyc
  have : IsCyclic ↥K :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  have : IsCyclic ↥Kstar :=
    isCyclic_of_injective (Subgroup.inclusion (le_sup_right : Kstar ≤ K ⊔ Kstar))
      (Subgroup.inclusion_injective _)
  -- `[Mstar:Mstar'] = |K*| = |W₂|`.
  refine ⟨Mstar, hMstarMem, hMstarII, ?_⟩
  rw [← OddOrder.BG.Ch4.S16.card_kappaHall_eq_derived_index (K := Kstar) hG hMstarMem hMstarP
    hKstarMstar hKstar_hall, hKstardef]
  exact card_Msigma_inf_centralizer_eq_card_W2 hG hM hP hKM hK data

/-- **Peterfalvi (8.10)**: the notation `M_s`, shared as `mainSubgroup`. -/
noncomputable abbrev mainSubgroup (M : Subgroup G) (tau : PeterfalviType) :=
  OddOrder.GroupTheory.mainSubgroup M tau

/-- **Peterfalvi (8.10)**: the notation `A_1(M) = M_s#`, shared as `A1`. -/
noncomputable abbrev A1 (M : Subgroup G) (tau : PeterfalviType) := OddOrder.GroupTheory.A1 M tau

/-- **`M`-conjugation invariance of `sharpSubgroup H`** when `M` normalizes `H` (general helper for
the type-`τ` Dade-support sets `A₁(M) = M_s#`, `A(M) = (M')#`, all of the form `sharpSubgroup H`
with `H ⊴ M`). -/
theorem sharpSubgroup_conj_mem {H : Subgroup G} {m : G}
    (hn : m ∈ Subgroup.normalizer (H : Set G)) {a : G}
    (ha : a ∈ OddOrder.GroupTheory.sharpSubgroup H) :
    m * a * m⁻¹ ∈ OddOrder.GroupTheory.sharpSubgroup H := by
  obtain ⟨haH, ha1⟩ := (Set.mem_sdiff a).mp ha
  rw [Subgroup.mem_normalizer_iff] at hn
  refine (Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr ((hn a).mp (SetLike.mem_coe.mp haH)), ?_⟩
  intro h
  refine ha1 (Set.mem_singleton_iff.mpr ?_)
  have harw : a = m⁻¹ * (m * a * m⁻¹) * m := by group
  rw [harw, Set.mem_singleton_iff.mp h]
  group

/-- **Peterfalvi (8.10)**: the book-literal type-`𝒫` support `A(M) = ⋃_{x ∈ M_s^#} C_{M'}(x)^#`,
the nonidentity elements of `M' = derivedInG M` centralizing some nonidentity element of the core
`M_s = M_σ`.  Faithful for every Peterfalvi type; for type `P₂` (= type II, `M_σ = M_F ⊊ M'`) it is
strictly smaller than `typePA = (M')^#`, which over-claims the Frobenius-complement points `U^#`
(they centralize nothing in `M_σ^#`).

Unlike `typePA` this takes **no** `TypePData` argument: the book's `A(M)` depends only on `M`. -/
def typePACore (M : Subgroup G) : Set G :=
  OddOrder.GroupTheory.centralizerSupport
    (OddOrder.GroupTheory.sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)) (derivedInG M)

/-- **Peterfalvi (8.10)**: `A₀(M) = A(M) ∪ V^M` on the book-literal `A(M) = typePACore M`, with
`V^M = conjClassSetIn M (typePV M data)` the **`M`**-conjugacy closure of the cyclic-TI regular set
`V = W ∖ (W₁ ∪ W₂)` (Coq `class_support V L`; the `G`-closure would not fit inside the proper `M`,
cf. the `typePA0` docstring). -/
def typePACore0 (M : Subgroup G) (data : TypePData M) : Set G :=
  typePACore M ∪ OddOrder.GroupTheory.conjClassSetIn M (OddOrder.GroupTheory.typePV M data)

@[simp] theorem mem_typePACore {M : Subgroup G} {y : G} :
    y ∈ typePACore M ↔
      y ∈ derivedInG M ∧ y ≠ 1 ∧
        ∃ x ∈ OddOrder.GroupTheory.sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M),
          y ∈ Subgroup.centralizer ({x} : Set G) :=
  Iff.rfl

/-- Every element of `A(M)` is a nonidentity element of `G`. -/
theorem typePACore_subset_sharp {M : Subgroup G} :
    typePACore M ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G) := by
  rintro y ⟨-, hy1, -⟩
  exact OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ y, hy1⟩

/-- **`1 ∉ A(M)`**: the support consists of nonidentity elements (`typePACore_subset_sharp`).
This is the `h1notA` input the Dade-coherence producer `S07.coherentEqualDegree_fromDade`
requires (`1 ∉ A` guarantees the induced difference `τ(χ_j − χ_0)` sees the whole Dade
support). -/
theorem typePACore_one_not_mem {M : Subgroup G} : (1 : G) ∉ typePACore M := fun h =>
  (OddOrder.Peterfalvi.S04.mem_sharp.mp (typePACore_subset_sharp h)).2 rfl

/-- `A(M) ⊆ M'` (the support lives in the derived subgroup). -/
theorem typePACore_subset_derived {M : Subgroup G} :
    typePACore M ⊆ (derivedInG M : Set G) := fun _ hy => hy.1

/-- `A(M) ⊆ M`. -/
theorem typePACore_subset {M : Subgroup G} : typePACore M ⊆ (M : Set G) := fun _ hy =>
  Subgroup.map_subtype_le _ hy.1

/-- **`A(M)` is `M`-conjugation invariant.**  Both `M_σ` (`Msigma`) and `M' = derivedInG M` are
`M`-normal, so conjugating `y ∈ A(M)` and its centralized `M_σ`-witness by `m ∈ M` stays in
`A(M)`. -/
theorem typePACore_conj_mem [Finite G] {M : Subgroup G} {m : G} (hm : m ∈ M) {y : G}
    (hy : y ∈ typePACore M) : m * y * m⁻¹ ∈ typePACore M := by
  obtain ⟨hyM', hy1, x, hxσ, hyC⟩ := hy
  have hmM' : m ∈ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) :=
    OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M hm
  have hmMσ : m ∈ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hm
  refine ⟨?_, ?_, m * x * m⁻¹, ?_, ?_⟩
  · -- `m·y·m⁻¹ ∈ M'` since `m ∈ M ≤ N_G(M')`.
    exact (Subgroup.mem_normalizer_iff.mp hmM' y).mp hyM'
  · exact fun h => hy1 (by
      have hyeq : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [hyeq, h]; group)
  · exact sharpSubgroup_conj_mem hmMσ hxσ
  · -- `m·y·m⁻¹` centralizes `m·x·m⁻¹`.
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    calc m * y * m⁻¹ * (m * x * m⁻¹)
        = m * (y * x) * m⁻¹ := by group
      _ = m * (x * y) * m⁻¹ := by rw [hyC]
      _ = m * x * m⁻¹ * (m * y * m⁻¹) := by group

/-- **`A(M) ⊆ hatMsigma M`** (BG Theorem-E notation): every `A(M)`-point centralizes a nonidentity
`M_σ`-element, so `M_σ ⊓ C_G(y) ≠ ⊥`, and lies in `M' ≤ M`. -/
theorem typePACore_subset_hatMsigma [Finite G] {M : Subgroup G} :
    typePACore M ⊆ OddOrder.BG.Ch4.S16.hatMsigma M := by
  rintro y ⟨hyM', -, x, hxσ, hyC⟩
  obtain ⟨hxMσ, hx1⟩ := (Set.mem_sdiff _).mp hxσ
  refine ⟨Subgroup.map_subtype_le _ hyM', ?_⟩
  -- `x ∈ M_σ ⊓ C_G(y)` is a nonidentity witness (`y ∈ C_G(x) ↔ x ∈ C_G(y)`).
  intro hbot
  have hxCy : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    exact hyC.symm
  have : x ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_inf.mpr ⟨SetLike.mem_coe.mp hxMσ, hxCy⟩
  rw [hbot] at this
  exact hx1 (Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp this))

/-- **(8.10) on the types of class `𝒫`**: the type-uniform support `A(M) = typeA M tau` is the
book-literal `typePACore M`.  The index subgroup is `M_s = M_σ` for every type
(`mainSubgroup_eq_Msigma`, BG Proposition 16.1) and, off Type I, the host of the centralizers is
`M'`.  Together with `typeA_eq_typeIA` this identifies `typeA` with (8.10) on the nose. -/
theorem typeA_eq_typePACore [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau M) (h : tau ≠ PeterfalviType.I) :
    OddOrder.GroupTheory.typeA M tau = typePACore M := by
  rw [OddOrder.GroupTheory.typeA, OddOrder.GroupTheory.supportHost_of_ne_typeI M h,
    OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hM htau, typePACore]

/-- **`A₁(M) ⊆ A(M)` for every type** (the first inclusion of (8.10)'s closing sentence).
`M_s = M_σ` lies in the host of `A(M)`: inside `M` on Type I (`Msigma_le`), inside `M'`
elsewhere (`Msigma_le_derived`). -/
theorem A1_subset_typeA [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau M) :
    A1 M tau ⊆ OddOrder.GroupTheory.typeA M tau := by
  refine OddOrder.GroupTheory.A1_subset_typeA ?_
  rw [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hM htau]
  cases tau with
  | I => exact OddOrder.BG.Ch3.S10.Msigma_le M
  | _ => exact OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM

/-- **`A₁(M) = M_σ^#` for every Peterfalvi type**: `A₁(M) = M_s^#` by (8.10), and `M_s = M_σ`
by (8.11)'s Reference (BG Proposition 16.1, `mainSubgroup_eq_Msigma`).  Type-uniform form of
`S10Interface.A1_eq_sigmaSharp_of_typeI_or_II`. -/
theorem A1_eq_sigmaSharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau M) :
    A1 M tau = OddOrder.BG.Ch4.S14.sigmaSharp M := by
  change OddOrder.GroupTheory.sharpSubgroup (OddOrder.GroupTheory.mainSubgroup M tau) = _
  rw [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hM htau]
  rfl

/-- **Peterfalvi (8.11)**: if `M` has one of the five Peterfalvi types, then
`M_F` and `M_s` are Hall subgroups of `G`.

The proof is a BG Section 16 consequence, not a local Peterfalvi argument: `M_s = M_σ`
(`mainSubgroup_eq_Msigma`, BG Prop 16.1) is an ambient Hall subgroup by BG Theorem A(1)
(`Msigma_isHall`, re-indexed to `π(M_σ)` by `primeFactors_Msigma_eq_sigma`), and `M_F` combines
its Hall-in-`M` property (`maxNilpotentNormalHall_isHall`) with `M_F ≤ M_σ` for the
`[G : M]`-part of its index. -/
theorem hall_maxNilpotentNormalHall_and_mainSubgroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (hType : HasPeterfalviType tau M) :
    Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
        (maxNilpotentNormalHall M) ∧
      Ch03.IsHallSubgroup (Nat.card ↥(mainSubgroup M tau)).primeFactors
        (mainSubgroup M tau) := by
  have hMsHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  constructor
  · refine ⟨fun p hp => hp, fun p hpidx hpH => ?_⟩
    have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hpidx).1
    -- `p ∈ σ(M)`, via `M_F ≤ M_σ` and `π(M_σ) = σ(M)`.
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      (OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hM p).mp
        (Nat.mem_primeFactors.mpr ⟨hp_prime,
          (Nat.dvd_of_mem_primeFactors hpH).trans (Subgroup.card_dvd_of_le
            (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM)),
          Nat.card_pos.ne'⟩)
    -- Split `[G : M_F] = [M : M_F] · [G : M]`.
    have hrel : ((maxNilpotentNormalHall M).subgroupOf M).index * M.index
        = (maxNilpotentNormalHall M).index :=
      Subgroup.relIndex_mul_index (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le M)
    have hp_dvd : p ∣ ((maxNilpotentNormalHall M).subgroupOf M).index * M.index := by
      rw [hrel]; exact Nat.dvd_of_mem_primeFactors hpidx
    rcases hp_prime.dvd_mul.mp hp_dvd with hin | hout
    · -- the `[M : M_F]`-part is coprime to `|M_F|`: `M_F` is Hall in `M`.
      exact (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall M).2 p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hin, Subgroup.index_ne_zero_of_finite⟩) hpH
    · -- the `[G : M]`-part divides `[G : M_σ]`, which avoids `σ(M)`-primes.
      have hpMσidx : p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index :=
        hout.trans ⟨((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index,
          ((Nat.mul_comm _ _).trans
            (Subgroup.relIndex_mul_index (OddOrder.BG.Ch3.S10.Msigma_le M))).symm⟩
      exact hMsHall.2 p
        (Nat.mem_primeFactors.mpr ⟨hp_prime, hpMσidx, Subgroup.index_ne_zero_of_finite⟩) hpσ
  · -- `M_s = M_σ` (BG Prop 16.1); the Hall property is `Msigma_isHall` re-indexed to `π(M_σ)`.
    change Ch03.IsHallSubgroup
      (Nat.card ↥(OddOrder.GroupTheory.mainSubgroup M tau)).primeFactors
      (OddOrder.GroupTheory.mainSubgroup M tau)
    rw [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hM hType]
    exact ⟨fun p hp => hp, fun p hpidx hp => hMsHall.2 p hpidx
      ((OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hM p).mp hp)⟩

/-- **Peterfalvi (8.12.b)**, faithful form: type I/II Sylow-complement centralizer control.

For `M` of type I or II, its genuine `(κ ∪ σ)ᶜ`-Hall complement `U` (`M = H ⋊ U` for type I,
`[M,M] = H ⋊ U` for type II), and every non-empty `X ⊆ U#` with `C_H(X) ≠ 1`, `M` is the unique
maximal subgroup of `G` over `C_G(X)`.  Proof: `⟨X⟩ ≤ U` is a nontrivial `(κ ∪ σ)ᶜ`-subgroup with
`C_{M_σ}(⟨X⟩) = C_{M_σ}(X) ≠ 1` (`M_F = M_σ` for type I/II), so BG **Theorem B(4)**
(`typeP_hall_small_subgroup_cyclic_tau2`) pins `ℳ(C_G(⟨X⟩)) = {M}`, and `C_G(X) = C_G(⟨X⟩)`
(`centralizer_closure`).  Reference: [BG], §16, Theorem B and Proposition 16.1. -/
theorem typeI_or_typeII_centralizer_unique_hall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M ∨ IsTypeII M) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    ∀ X : Set G, X.Nonempty → X ⊆ sharpSubgroup U →
      maxNilpotentNormalHall M ⊓ Subgroup.centralizer X ≠ ⊥ →
        Subgroup.centralizer X ≤ M ∧ IsUniquelyMaximal (Subgroup.centralizer X) := by
  intro X hXne hXU hCX
  classical
  -- `Y = ⟨X⟩ ≤ U` is a nontrivial `(κ ∪ σ)ᶜ`-subgroup.
  set Y : Subgroup G := Subgroup.closure X with hYdef
  have hXsubU : X ⊆ (U : Set G) := hXU.trans (by rw [sharpSubgroup]; exact Set.sdiff_subset)
  have hYU : Y ≤ U := (Subgroup.closure_le U).mpr hXsubU
  obtain ⟨x0, hx0X⟩ := hXne
  have hx0mem : x0 ∈ (U : Set G) ∧ x0 ∉ ({1} : Set G) := hXU hx0X
  have hYne : Y ≠ ⊥ := fun hbot => hx0mem.2
    (by rw [Set.mem_singleton_iff]; exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.subset_closure hx0X))
  -- `C_G(X) = C_G(Y)` and `M_F = M_σ` for type I/II.
  have hCeq : Subgroup.centralizer X = Subgroup.centralizer (Y : Set G) :=
    (Subgroup.centralizer_closure X).symm
  have hMFσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II hG hM hType
  have hCY : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (Y : Set G) ≠ ⊥ := by
    rw [← hCeq, ← hMFσ]; exact hCX
  -- BG Theorem B(4): `ℳ(C_G(Y)) = {M}`.
  have hM4 := (OddOrder.BG.Ch4.S14.typeP_hall_small_subgroup_cyclic_tau2 hG hM hUM hU hYU hYne
      hCY).1
  rw [hCeq]
  have hCleM : Subgroup.centralizer (Y : Set G) ≤ M :=
    (mem_maximalSubgroupsContaining.mp (hM4 ▸ Set.mem_singleton M)).2
  refine ⟨hCleM, IsUniquelyMaximal.of_unique_maximal
    (hCleM.trans_lt (lt_top_iff_ne_top.mpr hM.1)) hM hCleM (fun K hK hHK => ?_)⟩
  have hKmem : K ∈ maximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := ⟨hK, hHK⟩
  rw [hM4, Set.mem_singleton_iff] at hKmem
  exact hKmem

/-- **Peterfalvi (8.6.b II)**, canonical form: for a maximal subgroup `M` of Type II and **any**
type-`P` data on `M`, the complement `U` has `N_G(U) ⊄ M`.

Definition (8.6.b II) records `N_G(U) ⊄ M` for *the* `U` of the chosen `(8.4)` data; since any two
type-`P` complements of `H = M_F` in `M' = [M,M]` are `M'`-conjugate (Schur–Zassenhaus in the
solvable proper subgroup `M'`) and `N_G(U^g) = N_G(U)^g` with `g ∈ M' ≤ M`, the property is
independent of the witness.  Stated here so the (9.3) order relations can apply it to the type-`P`
data carried by `TypesIIIIIIVSetup` (which need not be the `IsTypeII` witness).  The
complement-conjugacy step is the residual obligation. -/
theorem typeII_normalizer_not_le_of_typePData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (data : TypePData M)
    (hM : M ∈ maximalSubgroups G) (hII : IsTypeII M) :
    ¬ Subgroup.normalizer (data.U : Set G) ≤ M := by
  classical
  obtain ⟨td⟩ := hII
  -- The Type-II witness carries `¬ N_G(U₀) ≤ M` for its own complement `U₀ = td.typeP.U`.
  -- `M_F = maxNilpotentNormalHall M` also equals `maxNilpotentNormalHall M'` (type II Fitting).
  have hMFeq : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M :=
    td.derived_fitting_eq.trans td.typeP.H_eq
  -- Kernel `N = M_F` inside `M' = derivedInG M`: normal and Hall (hence coprime index).
  have hNnormal : ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)).Normal :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal (derivedInG M)
  have hcop : Nat.Coprime
      (Nat.card ↥((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)))
      ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)).index :=
    (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall (derivedInG M)).coprime_index
  -- Both `td.typeP.U` and `data.U` complement `M_F` in `M'` (Definition (8.4)
  -- `derived_complement`).
  have hTd_compl : Subgroup.IsComplement'
      ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M))
      (td.typeP.U.subgroupOf (derivedInG M)) := by
    have h := td.typeP.derived_complement; rwa [td.typeP.H_eq, ← hMFeq] at h
  have hData_compl : Subgroup.IsComplement'
      ((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M))
      (data.U.subgroupOf (derivedInG M)) := by
    have h := data.derived_complement; rwa [data.H_eq, ← hMFeq] at h
  -- `M'` (and hence `M_F ≤ M'`) is solvable, giving Schur–Zassenhaus conjugacy of complements.
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hM'leM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have : Group.IsSolvable ↥(derivedInG M) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM'leM)
  obtain ⟨n, -, hnconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) hTd_compl hData_compl
  -- Lift the `M'`-conjugation to `G`: `conj (↑n) • td.typeP.U = data.U`, with `↑n ∈ M' ≤ M`.
  have hnM : (n : G) ∈ M := hM'leM (SetLike.coe_mem n)
  have hconjG : MulAut.conj (n : G) • td.typeP.U = data.U := by
    have h2 : MulAut.conj (n : G) •
          ((td.typeP.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype)
          = (data.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype := by
      rw [← map_subtype_conj_smul]
      exact congrArg (Subgroup.map (derivedInG M).subtype) hnconj
    rwa [Subgroup.map_subgroupOf_eq_of_le td.typeP.U_le,
      Subgroup.map_subgroupOf_eq_of_le data.U_le] at h2
  -- If `N_G(data.U) ≤ M`, transport back to `N_G(U₀) ≤ M`, contradicting the Type-II witness.
  intro hle
  refine td.normalizer_not_le ?_
  have htrans : Subgroup.normalizer (data.U : Set G)
      = MulAut.conj (n : G) • Subgroup.normalizer (td.typeP.U : Set G) := by
    rw [normalizer_pointwise_smul, hconjG]
  have hMconj : MulAut.conj (n : G) • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hnM)
  rw [htrans] at hle
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp (hle.trans_eq hMconj.symm)

/-- **Peterfalvi (8.14), the faithful per-`x` signalizer kernel `R(x)`** (Coq `FTsignalizer`,
PFsection8): on the escaping set (`x ∈ A` with `C_G(x) ⊄ M`) it is the BG Theorem-D signalizer
`FT_signalizer x = (N[x])_σ ⊓ C_G(x)` attached to the *supporting* maximal `N[x] ⊇ C_G(x)`; off
the escaping set `R(x) = 1`.  For the supporting `N[x]` (type `F` or `P₂`,
`signalizer_structure_of_mem_sigmaSharp`) one has `(N[x])_F = (N[x])_σ`
(`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`), so on the escaping set this is
Peterfalvi's `R(x) = C_{(N[x])_F}(x)`.

This is **not** `supportKernel M M A` (`= C_{M_F}(x)` on the escaping set): the self-based kernel
is unsatisfiable as an (2.2) kernel, since for escaping `x` both `C_{M_F}(x)` and `C_M(x)`
contain `x`, contradicting the `(2.2.b)` complement-disjointness and `(2.2.c)` coprimality (the
issue-8021 unfaithfulness, at the Dade-hypothesis carrier). -/
noncomputable def ftSupportKernel (M : Subgroup G) (A : Set G) (x : G) : Subgroup G := by
  classical
  exact
    if x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A then
      OddOrder.BG.Ch4.S16.FT_signalizer x
    else ⊥

/-- Off the escaping set the faithful kernel is trivial. -/
theorem ftSupportKernel_eq_bot_of_not_escaping {M : Subgroup G} {A : Set G} {x : G}
    (hx : x ∉ OddOrder.GroupTheory.escapingCentralizerSet M A) :
    ftSupportKernel M A x = ⊥ := by
  unfold ftSupportKernel
  rw [if_neg hx]

/-- On the escaping set the faithful kernel is the BG signalizer. -/
theorem ftSupportKernel_eq_of_escaping {M : Subgroup G} {A : Set G} {x : G}
    (hx : x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A) :
    ftSupportKernel M A x = OddOrder.BG.Ch4.S16.FT_signalizer x := by
  unfold ftSupportKernel
  rw [if_pos hx]

/-- The escaping-set membership (hence the faithful kernel) only depends on the point, not on
which support set `A ∋ x` it is tested against: for `x ∈ A₁ ⊆ A`,
`ftSupportKernel M A₁ x = ftSupportKernel M A x`.  This is what makes the (2.11) restriction of a
faithful Dade datum to a smaller support again faithful. -/
theorem ftSupportKernel_restrict {M : Subgroup G} {A A₁ : Set G} (hA₁A : A₁ ⊆ A) {x : G}
    (hx : x ∈ A₁) :
    ftSupportKernel M A₁ x = ftSupportKernel M A x := by
  by_cases hC : Subgroup.centralizer ({x} : Set G) ≤ M
  · rw [ftSupportKernel_eq_bot_of_not_escaping (fun h => h.2 hC),
      ftSupportKernel_eq_bot_of_not_escaping (fun h => h.2 hC)]
  · rw [ftSupportKernel_eq_of_escaping ⟨hx, hC⟩, ftSupportKernel_eq_of_escaping ⟨hA₁A hx, hC⟩]

/-- **Peterfalvi (8.14), the faithful thickened support** `Ã(M,A) = ⋃_{x∈A} (x·R(x))^G`, with the
per-`x` signalizer `R = ftSupportKernel M A`. -/
noncomputable def ftThickenedSupport (M : Subgroup G) (A : Set G) : Set G :=
  {y | ∃ x ∈ A, y ∈ conjClassSet (OddOrder.GroupTheory.leftCosetSet x (ftSupportKernel M A x))}

/-- Carrier for the Dade-hypothesis part of **Peterfalvi (8.15)** for a single
support set `A`.

It records the part already expressible with the existing §4 API: `L = M`,
`N_G(A) = M`, the Dade Hypothesis (2.2), the recovered formula `H(a)=R(a)` with
the *faithful per-`x`* kernel `ftSupportKernel` of (8.14), and the
`M`-conjugation invariance of the kernels (Peterfalvi's `R(x^m) = R(x)^m`, from
the uniqueness of the supporting maximal `N[x]`, BG Theorem D).  The §4 Dade
support then *is* the faithful thickened support of (8.14)
(`dadeSupport_eq_ftThickenedSupport`, a lemma rather than a field).  The later
Hypothesis (4.6)/(5.2) specializations add character-family data and are kept as
a separate TODO below.

⚠ The earlier revision pinned `H(a) = supportKernel M M A a = C_{M_F}(a)`, which is
**unsatisfiable** whenever `A` has an escaping element (see `ftSupportKernel`); consumers
(`S12.Hypothesis`, `S14.Hypothesis`) were therefore vacuously parameterized.  Fixed 2026-07-02
(lane b, carve-out issue 0096). -/
structure DadeSupportHypothesisData [Fintype G] (M : Subgroup G) (A : Set G) where
  /-- Peterfalvi (8.15): `M = N_G(A)`. -/
  normalizer_eq : Subgroup.normalizer A = M
  /-- Peterfalvi (8.15): Hypothesis (2.2) holds with `L = M`. -/
  dade : OddOrder.Peterfalvi.S04.Hypothesis G A M
  /-- Peterfalvi (8.15): the subgroups in Hypothesis (2.2) are the recovered
  faithful `R(a)` from (8.14). -/
  H_eq_ftSupportKernel :
    ∀ a : {a : G // a ∈ A}, dade.H a = ftSupportKernel M A a.1

/-- **The (8.14) faithful kernel only sees the point, not the ambient support**: for `x` in a
subset `A₁ ⊆ A`, `R(x)` is computed the same way from either.

`ftSupportKernel M A x` branches on `x ∈ escapingCentralizerSet M A = {x ∈ A | C_G(x) ⊄ M}`, and
for `x ∈ A₁` the membership clause holds on both sides, so only the escaping condition — which
does not mention the support — decides. -/
theorem ftSupportKernel_congr_of_subset {M : Subgroup G} {A A₁ : Set G} (hA₁A : A₁ ⊆ A) {x : G}
    (hx : x ∈ A₁) : ftSupportKernel M A x = ftSupportKernel M A₁ x := by
  classical
  by_cases hc : Subgroup.centralizer ({x} : Set G) ≤ M
  · rw [ftSupportKernel, ftSupportKernel,
      if_neg (fun h : x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A => h.2 hc),
      if_neg (fun h : x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A₁ => h.2 hc)]
  · rw [ftSupportKernel, ftSupportKernel,
      if_pos (show x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A from ⟨hA₁A hx, hc⟩),
      if_pos (show x ∈ OddOrder.GroupTheory.escapingCentralizerSet M A₁ from ⟨hx, hc⟩)]

namespace DadeSupportHypothesisData

/-- **Restrict an (8.15) Dade support datum to a smaller `M`-stable support** — Peterfalvi (2.11)
at the level of the whole (8.15) package.

`S04.Hypothesis.restrict` restricts the Dade hypothesis (its `M`-equivariance needs no transport:
`S04.Hypothesis.hConjInvariant` proves (2.4.a) for the restricted datum outright), and the
faithful-kernel pin transports by `ftSupportKernel_congr_of_subset`.
Only `N_G(A₁) = M` has to be supplied afresh, since (8.16) is a statement about the particular
support.

The intended instance is `A = A₀(M) = A(M) ∪ V^M ↝ A₁ = A(M)` (issue 1045 着手順 3): the §10
`Hypothesis` carries its (8.15) datum on `A₀(M)`, while the §9 (9.11) chain consumes one on
`A(M)`. -/
noncomputable def restrict [Fintype G] {M : Subgroup G} {A A₁ : Set G}
    (d : DadeSupportHypothesisData M A) (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hnormalizer : Subgroup.normalizer A₁ = M) :
    DadeSupportHypothesisData M A₁ where
  normalizer_eq := hnormalizer
  dade := d.dade.restrict hA₁A hA₁norm
  H_eq_ftSupportKernel := fun a => by
    rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H, d.H_eq_ftSupportKernel,
      ftSupportKernel_congr_of_subset hA₁A a.2]

/-- The restricted datum's Dade hypothesis is the restriction — the pin `hdd` that the §9 (9.11)
chain asks for, definitionally. -/
@[simp] theorem restrict_dade [Fintype G] {M : Subgroup G} {A A₁ : Set G}
    (d : DadeSupportHypothesisData M A) (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hnormalizer : Subgroup.normalizer A₁ = M) :
    (d.restrict hA₁A hA₁norm hnormalizer).dade = d.dade.restrict hA₁A hA₁norm := rfl

/-- The §4 Dade support of a faithful (8.15) datum is the faithful thickened support
`Ã(M,A) = ⋃_{x∈A}(x·R(x))^G` of (8.14). -/
theorem dadeSupport_eq_ftThickenedSupport [Fintype G] {M : Subgroup G} {A : Set G}
    (d : DadeSupportHypothesisData M A) :
    d.dade.dadeSupport = ftThickenedSupport M A := by
  ext g
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff]
  constructor
  · rintro ⟨a, h, hh, hconj⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine ⟨a.1, a.2, ?_⟩
    rw [mem_conjClassSet]
    refine ⟨a.1 * h, ⟨h, ?_, rfl⟩, c, hc⟩
    rw [SetLike.mem_coe, ← d.H_eq_ftSupportKernel a]
    exact hh
  · rintro ⟨x, hx, hg⟩
    rw [mem_conjClassSet] at hg
    obtain ⟨t, ⟨h, hh, rfl⟩, c, hc⟩ := hg
    refine ⟨⟨x, hx⟩, h, ?_, isConj_iff.mpr ⟨c, hc⟩⟩
    rw [d.H_eq_ftSupportKernel ⟨x, hx⟩]
    exact SetLike.mem_coe.mp hh

end DadeSupportHypothesisData

end OddOrder.Peterfalvi.S10


