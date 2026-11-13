-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleStructure
-- name    : OddOrder_Peterfalvi_S10_MinimalSimpleStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:23:45.777926+00:00
-- url     : https://prove2.me/theorems/20b45f1c-e69b-40a8-862e-6ee4cd14e250
-- title:
--   Peterfalvi §10: minimal simple groups, structure (8.17) BG Theorem E covering data
-- statement:
--   A continuation of the minimal-simple-groups structure development of Peterfalvi, *Character Theory for the Odd Order Theorem*, §10. It introduces the BG Theorem E covering data of (8.17), in the case (8.8.a) where all maximal subgroups are type I and the case (8.8.b) with two exceptional subgroups, and a producer of the non-type-I covering from type $\mathcal{P}$.
--
--   Main declarations: `BGTheoremECoverData`; `BGTheoremETypeICovering`; `BGTheoremENonTypeICovering`; `nonTypeICovering_of_isTypeP`.
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_MinimalSimpleStructure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleBasic
import Definitions.Def_OddOrder_Peterfalvi_S10_TypePSupport

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **The faithful kernel agrees with the BG signalizer on escaping `σ`-sharp points**:
`FT_signalizer x = Rsub x`.  Escape forces `1 < |𝓜_σ(x)|`
(`centralizer_le_of_maximalSigma_le_one`), so both branches are live, and both choices are *the*
unique maximal over `C_G(x)`
(`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`). -/
theorem FT_signalizer_eq_Rsub_of_escape [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    OddOrder.BG.Ch4.S16.FT_signalizer x
      = OddOrder.BG.Ch4.S14.Rsub hG (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) x := by
  classical
  have hx1 : x ≠ 1 := hx.2
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hx.1
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    exact hesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hxMσ hx1
      (not_lt.mp h))
  have hlen : (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG).length x = 1 :=
    OddOrder.BG.Ch4.S14.Msigma_ell1 hG hM hxMσ hx1
  obtain ⟨N, hsingle⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hx hesc
  have hbranch : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty :=
    ⟨hgt, hsingle ▸ ⟨N, rfl⟩⟩
  -- both `choose`s land in the singleton `{N}`
  have hbase_eq : OddOrder.BG.Ch4.S16.FT_signalizerBase x = N := by
    have hmem : OddOrder.BG.Ch4.S16.FT_signalizerBase x
        ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
      rw [show OddOrder.BG.Ch4.S16.FT_signalizerBase x = hbranch.2.choose from dif_pos hbranch]
      exact hbranch.2.choose_spec
    rw [hsingle, Set.mem_singleton_iff] at hmem
    exact hmem
  have hstruct := (OddOrder.BG.Ch4.S14.sigmaLength_one_centralizer_structure hG
    (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) hx1 hlen).2 hgt
  have hN'_eq : hstruct.exists.choose = N := by
    have hmem : hstruct.exists.choose
        ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      ⟨mem_maximalSubgroups.mp hstruct.exists.choose_spec.1, hstruct.exists.choose_spec.2.1⟩
    have hmem2 : hstruct.exists.choose ∈ ({N} : Set (Subgroup G)) := by
      rw [← hsingle]; exact hmem
    exact Set.mem_singleton_iff.mp hmem2
  rw [OddOrder.BG.Ch4.S14.Rsub_eq_inf hG (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG)
    hx1 hlen hgt]
  change OddOrder.BG.Ch3.S10.Msigma (OddOrder.BG.Ch4.S16.FT_signalizerBase x)
      ⊓ Subgroup.centralizer ({x} : Set G) = _
  rw [hbase_eq, hN'_eq]

/-- **The faithful thickened `A₁`-support lands in the `M̃`-cover**: `Ã₁(M) ⊆ 𝒞_G(M̃)`, for a
maximal subgroup of **any** Peterfalvi type.  Escaping points contribute `x·R(x)` with
`R(x) = FT_signalizer x = Rsub x` (the defining generators of `M̃`); non-escaping points
contribute the bare `x = x·1 ∈ M̃`.

The only place the type entered was `A₁(M) = M_σ^#`, which holds for every type
(`A1_eq_sigmaSharp`); the rest of the argument is type-agnostic. -/
theorem ftThickenedSupport_A1_subset_conjClassSet_Mtilde [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau M) :
    ftThickenedSupport M (A1 M tau) ⊆
      conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG
        (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) M) := by
  have hA1σ : A1 M tau = OddOrder.BG.Ch4.S14.sigmaSharp M := A1_eq_sigmaSharp hG hM htau
  rintro y ⟨x, hxA1, hy⟩
  have hxσ : x ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := hA1σ ▸ hxA1
  refine conjClassSet_mono ?_ hy
  rintro z ⟨r, hr, rfl⟩
  by_cases hesc : x ∈ OddOrder.GroupTheory.escapingCentralizerSet M (A1 M tau)
  · rw [SetLike.mem_coe, ftSupportKernel_eq_of_escaping hesc,
      FT_signalizer_eq_Rsub_of_escape hG hM hxσ hesc.2] at hr
    exact ⟨x, hxσ, r, hr, rfl⟩
  · rw [SetLike.mem_coe, ftSupportKernel_eq_bot_of_not_escaping hesc, Subgroup.mem_bot] at hr
    exact ⟨x, hxσ, r, by rw [hr]; exact one_mem _, rfl⟩

/-- **Peterfalvi (8.17.c), `Ã₁`-disjointness** (the disjointness core of BG Theorem E /
Coq `FT_Dade1_support_disjoint`): the faithful thickened `A₁`-supports of **any** two
non-conjugate maximal subgroups are disjoint — the book states (8.17) over a full system of
representatives of the conjugacy classes of maximal subgroups, with no type hypothesis.  Both
supports embed in the disjoint `𝒞_G(M̃)`-covers (`conjClassSet_Mtilde_disjoint`, BG 14.5(b)). -/
theorem ftThickenedSupport_A1_disjoint_of_nonconjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L1 L2 : Subgroup G}
    (hL1 : L1 ∈ maximalSubgroups G) (hL2 : L2 ∈ maximalSubgroups G)
    {tau1 tau2 : PeterfalviType}
    (ht1 : HasPeterfalviType tau1 L1) (ht2 : HasPeterfalviType tau2 L2)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L1 L2) :
    Disjoint (ftThickenedSupport L1 (A1 L1 tau1)) (ftThickenedSupport L2 (A1 L2 tau2)) :=
  Disjoint.mono (ftThickenedSupport_A1_subset_conjClassSet_Mtilde hG hL1 ht1)
    (ftThickenedSupport_A1_subset_conjClassSet_Mtilde hG hL2 ht2)
    (OddOrder.BG.Ch4.S14.conjClassSet_Mtilde_disjoint hG
      (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG) hL1 hL2 hnc)

/-- **Peterfalvi (8.13.b), `D ⊆ A₁` conjunct**: an escaping point of the type-I support `A(M)`
lies in the sharp core `A₁(M)`.  The BG `D ⊆ M_σ^#` reduction of Theorem II conjunct 2
(`mem_sigmaSharp_of_mem_aSet_of_escape`, fed through the `typeIA_subset_ASet` bridge), with
`A₁(M) = M_σ^#` the type-I support-set bridge (`A1_eq_sigmaSharp_of_typeI_or_II`). -/
theorem escaping_typeIA_mem_A1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typeIA M data)) :
    a ∈ A1 M PeterfalviType.I := by
  obtain ⟨haA, hesc⟩ := ha
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro p _
    rw [hκ]
    exact Set.notMem_empty p
  have hσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM bot_le data.typeF.U_le hK
      (typeF_complement_isHall_kappa_sigma_compl hG hM data) (Or.inl rfl)
      (typeIA_subset_ASet hG hM data haA) haA.2.1 hesc
  have hA1 : A1 M PeterfalviType.I = OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.Peterfalvi.S10Interface.A1_eq_sigmaSharp_of_typeI_or_II hG hM
      (Or.inl ⟨data⟩) (Or.inl rfl)
  rw [hA1]
  exact hσ

/-- The centralizer of the cyclic subgroup `⟨z⟩` is the centralizer of `z` (powers commute). -/
private theorem centralizer_zpowers_eq_singleton' (z : G) :
    Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)
      = Subgroup.centralizer ({z} : Set G) := by
  ext c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hc z (SetLike.mem_coe.mpr (Subgroup.mem_zpowers z))
  · intro hc y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    have hzc : Commute z c := hc z (Set.mem_singleton z)
    exact (hzc.zpow_left n).eq

/-- **Peterfalvi (8.12.b), single-point form**: for type-I `T` and `x ∈ T` of order coprime to
`|T_F|` centralizing a nontrivial element of `T_F`, `T` is the unique maximal subgroup
containing `C_G(x)`.

BG §16 Theorem B, centralizer clause (`theoremB_U_and_A_tame`, conjunct 4), reached through the
Hall-conjugacy move: `x` is a `(κ ∪ σ)′`-element of the solvable `T` (its order is coprime to
`|T_F| = |M_σ|`), so Hall D/C (`hall_D`/`hall_C`) conjugate `⟨x⟩` into the type-`F` complement
`U` by some `t ∈ T`; the conjugated witness keeps `M_σ ⊓ C_G(⟨t x t⁻¹⟩) ≠ ⊥`, so Theorem B pins
`ℳ(C_G(t x t⁻¹)) = {T}`, and conjugating back by `t ∈ T` (which fixes `T`) gives both
conjuncts for `x`. -/
theorem typeI_centralizer_le_and_unique [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {T : Subgroup G} (hT : T ∈ maximalSubgroups G) (dT : TypeIData T)
    {x : G} (hxT : x ∈ T) (hx1 : x ≠ 1)
    (hord : Nat.Coprime (orderOf x) (Nat.card (maxNilpotentNormalHall T)))
    (hwit : ∃ h ∈ maxNilpotentNormalHall T, h ≠ 1 ∧ Commute x h) :
    Subgroup.centralizer ({x} : Set G) ≤ T ∧
      ∀ L ∈ maximalSubgroups G, Subgroup.centralizer ({x} : Set G) ≤ L → L = T := by
  classical
  have : Group.IsSolvable ↥T := hG.isSolvable_of_mem_maximalSubgroups hT
  have hκ : OddOrder.BG.Ch4.S14.kappa T = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hT).mp ⟨dT⟩
  have hMFMσ : maxNilpotentNormalHall T = OddOrder.BG.Ch3.S10.Msigma T :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hT (Or.inl ⟨dT⟩)
  -- (i) `x` is a `(κ ∪ σ)′`-element of `T`.
  set xT : ↥T := ⟨x, hxT⟩ with hxTdef
  have hordeq : orderOf x = orderOf xT :=
    orderOf_injective T.subtype T.subtype_injective xT
  have hZπ : ∀ q ∈ (Nat.card ↥(Subgroup.zpowers xT)).primeFactors,
      q ∈ (OddOrder.BG.Ch4.S14.kappa T ∪ OddOrder.BG.Ch3.S10.sigma T)ᶜ := by
    intro q hq
    rw [Nat.card_zpowers, ← hordeq] at hq
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    simp only [Set.mem_compl_iff, Set.mem_union, hκ, Set.mem_empty_iff_false, false_or]
    intro hqσ
    -- `q ∈ σ(T)` divides `|M_σ| = |T_F|`, contradicting the coprimality with `orderOf x`.
    have hHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hT
    have hqnidx : ¬ q ∣ (OddOrder.BG.Ch3.S10.Msigma T).index := fun hdvd =>
      hHall.2 q (Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqσ
    have hqG : q ∣ Nat.card G := hqdvd.trans ((orderOf_dvd_natCard x).trans dvd_rfl)
    have hqMσ : q ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma T) := by
      rcases (Nat.Prime.dvd_mul hqp).mp
        ((Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma T)) ▸ hqG) with h | h
      · exact h
      · exact absurd h hqnidx
    have hgcd : q ∣ Nat.gcd (orderOf x) (Nat.card (maxNilpotentNormalHall T)) :=
      Nat.dvd_gcd hqdvd (hMFMσ ▸ hqMσ)
    rw [Nat.Coprime.gcd_eq_one hord] at hgcd
    exact hqp.one_lt.ne' (Nat.dvd_one.mp hgcd)
  -- (ii) Hall D + C inside `T`: conjugate `x` into the type-`F` complement `U`.
  obtain ⟨W, hWhall, hZW⟩ := OddOrder.Isaacs.Ch03.hall_D (G := ↥T) hZπ
  obtain ⟨t, htmap⟩ := OddOrder.Isaacs.Ch03.hall_C (G := ↥T) hWhall
    (typeF_complement_isHall_kappa_sigma_compl hG hT dT)
  set τ : G := (t : G) with hτdef
  have hτT : τ ∈ T := t.2
  set x' : G := τ * x * τ⁻¹ with hx'def
  have hx'U : x' ∈ dT.typeF.U := by
    have hxW : xT ∈ W := hZW (Subgroup.mem_zpowers xT)
    have hmem : (MulAut.conj t) xT ∈ W.map (MulAut.conj t).toMonoidHom :=
      ⟨xT, hxW, rfl⟩
    rw [htmap] at hmem
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [hx'def, hτdef, MulAut.conj_apply] using this
  have hx'1 : x' ≠ 1 := by
    simp only [hx'def, ne_eq, conj_eq_one_iff]
    exact hx1
  -- (iii) the conjugated witness keeps `M_σ ⊓ C_G(⟨x'⟩) ≠ ⊥`.
  obtain ⟨h, hhMF, hh1, hcomm⟩ := hwit
  have hMFle := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le T
  have hh'MF : τ * h * τ⁻¹ ∈ maxNilpotentNormalHall T := by
    have hnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal T
    have hmem : (⟨h, hMFle hhMF⟩ : ↥T) ∈ (maxNilpotentNormalHall T).subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr hhMF
    have := Subgroup.mem_subgroupOf.mp (hnorm.conj_mem _ hmem t)
    simpa [hτdef] using this
  have hh'1 : τ * h * τ⁻¹ ≠ 1 := by
    simp only [ne_eq, conj_eq_one_iff]
    exact hh1
  have hcomm' : Commute x' (τ * h * τ⁻¹) := by
    have := hcomm.map (MulAut.conj τ : G →* G)
    simpa [hx'def, MulAut.conj_apply] using this
  have hCne : OddOrder.BG.Ch3.S10.Msigma T ⊓
      Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) ≠ ⊥ := by
    intro hbot
    have hmem : τ * h * τ⁻¹ ∈ OddOrder.BG.Ch3.S10.Msigma T ⊓
        Subgroup.centralizer ((Subgroup.zpowers x' : Subgroup G) : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hMFMσ ▸ hh'MF, ?_⟩
      rw [centralizer_zpowers_eq_singleton']
      exact Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hcomm'.eq
    rw [hbot] at hmem
    exact hh'1 (Subgroup.mem_bot.mp hmem)
  -- (iv) BG Lemma 15.1(c) / Theorem B(4) pins `ℳ(C_G(x')) = {T}` (sorry-free, no Theorem B gate).
  have hB := (OddOrder.BG.Ch4.S14.typeP_hall_small_subgroup_cyclic_tau2 hG hT dT.typeF.U_le
    (typeF_complement_isHall_kappa_sigma_compl hG hT dT)
    (Subgroup.zpowers_le.mpr hx'U)
    (by simpa [Subgroup.zpowers_eq_bot] using hx'1) hCne).1
  rw [centralizer_zpowers_eq_singleton'] at hB
  -- (v) conjugate back by `τ ∈ T`.
  have hCconj : Subgroup.centralizer ({x'} : Set G)
      = MulAut.conj τ • Subgroup.centralizer ({x} : Set G) :=
    (conj_smul_centralizer_singleton' τ x).symm
  have hconj_self : ∀ g ∈ T, MulAut.conj g • T = T := by
    intro g hg
    ext z
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (MulAut.conj g)⁻¹ • z = g⁻¹ * z * g := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [hinv]
    constructor
    · intro hz
      have := mul_mem (mul_mem hg hz) (inv_mem hg)
      simpa [mul_assoc] using this
    · intro hz
      exact mul_mem (mul_mem (inv_mem hg) hz) hg
  have hTmem : T ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) := by
    rw [hB]
    rfl
  have hCT' : Subgroup.centralizer ({x'} : Set G) ≤ T :=
    (mem_maximalSubgroupsContaining.mp hTmem).2
  constructor
  · -- `C_G(x) ≤ T`
    intro c hc
    have hc' : τ * c * τ⁻¹ ∈ Subgroup.centralizer ({x'} : Set G) := by
      rw [hCconj]
      exact ⟨c, hc, rfl⟩
    have hcT : τ * c * τ⁻¹ ∈ T := hCT' hc'
    have := mul_mem (mul_mem (inv_mem hτT) hcT) hτT
    simpa [mul_assoc] using this
  · -- uniqueness
    intro L hL hCL
    have hLconj : MulAut.conj τ • L ∈
        maximalSubgroupsContaining (Subgroup.centralizer ({x'} : Set G)) := by
      rw [mem_maximalSubgroupsContaining]
      refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hL), ?_⟩
      rw [hCconj]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCL
    rw [hB, Set.mem_singleton_iff] at hLconj
    calc L = MulAut.conj τ⁻¹ • (MulAut.conj τ • L) := by
            rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ = MulAut.conj τ⁻¹ • T := by rw [hLconj]
      _ = T := hconj_self τ⁻¹ (inv_mem hτT)

/-- **`π`-part extraction from a commuting coprime product**: if `b, k` commute with coprime
orders then `b ∈ ⟨b·k⟩` (`b` is the `primeFactors (orderOf b)`-part of `b·k`). -/
theorem mem_zpowers_mul_right_of_coprime [Finite G] {b k : G} (hcomm : Commute b k)
    (hcop : Nat.Coprime (orderOf b) (orderOf k)) :
    b ∈ Subgroup.zpowers (b * k) := by
  classical
  set π : Set ℕ := {p | p ∈ (orderOf b).primeFactors} with hπ
  have hbπ : OddOrder.GroupTheory.IsPiElement π b := fun p hp => hp
  have hkπ' : OddOrder.GroupTheory.IsPiElement πᶜ k := by
    intro p hp hpb
    have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpk : p ∣ orderOf k := (Nat.mem_primeFactors.mp hp).2.1
    have hpb' : p ∣ orderOf b := (Nat.mem_primeFactors.mp hpb).2.1
    have : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpb' hpk
    exact hpprime.one_lt.ne' (Nat.dvd_one.mp this)
  have hmul : OddOrder.BG.Ch4.S14.piPart π (b * k) = b := by
    rw [OddOrder.BG.Ch4.S14.piPart_mul_of_commute hcomm,
      OddOrder.BG.Ch4.S14.piPart_self_of_isPiElement hbπ,
      OddOrder.BG.Ch4.S14.piPart_eq_one_of_isPiElement_compl hkπ', mul_one]
  have hz := OddOrder.BG.Ch4.S14.piPart_mem_zpowers π (b * k)
  rwa [hmul] at hz

/-- **Peterfalvi (8.13.b), `D ⊆ A₁` conjunct, type-uniform**: an escaping point of `A(M)` lies
in the sharp core `A₁(M)`, for a maximal subgroup of *any* Peterfalvi type.

Both halves go through BG's `D ⊆ M_σ^#` reduction of Theorem II conjunct 2
(`mem_sigmaSharp_of_mem_aSet_of_escape`), fed through the respective `ASet` bridge —
`typeIA_subset_ASet` on Type I, `typePACore_subset_ASet` on the types of class `𝒫` — and land in
`A₁(M) = M_σ^#` (`A1_eq_sigmaSharp`, valid for every type).  The matched `κ`-Hall /
`(κ ∪ σ)′`-Hall pair the `𝒫`-side reduction needs is supplied by
`typeP_exists_kappa_hall_pair`. -/
theorem escaping_typeA_mem_A1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau M)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M
      (OddOrder.GroupTheory.typeA M tau)) :
    a ∈ A1 M tau := by
  classical
  by_cases htauI : tau = PeterfalviType.I
  · subst htauI
    obtain ⟨dM⟩ : IsTypeI M := htau
    refine escaping_typeIA_mem_A1 hG hM dM ?_
    rwa [OddOrder.GroupTheory.typeA_eq_typeIA dM] at ha
  · have hTP : OddOrder.BG.Ch4.S14.IsTypeP M := by
      cases tau with
      | I => exact absurd rfl htauI
      | II => exact OddOrder.BG.Ch4.S16.isTypeP_of_isTypeII hG hM htau
      | III => exact OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIII hG hM htau
      | IV => exact OddOrder.BG.Ch4.S16.isTypeP_of_isTypeIV hG hM htau
      | V => exact OddOrder.BG.Ch4.S16.isTypeP_of_isTypeV hG hM htau
    obtain ⟨K₀, U₀, hKM, hUM, hKne, hK, hU⟩ := typeP_exists_kappa_hall_pair hG hM hTP
    rw [typeA_eq_typePACore hG hM htau htauI] at ha
    rw [A1_eq_sigmaSharp hG hM htau]
    exact escaping_typePACore_mem_sigmaSharp hG hM hKM hUM hKne hK hU ha

/-- **The `σ`-disjointness step of (8.13.c2)/(8.18), type-uniform**: for an escaping point `z`
of `A(S)` and any `w ∈ A(S)`, no prime of `σ(N[z])` divides `|C_S(w)|`.

The type-agnostic core is `escaping_sigmaSharp_disjoint_centralizer_of_witness`; membership in
`A(S) = typeA S tau` supplies its three inputs directly — `w` lies in the (8.10) host, hence in
`S` (`supportHost_le`); `w ≠ 1`; and `w` centralizes a nonidentity element of
`M_s = M_σ` (`mainSubgroup_eq_Msigma`), which is the Frobenius-absorption witness.  The
`σ`-sharpness of `z` is `escaping_typeA_mem_A1` composed with `A1_eq_sigmaSharp`. -/
theorem escaping_sigma_disjoint_centralizer_typeA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G} (hS : S ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau S)
    {z : G} (hz : z ∈ OddOrder.GroupTheory.escapingCentralizerSet S
      (OddOrder.GroupTheory.typeA S tau))
    {w : G} (hw : w ∈ OddOrder.GroupTheory.typeA S tau) {p : ℕ} (hpp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z))
    (hpC : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) : False := by
  have hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S :=
    A1_eq_sigmaSharp hG hS htau ▸ escaping_typeA_mem_A1 hG hS htau hz
  obtain ⟨hwH, hw1, x, hxσ, hwx⟩ := hw
  refine escaping_sigmaSharp_disjoint_centralizer_of_witness hG hS hσz hz.2
    (OddOrder.GroupTheory.supportHost_le S tau hwH) hw1 ⟨x, ?_, ?_, ?_⟩ hpp hpσ hpC
  · have hx := hxσ.1
    rwa [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hS htau, SetLike.mem_coe] at hx
  · exact fun h => hxσ.2 (Set.mem_singleton_iff.mpr h)
  · exact Subgroup.mem_centralizer_singleton_iff.mp hwx

/-- **Peterfalvi (8.13.c2), type-uniform**: for an escaping point `a` of `A(M)` and *any*
`b ∈ A(M)`, the signalizer `R(a)` has order coprime to `|C_M(b)|`, for a maximal subgroup of any
Peterfalvi type.

Type I is the last conjunct of `escaping_typeIA_signalizer_structure`; the types of class `𝒫`
are `coprime_FT_signalizer_centralizerIn_typePACore`.  The `σ`-sharpness of `a` that the
`𝒫`-side needs is `escaping_typeA_mem_A1` composed with `A1_eq_sigmaSharp`. -/
theorem coprime_FT_signalizer_centralizerIn_typeA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau M)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M
      (OddOrder.GroupTheory.typeA M tau))
    {b : G} (hb : b ∈ OddOrder.GroupTheory.typeA M tau) :
    Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
      (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b)) := by
  classical
  by_cases htauI : tau = PeterfalviType.I
  · subst htauI
    obtain ⟨dM⟩ : IsTypeI M := htau
    rw [OddOrder.GroupTheory.typeA_eq_typeIA dM] at ha hb
    exact (escaping_typeIA_signalizer_structure hG hM dM ha).2.2.2 b hb
  · have haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
      A1_eq_sigmaSharp hG hM htau ▸ escaping_typeA_mem_A1 hG hM htau ha
    rw [typeA_eq_typePACore hG hM htau htauI] at ha hb
    exact coprime_FT_signalizer_centralizerIn_typePACore hG hM haσ ha.2 hb

/-- **Peterfalvi (8.13.c2)/(8.18) cross-coprimality, type-uniform**: if some escaping point `z`
of `A(S)` has `C_G(z)` inside a maximal `N` conjugate to `T`, then `|T_σ|` is coprime to
`|C_S(w)|` for *every* `w ∈ A(S)`.

The supporting configuration identifies `N` with `N[z] = FT_signalizerBase z` through the
singleton uniqueness of the maximal over an escaping centralizer, so a common prime would lie in
`σ(N[z])` and be killed by `escaping_sigma_disjoint_centralizer_typeA`.  No type hypothesis on
either `S` or `T`. -/
theorem supported_sigma_coprime_typeA [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S T : Subgroup G} (hS : S ∈ maximalSubgroups G)
    {tauS : PeterfalviType} (htauS : HasPeterfalviType tauS S)
    (hsupp : ∃ z ∈ OddOrder.GroupTheory.escapingCentralizerSet S
        (OddOrder.GroupTheory.typeA S tauS),
      ∃ N ∈ maximalSubgroups G, Subgroup.centralizer ({z} : Set G) ≤ N ∧
        OddOrder.BG.Ch4.S14.IsConjugateSubgroup T N) :
    ∀ w ∈ OddOrder.GroupTheory.typeA S tauS,
      Nat.Coprime (Nat.card (OddOrder.BG.Ch3.S10.Msigma T))
        (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) := by
  classical
  intro w hw
  by_contra hnc
  obtain ⟨p, hpp, hpT, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  obtain ⟨z, hz, N, hNmax, hCN, hTN⟩ := hsupp
  have hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S :=
    A1_eq_sigmaSharp hG hS htauS ▸ escaping_typeA_mem_A1 hG hS htauS hz
  have hz1 : z ≠ 1 := hσz.2
  have hzesc := hz.2
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard := by
    by_contra h
    exact hzesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hS hσz.1 hz1
      (not_lt.mp h))
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hS hσz hzesc
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G)),
      L = N₀ := by
    intro L hL
    rw [hN₀, Set.mem_singleton_iff] at hL
    exact hL
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G))).Nonempty :=
    ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase z = N₀ := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase z = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  have hNN₀ : N = N₀ :=
    huniq N (mem_maximalSubgroupsContaining.mpr ⟨hNmax, hCN⟩)
  -- `p ∈ σ(T) = σ(N) = σ(N[z])`.
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z) := by
    obtain ⟨g, hg⟩ := hTN
    rw [hbase, ← hNN₀, ← hg, OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]
    exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup T p
      (Nat.mem_primeFactors.mpr ⟨hpp, hpT, Nat.card_pos.ne'⟩)
  exact escaping_sigma_disjoint_centralizer_typeA hG hS htauS hz hw hpp hpσ hpC

/-- **Peterfalvi (8.12.b), type-`𝒫` half**: for a type-`𝒫` maximal `T` and a point
`b ∈ A(T) = typePACore T` whose order is coprime to `|T_σ|`, `T` is the unique maximal subgroup
of `G` containing `C_G(b)`.

The book states (8.12) for Types I **and** II, splitting on `M = H ⋊ U` (Type I) versus
`[M,M] = H ⋊ U` (Type II), and asks for `X ⊆ U^#`.  It is that second clause which makes the
`κ`-side free here: an `A(T)`-point already lies in `T' = derivedInG T` by (8.10), and `T'`
complements the `κ(T)`-Hall `W₁` in `T` (`TypePData.M_complement`), so the index of `W₁` is
`|T'|` and no prime of `κ(T)` can divide `orderOf b`.  The `σ`-side is the assumed coprimality
with `|T_σ|` (`π(T_σ) = σ(T)` via `Msigma_isHall`).  So `b` is a `(κ(T) ∪ σ(T))′`-element and BG
Lemma 15.1(c) (`uniqueMaximal_of_kappaSigmaCompl_element`, the type-generic core of (8.12.b))
applies — its `M_σ ⊓ C_G(b) ≠ ⊥` input being exactly the `M_σ^#`-witness that membership in
`A(T)` carries.

Contrast `typeI_centralizer_le_and_unique`, the Type-I half, which must conjugate `⟨x⟩` into the
complement by Hall D/C: there `x` is only known to lie in `T`, and `κ(T) = ∅` is what rescues
the argument.  For type `𝒫` the (8.10) host `M'` does that work outright, so no Hall conjugation
is needed.

`hW1hall` is an explicit hypothesis so that this stays upstream of §12
(`S12.typePData_W1_isHallSubgroup_kappa` discharges it from `hG`/`hT`/`IsTypeP T`). -/
theorem typeP_centralizer_unique_of_mem_typePACore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {T : Subgroup G} (hT : T ∈ maximalSubgroups G)
    (data : TypePData T)
    (hW1hall : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa T)
      (data.W1.subgroupOf T))
    {b : G} (hbA : b ∈ typePACore T)
    (hcop : Nat.Coprime (orderOf b) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma T))) :
    maximalSubgroupsContaining (Subgroup.centralizer ({b} : Set G)) = {T} := by
  classical
  have : Group.IsSolvable ↥T := hG.isSolvable_of_mem_maximalSubgroups hT
  obtain ⟨hbM', hb1, u, huS, hbu⟩ := hbA
  have hcardT' : Nat.card ((derivedInG T).subgroupOf T) = Nat.card (derivedInG T) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  -- `b` is a `(κ(T) ∪ σ(T))′`-element.
  have hyπ : OddOrder.GroupTheory.IsPiElement
      ((OddOrder.BG.Ch4.S14.kappa T ∪ OddOrder.BG.Ch3.S10.sigma T)ᶜ) b := by
    intro q hq
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    refine ⟨?_, ?_⟩
    · -- `q ∉ κ(T)`: `q ∣ |b| ∣ |T′| = index(W₁)`, and a `κ`-Hall has `κ`-free index.
      intro hqκ
      have hbord : orderOf b ∣ Nat.card (derivedInG T) :=
        Subgroup.orderOf_dvd_natCard _ hbM'
      have hqidx : q ∣ (data.W1.subgroupOf T).index := by
        rw [data.M_complement.index_eq_card, hcardT']
        exact hqdvd.trans hbord
      exact hW1hall.2 q (Nat.mem_primeFactors.mpr
        ⟨hqp, hqidx, Subgroup.index_ne_zero_of_finite⟩) hqκ
    · -- `q ∉ σ(T)`: `σ`-primes divide `|T_σ|`, coprime to `orderOf b` by hypothesis.
      intro hqσ
      have hHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hT
      have hqnidx : ¬ q ∣ (OddOrder.BG.Ch3.S10.Msigma T).index := fun hdvd =>
        hHall.2 q (Nat.mem_primeFactors.mpr
          ⟨hqp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqσ
      have hqG : q ∣ Nat.card G := hqdvd.trans (orderOf_dvd_natCard b)
      have hqMσ : q ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma T) := by
        rcases (Nat.Prime.dvd_mul hqp).mp
          ((Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma T)) ▸ hqG) with h | h
        · exact h
        · exact absurd h hqnidx
      have hgcd : q ∣ Nat.gcd (orderOf b) (Nat.card (OddOrder.BG.Ch3.S10.Msigma T)) :=
        Nat.dvd_gcd hqdvd hqMσ
      rw [Nat.Coprime.gcd_eq_one hcop] at hgcd
      exact hqp.one_lt.ne' (Nat.dvd_one.mp hgcd)
  -- a `(κ ∪ σ)′`-Hall of the solvable `T` (Hall E)
  obtain ⟨U', hU'⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥T)
    ((OddOrder.BG.Ch4.S14.kappa T ∪ OddOrder.BG.Ch3.S10.sigma T)ᶜ)
  have hUeq : (U'.map T.subtype).subgroupOf T = U' :=
    Subgroup.comap_map_eq_self_of_injective T.subtype_injective U'
  have hUhall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa T ∪ OddOrder.BG.Ch3.S10.sigma T)ᶜ)
      ((U'.map T.subtype).subgroupOf T) := by
    rw [hUeq]; exact hU'
  -- the `A(T)`-witness `u ∈ M_σ^#` is the nontrivial `M_σ`-centralizer input of 15.1(c)
  have hCne : OddOrder.BG.Ch3.S10.Msigma T ⊓ Subgroup.centralizer ({b} : Set G) ≠ ⊥ := by
    intro hbot
    have humem : u ∈ OddOrder.BG.Ch3.S10.Msigma T ⊓ Subgroup.centralizer ({b} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨huS.1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Subgroup.mem_centralizer_singleton_iff.mp hbu
    rw [hbot] at humem
    exact huS.2 (Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp humem))
  exact OddOrder.BG.Ch4.S16.uniqueMaximal_of_kappaSigmaCompl_element hG hT
    (Subgroup.map_subtype_le U') hUhall (Subgroup.map_subtype_le _ hbM') hb1 hyπ hCne

/-- **Peterfalvi (8.12.b), type-uniform form**: for *any* maximal subgroup `T` and any point
`b ∈ A(T)` whose order is coprime to `|T_s| = |T_σ|`, `T` is the unique maximal subgroup of `G`
containing `C_G(b)`.

Assembles the book's two clauses of (8.12) on the type-uniform support `typeA`: Type I through
`typeI_centralizer_le_and_unique` (there `A(T) ⊆ T` and `κ(T) = ∅`), the types of class `𝒫`
through `typeP_centralizer_unique_of_mem_typePACore` (there `A(T) ⊆ T'`).  The identification of
`A(T)` with the respective clause of (8.10) is `typeA_eq_typeIA` / `typeA_eq_typePACore`, and
`M_F = M_σ` on Type I is Proposition 16.1.

This is the shape (8.18.a) consumes: "Since `x` has order prime to `|T_s|`, it follows from
(8.12.b) that `T` is the unique maximal subgroup of `G` such that `C_G(x) ⊂ T`." -/
theorem centralizer_unique_of_mem_typeA [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {T : Subgroup G} (hT : T ∈ maximalSubgroups G)
    {tau : PeterfalviType} (htau : HasPeterfalviType tau T)
    (hW1hall : tau ≠ PeterfalviType.I → ∀ data : TypePData T,
      OddOrder.Isaacs.Ch03.IsHallSubgroup
        (OddOrder.BG.Ch4.S14.kappa T) (data.W1.subgroupOf T))
    {b : G} (hbA : b ∈ OddOrder.GroupTheory.typeA T tau)
    (hcop : Nat.Coprime (orderOf b) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma T))) :
    maximalSubgroupsContaining (Subgroup.centralizer ({b} : Set G)) = {T} := by
  classical
  by_cases htauI : tau = PeterfalviType.I
  · -- Type I: `A(T) = typeIA T dT ⊆ T`, and `M_F = M_σ` supplies the (8.12.b) coprimality.
    subst htauI
    obtain ⟨dT⟩ : IsTypeI T := htau
    rw [OddOrder.GroupTheory.typeA_eq_typeIA dT] at hbA
    obtain ⟨hbT, hb1, u, huH, hbu⟩ := hbA
    have hMF : maxNilpotentNormalHall T = OddOrder.BG.Ch3.S10.Msigma T :=
      OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
        hG hT (Or.inl ⟨dT⟩)
    have hwit : ∃ h ∈ maxNilpotentNormalHall T, h ≠ 1 ∧ Commute b h :=
      ⟨u, by rw [← dT.typeF.H_eq]; exact huH.1,
        fun he => huH.2 (Set.mem_singleton_iff.mpr he),
        Subgroup.mem_centralizer_singleton_iff.mp hbu⟩
    obtain ⟨hle, huniq⟩ :=
      typeI_centralizer_le_and_unique hG hT dT hbT hb1 (by rw [hMF]; exact hcop) hwit
    ext L
    simp only [mem_maximalSubgroupsContaining, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hLmax, hLle⟩
      exact huniq L (mem_maximalSubgroups.mpr hLmax) hLle
    · rintro rfl
      exact ⟨mem_maximalSubgroups.mp hT, hle⟩
  · -- Types II--V: `A(T) = typePACore T ⊆ T'`, and the `κ`-side is free.
    obtain ⟨data⟩ : Nonempty (TypePData T) := by
      cases tau with
      | I => exact absurd rfl htauI
      | II => exact ⟨(Classical.choice (htau : IsTypeII T)).typeP⟩
      | III => exact ⟨(Classical.choice (htau : IsTypeIII T)).typeP⟩
      | IV => exact ⟨(Classical.choice (htau : IsTypeIV T)).typeP⟩
      | V => exact ⟨(Classical.choice (htau : IsTypeV T)).typeP⟩
    rw [typeA_eq_typePACore hG hT htau htauI] at hbA
    exact typeP_centralizer_unique_of_mem_typePACore hG hT data (hW1hall htauI data) hbA hcop

/-- **Peterfalvi (8.18.a), conjugation-free core, type-uniform**: for two **non-conjugate
maximal subgroups** `S, T` with no type hypothesis, if `x ∈ A₁(S)` and some conjugate
`g·x·g⁻¹ ∈ A(T)`, then `x` is an escaping point of `A(S)` and its centralizer lies in the
`T`-conjugate `g⁻¹·T·g`.

This is the book's statement verbatim (the earlier `escaping_supported_of_A1_conj_mem_typeIA`
fixed both `S` and `T` at Type I).  Peterfalvi's proof, step by step:

* `x ∈ A₁(S) = M_s(S)^#` and `M_s = M_σ` for every type (`mainSubgroup_eq_Msigma`), so
  `orderOf x` is a `σ(S)`-number (`isPiElement_sigma_of_mem_Msigma`);
* `σ(S) ∩ σ(T) = ∅` because `S` and `T` are non-conjugate
  (`sigma_disjoint_of_nonconjugate`, part of (8.17.a)), so `orderOf (g·x·g⁻¹) = orderOf x` is
  prime to `|T_σ| = |T_s|` (`primeFactors_Msigma_eq_sigma`);
* hence (8.12.b) in its type-uniform form (`centralizer_unique_of_mem_typeA`) pins
  `ℳ(C_G(g·x·g⁻¹)) = {T}`;
* `C_G(x) ≤ S` would then make the maximal `g·S·g⁻¹` a member of that singleton, forcing
  `g·S·g⁻¹ = T` — contradicting non-conjugacy.  So `x` escapes, and transporting the
  containment back by `g` gives the second conjunct. -/
theorem escaping_supported_of_A1_conj_mem_typeA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    {tauS tauT : PeterfalviType}
    (htauS : HasPeterfalviType tauS S) (htauT : HasPeterfalviType tauT T)
    (hW1hall : tauT ≠ PeterfalviType.I → ∀ data : TypePData T,
      OddOrder.Isaacs.Ch03.IsHallSubgroup
        (OddOrder.BG.Ch4.S14.kappa T) (data.W1.subgroupOf T))
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T)
    {x g : G} (hxA1 : x ∈ A1 S tauS)
    (hgx : g * x * g⁻¹ ∈ OddOrder.GroupTheory.typeA T tauT) :
    x ∈ OddOrder.GroupTheory.escapingCentralizerSet S (OddOrder.GroupTheory.typeA S tauS) ∧
      Subgroup.centralizer ({x} : Set G) ≤ MulAut.conj g⁻¹ • T := by
  obtain ⟨hxMs, hx1s⟩ := (Set.mem_sdiff x).mp hxA1
  have hx1 : x ≠ 1 := fun h => hx1s (Set.mem_singleton_iff.mpr h)
  set y := g * x * g⁻¹ with hydef
  have hy1 : y ≠ 1 := conj_ne_one hx1
  -- `x ∈ M_σ(S)`, so `orderOf x` is a `σ(S)`-number.
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    have hx := hxMs
    rwa [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hS htauS, SetLike.mem_coe] at hx
  have hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma S) x :=
    OddOrder.BG.Ch4.S14.isPiElement_sigma_of_mem_Msigma hxMσ
  have horder_eq : orderOf y = orderOf x := by
    have hinj : Function.Injective (MulAut.conj g) := (MulAut.conj g).injective
    simpa [hydef] using orderOf_injective (MulAut.conj g).toMonoidHom hinj x
  have hσdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma S) (OddOrder.BG.Ch3.S10.sigma T) :=
    OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hS hT hnc
  have hord : Nat.Coprime (orderOf y) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma T)) := by
    rw [← Nat.disjoint_primeFactors (orderOf_pos y).ne' Nat.card_pos.ne', Finset.disjoint_left]
    intro p hpy hpT
    have hpσS : p ∈ OddOrder.BG.Ch3.S10.sigma S := hxpi p (horder_eq ▸ hpy)
    have hpσT : p ∈ OddOrder.BG.Ch3.S10.sigma T := by
      have hprim := OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG hT
      rw [← hprim]
      exact hpT
    exact Set.disjoint_left.mp hσdisj hpσS hpσT
  -- (8.12.b) at `y`, in its type-uniform form.
  have hB := centralizer_unique_of_mem_typeA hG hT htauT hW1hall hgx hord
  have hCyT : Subgroup.centralizer ({y} : Set G) ≤ T :=
    (mem_maximalSubgroupsContaining.mp (by rw [hB]; rfl)).2
  have huniq : ∀ L ∈ maximalSubgroups G,
      Subgroup.centralizer ({y} : Set G) ≤ L → L = T := by
    intro L hL hLle
    have hmem : L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hL, hLle⟩
    rw [hB, Set.mem_singleton_iff] at hmem
    exact hmem
  refine ⟨⟨A1_subset_typeA hG hS htauS hxA1, fun hle => ?_⟩, ?_⟩
  · -- If `C(x) ≤ S` then `C(y) ≤ g·S·g⁻¹`, a maximal over `C(y)`, so `g·S·g⁻¹ = T`.
    have hCyS : Subgroup.centralizer ({y} : Set G) ≤ MulAut.conj g • S := by
      intro c hc
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
        calc g⁻¹ * c * g * x = g⁻¹ * (c * y) * g := by rw [hydef]; group
          _ = g⁻¹ * (y * c) * g := by rw [hc]
          _ = x * (g⁻¹ * c * g) := by rw [hydef]; group
      simpa [MulAut.smul_def] using hle hc'
    have hmax : MulAut.conj g • S ∈ maximalSubgroups G :=
      mem_maximalSubgroups.mpr
        (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hS))
    exact hnc ⟨g, huniq _ hmax hCyS⟩
  · intro c hc
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc g * c * g⁻¹ * y = g * (c * x) * g⁻¹ := by rw [hydef]; group
        _ = g * (x * c) * g⁻¹ := by rw [hc]
        _ = y * (g * c * g⁻¹) := by rw [hydef]; group
    simpa [MulAut.smul_def] using hCyT hc'

/-- **Peterfalvi (8.18.b), type-uniform**: for two **non-conjugate maximal subgroups** `S, T`
with no type hypothesis, a nonempty intersection of the thickened supports `Ã₁(S) ∩ Ã(T) ≠ ∅`
descends to a *bare* intersection: some `x ∈ A₁(S)` has a conjugate in `A(T)`.  Together with
(8.18.a) this is the book's "there is a conjugate of `T` supporting `S` iff
`Ã₁(S) ∩ Ã(T) ≠ ∅`".

The book's argument, followed step by step:

* if the `T`-side point `a` **escapes**, it lies in `A₁(T)` (`escaping_typeA_mem_A1`, (8.13.b))
  and the thickenings agree there, so the intersection would sit inside
  `Ã₁(S) ∩ Ã₁(T) = ∅` — the type-uniform (8.17.c)
  (`ftThickenedSupport_A1_disjoint_of_nonconjugate`);
* otherwise the `T`-side thickening is trivial (`R(a) = 1`), so `y` is a bare conjugate of `a`.
  On the `S`-side, `y` is a conjugate of `b·k` with `k ∈ R(b)`; `|R(b)|` is coprime to
  `|C_S(b)|` by (8.13.c2) (`coprime_FT_signalizer_centralizerIn_typeA`) and `b` commutes with
  `k`, so `b` is a power of `b·k` (`mem_zpowers_mul_right_of_coprime`) and the corresponding
  power of `a` is the required conjugate of `b`.  Powers stay inside the `A(T)`-data: the host
  is a subgroup and so is each centralizer. -/
theorem exists_A1_conj_mem_typeA_of_not_disjoint [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    {tauS tauT : PeterfalviType}
    (htauS : HasPeterfalviType tauS S) (htauT : HasPeterfalviType tauT T)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T)
    (hint : ¬ Disjoint (ftThickenedSupport S (A1 S tauS))
      (ftThickenedSupport T (OddOrder.GroupTheory.typeA T tauT))) :
    ∃ x u : G, x ∈ A1 S tauS ∧ u * x * u⁻¹ ∈ OddOrder.GroupTheory.typeA T tauT := by
  rw [Set.not_disjoint_iff] at hint
  obtain ⟨y, ⟨b, hbA1, hyb⟩, ⟨a, haA, hya⟩⟩ := hint
  by_cases haesc : a ∈ OddOrder.GroupTheory.escapingCentralizerSet T
      (OddOrder.GroupTheory.typeA T tauT)
  · -- escaping `a`: `y ∈ Ã₁(S) ∩ Ã₁(T)`, contradicting the type-uniform (8.17.c).
    exfalso
    have haA1 : a ∈ A1 T tauT := escaping_typeA_mem_A1 hG hT htauT haesc
    have hyT1 : y ∈ ftThickenedSupport T (A1 T tauT) := by
      refine ⟨a, haA1, ?_⟩
      rwa [ftSupportKernel_eq_of_escaping haesc,
        ← ftSupportKernel_eq_of_escaping (⟨haA1, haesc.2⟩ :
          a ∈ OddOrder.GroupTheory.escapingCentralizerSet T (A1 T tauT))] at hya
    exact Set.disjoint_left.mp
      (ftThickenedSupport_A1_disjoint_of_nonconjugate hG hS hT htauS htauT hnc)
      ⟨b, hbA1, hyb⟩ hyT1
  · -- non-escaping `a`: the `T`-side thickening is trivial, `y ~ a`.
    rw [ftSupportKernel_eq_bot_of_not_escaping haesc] at hya
    obtain ⟨t, ⟨r0, hr0, rfl⟩, w, hw⟩ := hya
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hr0
    subst hr0
    simp only [mul_one] at hw
    obtain ⟨t', ⟨k, hk, rfl⟩, v, hv⟩ := hyb
    have hb1 : b ≠ 1 := fun h =>
      ((Set.mem_sdiff b).mp hbA1).2 (Set.mem_singleton_iff.mpr h)
    obtain ⟨haT, ha1, hwitA⟩ := haA
    have hbA : b ∈ OddOrder.GroupTheory.typeA S tauS := A1_subset_typeA hG hS htauS hbA1
    by_cases hbesc : b ∈ OddOrder.GroupTheory.escapingCentralizerSet S (A1 S tauS)
    · -- thick `S`-side: extract `b` as a power of `b·k`.
      rw [SetLike.mem_coe, ftSupportKernel_eq_of_escaping hbesc] at hk
      have hbescA : b ∈ OddOrder.GroupTheory.escapingCentralizerSet S
          (OddOrder.GroupTheory.typeA S tauS) :=
        ⟨A1_subset_typeA hG hS htauS hbesc.1, hbesc.2⟩
      have hcards := coprime_FT_signalizer_centralizerIn_typeA hG hS htauS hbescA hbA
      have hob : orderOf b ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S b) :=
        Subgroup.orderOf_dvd_natCard _
          (OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
            ⟨OddOrder.GroupTheory.typeA_subset hbA, rfl⟩)
      have hok : orderOf k ∣ Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer b) :=
        Subgroup.orderOf_dvd_natCard _ hk
      have hcop : Nat.Coprime (orderOf b) (orderOf k) :=
        ((Nat.Coprime.coprime_dvd_left hok hcards).coprime_dvd_right hob).symm
      have hcomm : Commute b k := by
        have hkc := OddOrder.BG.Ch4.S16.FT_signalizer_le_centralizer b hk
        exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_mul_right_of_coprime hcomm hcop)
      set u := w⁻¹ * v with hudef
      have hau : a = u * (b * k) * u⁻¹ := by
        have hwv : w * a * w⁻¹ = v * (b * k) * v⁻¹ := by rw [hw, hv]
        calc a = w⁻¹ * (w * a * w⁻¹) * w := by group
          _ = w⁻¹ * (v * (b * k) * v⁻¹) * w := by rw [hwv]
          _ = u * (b * k) * u⁻¹ := by rw [hudef]; group
      have hazn : a ^ n = u * b * u⁻¹ := by
        rw [hau]
        calc (u * (b * k) * u⁻¹) ^ n = u * (b * k) ^ n * u⁻¹ := by
              rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
          _ = u * b * u⁻¹ := by rw [hn]
      refine ⟨b, u, hbA1, ?_⟩
      rw [← hazn]
      obtain ⟨h, hh, hah⟩ := hwitA
      exact ⟨Subgroup.zpow_mem _ haT n, by rw [hazn]; exact conj_ne_one hb1,
        h, hh, Subgroup.zpow_mem _ hah n⟩
    · -- trivial `S`-side: `k = 1`, `a = u·b·u⁻¹` directly.
      rw [SetLike.mem_coe, ftSupportKernel_eq_bot_of_not_escaping hbesc,
        Subgroup.mem_bot] at hk
      subst hk
      simp only [mul_one] at hv
      refine ⟨b, w⁻¹ * v, hbA1, ?_⟩
      have heq : w⁻¹ * v * b * (w⁻¹ * v)⁻¹ = a := by
        have h1 : w * a * w⁻¹ = v * b * v⁻¹ := by rw [hw, hv]
        calc w⁻¹ * v * b * (w⁻¹ * v)⁻¹ = w⁻¹ * (v * b * v⁻¹) * w := by group
          _ = w⁻¹ * (w * a * w⁻¹) * w := by rw [h1]
          _ = a := by group
      rw [heq]
      exact ⟨haT, ha1, hwitA⟩

/-- **Peterfalvi (8.18.c), type-uniform** (mixed `Ã₁ ∩ Ã` disjointness): for **any** two
non-conjugate maximal subgroups `S, T`, `Ã₁(S) ∩ Ã(T) = ∅` or `Ã₁(T) ∩ Ã(S) = ∅`.

The book's proof: if both intersections were nonempty, (8.18.b) at `(S,T)` produces a bare
supporting configuration whose (8.18.a) escape feeds the (8.13.c2) cross-coprimality
`|T_σ| ⊥ |C_S(w)|`; (8.18.b) at `(T,S)` produces `x' ∈ A₁(T)` with a conjugate `w ∈ A(S)`, and
`orderOf x'` divides both coprime cardinalities — forcing `x' = 1`, absurd.

`hW1T` is the `κ`-Hall side condition of (8.12.b) on the `T`-side, vacuous when `T` is of
Type I (`S12.typePData_W1_isHallSubgroup_kappa` discharges it otherwise). -/
theorem ftThickenedSupport_mixed_disjoint_of_nonconjugate_typeA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    {tauS tauT : PeterfalviType}
    (htauS : HasPeterfalviType tauS S) (htauT : HasPeterfalviType tauT T)
    (hW1T : tauT ≠ PeterfalviType.I → ∀ data : TypePData T,
      OddOrder.Isaacs.Ch03.IsHallSubgroup
        (OddOrder.BG.Ch4.S14.kappa T) (data.W1.subgroupOf T))
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T) :
    Disjoint (ftThickenedSupport S (A1 S tauS))
        (ftThickenedSupport T (OddOrder.GroupTheory.typeA T tauT)) ∨
      Disjoint (ftThickenedSupport T (A1 T tauT))
        (ftThickenedSupport S (OddOrder.GroupTheory.typeA S tauS)) := by
  by_contra hcon
  obtain ⟨hST, hTS⟩ := not_or.mp hcon
  -- (8.18.b) + (8.18.a) at `(S,T)`: a supporting configuration for the coprimality.
  obtain ⟨x, g, hxA1S, hgx⟩ :=
    exists_A1_conj_mem_typeA_of_not_disjoint hG hS hT htauS htauT hnc hST
  obtain ⟨hxesc, hxle⟩ :=
    escaping_supported_of_A1_conj_mem_typeA hG hS hT htauS htauT hW1T hnc hxA1S hgx
  have hcop := supported_sigma_coprime_typeA hG (T := T) hS htauS
    ⟨x, hxesc, MulAut.conj g⁻¹ • T,
      mem_maximalSubgroups.mpr
        (OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hT)),
      hxle, ⟨g⁻¹, rfl⟩⟩
  -- (8.18.b) at `(T,S)`: an `A₁(T)`-point with a conjugate in `A(S)`.
  have hncTS : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup T S := fun h => hnc h.symm
  obtain ⟨x', u, hx'A1T, hux'⟩ :=
    exists_A1_conj_mem_typeA_of_not_disjoint hG hT hS htauT htauS hncTS hTS
  -- `orderOf x'` divides the coprime pair `|T_σ|`, `|C_S(u·x'·u⁻¹)|`.
  set w := u * x' * u⁻¹ with hwdef
  have hx'1 : x' ≠ 1 := fun h =>
    ((Set.mem_sdiff x').mp hx'A1T).2 (Set.mem_singleton_iff.mpr h)
  have h1 : orderOf x' ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma T) := by
    have hx'Mσ : x' ∈ OddOrder.BG.Ch3.S10.Msigma T := by
      have hx'm := ((Set.mem_sdiff x').mp hx'A1T).1
      rwa [OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG hT htauT, SetLike.mem_coe] at hx'm
    exact Subgroup.orderOf_dvd_natCard _ hx'Mσ
  have h2 : orderOf x' ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w) := by
    have hworder : orderOf w = orderOf x' := by
      have hinj : Function.Injective (MulAut.conj u) := (MulAut.conj u).injective
      simpa [hwdef] using orderOf_injective (MulAut.conj u).toMonoidHom hinj x'
    have hdvd := Subgroup.orderOf_dvd_natCard (OddOrder.Peterfalvi.S04.centralizerIn S w)
      (OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
        ⟨OddOrder.GroupTheory.typeA_subset hux', rfl⟩)
    rwa [hworder] at hdvd
  have hone : orderOf x' ∣ 1 := (hcop w hux') ▸ Nat.dvd_gcd h1 h2
  exact hx'1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone))

/-- **Peterfalvi (8.18.c) for a type-I pair**: the both-Type-I specialisation of
`ftThickenedSupport_mixed_disjoint_of_nonconjugate_typeA` (`typeA_eq_typeIA`). -/
theorem ftThickenedSupport_mixed_disjoint_of_nonconjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S T : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (hT : T ∈ maximalSubgroups G)
    (dS : TypeIData S) (dT : TypeIData T)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup S T) :
    Disjoint (ftThickenedSupport S (A1 S PeterfalviType.I))
        (ftThickenedSupport T (typeIA T dT)) ∨
      Disjoint (ftThickenedSupport T (A1 T PeterfalviType.I))
        (ftThickenedSupport S (typeIA S dS)) := by
  have h := ftThickenedSupport_mixed_disjoint_of_nonconjugate_typeA hG hS hT
    (tauS := PeterfalviType.I) (tauT := PeterfalviType.I) ⟨dS⟩ ⟨dT⟩
    (fun hne => absurd rfl hne) hnc
  rwa [OddOrder.GroupTheory.typeA_eq_typeIA dT,
    OddOrder.GroupTheory.typeA_eq_typeIA dS] at h

/-- **Peterfalvi (8.17)**: BG Theorem E data for a set of conjugacy-class
representatives of maximal subgroups.

The field `ι` indexes the representatives `M_i`.  The prime-factor fields record
the statement that `π(G)` is the disjoint union of the `π((M_i)_s)`, while
`cover_card` records the faithful BG cover cardinality
`|𝒞_G(M̃_i)| = (|(M_i)_s| - 1) |G : M_i|`. -/
structure BGTheoremECoverData (G : Type*) [Group G] where
  /-- Indexing type for the representative maximal subgroups. -/
  ι : Type*
  /-- The representative maximal subgroup `M_i`. -/
  reps : ι → Subgroup G
  /-- The Peterfalvi type attached to `M_i`. -/
  tau : ι → PeterfalviType
  /-- The faithful BG cover set `𝒞_G(M̃_i)` attached to `M_i`: the conjugacy-saturation of the
  `σ`-decomposition support `M̃_i = ⋃_{x ∈ (M_i)_σ#} x R(x)` of BG Lemma 14.5.  Abstracted as a
  bare `Set G` so the structure need not carry the `SigmaDecompositionData`/`Finite` data of `M̃`.
  (This replaces the unfaithful `thickenedA1 (M_i) (M_i)`, whose `(M_i)_F`-based kernel disagrees
  with the per-`x` signalizer `(N[x])_F` of Peterfalvi (8.14); see issue 8021.) -/
  cover : ι → Set G
  /-- The representatives form a finite family. -/
  finite_index : Fintype ι
  /-- Every representative is maximal. -/
  maximal : ∀ i : ι, reps i ∈ maximalSubgroups G
  /-- Every representative has its indicated Peterfalvi type. -/
  typed : ∀ i : ι, HasPeterfalviType (tau i) (reps i)
  /-- Every maximal subgroup is conjugate to one of the representatives. -/
  representatives :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      ∃ i : ι, ∃ g : G, MulAut.conj g • M = reps i
  /-- The representatives have no repeated conjugacy classes. -/
  nonconjugate :
    ∀ i j : ι, (∃ g : G, MulAut.conj g • reps i = reps j) → i = j
  /-- `π(G)` is covered by the `π((M_i)_s)`. -/
  primeFactors_cover :
    ∀ p : ℕ, p.Prime →
      (p ∈ (Nat.card G).primeFactors ↔
        ∃ i : ι, p ∈ (Nat.card ↥(mainSubgroup (reps i) (tau i))).primeFactors)
  /-- The `π((M_i)_s)` are pairwise disjoint. -/
  primeFactors_disjoint :
    ∀ i j : ι, i ≠ j →
      Disjoint
        ((Nat.card ↥(mainSubgroup (reps i) (tau i))).primeFactors : Finset ℕ)
        ((Nat.card ↥(mainSubgroup (reps j) (tau j))).primeFactors : Finset ℕ)
  /-- **BG Lemma 14.5(c)**: the cardinality formula for the faithful cover `𝒞_G(M̃_i)`:
  `|𝒞_G(M̃_i)| = (|(M_i)_s| - 1) |G : M_i|`. -/
  cover_card :
    ∀ i : ι,
      Nat.card ↥(cover i) =
        (Nat.card ↥(mainSubgroup (reps i) (tau i)) - 1) * (reps i).index

/-- **Peterfalvi (8.17), case (8.8.a)**: when all maximal subgroups are type I,
`G#` is the disjoint union of the thickened `A_1(M_i)` sets. -/
structure BGTheoremETypeICovering (data : BGTheoremECoverData G) : Prop where
  /-- The cover sets `𝒞_G(M̃_i)` cover all nonidentity elements of `G`. -/
  cover_nonidentity :
    sharpSubgroup (⊤ : Subgroup G) =
      ⋃ i : data.ι, data.cover i
  /-- The cover by the `𝒞_G(M̃_i)` is disjoint. -/
  pairwise_disjoint_thickened :
    (Set.univ : Set data.ι).PairwiseDisjoint fun i => data.cover i

/-- **Peterfalvi (8.17), case (8.8.b)**: in the two-exceptional-subgroup case,
`G#` is covered by the thickened `A_1(M_i)` sets together with the conjugates of
the exceptional `W#`. -/
structure BGTheoremENonTypeICovering (data : BGTheoremECoverData G) where
  /-- The exceptional TI-set `Ẑ` (BG `zTilde K K* = (K ⊔ K*) \ (K ∪ K*)`) whose nonidentity
  conjugates supplement the cover.  Modelled as a bare `Set G`, **not** `W#` for a subgroup `W`:
  `Ẑ` removes all of `K ∪ K*` (not just `1`), so no `sharpSubgroup W = W \ {1}` equals it.  The
  earlier `W : Subgroup` form is unsatisfiable — the minimal subgroup containing `Ẑ` is `K ⊔ K*`,
  whose `K*# ⊆ M_σ# ⊆ M̃` would overlap the cover, breaking `exceptional_disjoint_thickened`
  (issue 8020).  Satisfied by `exceptionalSet = zTilde K K*` via the fixed-`W` cover
  (`BG.Ch4.S14.exists_mem_conjClassSet_Mtilde_or_fixed_zTilde`). -/
  exceptionalSet : Set G
  /-- The cover sets `𝒞_G(M̃_i)` and the conjugates of `Ẑ` cover `G#`. -/
  cover_nonidentity :
    sharpSubgroup (⊤ : Subgroup G) =
      (⋃ i : data.ι, data.cover i) ∪
        conjClassSet exceptionalSet
  /-- The `𝒞_G(M̃_i)` part of the cover is disjoint. -/
  pairwise_disjoint_thickened :
    (Set.univ : Set data.ι).PairwiseDisjoint fun i => data.cover i
  /-- The exceptional part is disjoint from every `𝒞_G(M̃_i)`. -/
  exceptional_disjoint_thickened :
    ∀ i : data.ι,
      Disjoint (conjClassSet exceptionalSet) (data.cover i)

/-- **NonTypeICovering producer** (the `𝓜_P ≠ ∅` side of the (8.8) dichotomy): when `data`'s cover
is the faithful `𝒞_G(M̃_i)` family and a reference type-`P` maximal `Mref` exists (Theorem 14.7 data
`Kref, K*ref, Uref`), `data` admits a `BGTheoremENonTypeICovering` with exceptional set
`Ẑ = zTilde Kref K*ref`.

- `cover_nonidentity`: the fixed-`W` cover (`exists_mem_conjClassSet_Mtilde_or_fixed_zTilde`) puts
  every `x ≠ 1` in some `𝒞_G(M̃_M)` — moved to a representative via `data.representatives` +
  `Mtilde_conj_smul` + `conjClassSet_conj_smul` — or in the fixed `𝒞_G(Ẑ)`; the reverse uses that
  conjugacy-saturations of `1`-free sets avoid `1`.
- `pairwise_disjoint_thickened`: `conjClassSet_Mtilde_disjoint` on nonconjugate reps.
- `exceptional_disjoint_thickened`: `conjClassSet_T_Mtilde_disjoint`, with `Ẑ` rewritten to the
  family `T`-set form via `family_inf_msigma_union_eq`. -/
noncomputable def nonTypeICovering_of_isTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (data : BGTheoremECoverData G)
    (hcover : ∀ j : data.ι, data.cover j = conjClassSet
      (OddOrder.BG.Ch4.S14.Mtilde hG (OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG)
        (data.reps j)))
    {Mref Kref Kstarref Uref : Subgroup G} (hMref : Mref ∈ maximalSubgroups G)
    (hMPref : OddOrder.BG.Ch4.S14.IsTypeP Mref) (hKMref : Kref ≤ Mref)
    (hKref : Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa Mref)
      (Kref.subgroupOf Mref))
    (hKstarref : Kstarref =
      OddOrder.BG.Ch3.S10.Msigma Mref ⊓ Subgroup.centralizer (Kref : Set G))
    (hUref : Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa Mref ∪ OddOrder.BG.Ch3.S10.sigma Mref)ᶜ)
      (Uref.subgroupOf Mref)) :
    BGTheoremENonTypeICovering data := by
  classical
  set D := OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG with hD
  -- conjugacy-saturation of a `1`-free set avoids `1`, hence lands in `(⊤)#`.
  have hsub : ∀ S : Set G, (1 : G) ∉ S → conjClassSet S ⊆ sharpSubgroup (⊤ : Subgroup G) := by
    rintro S hS y ⟨t, ht, g, rfl⟩
    rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff]
    refine ⟨Subgroup.mem_top _, fun h1 => hS ?_⟩
    have ht1 : t = 1 := mul_left_cancel ((mul_inv_eq_one.mp h1).trans (mul_one g).symm)
    exact ht1 ▸ ht
  refine ⟨OddOrder.BG.Ch4.S14.zTilde Kref Kstarref, ?_, ?_, ?_⟩
  · -- cover_nonidentity
    apply Set.Subset.antisymm
    · intro x hx
      have hx1 : x ≠ 1 := by
        rw [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff] at hx; exact hx.2
      rcases OddOrder.BG.Ch4.S14.exists_mem_conjClassSet_Mtilde_or_fixed_zTilde hG hMref hMPref
        hKMref hKref hKstarref hUref hx1 with ⟨M, hMmax, hxM⟩ | hxZ
      · obtain ⟨j, g, hgconj⟩ := data.representatives M hMmax
        refine Or.inl (Set.mem_iUnion.mpr ⟨j, ?_⟩)
        rw [hcover j, ← hgconj, ← OddOrder.BG.Ch4.S14.Mtilde_conj_smul hG D g M,
          OddOrder.BG.Ch4.S14.conjClassSet_conj_smul]
        exact hxM
      · exact Or.inr hxZ
    · rintro y (hy | hy)
      · obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
        rw [hcover j] at hyj
        exact hsub _ (OddOrder.BG.Ch4.S14.one_not_mem_Mtilde hG D (data.maximal j)) hyj
      · exact hsub _ (OddOrder.BG.Ch4.S14.one_not_mem_zTilde Kref Kstarref) hy
  · -- pairwise_disjoint_thickened
    intro j _ k _ hjk
    change Disjoint (data.cover j) (data.cover k)
    rw [hcover j, hcover k]
    exact OddOrder.BG.Ch4.S14.conjClassSet_Mtilde_disjoint hG D (data.maximal j) (data.maximal k)
      (fun hconj => hjk (data.nonconjugate j k hconj))
  · -- exceptional_disjoint_thickened
    intro j
    rw [hcover j]
    obtain ⟨Mstar, hMstarne, hMstarmem, hpart⟩ :=
      OddOrder.BG.Ch4.S14.exists_partner hG D hMref hMPref hKMref hKref hKstarref hUref
    have hunion := OddOrder.BG.Ch4.S14.family_inf_msigma_union_eq hG hMref hMPref hKMref hKref
      hKstarref hUref hMstarmem hMstarne hpart
    have hzeq : OddOrder.BG.Ch4.S14.zTilde Kref Kstarref =
        ((Kref ⊔ Kstarref : Subgroup G) : Set G) \
        ⋃ N ∈ OddOrder.BG.Ch4.S14.ZFamilyFinset Mref Kref,
          (((Kref ⊔ Kstarref) ⊓ OddOrder.BG.Ch3.S10.Msigma N : Subgroup G) : Set G) := by
      simp only [OddOrder.BG.Ch4.S14.zTilde]; rw [hunion]
    rw [hzeq]
    exact OddOrder.BG.Ch4.S14.conjClassSet_T_Mtilde_disjoint hG D hMref hMPref hKMref hKref
      hKstarref hUref (data.maximal j)

/-- **Peterfalvi (8.17)**: BG Theorem E, repackaged as the Section 10 covering
interface.

This statement deliberately does not prove BG Theorem E.  It records the exact
data Peterfalvi uses after (8.14): the `π(G)` partition by the `M_i_s`, the
cardinality of each thickened `A_1(M_i)`, and the appropriate `G#` cover in the
two cases from (8.8).

The case-(b) branch carries its **type-`P` provenance** (`maximalTypePFamily G` nonempty):
per (8.8), the two-exceptional-subgroup cover arises *only* from a type-`P` maximal (the
exceptional `Ẑ` is built from a reference type-`P` maximal's `κ`-Hall data,
`nonTypeICovering_of_isTypeP`).  Recording the witness is the (8.8.a) *exclusivity* — the
carrier `BGTheoremENonTypeICovering` alone does not expose it (an empty exceptional set
satisfies the carrier whenever the type-I cover holds), and the all-type-I consumer (12.17)
needs it to rule the branch out (`S14.not_nonTypeICovering_of_all_typeI`). -/
theorem bgTheoremE_cover_data [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∃ data : BGTheoremECoverData G,
      BGTheoremETypeICovering data ∨
        ((OddOrder.BG.Ch4.S14.maximalTypePFamily G).Nonempty ∧
          Nonempty (BGTheoremENonTypeICovering data)) := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨reps, hrepsMax, hreps⟩ := OddOrder.BG.Ch4.S16.exists_maximal_conjugacy_reps (G := G)
  have : Fintype ↥reps := Fintype.ofFinite _
  -- Index the representatives by `Fin n`, then `ULift` to the (universe-polymorphic) struct index.
  let e := Fintype.equivFin (↥reps)
  -- Peterfalvi type label + classification proof for each representative (exhaustiveness).
  let tau : ↥reps → PeterfalviType := fun i =>
    (OddOrder.BG.Ch4.S16.exists_peterfalviType hG (hrepsMax i.1 i.2)).choose
  have htyped : ∀ i : ↥reps, HasPeterfalviType (tau i) i.1 := fun i =>
    (OddOrder.BG.Ch4.S16.exists_peterfalviType hG (hrepsMax i.1 i.2)).choose_spec
  -- Prime-factor bridge: `π(M_s) = σ(M)`, via `M_s = M_σ` (Pf 8.10, `mainSubgroup_eq_Msigma`)
  -- and `π(M_σ) = σ(M)` (`primeFactors_Msigma_eq_sigma`).
  have hbridge : ∀ (i : ↥reps) (t : PeterfalviType), HasPeterfalviType t i.1 → ∀ p : ℕ,
      p ∈ (Nat.card ↥(mainSubgroup i.1 t)).primeFactors ↔
        p ∈ OddOrder.BG.Ch3.S10.sigma i.1 := fun i t ht p => by
    have h : mainSubgroup i.1 t = OddOrder.BG.Ch3.S10.Msigma i.1 :=
      OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG (hrepsMax i.1 i.2) ht
    rw [h]
    exact OddOrder.BG.Ch4.S16.primeFactors_Msigma_eq_sigma hG (hrepsMax i.1 i.2) p
  -- Canonical `σ`-decomposition data (the faithful cover `𝒞_G(M̃)` is independent of the choice).
  let D := OddOrder.BG.Ch4.S14.genuineSigmaDecomposition hG
  refine ⟨{
    ι := ULift (Fin (Fintype.card (↥reps)))
    reps := fun j => (e.symm j.down).1
    tau := fun j => tau (e.symm j.down)
    cover := fun j => conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG D (e.symm j.down).1)
    finite_index := inferInstance
    maximal := fun j => hrepsMax _ (e.symm j.down).2
    typed := fun j => htyped (e.symm j.down)
    representatives := fun M hM => by
      obtain ⟨Mi, ⟨hMirep, hconj⟩, _⟩ := hreps M hM
      refine ⟨⟨e ⟨Mi, hMirep⟩⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      exact hconj
    nonconjugate := fun j k hconj => by
      have hsub : e.symm j.down = e.symm k.down := by
        obtain ⟨_, _, huniq⟩ := hreps (e.symm j.down).1 (hrepsMax _ (e.symm j.down).2)
        exact Subtype.ext
          ((huniq _ ⟨(e.symm j.down).2, OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl _⟩).trans
            (huniq _ ⟨(e.symm k.down).2, hconj⟩).symm)
      exact ULift.ext _ _ (e.symm.injective hsub)
    primeFactors_cover := fun p _ => by
      rw [OddOrder.BG.Ch4.S16.sigma_reps_prime_cover hG hrepsMax hreps p]
      constructor
      · rintro ⟨Mi, hMirep, hpMi⟩
        refine ⟨⟨e ⟨Mi, hMirep⟩⟩, ?_⟩
        simp only [Equiv.symm_apply_apply]
        exact (hbridge ⟨Mi, hMirep⟩ _ (htyped ⟨Mi, hMirep⟩) p).mpr hpMi
      · rintro ⟨j, hpj⟩
        exact ⟨(e.symm j.down).1, (e.symm j.down).2,
          (hbridge (e.symm j.down) _ (htyped (e.symm j.down)) p).mp hpj⟩
    primeFactors_disjoint := fun j k hjk => by
      rw [Finset.disjoint_left]
      intro p hpj hpk
      have hne : (e.symm j.down).1 ≠ (e.symm k.down).1 := fun h =>
        hjk (ULift.ext _ _ (e.symm.injective (Subtype.ext h)))
      have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (e.symm j.down).1 ∩
          OddOrder.BG.Ch3.S10.sigma (e.symm k.down).1 :=
        ⟨(hbridge (e.symm j.down) _ (htyped (e.symm j.down)) p).mp hpj,
          (hbridge (e.symm k.down) _ (htyped (e.symm k.down)) p).mp hpk⟩
      rw [OddOrder.BG.Ch4.S16.sigma_reps_pairwise_disjoint hG hrepsMax hreps
        (e.symm j.down).2 (e.symm k.down).2 hne] at hpσ
      exact Set.notMem_empty p hpσ
    cover_card := fun j => by
      -- **BG Lemma 14.5(c)** for the faithful cover (issue 8021 resolution): the cover is
      -- `𝒞_G(M̃)` with `M̃ = ⋃_{x ∈ M_σ#} x R(x)` the per-`x` signalizer support, whose cardinality
      -- `sigmaConjugacySaturation_Mtilde_ncard` proves to be `(|M_σ| − 1)·[G:M]`.  The
      -- `mainSubgroup`-stated RHS is rewritten to `M_σ` by `mainSubgroup_eq_Msigma` (Pf 8.10).
      have hms : mainSubgroup (e.symm j.down).1 (tau (e.symm j.down))
          = OddOrder.BG.Ch3.S10.Msigma (e.symm j.down).1 :=
        OddOrder.BG.Ch4.S16.mainSubgroup_eq_Msigma hG (hrepsMax _ (e.symm j.down).2)
          (htyped (e.symm j.down))
      change Nat.card ↥(conjClassSet (OddOrder.BG.Ch4.S14.Mtilde hG D (e.symm j.down).1)) = _
      rw [Nat.card_coe_set_eq,
        OddOrder.BG.Ch4.S14.sigmaConjugacySaturation_Mtilde_ncard hG D
          (hrepsMax _ (e.symm j.down).2), hms]
  }, ?_⟩
  -- The (8.8) covering dichotomy (BG Cor 14.9) splits on whether a type-`P` maximal exists.
  by_cases hP : (OddOrder.BG.Ch4.S14.maximalTypePFamily G).Nonempty
  · -- `𝓜_P ≠ ∅`: the non-Type-I covering, exceptional `Ẑ` of a reference type-`P`
    -- maximal (fix-`W`).
    obtain ⟨Mref, hMrefmax, hMrefP⟩ := hP
    obtain ⟨Kref, Kstarref, Uref, hKMref, hKref, hKstarref, hUref⟩ :=
      OddOrder.BG.Ch4.S14.exists_typeP_data hG hMrefmax
    exact Or.inr ⟨⟨Mref, hMrefmax, hMrefP⟩,
      ⟨nonTypeICovering_of_isTypeP hG _ (fun _ => rfl) hMrefmax hMrefP hKMref hKref
        hKstarref hUref⟩⟩
  · -- `𝓜_P = ∅` (every maximal is type-F/I): the Type-I covering — the faithful BG Cor 14.9
    -- all-type-`F` cover and Lemma 14.5(b) disjointness.  (The former kernel-collapse field was
    -- mis-layered §8 content and is discharged at the §12 consumer via the (12.17)-faithful
    -- route; issue 9080.)
    have hPempty : OddOrder.BG.Ch4.S14.maximalTypePFamily G = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hP
    have htypeF : ∀ M' ∈ maximalSubgroups G, OddOrder.BG.Ch4.S14.IsTypeF M' := fun M' hM'max =>
      OddOrder.BG.Ch4.S14.isTypeF_iff_not_isTypeP.mpr fun hPM' =>
        Set.notMem_empty M'
          (hPempty ▸ (⟨hM'max, hPM'⟩ : M' ∈ OddOrder.BG.Ch4.S14.maximalTypePFamily G))
    refine Or.inl ⟨?_, ?_⟩
    · -- `cover_nonidentity`: BG Cor 14.9 (the all-type-`F` cover), converted to representatives.
      refine (OddOrder.BG.Ch4.S14.sharpSubgroup_top_eq_iUnion_conjClassSet_Mtilde_of_typeF hG
        htypeF).trans ?_
      ext g
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · intro hex
        obtain ⟨Mi, hMirep, hg⟩ :=
          (OddOrder.BG.Ch4.S16.mem_conjClassSet_Mtilde_maximals_iff_reps hG hrepsMax
            (fun H hH => (hreps H hH).exists) g).mp hex
        refine ⟨⟨e ⟨Mi, hMirep⟩⟩, ?_⟩
        simp only [Equiv.symm_apply_apply]
        exact hg
      · rintro ⟨j, hg⟩
        exact ⟨(e.symm j.down).1, hrepsMax _ (e.symm j.down).2, hg⟩
    · -- `pairwise_disjoint_thickened`: Lemma 14.5(b) over nonconjugate representatives.
      intro j _ k _ hjk
      have hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup
          (e.symm j.down).1 (e.symm k.down).1 := by
        intro hconj
        apply hjk
        obtain ⟨_, _, huniq⟩ := hreps (e.symm j.down).1 (hrepsMax _ (e.symm j.down).2)
        exact ULift.ext _ _ (e.symm.injective (Subtype.ext
          ((huniq _ ⟨(e.symm j.down).2, OddOrder.BG.Ch4.S14.IsConjugateSubgroup.refl _⟩).trans
            (huniq _ ⟨(e.symm k.down).2, hconj⟩).symm)))
      exact OddOrder.BG.Ch4.S14.conjClassSet_Mtilde_disjoint hG D
        (hrepsMax _ (e.symm j.down).2) (hrepsMax _ (e.symm k.down).2) hnc

end OddOrder.Peterfalvi.S10


