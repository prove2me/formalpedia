-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_CrossIsometrySetup
-- name    : OddOrder_Peterfalvi_S12_CrossIsometrySetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:20:53.431229+00:00
-- url     : https://prove2.me/theorems/9f6add3d-5c6d-4551-8725-ee51ec837878
-- title:
--   Peterfalvi §12: the type II cross-isometry pair, opening layer
-- statement:
--   The opening layer of the type II cross-isometry development: the (5.3.b) base orthogonality on the $S$-side and (5.5) for the $T_2$-coherence.
--
--   Main declarations: `typeII_tau_diff_inner_chiFam_eq_zero` (The (5.3.b) base-orthogonality kernel, `S`-side); `typeII_R_mem_inner_chiFam_eq_zero` (The (5.3.b) base orthogonality, per `R`-element); `typeII_T2_extension_lam_mem_span_RFamily` (Peterfalvi (5.5) for the `T2`-coherence); `typeII_T2_extension_lam_inner_chiFam_eq_zero` (The (5.3.b) `S`-side grid orthogonality of the coherent image).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_CrossIsometrySetup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_CrossIsometrySetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIGridTranspose
import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIFrobenius
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

open scoped Classical FiniteInduce in
/-- **The (5.3.b) base-orthogonality kernel, `S`-side** (the honest content of Coq
`FTtypeP_base_ortho` at an irreducible family member): the `τ_S`-image of the conjugate
difference `λ − λ̄` is orthogonal to every (3.5) grid vector `χ_P`.

`λ − λ̄` is supported on `A(S)` (member supports lie in `A(S) ∪ {1}` and the degrees at `1`
agree), so its Dade image **vanishes on the exceptional set `V`**
(`typeII_tau_apply_eq_zero_of_mem_ticVdiffV` — `V ⊆ A₀(S)` consists of Dade base points
whose value is `(λ − λ̄)(v) = 0` off `S'`).  It is a norm-`2` virtual character (Dade
isometry on the supported pair of distinct orthonormal irreducibles), so the (3.7)/(3.8)
counting kills every σ-coefficient (`sigmaCoeff_eq_zero_of_vanishOnV`) — and the
σ-coefficients **are** the inner products with the grid. -/
theorem typeII_tau_diff_inner_chiFam_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (P : ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W1.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ) ×
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W2.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ)) :
    ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 0 := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  -- family memberships of `λ` and `λ̄` (through the world bridge)
  have hlamIKF := typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  have hlamBarIKF := OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate
    _ hlamIKF
  -- `λ ≠ λ̄` (no real characters in the family, `|S|` odd)
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (Y.subgroupOf S) hlamIKF
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  -- support of the difference: in `A(S)` (degrees at `1` agree)
  have hsupp : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
        (derivedInG S)) S := by
    have hmem := typeII_T2_member_support hG hSmax hSII data hlam_mem hlam_mem
    refine diff_support_subset_of_support_subset_union_one
      (hmem lam (by simp)) (hmem lam.conj (by simp)) ?_
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [ClassFunction.conj_apply, hn, star_natCast]
  -- the `A₀`-supported form (the Dade hypothesis' set is `A(S) ∪ V^S`)
  have hsuppA0 : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data.typeP)) S :=
    hsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- `ψ ∈ ZIrr G`
  have hψZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
      (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
      hsuppA0
      (Submodule.sub_mem _
        (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hlamIKF)
        (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr hlamBarIKF))
  -- `‖ψ‖² = 2` (Dade isometry + distinct orthonormal irreducible pair)
  have hcross : ClassFunction.inner lam lam.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam.conj, hlam_irr.conj⟩
    rwa [if_neg (fun heq => hlamne (congrArg Subtype.val heq))] at h
  have hcross' : ClassFunction.inner lam.conj lam = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcross, star_zero]
  have hiso : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      = ClassFunction.inner (lam - lam.conj) (lam - lam.conj) :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0 hsuppA0 hsuppA0
  have hψ2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj))
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj)) = 2 := by
    rw [hiso, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hlam_irr.inner_self_eq_one,
      hlam_irr.conj.inner_self_eq_one, hcross, hcross']
    norm_num
  -- `ψ` vanishes on `V` (the anchor)
  have hψV : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).V,
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau (lam - lam.conj) v = 0 :=
    fun v hv => typeII_tau_apply_eq_zero_of_mem_ticVdiffV hG hSmax hSII data.typeP hsupp hv
  -- the (3.7)/(3.8) counting kills every σ-coefficient
  have hall := (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).sigmaCoeff_eq_zero_of_vanishOnV rfl
    (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
      (typeIIHypothesis46 hG hSmax hSII data.typeP)) hψZ hψ2 hψV
  exact hall P

open scoped Classical FiniteInduce in
/-- **The (5.3.b) base orthogonality, per `R`-element** (Coq `FTtypeP_base_ortho`): every
member of the dispatched `R(λ)`-family is orthogonal to every (3.5) grid vector `χ_P`.

The constituent trick over the kernel `typeII_tau_diff_inner_chiFam_eq_zero`: an
`R`-element `α` with `⟨α, χ_P⟩ ≠ 0` would satisfy `χ_P = ±α` (both are norm-one virtual
characters, so the integer inner product is `±1` and the difference/sum has norm `0`);
but then the flat expansion `τ_S(λ − λ̄) = ∑_{β ∈ R(λ)} β` (`image_eq`) pairs with `χ_P`
to `⟨α, χ_P⟩ = ±1 ≠ 0` (all other terms die by orthonormality of `R(λ)`), contradicting
the kernel. -/
theorem typeII_R_mem_inner_chiFam_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    {α : ClassFunction G ℂ}
    (hα : α ∈ (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).imageSet)
    (P : ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W1.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ) ×
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W2.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ)) :
    ClassFunction.inner α
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 0 := by
  classical
  by_contra hne
  -- both sides are norm-one virtual characters
  have hαZ : α ∈ ZIrr G :=
    (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).mem_ZIrr α hα
  have hα1 : ClassFunction.inner α α = 1 :=
    (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).inner_self_of_mem hα
  have hPZ : (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P ∈ ZIrr G :=
    ((OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam_spec rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP))).2.1 P
  have hP1 : ClassFunction.inner
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 1 := by
    rw [((OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam_spec rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP))).2.2.1, if_pos rfl]
  -- the integer inner product is `±1`
  obtain ⟨c, hc⟩ := inner_intCast_of_mem_ZIrr hαZ hPZ
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0] at hc
    exact hne (by rw [hc]; norm_num)
  have hcstar : ClassFunction.inner
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) α = (c : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hc, star_intCast]
  have hsub : ClassFunction.inner
      (α - (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      (α - (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = ((2 - 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hα1, hP1, hc, hcstar]
    push_cast; ring
  have hadd : ClassFunction.inner
      (α + (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      (α + (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = ((2 + 2 * c : ℤ) : ℂ) := by
    rw [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, hα1, hP1, hc, hcstar]
    push_cast; ring
  have hle : c ≤ 1 := by
    have h0 := inner_self_re_nonneg (α - (OddOrder.Peterfalvi.S06.ticVdiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
    rw [hsub, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 - 2 * c := by exact_mod_cast h0
    omega
  have hge : -1 ≤ c := by
    have h0 := inner_self_re_nonneg (α + (OddOrder.Peterfalvi.S06.ticVdiff
        (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
    rw [hadd, Complex.intCast_re] at h0
    have : (0 : ℤ) ≤ 2 + 2 * c := by exact_mod_cast h0
    omega
  -- `χ_P = ±α`
  have hPeq : (OddOrder.Peterfalvi.S06.ticVdiff
      (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
        (typeIIHypothesis46 hG hSmax hSII data.typeP)) P = (c : ℂ) • α := by
    interval_cases c
    · -- `c = −1`: `χ_P = −α`
      have hzero : α + (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P = 0 := by
        refine eq_zero_of_inner_self_re_eq_zero ?_
        rw [hadd]
        norm_num
      rw [show (((-1 : ℤ) : ℂ)) = -1 from by norm_num, neg_one_smul]
      exact eq_neg_of_add_eq_zero_right hzero
    · exact absurd rfl hcne
    · -- `c = 1`: `χ_P = α`
      have hzero : α - (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P = 0 := by
        refine eq_zero_of_inner_self_re_eq_zero ?_
        rw [hsub]
        norm_num
      rw [show (((1 : ℤ) : ℂ)) = 1 from by norm_num, one_smul]
      exact (sub_eq_zero.mp hzero).symm
  -- the flat `R`-expansion pairs to `±1 ≠ 0`, contradicting the kernel
  have hk1 := typeII_tau_diff_inner_chiFam_eq_zero hG hSmax hSII data hlam_mem hlam_irr P
  rw [(typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).image_eq,
    OddOrder.RepresentationTheory.inner_sum_left] at hk1
  have hsingle : ∀ β ∈ (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
      (Set.mem_insert _ _)).imageSet, β ≠ α →
      ClassFunction.inner β
        ((OddOrder.Peterfalvi.S06.ticVdiff
            (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) = 0 := by
    intro β hβ hβne
    rw [hPeq, OddOrder.RepresentationTheory.inner_smul_right,
      (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
        (Set.mem_insert _ _)).orthonormal β hβ α hα, if_neg hβne]
    simp
  rw [Finset.sum_eq_single α hsingle (fun h => absurd hα h)] at hk1
  rw [hPeq, OddOrder.RepresentationTheory.inner_smul_right, hα1, mul_one] at hk1
  have : (c : ℂ) = 0 := star_eq_zero.mp hk1
  exact hcne (by exact_mod_cast this)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.5) for the `T2`-coherence** (the lane-b template
`coherent_extension_mem_span_Rset_of_mem` re-enacted at the type-II member family): the
coherent image of the irreducible member `λ` lies in `ℤ[R(λ)]`.

The `ofProjection (ψ := 0)` engine against the dispatched `R(λ)`-family
(`typeII_T2_memberRFamily`): the (5.4) decomposition `λ^{τ₂} = X − Y` has `‖Y‖² ≥ 0 = ‖ψ‖²`
automatically, so (5.4.b) forces `Y = 0` and `λ^{τ₂} = X ∈ ℤ[R(λ)]`
(`eq_sum_of_psi_eq_zero`).  The isometry/agreement inputs are the coherence's own fields on
the sponsoring lattice `ℤ[λ, λ̄]  ⊆ ℤ[T2]`; the support input is the `A₀(S)`-support of
`λ − λ̄` (as in the kernel `typeII_tau_diff_inner_chiFam_eq_zero`). -/
theorem typeII_T2_extension_lam_mem_span_RFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
            (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S)) :
    c.extension lam ∈ Submodule.span ℤ
      ((typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
        (Set.mem_insert _ _)).imageSet : Set (ClassFunction G ℂ)) := by
  classical
  have hModd : Odd (Nat.card ↥S) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card S)
  -- `λ ≠ λ̄`, and the `A₀(S)`-support of the difference (as in the kernel)
  have hlamIKF := typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (Y.subgroupOf S) hlamIKF
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  have hsupp : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
        (derivedInG S)) S := by
    have hmem := typeII_T2_member_support hG hSmax hSII data hlam_mem hlam_mem
    refine diff_support_subset_of_support_subset_union_one
      (hmem lam (by simp)) (hmem lam.conj (by simp)) ?_
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [ClassFunction.conj_apply, hn, star_natCast]
  have hsuppA0 : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S)) (derivedInG S)
        ∪ conjClassSetIn S (typePV S data.typeP)) S :=
    hsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  -- `⟨λ, λ̄⟩ = 0`
  have hcross : ClassFunction.inner lam lam.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite ⟨lam, hlam_irr⟩ ⟨lam.conj, hlam_irr.conj⟩
    rwa [if_neg (fun heq => hlamne (congrArg Subtype.val heq))] at h
  -- lattice memberships
  have hchi_zSpan : lam ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hchibar_zSpan : lam.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hdiff_zSpan : lam - lam.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) :=
    Submodule.sub_mem _ hchi_zSpan hchibar_zSpan
  have hsub : OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
      ({lam - lam.conj, lam - 0} : Set (ClassFunction ↥S ℂ)) ≤
      OddOrder.Peterfalvi.S07.zSpan (L := ↥S)
        ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ)) := by
    change Submodule.span ℤ _ ≤ Submodule.span ℤ _
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hdiff_zSpan
    · rw [sub_zero]; exact hchi_zSpan
  -- the (5.4)/(5.5) engine at `ψ = 0`
  obtain ⟨-, hτ1χ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection (ψ := 0)
        (typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
          (Set.mem_insert _ _)) c.extension
        (fun φ ζ hφ hζ => c.extension_inner_eq φ ζ (hsub hφ) (hsub hζ))
        (c.extends_on_supported (lam - lam.conj) ⟨hdiff_zSpan, hsuppA0⟩)
        (by rw [sub_zero]; exact c.extension_mem_ZIrr _ hchi_zSpan)
        (ClassFunction.inner_zero_right _)
        (ClassFunction.inner_zero_right _)
        hcross)
  have hgoal : c.extension lam = ∑ α ∈ E, α := hτ1χ.trans hXsum
  rw [hgoal]
  exact Submodule.sum_mem _ fun α hα =>
    Submodule.subset_span (Finset.mem_coe.mpr (hEsub hα))

open scoped Classical FiniteInduce in
/-- **The (5.3.b) `S`-side grid orthogonality of the coherent image** (Coq
`coherent_ortho_cycTIiso` at the irreducible member): `⟨χ_P, λ^{τ₂}⟩ = 0` for every (3.5)
grid vector.  `λ^{τ₂} ∈ ℤ[R(λ)]` by (5.5) (`typeII_T2_extension_lam_mem_span_RFamily`) and
every `R(λ)`-element is orthogonal to `χ_P` (`typeII_R_mem_inner_chiFam_eq_zero`), so the
inner product dies by ℤ-linearity of the right slot. -/
theorem typeII_T2_extension_lam_inner_chiFam_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hSmax : S ∈ maximalSubgroups G) (hSII : IsTypeII S)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    [NeZero (Nat.card (typeIIHypothesis46 hG hSmax hSII data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG hSmax hSII data.typeP).dade0
        (typeIIHypothesis46 hG hSmax hSII data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma S))
            (derivedInG S)
          ∪ conjClassSetIn S (typePV S data.typeP)) S))
    (P : ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W1.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ) ×
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W2.subgroupOf
        (OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).W →* ℂˣ)) :
    ClassFunction.inner
      ((OddOrder.Peterfalvi.S06.ticVdiff
          (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
          (typeIIHypothesis46 hG hSmax hSII data.typeP)) P)
      (c.extension lam) = 0 := by
  classical
  have key : ∀ x ∈ Submodule.span ℤ
      ((typeII_T2_memberRFamily hG hSmax hSII data hlam_mem hnu_mem hdeg
        (Set.mem_insert _ _)).imageSet : Set (ClassFunction G ℂ)),
      ClassFunction.inner
        ((OddOrder.Peterfalvi.S06.ticVdiff
            (typeIIHypothesis46 hG hSmax hSII data.typeP)).chiFam rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
            (typeIIHypothesis46 hG hSmax hSII data.typeP)) P) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        have h0 := typeII_R_mem_inner_chiFam_eq_zero hG hSmax hSII data
          hlam_mem hlam_irr hnu_mem hdeg (Finset.mem_coe.mp hy) P
        rw [OddOrder.RepresentationTheory.inner_conj_symm, h0, star_zero]
    | zero => exact ClassFunction.inner_zero_right _
    | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ih =>
        rw [← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]
  exact key _ (typeII_T2_extension_lam_mem_span_RFamily hG hSmax hSII data
    hlam_mem hlam_irr hnu_mem hdeg c)

open scoped Classical FiniteInduce in
/-- **The (5.3.b) `λ`-orthogonality against the aligned `M`-grid at the canonical pair**
(the `lam_ortho_grid` production; Coq `coherent_ortho_cycTIiso` consumed at `etaC`): the
`T2`-coherent image of the irreducible member `λ` is orthogonal to every `M`-side aligned
σ-grid vector.

Chain: the aligned grid vector is an `M`-side `χ`-family member
(`exists_alignedOmegaSigmaGrid_chiFam_family`); the per-index pair transpose reads it as an
`S`-side grid vector (`section16_pair_chiFam_transpose_T`); and the `S`-side grid is
orthogonal to `λ^{τ₂}` by (5.5) + the constituent trick
(`typeII_T2_extension_lam_inner_chiFam_eq_zero`). -/
theorem Hypothesis.extension_lam_inner_alignedGrid_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
            (derivedInG mp.S)
          ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S))
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i j) (c.extension lam) = 0 := by
  classical
  subst hT
  -- the aligned vector is an `M`-side `χ`-family member
  obtain ⟨P, -, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hG.odd i
  rw [hP j]
  -- transpose to an `S`-side grid vector, then apply the `S`-side orthogonality
  rw [section16_pair_chiFam_transpose_T hG hG.odd hSW1 hSW2 hyp.typeP hKstar.symm
    (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication
      (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP))
    (hyp.canonicalFullDadeApp hG hG.odd) (P j)]
  exact typeII_T2_extension_lam_inner_chiFam_eq_zero hG mp.S_maximal
    (section16_S_isTypeII hG mp) data hlam_mem hlam_irr hnu_mem hdeg c _

open scoped Classical FiniteInduce in
/-- **Peterfalvi (5.3.b), `M`-side: `ζ^{τ₁}` is orthogonal to the aligned σ-grid** (the
`zeta_ortho_grid` production — the full-`𝒮`-coherence form of the grid-orthogonality
intermediate of `tau1_zeta_vanishes_on_typePV`; cf. its `S(HC)`-port
`SHC_extension_inner_alignedOmegaSigma_eq_zero`).

`(ζ − ζ̄)^τ = ζ^{τ₁} − ζ̄^{τ₁}` (`tau_zeta_sub_conj_eq_tau1`) vanishes on `V`
(`tau_zeta_sub_conj_vanishes_on_typePV`) and has at most `2 < min(w₁, w₂)` nonzero
σ-coefficients (each `τ₁`-image is norm-`1` with at most one,
`ncard_inner_chiFam_ne_zero_le_one`), so every σ-coefficient dies
(`sigmaCoeff_eq_zero_of_sigmaNC_lt`); the norm-`1` projection
(`inner_left_eq_zero_of_inner_sub_eq_zero`) upgrades the difference orthogonality to
`⟨ζ^{τ₁}, χ_P⟩ = 0`, and the aligned grid vector **is** a `χ_P`
(`exists_alignedOmegaSigmaGrid_chiFam_family`). -/
theorem Hypothesis.tau1_zeta_inner_alignedGrid_eq_zero [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (coh.tau1 ζ) (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0 := by
  have := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hζne : ζ.conj ≠ ζ := inducedFamily_hasNoRealCharacters hModd hζS
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app := hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  obtain ⟨P, -, hPeq⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  rw [hPeq j]
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have haZ : coh.tau1 ζ ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 ζ.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζcS)
  have ha1 : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζS hζirr
  have hb1 : ClassFunction.inner (coh.tau1 ζ.conj) (coh.tau1 ζ.conj) = 1 :=
    hyp.zeta_tau1_inner_self hG hodd coh hζcS hζcirr
  have hab : ClassFunction.inner (coh.tau1 ζ) (coh.tau1 ζ.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension ζ) (coh.coherent.extension ζ.conj) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζcirr, if_neg (fun h => hζne h.symm)]
  -- `(ζ − ζ̄)^τ` vanishes on `V`, with `NC ≤ 2 < min(w₁, w₂)`
  have hvanish : ∀ w ∈ tic.V, hyp.tau (ζ - ζ.conj) w = 0 := fun w hw =>
    hyp.tau_zeta_sub_conj_vanishes_on_typePV hG hodd hζS hζirr hw
  have hNC : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
      < min (Nat.card ↥tic.W1) (Nat.card ↥tic.W2) := by
    have hbound : tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj)) ≤ 2 := by
      have hsub : {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0} ⊆
          {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner (coh.tau1 ζ.conj) (tic.chiFam hVeq app pq) ≠ 0} := by
        intro pq hpq
        by_contra hcon
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
        apply hpq
        change ClassFunction.inner (hyp.tau (ζ - ζ.conj)) (tic.chiFam hVeq app pq) = 0
        rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
          ClassFunction.inner_sub_left, hcon.1, hcon.2, sub_zero]
      calc tic.sigmaNC hVeq app (hyp.tau (ζ - ζ.conj))
          = {pq | tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) pq ≠ 0}.ncard := rfl
        _ ≤ ({pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0} ∪
              {pq | ClassFunction.inner (coh.tau1 ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {pq | ClassFunction.inner (coh.tau1 ζ) (tic.chiFam hVeq app pq) ≠ 0}.ncard +
              {pq | ClassFunction.inner (coh.tau1 ζ.conj)
                (tic.chiFam hVeq app pq) ≠ 0}.ncard :=
            Set.ncard_union_le _ _
        _ ≤ 1 + 1 := by
            gcongr
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app haZ ha1
            · exact tic.ncard_inner_chiFam_ne_zero_le_one hVeq app hbZ hb1
        _ = 2 := rfl
    have h3a := tic.three_le_card_W1
    have h3b := tic.three_le_card_W2
    omega
  -- σ-coefficient of the difference at `P j` dies; project to the `ζ^{τ₁}`-slot
  have hL3 : tic.sigmaCoeff hVeq app (hyp.tau (ζ - ζ.conj)) (P j) = 0 :=
    tic.sigmaCoeff_eq_zero_of_sigmaNC_lt hVeq app hvanish hNC (P j)
  have hdiff : ClassFunction.inner (coh.tau1 ζ - coh.tau1 ζ.conj)
      (tic.chiFam hVeq app (P j)) = 0 := by
    rw [← hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr]; exact hL3
  have hsZ : tic.chiFam hVeq app (P j) ∈ ZIrr G := (tic.chiFam_spec hVeq app).2.1 (P j)
  have hs1 : ClassFunction.inner (tic.chiFam hVeq app (P j))
      (tic.chiFam hVeq app (P j)) = 1 := by
    rw [(tic.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  exact inner_left_eq_zero_of_inner_sub_eq_zero haZ hsZ ha1 hb1 hs1 hab hdiff

end OddOrder.Peterfalvi.S12


