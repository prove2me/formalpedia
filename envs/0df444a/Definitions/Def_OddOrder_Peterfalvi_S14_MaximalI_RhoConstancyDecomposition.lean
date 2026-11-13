-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancyDecomposition
-- name    : OddOrder_Peterfalvi_S14_MaximalI_RhoConstancyDecomposition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:53:07.398849+00:00
-- url     : https://prove2.me/theorems/e9b78408-8e1c-4276-bcba-642617954cb1
-- title:
--   Peterfalvi (12.3)–(12.5): orthogonality and decomposition data (first half)
-- statement:
--   The first half of the $\rho$-constancy development for type I maximal subgroups: orthogonality and the character decomposition data, with the support properties of $\mathcal{S}$ and its $\tau$-images.
--
--   Main declarations: `Sset_vanishes_off_H` (Peterfalvi (12.4)/(12.5) input); `Sset_diff_support_subset_A1` (The full-member difference is `A₁`-supported); `Sset_diff_tau_support_subset_ftThickenedA1` (The `τ`-image of a full-member difference is `Ã₁`-supported); `constituentDiff_tau_support_subset_ftThickenedA` (The `τ`-image of a constituent difference is `Ã`-supported).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/RhoConstancyDecomposition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/RhoConstancyDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_Hypothesis

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The difference `φ − φ̄` of a constituent is supported in `A(L)` (each constituent is supported
in
`A(L) ∪ {1}` by `data.supported`, and `(φ − φ̄)(1) = 0` by equal degree — `φ(1)` is real). -/
theorem constituentDiff_support_subset {L : Subgroup G} {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  have := hyp.finiteG
  have hsupp_eq : (φ : ClassFunction ↥L ℂ).conj.support = (φ : ClassFunction ↥L ℂ).support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj) x ≠ 0 := hx
  have hxsupp : x ∈ (φ : ClassFunction ↥L ℂ).support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases data.supported φ hφ hxsupp with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
    exact hx0 (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hd, star_natCast,
      sub_self])

/-- Evaluation of a finite sum of class functions at a point (the eval map is additive). -/
theorem classFunction_sum_apply {H : Type*} [Group H] {ι : Type*} (s : Finset ι)
    (F : ι → ClassFunction H ℂ) (g : H) : (∑ i ∈ s, F i) g = ∑ i ∈ s, (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ClassFunction.add_apply, ih]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)/(12.5) input**: each member `χ = Ind_H^L θ` of `S` vanishes on `L − H`.
`H = L_F` is normal in `L` (`maxNilpotentNormalHall_subgroupOf_normal`, the Fitting subgroup `L_F`),
so the induced character is supported on `H` (`ClassFunction.induce_eq_zero_of_not_mem_normal`).
This
is the "the elements of `S` vanish on `L − H`" step of the constant-on-coset conclusions of
(12.4)/(12.5) (`ψ(xh) = β(xh) + γ(xh) = γ(x)`, the `β ∈ ℂ[S]` part vanishing off `H`). -/
theorem Sset_vanishes_off_H {L : Subgroup G} (hyp : Hypothesis L) {χ : ClassFunction ↥L ℂ}
    (hχ : χ ∈ hyp.Sset) {x : ↥L} (hxH : (x : G) ∉ hyp.H) : χ x = 0 := by
  have := hyp.finiteG
  obtain ⟨θ, _, hχ_eq⟩ := hχ
  have hnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  have hxmem : x ∉ (hyp.typeI.typeF.H).subgroupOf L :=
    fun hcon => hxH (Subgroup.mem_subgroupOf.mp hcon)
  rw [hχ_eq]
  exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hxmem

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The full-member difference is `A₁`-supported**: for `χ ∈ S` (`χ = Ind_H^L θ`, `H = L_F`),
`supp(χ − χ̄) ⊆ A₁(L) = (L_F)^#` — `χ` vanishes off the normal `H` (`Sset_vanishes_off_H`) and
`χ(1) = ∑_φ φ(1)` is real, so the difference also vanishes at `1`.  The `Ã₁`-side support input
of the mixed (8.18.c) application in (12.3). -/
theorem Sset_diff_support_subset_A1 {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    (chi - chi.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (A1 L PeterfalviType.I) L := by
  have := hyp.finiteG
  intro x hx
  rw [ClassFunction.mem_support] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  by_contra hxA1
  apply hx
  rw [ClassFunction.sub_apply, ClassFunction.conj_apply]
  by_cases hxH : (x : G) ∈ hyp.typeI.typeF.H
  · -- inside `H` but not in `A₁ = H^#`: forced `x = 1`, where the difference cancels.
    have hx1 : x = 1 := by
      by_contra hx1
      refine hxA1 ((Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr ?_, fun h => ?_⟩)
      · change (x : G) ∈ maxNilpotentNormalHall L
        rw [← hyp.typeI.typeF.H_eq]
        exact hxH
      · rw [Set.mem_singleton_iff] at h
        exact hx1 (Subtype.ext h)
    subst hx1
    have hreal : star (chi 1) = chi 1 := by
      rw [data.decomp, classFunction_sum_apply, star_sum]
      refine Finset.sum_congr rfl fun φ _ => ?_
      obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
      rw [hd, star_natCast]
    rw [hreal, sub_self]
  · rw [Sset_vanishes_off_H hyp data.chi_mem hxH, star_zero, sub_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `τ`-image of a full-member difference is `Ã₁`-supported** (the (2.11) restriction
computation): `supp((χ−χ̄)^τ) ⊆ Ã₁(L) = ftThickenedSupport L A₁`.  The difference is
`A₁`-supported (`Sset_diff_support_subset_A1`), so `τ` agrees with the `A₁`-restricted Dade map
(`Hypothesis.dadeMap_restrict_apply`), whose image vanishes off the restricted Dade support —
which is exactly the faithful thickened `A₁`-support (the per-point kernels agree,
`ftSupportKernel_restrict`). -/
theorem Sset_diff_tau_support_subset_ftThickenedA1 {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) :
    (hyp.tau (chi - chi.conj)).support ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport L (A1 L PeterfalviType.I) := by
  have := hyp.finiteG
  have hA₁A : A1 L PeterfalviType.I ⊆ typeIA L hyp.typeI :=
    OddOrder.Peterfalvi.S10.A1_subset_typeIA L hyp.typeI
  have hA₁norm : ∀ (l : ↥L) ⦃a : G⦄, a ∈ A1 L PeterfalviType.I →
      (l : G) * a * (l : G)⁻¹ ∈ A1 L PeterfalviType.I := fun l _ ha =>
    OddOrder.Peterfalvi.S10.A1_conj_mem L OddOrder.GroupTheory.PeterfalviType.I l.2 ha
  have hsuppA1 := Sset_diff_support_subset_A1 hyp data
  have hsuppA : (chi - chi.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := fun x hx => hA₁A (hsuppA1 hx)
  -- `τ(χ−χ̄)` is the (A₁-restricted) Dade map value on the A₁-supported difference
  have htau_eq : hyp.tau (chi - chi.conj)
      = (hyp.dadeData.dade.restrict hA₁A hA₁norm).dadeMap (k := ℂ)
          ⟨chi - chi.conj, (ClassFunction.mem_supportedSubmodule).mpr hsuppA1⟩ := by
    rw [OddOrder.Peterfalvi.S04.Hypothesis.dadeMap_restrict_apply]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) hsuppA
  -- the restricted Dade support is the faithful thickened `A₁`-support
  have hsub : (hyp.dadeData.dade.restrict hA₁A hA₁norm).dadeSupport ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport L (A1 L PeterfalviType.I) := by
    intro g hg
    obtain ⟨a, h, hh, hconj⟩ :=
      (hyp.dadeData.dade.restrict hA₁A hA₁norm).mem_dadeSupport_iff.mp hg
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    refine ⟨a.1, a.2, ?_⟩
    rw [OddOrder.GroupTheory.mem_conjClassSet]
    refine ⟨a.1 * h, ⟨h, ?_, rfl⟩, c, hc⟩
    rw [SetLike.mem_coe, OddOrder.Peterfalvi.S10.ftSupportKernel_restrict hA₁A a.2,
      ← hyp.dadeData.H_eq_ftSupportKernel ⟨a.1, hA₁A a.2⟩]
    exact hh
  intro g hg
  rw [ClassFunction.mem_support, htau_eq] at hg
  by_contra hgnot
  refine hg (OddOrder.Peterfalvi.S04.IsDadeMap.map_eq_zero_of_not_mem_dadeSupport
    ((hyp.dadeData.dade.restrict hA₁A hA₁norm).isDadeMap_dadeMap) _ g
    (fun hmem => hgnot (hsub hmem)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The `τ`-image of a constituent difference is `Ã`-supported**:
`supp((φ−φ̄)^τ) ⊆ Ã(L) = ftThickenedSupport L A(L)`.  The difference is `A`-supported
(`constituentDiff_support_subset`), `τ` is the Dade map there, and the (8.15) faithful Dade
support is `Ã(L)` (`dadeSupport_eq_ftThickenedSupport`). -/
theorem constituentDiff_tau_support_subset_ftThickenedA {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    (hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj)).support ⊆
      OddOrder.Peterfalvi.S10.ftThickenedSupport L (typeIA L hyp.typeI) := by
  have := hyp.finiteG
  have hsupp := constituentDiff_support_subset data hφ
  have htau_eq : hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj)
      = hyp.dadeData.dade.dadeMap (k := ℂ)
          ⟨(φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj,
            (ClassFunction.mem_supportedSubmodule).mpr hsupp⟩ :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      hyp.dadeData.dade (hyp.dadeData.dade.fullDadeIsometryData) hsupp
  intro g hg
  rw [ClassFunction.mem_support, htau_eq] at hg
  by_contra hgnot
  refine hg (OddOrder.Peterfalvi.S04.IsDadeMap.map_eq_zero_of_not_mem_dadeSupport
    hyp.dadeData.dade.isDadeMap_dadeMap _ g ?_)
  rw [hyp.dadeData.dadeSupport_eq_ftThickenedSupport]
  exact hgnot

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.18.c), the (12.3) instantiation**: for non-conjugate type-I maximals
`L₁, L₂`, either `Ã(L₁) ∩ Ã₁(L₂) = ∅` or `Ã(L₂) ∩ Ã₁(L₁) = ∅` — the mixed asymmetric
disjointness, from the S10 `ftThickenedSupport_mixed_disjoint_of_nonconjugate` (issue 0096). -/
theorem nonconjugate_thickened_mixed_disjoint_or_swap {L1 L2 : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2) :
    Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (typeIA L1 hyp1.typeI))
        (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (A1 L2 PeterfalviType.I)) ∨
      Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (typeIA L2 hyp2.typeI))
        (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (A1 L1 PeterfalviType.I)) := by
  have := hyp1.finiteG
  have hncTS : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L2 L1 := fun hc =>
    hnot_conj hc.symm
  rcases OddOrder.Peterfalvi.S10.ftThickenedSupport_mixed_disjoint_of_nonconjugate hG
    hyp2.maximal hyp1.maximal hyp2.typeI hyp1.typeI hncTS with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Mixed inner vanishing from the (8.18.c) disjointness**: when `Ã(L₁) ∩ Ã₁(L₂) = ∅`, every
`L₁`-constituent difference image is orthogonal to every `L₂`-full-member difference image.  The
two support computations + disjointly-supported orthogonality. -/
theorem constituent_fullDiff_inner_zero_of_disjoint {L1 L2 : Subgroup G} [Finite G]
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hdisj : Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (typeIA L1 hyp1.typeI))
      (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (A1 L2 PeterfalviType.I)))
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau (chi2 - chi2.conj)) = 0 := by
  have := hyp1.finiteG
  exact ClassFunction.inner_eq_zero_of_disjoint_support
    (Disjoint.mono (constituentDiff_tau_support_subset_ftThickenedA hyp1 data1 hφ1)
      (Sset_diff_tau_support_subset_ftThickenedA1 hyp2 data2) hdisj)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Dade `τ` commutes with complex conjugation on `A(L)`-supported functions** — the
coefficientwise form of `S07.dadeIntegralCharacterMap_mapRingEquiv_comm` (the map's value at a
Dade-support point is an evaluation, and `0` elsewhere, so conjugating coefficients commutes).
The τ/conj commutation input of the (12.3) bar-trick ((5.9.b) via
`CharacterDifferenceImage.nu_eq_mu_conj`). -/
theorem tau_conj_of_supported {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {f : ClassFunction ↥L ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L) :
    hyp.tau f.conj = (hyp.tau f).conj := by
  have := hyp.finiteG
  have h1 : f.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv f := by
    ext g
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  have h2 : (hyp.tau f).conj
      = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (hyp.tau f) := by
    ext g
    rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
    rfl
  rw [h1, h2]
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    hyp.dadeData.dade _ _ hf

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(12.2.b) conjugate pairing of the difference-image block `R₁(φ)`**: `ν_φ = μ̄_φ`, so
`(φ − φ̄)^τ = ε·(μ_φ − μ̄_φ)`.  The (5.9.b) pairing `CharacterDifferenceImage.nu_eq_mu_conj`,
with the τ/conj commutation supplied by `tau_conj_of_supported` on the `A(L)`-supported
difference (`constituentDiff_support_subset`). -/
theorem R1cdi_nu_eq_mu_conj {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    (R1cdi data hφ).nuClassFunction = (R1cdi data hφ).muClassFunction.conj := by
  have := hyp.finiteG
  exact OddOrder.Peterfalvi.S07.CharacterDifferenceImage.nu_eq_mu_conj _
    (tau_conj_of_supported hyp (constituentDiff_support_subset data hφ))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(12.2.b) cross-constituent image orthogonality**: for distinct constituents `φ ≠ φ'` of
one `χ ∈ S`, the images `(φ−φ̄)^τ` and `(φ'−φ̄')^τ` are orthogonal.  The Dade isometry
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`) reduces to the `L`-side pairing
`⟨φ−φ̄, φ'−φ̄'⟩`, where the four irreducibles are pairwise distinct: `φ ≠ φ'` is given,
conjugation is injective, and `φ̄ ≠ φ'`, `φ ≠ φ̄'` are `data.conj_not_mem` — so all four
`Irr L` deltas vanish. -/
theorem constituentDiff_tau_inner_eq_zero_of_ne {L : Subgroup G} [Finite G]
    {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi)
    {φ φ' : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents)
    (hφ' : φ' ∈ data.constituents) (hne : φ ≠ φ') :
    ClassFunction.inner
        (hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj))
        (hyp.tau ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)) = 0 := by
  have := hyp.finiteG
  classical
  -- The two differences form a supported generating family.
  have hSsupp : ∀ s ∈ ({((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj),
      ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)} :
        Set (ClassFunction ↥L ℂ)), s.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    rcases hs with rfl | hs
    · exact constituentDiff_support_subset data hφ
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact constituentDiff_support_subset data hφ'
  -- The Dade isometry transports the pairing to `L`.
  refine Eq.trans (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hSsupp
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))) ?_
  -- `L`-side: expand into four `Irr L` deltas, all off-diagonal.
  have hcross : ∀ a c : IrreducibleCharacter ↥L,
      ClassFunction.inner (a : ClassFunction ↥L ℂ) (c : ClassFunction ↥L ℂ) =
        if a = c then (1 : ℂ) else 0 :=
    fun a c => OddOrder.RepresentationTheory.irreducibleCharacter_inner a c
  have h2 : φ ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ' := by
    intro h
    exact data.conj_not_mem φ' hφ' φ hφ
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h).symm
  have h3 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ ≠ φ' := by
    intro h
    exact data.conj_not_mem φ hφ φ' hφ'
      (congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h)
  have h4 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ
      ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ' := by
    intro h
    have hcf := congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h
    simp only [OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter] at hcf
    exact hne (IrreducibleCharacter.ext
      (by rw [← ClassFunction.conj_conj (φ : ClassFunction ↥L ℂ), hcf,
        ClassFunction.conj_conj]))
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ',
    hcross φ φ', hcross φ _, hcross _ φ', hcross _ _,
    if_neg hne, if_neg h2, if_neg h3, if_neg h4]
  norm_num

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Two-family variant of the constituent-difference block orthogonality.**  Same `L`, but the two
constituents may come from *different* members `χ₁, χ₂ ∈ S`: given `φ ∈ S(χ₁)`, `φ' ∈ S(χ₂)` with
the
distinctness conditions `φ ≠ φ'`, `φ ≠ φ̄'`, `φ̄ ≠ φ'` (a caller supplies these from
`χ₁ ∉ {χ₂, χ̄₂}`
+ disjoint constituents), the Dade images of the signed differences are orthogonal.

Generalizes `constituentDiff_tau_inner_eq_zero_of_ne` (same `χ`, where the conditions come from
`data.conj_not_mem`) — the cross-family input for the same-`L` `R(χ₁) ⊥ R(χ₂)` orthogonality.  The
proof is identical: the supports of both differences lie in `A(L)`
(`constituentDiff_support_subset`,
one per data), the Dade map is an isometry there, and the `L`-side pairing expands into four
off-diagonal `Irr L` deltas. -/
theorem constituentDiff_tau_inner_eq_zero_of_ne_across {L : Subgroup G} [Finite G]
    {hyp : Hypothesis L} {chi1 chi2 : ClassFunction ↥L ℂ}
    (data1 : CharacterDecompositionData hyp chi1) (data2 : CharacterDecompositionData hyp chi2)
    {φ φ' : IrreducibleCharacter ↥L} (hφ : φ ∈ data1.constituents)
    (hφ' : φ' ∈ data2.constituents) (hne : φ ≠ φ')
    (h2 : φ ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ')
    (h3 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ ≠ φ') :
    ClassFunction.inner
        (hyp.tau ((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj))
        (hyp.tau ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)) = 0 := by
  have := hyp.finiteG
  classical
  have hSsupp : ∀ s ∈ ({((φ : ClassFunction ↥L ℂ) - (φ : ClassFunction ↥L ℂ).conj),
      ((φ' : ClassFunction ↥L ℂ) - (φ' : ClassFunction ↥L ℂ).conj)} :
        Set (ClassFunction ↥L ℂ)), s.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro s hs
    rcases hs with rfl | hs
    · exact constituentDiff_support_subset data1 hφ
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact constituentDiff_support_subset data2 hφ'
  refine Eq.trans (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hSsupp
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))) ?_
  have hcross : ∀ a c : IrreducibleCharacter ↥L,
      ClassFunction.inner (a : ClassFunction ↥L ℂ) (c : ClassFunction ↥L ℂ) =
        if a = c then (1 : ℂ) else 0 :=
    fun a c => OddOrder.RepresentationTheory.irreducibleCharacter_inner a c
  have h4 : OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ
      ≠ OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L) φ' := by
    intro h
    have hcf := congrArg (fun c : IrreducibleCharacter ↥L => (c : ClassFunction ↥L ℂ)) h
    simp only [OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter] at hcf
    exact hne (IrreducibleCharacter.ext
      (by rw [← ClassFunction.conj_conj (φ : ClassFunction ↥L ℂ), hcf,
        ClassFunction.conj_conj]))
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ,
    ← OddOrder.Peterfalvi.S07.coe_conjIrreducibleCharacter (L := ↥L) φ',
    hcross φ φ', hcross φ _, hcross _ φ', hcross _ _,
    if_neg hne, if_neg h2, if_neg h3, if_neg h4]
  norm_num

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
open OddOrder.Peterfalvi.S07.CharacterDifferenceImage in
/-- **The (12.3) bar-trick descent, one-sided core.**  If `Ã(L₁) ∩ Ã₁(L₂) = ∅` ((8.18.c)),
each `L₁`-constituent image is orthogonal to each `L₂`-constituent image.

Peterfalvi's (12.3) argument: with `X = (χ₂−χ̄₂)^{τ₂}`, the support disjointness gives
`⟨(φ₁−φ̄₁)^{τ₁}, X⟩ = 0` (`constituent_fullDiff_inner_zero_of_disjoint`); writing
`(φ₁−φ̄₁)^{τ₁} = ε·(μ₁ − μ̄₁)` ((5.9.b), `R1cdi_nu_eq_mu_conj`) and using `X̄ = −X`
(`tau_conj_of_supported`) plus the integrality of the Fourier coefficients of `X ∈ ℤ[Irr G]`
(`mem_ZIrr_inner_int`) yields `⟨μ₁, X⟩ = ⟨μ̄₁, X⟩ = −conj ⟨μ₁, X⟩ = −⟨μ₁, X⟩`, so
`⟨μ₁, X⟩ = 0`.  Expanding `X = ∑_{φ∈S(χ₂)} (φ−φ̄)^{τ₂}`, the cross-`φ` block orthogonality
(`constituentDiff_tau_inner_eq_zero_of_ne` + the (4.1) member lemma) lets `μ₁` pair
nontrivially with at most one block, so every single summand `⟨μ₁, (φ₂−φ̄₂)^{τ₂}⟩` vanishes,
not just the sum — and likewise for `ν₁ = μ̄₁`. -/
theorem constituent_diffImage_inner_zero_of_disjoint {L1 L2 : Subgroup G} [Finite G]
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hdisj : Disjoint (OddOrder.Peterfalvi.S10.ftThickenedSupport L1 (typeIA L1 hyp1.typeI))
      (OddOrder.Peterfalvi.S10.ftThickenedSupport L2 (A1 L2 PeterfalviType.I)))
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2)
    {φ2 : IrreducibleCharacter ↥L2} (hφ2 : φ2 ∈ data2.constituents) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
  have := hyp1.finiteG
  classical
  set X : ClassFunction G ℂ := hyp2.tau (chi2 - chi2.conj) with hX
  -- (a) `χ₂ − χ̄₂ = ∑_{φ∈S(χ₂)} (φ − φ̄)`, hence `X = ∑ (φ−φ̄)^{τ₂}` and `X ∈ ℤ[Irr G]`.
  have hdiff_eq : chi2 - chi2.conj = ∑ φ ∈ data2.constituents,
      ((φ : ClassFunction ↥L2 ℂ) - (φ : ClassFunction ↥L2 ℂ).conj) := by
    have hconj : (∑ φ ∈ data2.constituents, (φ : ClassFunction ↥L2 ℂ)).conj
        = ∑ φ ∈ data2.constituents, (φ : ClassFunction ↥L2 ℂ).conj := by
      ext g
      rw [ClassFunction.conj_apply, classFunction_sum_apply, classFunction_sum_apply, star_sum]
      exact Finset.sum_congr rfl fun φ _ => by rw [ClassFunction.conj_apply]
    conv_lhs => rw [data2.decomp]
    rw [hconj, ← Finset.sum_sub_distrib]
  have hXsum : X = ∑ φ ∈ data2.constituents,
      hyp2.tau ((φ : ClassFunction ↥L2 ℂ) - (φ : ClassFunction ↥L2 ℂ).conj) := by
    rw [hX, hdiff_eq, map_sum]
  have hfsupp : (chi2 - chi2.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp2.ambientA L2 := by
    rw [hdiff_eq]
    intro x hx
    rw [ClassFunction.mem_support, classFunction_sum_apply] at hx
    obtain ⟨φ, hφm, hne0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact constituentDiff_support_subset data2 hφm (ClassFunction.mem_support.mpr hne0)
  have hXZIrr : X ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [hX]
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp2.dadeData.dade hfsupp ?_
    rw [hdiff_eq]
    exact Submodule.sum_mem _ fun φ _ => Submodule.sub_mem _ φ.mem_ZIrr
      (OddOrder.Peterfalvi.S07.conjIrreducibleCharacter (L := ↥L2) φ).mem_ZIrr
  -- (b) `⟨a, X⟩` is real for every irreducible `a` (integer Fourier coefficient).
  have hreal : ∀ a : IrreducibleCharacter G,
      star (ClassFunction.inner (a : ClassFunction G ℂ) X)
        = ClassFunction.inner (a : ClassFunction G ℂ) X := by
    intro a
    obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int a hXZIrr
    rw [OddOrder.RepresentationTheory.inner_conj_symm X (a : ClassFunction G ℂ), hm,
      star_star, star_intCast]
  -- (c) `X̄ = −X` (τ₂ commutes with conjugation on the supported difference).
  have hXconj : X.conj = -X := by
    rw [hX, ← tau_conj_of_supported hyp2 hfsupp, ClassFunction.conj_sub,
      ClassFunction.conj_conj, ← neg_sub, map_neg]
  -- (d) the bar-trick: `⟨μ₁, X⟩ = ⟨ν₁, X⟩ = 0`.
  have hfull : ClassFunction.inner
      (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj)) X = 0 :=
    constituent_fullDiff_inner_zero_of_disjoint hyp1 hyp2 hdisj data1 hφ1 data2
  rw [(R1cdi data1 hφ1).image_eq_signedDifference] at hfull
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.signedDifference,
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.difference] at hfull
  rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_left,
    ClassFunction.inner_sub_left] at hfull
  have hs1 : (((R1cdi data1 hφ1).sign : ℤ) : ℂ) ≠ 0 :=
    Int.cast_ne_zero.mpr (R1cdi data1 hφ1).sign_ne_zero
  have heq : ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X
      = ClassFunction.inner ((R1cdi data1 hφ1).nuClassFunction) X :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfull).resolve_left hs1)
  have hnux : ClassFunction.inner ((R1cdi data1 hφ1).nuClassFunction) X
      = -star (ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X) := by
    rw [R1cdi_nu_eq_mu_conj data1 hφ1]
    conv_lhs => rw [← ClassFunction.conj_conj X]
    rw [OddOrder.RepresentationTheory.inner_conj_conj, hXconj,
      ClassFunction.inner_neg_right, star_neg]
  have hmux : ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X = 0 := by
    have h1 : ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X
        = -(ClassFunction.inner ((R1cdi data1 hφ1).muClassFunction) X) := by
      conv_lhs => rw [heq, hnux, hreal (R1cdi data1 hφ1).mu]
    linear_combination h1 / 2
  have hnux0 : ClassFunction.inner ((R1cdi data1 hφ1).nuClassFunction) X = 0 :=
    heq.symm.trans hmux
  -- (e) descent: an irreducible orthogonal to `X` is orthogonal to the `φ₂`-summand.
  have hcrossG : ∀ a c : IrreducibleCharacter G,
      ClassFunction.inner (a : ClassFunction G ℂ) (c : ClassFunction G ℂ) =
        if a = c then (1 : ℂ) else 0 :=
    fun a c => OddOrder.RepresentationTheory.irreducibleCharacter_inner a c
  have hdescend : ∀ a : IrreducibleCharacter G,
      ClassFunction.inner (a : ClassFunction G ℂ) X = 0 →
      ClassFunction.inner (a : ClassFunction G ℂ)
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
    intro a haX
    by_contra ht2
    -- a nonzero pairing with the block of `φ'` puts `a` in its two-element image set.
    have hmem : ∀ φ' (hm : φ' ∈ data2.constituents),
        ClassFunction.inner (a : ClassFunction G ℂ)
          (hyp2.tau ((φ' : ClassFunction ↥L2 ℂ) - (φ' : ClassFunction ↥L2 ℂ).conj)) ≠ 0 →
        (a : ClassFunction G ℂ) ∈ (R1cdi data2 hm).imageSet := by
      intro φ' hm hne0
      rw [(R1cdi data2 hm).image_eq_signedDifference] at hne0
      simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.signedDifference,
        OddOrder.Peterfalvi.S07.CharacterDifferenceImage.difference] at hne0
      rw [← Int.cast_smul_eq_zsmul ℂ, OddOrder.RepresentationTheory.inner_smul_right,
        ClassFunction.inner_sub_right] at hne0
      have hsub : ClassFunction.inner (a : ClassFunction G ℂ)
            ((R1cdi data2 hm).muClassFunction)
          - ClassFunction.inner (a : ClassFunction G ℂ)
            ((R1cdi data2 hm).nuClassFunction) ≠ 0 :=
        fun h => hne0 (by rw [h, mul_zero])
      rw [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.mem_imageSet_iff]
      by_cases hc1 : a = (R1cdi data2 hm).mu
      · exact Or.inl (congrArg (fun c : IrreducibleCharacter G =>
          (c : ClassFunction G ℂ)) hc1)
      by_cases hc2 : a = (R1cdi data2 hm).nu
      · exact Or.inr (congrArg (fun c : IrreducibleCharacter G =>
          (c : ClassFunction G ℂ)) hc2)
      exfalso
      exact hsub (by rw [hcrossG a _, hcrossG a _, if_neg hc1, if_neg hc2, sub_zero])
    have hmem2 := hmem φ2 hφ2 ht2
    have hothers : ∀ φ' ∈ data2.constituents, φ' ≠ φ2 →
        ClassFunction.inner (a : ClassFunction G ℂ)
          (hyp2.tau ((φ' : ClassFunction ↥L2 ℂ) - (φ' : ClassFunction ↥L2 ℂ).conj)) = 0 := by
      intro φ' hm' hne'
      by_contra htne'
      have hmem' := hmem φ' hm' htne'
      have hsd : ClassFunction.inner ((R1cdi data2 hm').signedDifference)
          ((R1cdi data2 hφ2).signedDifference) = 0 := by
        rw [← (R1cdi data2 hm').image_eq_signedDifference,
          ← (R1cdi data2 hφ2).image_eq_signedDifference]
        exact constituentDiff_tau_inner_eq_zero_of_ne data2 hm' hφ2 hne'
      have hcontra := inner_eq_zero_of_signedDifference_inner_zero_of_mem
        (R1cdi data2 hm') (R1cdi data2 hφ2) hsd hmem' hmem2
      rw [hcrossG a a, if_pos rfl] at hcontra
      exact one_ne_zero hcontra
    have hsum0 : ∑ φ' ∈ data2.constituents,
        ClassFunction.inner (a : ClassFunction G ℂ)
          (hyp2.tau ((φ' : ClassFunction ↥L2 ℂ) - (φ' : ClassFunction ↥L2 ℂ).conj)) = 0 := by
      rw [← OddOrder.RepresentationTheory.inner_sum_right, ← hXsum]
      exact haX
    rw [Finset.sum_eq_single_of_mem φ2 hφ2 hothers] at hsum0
    exact ht2 hsum0
  -- (f) conclude: expand `(φ₁−φ̄₁)^{τ₁} = ε·(μ₁ − ν₁)` and apply the two descents.
  rw [(R1cdi data1 hφ1).image_eq_signedDifference]
  simp only [OddOrder.Peterfalvi.S07.CharacterDifferenceImage.signedDifference,
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage.difference]
  rw [← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_left,
    ClassFunction.inner_sub_left, hdescend (R1cdi data1 hφ1).mu hmux,
    hdescend (R1cdi data1 hφ1).nu hnux0, sub_zero, mul_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (8.18.c) difference-image orthogonality** (the geometric obligation of (12.3)).
For non-conjugate type-I maximals `L1, L2` and constituents `φ_i`, the Dade difference images
`τ_i(φ_i − φ̄_i)` are orthogonal.

**Genuine proof** (2026-07-03, loop¹⁰⁰): the mixed asymmetric `Ã(L₁) ∩ Ã₁(L₂) = ∅ ∨ swap` is
`nonconjugate_thickened_mixed_disjoint_or_swap` (S10 (8.18.c), three §16 pins); on the
disjoint side the bar-trick descent `constituent_diffImage_inner_zero_of_disjoint` closes the
per-constituent orthogonality, and the swap side follows by conjugate symmetry of the inner
product.  Hub issue 9003 Cluster B. -/
theorem nonconjugate_diffImage_inner_zero {L1 L2 : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {φ1 : IrreducibleCharacter ↥L1} (hφ1 : φ1 ∈ data1.constituents)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2)
    {φ2 : IrreducibleCharacter ↥L2} (hφ2 : φ2 ∈ data2.constituents) :
    ClassFunction.inner
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj))
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj)) = 0 := by
  have := hyp1.finiteG
  rcases nonconjugate_thickened_mixed_disjoint_or_swap hG hyp1 hyp2 hnot_conj with h | h
  · exact constituent_diffImage_inner_zero_of_disjoint hyp1 hyp2 h data1 hφ1 data2 hφ2
  · have hswap := constituent_diffImage_inner_zero_of_disjoint hyp2 hyp1 h data2 hφ2 data1 hφ1
    rw [OddOrder.RepresentationTheory.inner_conj_symm
        (hyp2.tau ((φ2 : ClassFunction ↥L2 ℂ) - (φ2 : ClassFunction ↥L2 ℂ).conj))
        (hyp1.tau ((φ1 : ClassFunction ↥L1 ℂ) - (φ1 : ClassFunction ↥L1 ℂ).conj)),
      hswap, star_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.3)**: for non-conjugate type-I maximal subgroups `L₁, L₂`, the families
`R(χ₁) = Rset data1` and `R(χ₂) = Rset data2` are mutually orthogonal.

Proof: a member `α ∈ R(χ₁)` lies in `R₁(φ₁) = (R1cdi data1 hφ₁).toOrthonormalImage` for some
constituent `φ₁`, and likewise `β ∈ R₁(φ₂)`.  The cross-`L` (4.1) orthogonality
`toOrthonormalImage_inner_eq_zero_across` reduces `⟨α, β⟩ = 0` to the orthogonality of the signed
differences `⟨(φ₁−φ̄₁)^{τ₁}, (φ₂−φ̄₂)^{τ₂}⟩ = 0` (`image_eq_signedDifference`), which is the
geometric
obligation `nonconjugate_diffImage_inner_zero` ((8.18.c): the supports lie in disjoint `Ã(L₁)`,
`Ã₁(L₂)`). -/
theorem nonconjugate_typeI_R_orthogonal {L1 L2 : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp1 : Hypothesis L1) (hyp2 : Hypothesis L2)
    (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L1 = L2)
    {chi1 : ClassFunction ↥L1 ℂ} (data1 : CharacterDecompositionData hyp1 chi1)
    {chi2 : ClassFunction ↥L2 ℂ} (data2 : CharacterDecompositionData hyp2 chi2) :
    ∀ α ∈ Rset data1, ∀ β ∈ Rset data2, ClassFunction.inner α β = 0 := by
  intro α hαm β hβm
  obtain ⟨φ1, hφ1, hα⟩ := hαm
  obtain ⟨φ2, hφ2, hβ⟩ := hβm
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across
    (R1cdi data1 hφ1) (R1cdi data2 hφ2) ?_ hα hβ
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference
        (R1cdi data1 hφ1),
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference (R1cdi data2 hφ2)]
  exact nonconjugate_diffImage_inner_zero hG hyp1 hyp2 hnot_conj data1 hφ1 data2 hφ2

/-- **Difference-uniqueness for signed irreducible-character differences** (Peterfalvi §3, the
reconciliation core of (1.4)).  If two *signed* differences of distinct irreducible characters
coincide, `s • (a − b) = t • (c − d)` with `a ≠ b`, `c ≠ d` and a nonzero left scalar `s`, then the
unordered pairs agree, with the sign tracking the orientation: either `a = c, b = d, s = t`
(same orientation) or `a = d, b = c, s = −t` (reversed).

This is the lemma by which the per-constituent families `R₁(φ)` (built from `τ(φ̄ − φ)`) are
reconciled with the global signed family of (1.4) in pin (a) `constituent_diff_tau_mem_span`:
the two presentations of `τ(φ − φ̄)` as a signed difference must share their underlying irreducible
pair, so each `μ_φ` lands in `ℤ[R(χ)]`.

Proof: pairing the hypothesis on the *left* with the irreducible `a` (resp. `b`) and using
orthonormality `⟨χ, ψ⟩ = δ_{χ,ψ}` (`irreducibleCharacter_inner_eq_ite`; `ClassFunction.inner` is
ℂ-linear in the left slot) gives `s = t·([c=a] − [d=a])` and `−s = t·([c=b] − [d=b])`.  Since
`s ≠ 0`, exactly one of `c = a`, `d = a` holds (the two cases are the two orientations), and the
`b`-pairing pins the remaining equality. -/
theorem irreducibleCharacter_signed_difference_uniqueness [Finite G]
    {a b c d : IrreducibleCharacter G} (hab : a ≠ b) (hcd : c ≠ d)
    {s t : ℂ} (hs : s ≠ 0)
    (h : s • ((a : ClassFunction G ℂ) - (b : ClassFunction G ℂ))
        = t • ((c : ClassFunction G ℂ) - (d : ClassFunction G ℂ))) :
    (a = c ∧ b = d ∧ s = t) ∨ (a = d ∧ b = c ∧ s = -t) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hba : b ≠ a := fun he => hab he.symm
  -- Pair the equation on the left with an arbitrary irreducible `e`; orthonormality turns each
  -- coercion-inner into a Kronecker delta.
  have key : ∀ e : IrreducibleCharacter G,
      s * ((if a = e then (1 : ℂ) else 0) - (if b = e then 1 else 0))
        = t * ((if c = e then (1 : ℂ) else 0) - (if d = e then 1 else 0)) := by
    intro e
    have h2 := congrArg (fun f => ClassFunction.inner f (e : ClassFunction G ℂ)) h
    simpa only [ClassFunction.inner_smul_left, ClassFunction.inner_sub_left,
      irreducibleCharacter_inner_eq_ite] using h2
  -- Evaluate at `a`: `s = t·([c=a] − [d=a])`.
  have ka : s = t * ((if c = a then (1 : ℂ) else 0) - (if d = a then 1 else 0)) := by
    have hka := key a
    rwa [if_pos rfl, if_neg hba, sub_zero, mul_one] at hka
  -- Evaluate at `b`: `−s = t·([c=b] − [d=b])`.
  have kb : -s = t * ((if c = b then (1 : ℂ) else 0) - (if d = b then 1 else 0)) := by
    have hkb := key b
    rwa [if_neg hab, if_pos rfl, zero_sub, mul_neg_one] at hkb
  by_cases hca : c = a
  · -- Orientation A: `c = a`, hence `d ≠ a`, and `ka` collapses to `s = t`.
    have hda : d ≠ a := fun he => hcd (hca.trans he.symm)
    rw [if_pos hca, if_neg hda, sub_zero, mul_one] at ka
    have hcb : c ≠ b := fun he => hab (hca.symm.trans he)
    rw [if_neg hcb, zero_sub, mul_neg] at kb
    by_cases hdb : d = b
    · exact Or.inl ⟨hca.symm, hdb.symm, ka⟩
    · rw [if_neg hdb, mul_zero, neg_zero] at kb
      exact absurd (neg_eq_zero.mp kb) hs
  · by_cases hda : d = a
    · -- Orientation B: `c ≠ a`, `d = a`, and `ka` collapses to `s = −t`.
      rw [if_neg hca, if_pos hda, zero_sub, mul_neg_one] at ka
      have hdb : d ≠ b := fun he => hab (hda.symm.trans he)
      rw [if_neg hdb, sub_zero] at kb
      by_cases hcb : c = b
      · exact Or.inr ⟨hda.symm, hcb.symm, ka⟩
      · rw [if_neg hcb, mul_zero] at kb
        exact absurd (neg_eq_zero.mp kb) hs
    · -- Neither: `ka` forces `s = 0`, contradiction.
      rw [if_neg hca, if_neg hda, sub_zero, mul_zero] at ka
      exact absurd ka hs

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (a), piece 3** (span membership): the two underlying irreducibles
`μ_φ, ν_φ` of the difference image `R1cdi data hφ` lie in `ℤ[R(χ)]`.  The orthonormal block
`R₁(φ).imageSet = {ε·μ_φ, −ε·ν_φ} ⊆ R(χ)` with `ε = ±1`, so `μ_φ = ε·(ε·μ_φ)` and
`ν_φ = (−ε)·(−ε·ν_φ)` are integer multiples of `R(χ)` members. -/
theorem R1cdi_muNu_mem_span_Rset {L : Subgroup G} [Finite G] {hyp : Hypothesis L}
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents) :
    (R1cdi data hφ).muClassFunction ∈ Submodule.span ℤ (Rset data) ∧
      (R1cdi data hφ).nuClassFunction ∈ Submodule.span ℤ (Rset data) := by
  have := hyp.finiteG
  classical
  have himg : (R1 data hφ).imageSet
      = ({(R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction,
          (-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction} :
            Finset (ClassFunction G ℂ)) := rfl
  have hsq : (R1cdi data hφ).sign * (R1cdi data hφ).sign = 1 := (R1cdi data hφ).sign_mul_self
  have hμRset : (R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction ∈ Rset data :=
    ⟨φ, hφ, by rw [himg]; exact Finset.mem_insert_self _ _⟩
  have hνRset : (-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction ∈ Rset data :=
    ⟨φ, hφ, by rw [himg]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  refine ⟨?_, ?_⟩
  · have hμ : (R1cdi data hφ).muClassFunction
        = (R1cdi data hφ).sign • ((R1cdi data hφ).sign • (R1cdi data hφ).muClassFunction) := by
      rw [smul_smul, hsq, one_smul]
    rw [hμ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hμRset)
  · have hν : (R1cdi data hφ).nuClassFunction
        = (-(R1cdi data hφ).sign) •
          ((-(R1cdi data hφ).sign) • (R1cdi data hφ).nuClassFunction) := by
      rw [smul_smul, neg_mul_neg, hsq, one_smul]
    rw [hν]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hνRset)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (a), piece 1** (global (1.4) coherence): the constituent set `S(χ)`
together with its complex conjugates forms a single coherent family under the Dade isometry `τ`.
There is a uniform sign `ε = ±1` and an injection `μ` of the conjugate-closed set
`T = S(χ) ∪ S(χ)‾` into `Irr G` with `τ(α − β) = ε·(μ α − μ β)` for all `α, β ∈ T`.

This is the §3 (1.4) keystone `isometry_difference_pair_structure` applied to the constant-degree
family `T` (every member supported in `A(L) ∪ {1}`, so member differences are `A(L)`-supported and
the three Dade-isometry hypotheses hold by `dadeIntegralCharacterMap_{mem_ZIrr_of_supported,
apply_one_eq_zero,inner_eq_on_supported_span}`). -/
theorem exists_uniform_image_of_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi) :
    ∃ (ε : ℤ) (μ : IrreducibleCharacter ↥L → IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
      Set.InjOn μ ↑(data.constituents ∪
          data.constituents.image (IrreducibleCharacter.conjPerm ↥L)) ∧
      ∀ α ∈ data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L),
        ∀ β ∈ data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L),
          hyp.tau ((α : ClassFunction ↥L ℂ) - (β : ClassFunction ↥L ℂ))
            = ε • ((μ α : ClassFunction G ℂ) - (μ β : ClassFunction G ℂ)) := by
  have := hyp.finiteG
  classical
  set T := data.constituents ∪ data.constituents.image (IrreducibleCharacter.conjPerm ↥L) with hTdef
  obtain ⟨φref, hφref⟩ := data.constituents_nonempty
  -- (1) every member of `T` is supported in `A(L) ∪ {1}`.
  have hTsupp : ∀ x ∈ T, (x : ClassFunction ↥L ℂ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1} := by
    intro x hx
    rw [hTdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact data.supported x hx
    · rw [Finset.mem_image] at hx
      obtain ⟨φ, hφ, rfl⟩ := hx
      rw [IrreducibleCharacter.conjPerm_apply_coe]
      have hconjsupp : (φ : ClassFunction ↥L ℂ).conj.support
          = (φ : ClassFunction ↥L ℂ).support := by
        ext y; simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
      rw [hconjsupp]; exact data.supported φ hφ
  -- (2) every member of `T` has the reference degree `φref(1)`.
  have hTdeg : ∀ x ∈ T, ((x : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((φref : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro x hx
    rw [hTdef, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact data.equal_degree x hx φref hφref
    · rw [Finset.mem_image] at hx
      obtain ⟨φ, hφ, rfl⟩ := hx
      rw [IrreducibleCharacter.conjPerm_apply_coe]
      obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
      rw [ClassFunction.conj_apply, hd, star_natCast, ← hd]
      exact data.equal_degree φ hφ φref hφref
  -- (3) enumerate `T` as a `Fin n` family.
  set n := T.card with hndef
  have hφrefT : φref ∈ T := Finset.mem_union_left _ hφref
  have hconjrefT : IrreducibleCharacter.conjPerm ↥L φref ∈ T :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hφref)
  have hrefne : φref ≠ IrreducibleCharacter.conjPerm ↥L φref := fun hcon =>
    data.not_real φref hφref ((IrreducibleCharacter.conjPerm_eq_self_iff φref).mp hcon.symm)
  have hn2 : 2 ≤ n := Finset.one_lt_card.mpr ⟨φref, hφrefT, _, hconjrefT, hrefne⟩
  have : NeZero n := ⟨by omega⟩
  set fam : Fin n → IrreducibleCharacter ↥L :=
    fun i => (T.equivFin.symm i : IrreducibleCharacter ↥L)
    with hfamdef
  have hfam_mem : ∀ i, fam i ∈ T := fun i => (T.equivFin.symm i).2
  have hfam_inj : Function.Injective fam :=
    fun i j h => T.equivFin.symm.injective (Subtype.ext h)
  -- (4) each member difference `fam i − fam 0` is `A(L)`-supported.
  have hdiff_supp : ∀ i, (irreducibleCharacterDifference fam i).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    intro i y hy
    have hne1 : y ≠ 1 := by
      rintro rfl
      refine (ClassFunction.mem_support.mp hy) ?_
      change (fam i : ClassFunction ↥L ℂ) 1 - (fam 0 : ClassFunction ↥L ℂ) 1 = 0
      rw [hTdeg (fam i) (hfam_mem i), hTdeg (fam 0) (hfam_mem 0), sub_self]
    rcases ClassFunction.support_sub_subset _ _ hy with h | h
    · rcases hTsupp _ (hfam_mem i) h with h2 | h2
      · exact h2
      · exact absurd (Set.mem_singleton_iff.mp h2) hne1
    · rcases hTsupp _ (hfam_mem 0) h with h2 | h2
      · exact h2
      · exact absurd (Set.mem_singleton_iff.mp h2) hne1
  have hSsupp : ∀ s ∈ Set.range (irreducibleCharacterDifference fam),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
    rintro s ⟨i, rfl⟩; exact hdiff_supp i
  -- (5) the three (1.4) hypotheses for the Dade isometry, via the supported-span lemmas.
  have hsame_deg : ∀ i, ((fam i : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
      = ((fam 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := fun i =>
    (hTdeg (fam i) (hfam_mem i)).trans (hTdeg (fam 0) (hfam_mem 0)).symm
  have hvirtual : IsometryDifferenceImagesAreVirtual hyp.tau fam := by
    intro i
    change hyp.tau (irreducibleCharacterDifference fam i) ∈ ZIrr G
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade (hdiff_supp i)
      (Submodule.sub_mem _ (fam i).mem_ZIrr (fam 0).mem_ZIrr)
  have hzero : IsometryDifferenceImagesVanishAtOne hyp.tau fam := by
    intro i
    change hyp.tau (irreducibleCharacterDifference fam i) (1 : G) = 0
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
      hyp.dadeData.dade (hdiff_supp i)
  have hisom : ∀ i j, ClassFunction.inner (isometryDifferenceImage hyp.tau fam i)
      (isometryDifferenceImage hyp.tau fam j)
      = ClassFunction.inner (irreducibleCharacterDifference fam i)
          (irreducibleCharacterDifference fam j) := by
    intro i j
    change ClassFunction.inner (hyp.tau (irreducibleCharacterDifference fam i))
      (hyp.tau (irreducibleCharacterDifference fam j)) = _
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hSsupp (Submodule.subset_span ⟨i, rfl⟩)
      (Submodule.subset_span ⟨j, rfl⟩)
  -- (6) apply the (1.4) keystone.
  obtain ⟨sdf, himage⟩ :=
    isometry_difference_pair_structure hn2 fam hfam_inj hsame_deg hyp.tau hvirtual hzero hisom
  -- (7) read off `ε` and `μ`.
  refine ⟨sdf.sign, fun x => if hx : x ∈ T then sdf.mu (T.equivFin ⟨x, hx⟩) else sdf.mu 0,
    sdf.sign_eq, ?_, ?_⟩
  · -- InjOn
    intro x hx y hy hxy
    have hxT : x ∈ T := Finset.mem_coe.mp hx
    have hyT : y ∈ T := Finset.mem_coe.mp hy
    simp only [dif_pos hxT, dif_pos hyT] at hxy
    exact Subtype.ext_iff.mp (T.equivFin.injective (sdf.injective hxy))
  · -- the pair relation
    intro α hα β hβ
    have hαT : α ∈ T := hα
    have hβT : β ∈ T := hβ
    -- key: for `x ∈ T`, `τ(x − fam 0) = ε·(μ x − μ₀)`.
    have key : ∀ x (hx : x ∈ T), hyp.tau ((x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ))
        = sdf.sign • ((sdf.mu (T.equivFin ⟨x, hx⟩) : ClassFunction G ℂ)
            - (sdf.mu 0 : ClassFunction G ℂ)) := by
      intro x hx
      have hfx : fam (T.equivFin ⟨x, hx⟩) = x := by
        simp only [hfamdef, Equiv.symm_apply_apply]
      have hLHS : (x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
          = irreducibleCharacterDifference fam (T.equivFin ⟨x, hx⟩) := by
        change (x : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
          = (fam (T.equivFin ⟨x, hx⟩) : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)
        rw [hfx]
      rw [hLHS]
      change isometryDifferenceImage hyp.tau fam (T.equivFin ⟨x, hx⟩) = _
      rw [himage (T.equivFin ⟨x, hx⟩),
        SignedIrreducibleDifferenceFamily.signedDifference_apply,
        SignedIrreducibleDifferenceFamily.difference_apply,
        SignedIrreducibleDifferenceFamily.classFunction_apply,
        SignedIrreducibleDifferenceFamily.classFunction_apply]
    have hsub : (α : ClassFunction ↥L ℂ) - (β : ClassFunction ↥L ℂ)
        = ((α : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ))
          - ((β : ClassFunction ↥L ℂ) - (fam 0 : ClassFunction ↥L ℂ)) := by abel
    rw [hsub, map_sub, key α hαT, key β hβT, ← smul_sub]
    congr 1
    simp only [dif_pos hαT, dif_pos hβT]
    abel

end OddOrder.Peterfalvi.S14


