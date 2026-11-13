-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_NuRowPin
-- name    : OddOrder_Peterfalvi_S15_NuRowPin
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:45:15.438217+00:00
-- url     : https://prove2.me/theorems/9efe337f-e472-4f34-9351-a1db426d7833
-- title:
--   Peterfalvi (13.3.c) at $T$: the $\nu$-row pin machinery
-- statement:
--   The $T$-side mirror of the $\mu$-column pin machinery: $\nu$-row degree and inner-product facts for a (9.11)-coherent extension of the honest $T$-instance family.
--
--   Main declarations: `Hypothesis.nuRow_apply_one` (ν-row degree); `Hypothesis.nuRow_inner` (ν-row self/cross inner product); `Hypothesis.nuRow_not_irreducible` (A ν-row sum is not irreducible); `Hypothesis.nuRow_diff_supported` (ν-row differences are `A(T)`-supported).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_NuRowPin.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_NuRowPin.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherenceT

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **ν-row degree** (Peterfalvi (13.3.a)-at-`T`, case-agnostic): `(∑_j ν_{ij})(1) = p·v` for
`i ≠ 0`.  Each per-entry `ν_{ij}(1) = v` (`nu_apply_one_eq_v`).  Mirror of
`muColumn_apply_one`. -/
theorem Hypothesis.nuRow_apply_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (i : Fin hyp.q) (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    ((∑ j : Fin hyp.p, hyp.nu i j : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1
      = (hyp.p : ℂ) * (hyp.v : ℂ) := by
  rw [ClassFunction.finset_sum_apply,
    Finset.sum_congr rfl (fun j _ => hyp.nu_apply_one_eq_v hG pins i j hi),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open scoped FiniteInduce in
/-- **ν-row self/cross inner product**: `⟨∑_j ν_{rj}, ∑_j ν_{sj}⟩ = p·[r = s]`, from the
full-grid orthonormality `nu_orthonormal`.  Mirror of `muColumn_inner`. -/
theorem Hypothesis.nuRow_inner [Finite G] (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (r s : Fin hyp.q) :
    ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu r j) (∑ j : Fin hyp.p, hyp.nu s j)
      = if r = s then (hyp.p : ℂ) else 0 := by
  have := hyp.finiteG
  by_cases hrs : r = s
  · subst hrs; rw [if_pos rfl, OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ j : Fin hyp.p, ClassFunction.inner (hyp.nu r j) (∑ j' : Fin hyp.p, hyp.nu r j')
        = ∑ _j : Fin hyp.p, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right,
            Finset.sum_congr rfl (fun j' _ => pins.nu_orthonormal r r j j')]
          simp
      _ = (hyp.p : ℂ) := by simp
  · rw [if_neg hrs, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun j' _ => by
      rw [pins.nu_orthonormal r s j j', if_neg (fun h => hrs h.1)]

open scoped FiniteInduce in
/-- **A ν-row sum is not irreducible**: `⟨ν_i, ν_i⟩ = p ≠ 1`, while irreducible characters have
norm `1`.  Mirror of `muColumn_not_irreducible`. -/
theorem Hypothesis.nuRow_not_irreducible [Finite G] (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (i : Fin hyp.q) :
    ¬ IsIrreducibleCharacter (∑ j : Fin hyp.p, hyp.nu i j) := by
  have := hyp.finiteG
  intro hirr
  have h1 := hirr.inner_self_eq_one
  rw [hyp.nuRow_inner pins i i, if_pos rfl] at h1
  have : hyp.p = 1 := by exact_mod_cast h1
  exact absurd (this ▸ hyp.p_prime) Nat.not_prime_one

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **ν-row differences are `A(T)`-supported** (case-agnostic, arbitrary rows; mirror of
`muColumn_diff_supported`).  Both rows have degree `p·v` (`nuRow_apply_one`), so `ν_r − ν_s`
vanishes at `1`; each row lies in `𝒯` (`nu_rowSum_mem_sOf_H0_T` + `sOf_subset_sSet`) whose
members are supported on `A(T) ∪ {1}` (`sSet_member_support_subset_T`), so the difference
avoids `{1}` and lands in `A(T)`. -/
theorem Hypothesis.nuRow_diff_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    {r s : Fin hyp.q} (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) :
    ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  intro z hz
  have hz0 : ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j)) z ≠ 0 := hz
  have hxmem : (∑ j : Fin hyp.p, hyp.nu r j) ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sOf_subset_sSet _ chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief r hr)
  have hymem : (∑ j : Fin hyp.p, hyp.nu s j) ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sOf_subset_sSet _ chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief s hs)
  have hdeg : ((∑ j : Fin hyp.p, hyp.nu r j : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1
      = ((∑ j : Fin hyp.p, hyp.nu s j : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1 := by
    rw [hyp.nuRow_apply_one hG pins r hr, hyp.nuRow_apply_one hG pins s hs]
  rcases ClassFunction.support_sub_subset _ _ hz with h | h
  · rcases hyp.sSet_member_support_subset_T hG hvd hxmem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSet_member_support_subset_T hG hvd hymem h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁` row-difference identity, coherence-generic** (the (13.3.c)-at-`T` row-independence;
mirror of `coherentIndS_muColumn_diff`): *any* coherent extension `c` of `𝒯 = sSet(setupT)` on
`Ind_T^G` sends the reducible row difference to the aligned `η`-row difference,
`c(∑_j ν_{rj}) − c(∑_j ν_{sj}) = (∑_j η_{rj}) − (∑_j η_{sj})`, for distinct nonzero `r ≠ s`.
`c` agrees with `Ind_T^G` on the `A(T)`-supported row difference (`extends_on_supported`),
which is the honest `A₀(T)`-Dade image (`tInstance_dade0_eq_induce`), evaluated per-column by
the prime-`TI` cross-relation `tauT_nu_cross`. -/
theorem Hypothesis.coherentIndT_nuRow_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))
    {r s : Fin hyp.q} (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩)
    (hrs : r ≠ s) :
    c.extension (∑ j : Fin hyp.p, hyp.nu r j) - c.extension (∑ j : Fin hyp.p, hyp.nu s j)
      = (∑ j : Fin hyp.p, hyp.eta r j) - (∑ j : Fin hyp.p, hyp.eta s j) := by
  classical
  have := hyp.finiteG
  have hAsupp := hyp.nuRow_diff_supported hG pins hvd chief hr hs
  have hmemSpan : ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j)) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) :=
    ⟨Submodule.sub_mem _
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0
        (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief r hr)))
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0
        (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief s hs))),
      hAsupp⟩
  have hA0supp := hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
    (S10.typePACore_subset_A0Set Tdata))
  rw [← map_sub, c.extends_on_supported _ hmemSpan, hyp.indT_apply,
    ← hyp.tInstance_dade0_eq_induce hG hnoV hTP Tdata hA0supp,
    show ((∑ j : Fin hyp.p, hyp.nu r j) - (∑ j : Fin hyp.p, hyp.nu s j))
      = ∑ j : Fin hyp.p, (hyp.nu r j - hyp.nu s j) from by rw [Finset.sum_sub_distrib],
    map_sum, Finset.sum_congr rfl (fun j _ =>
      tauT_nu_cross hG hnoV hyp pins hTP Tdata hU hW1 hW2 j hr hs hrs),
    Finset.sum_sub_distrib]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.3.b)-at-`T`, coherent images are orthogonal to the shared `η`-grid**
(mirror of `coherentIndS_image_inner_eta_eq_zero`, family-generic; issue 2035 #41 step 5's
`(5.3.b)-T` input).

For a conjugate-closed no-real family `𝒮` of characters of the type-`P₂` maximal `T` whose
conjugate differences are `A(T) = S10.typePACore T`-supported, and a coherence
`coh : IsCoherent (Ind_T^G) 𝒮 A(T)` of the induction map `τ = Ind_T^G` (`hyp.indT`), every
coherent image `coh.extension ζ` (`ζ ∈ 𝒮` irreducible) is orthogonal to the entire `η`-grid.
The coherent conjugate difference agrees with the `A₀(T)`-Dade image
(`tInstance_dade0_eq_induce`), which vanishes on the saturated regular set `Ŵ^G`
(`dadeT0_apply_eq_zero_of_regular`); the (3.7)–(3.8) norm-two engine
`eta_orthogonal_of_norm_one_pair_vanish` finishes. -/
theorem coherentIndT_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {S : Set (ClassFunction ↥hyp.T ℂ)}
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hnoReal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hsupp : ∀ ζ ∈ S, (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))
    {ζ : ClassFunction ↥hyp.T ℂ} (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.q) (j : Fin hyp.p),
      ClassFunction.inner (coh.extension ζ) (hyp.eta i j) = 0 := by
  have := hyp.finiteG
  have hζc : ζ.conj ∈ S := hconj hζ
  -- `ζ − ζ̄` lies in the `A(T)`-supported span of `𝒮`.
  have hdiffSpan : ζ - ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.T) S :=
    Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζc)
  have hdiffSupp := hsupp ζ hζ
  have hdiffSupported : ζ - ζ.conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T) S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) :=
    ⟨hdiffSpan, hdiffSupp⟩
  -- `A(T) ⊆ A₀(T)`, so the difference is also `A₀(T)`-supported (the `dadeHypT0` support).
  have hA0Supp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.T Tdata) hyp.T :=
    hdiffSupp.trans
      (OddOrder.Peterfalvi.S04.supportInSubgroup_mono (S10.typePACore_subset_A0Set Tdata))
  -- `τ = Ind_T^G` equals the `A₀(T)`-Dade image on the `A₀(T)`-supported difference.
  have hmaps : hyp.indT (ζ - ζ.conj) =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
        ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData) (ζ - ζ.conj) := by
    rw [hyp.indT_apply]
    exact (hyp.tInstance_dade0_eq_induce hG hnoV hTP Tdata hA0Supp).symm
  -- the coherent conjugate difference agrees with that Dade image.
  have hextDiff : coh.extension ζ - coh.extension ζ.conj =
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
        ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData) (ζ - ζ.conj) := by
    rw [← hmaps, ← coh.extends_on_supported (ζ - ζ.conj) hdiffSupported, map_sub]
  -- the crux: the difference vanishes on the saturated regular set.
  have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (coh.extension ζ - coh.extension ζ.conj) x = 0 := by
    intro x hx
    rw [hextDiff]
    exact hyp.dadeT0_apply_eq_zero_of_regular hG hTP Tdata hW1 hW2 hdiffSupp hx
  -- the straightforward `dirr`-input norms.
  have hpsiZ : coh.extension ζ ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ (Submodule.subset_span hζ)
  have hconjZ : coh.extension ζ.conj ∈ ZIrr G :=
    coh.extension_mem_ZIrr ζ.conj (Submodule.subset_span hζc)
  have hpsi1 : ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 := by
    rw [coh.extension_inner_eq ζ ζ (Submodule.subset_span hζ) (Submodule.subset_span hζ)]
    exact hζirr.inner_self_eq_one
  have hconj1 : ClassFunction.inner (coh.extension ζ.conj) (coh.extension ζ.conj) = 1 := by
    rw [coh.extension_inner_eq ζ.conj ζ.conj (Submodule.subset_span hζc)
      (Submodule.subset_span hζc)]
    exact hζirr.conj.inner_self_eq_one
  have hcross : ClassFunction.inner (coh.extension ζ) (coh.extension ζ.conj) = 0 := by
    rw [coh.extension_inner_eq ζ ζ.conj (Submodule.subset_span hζ)
      (Submodule.subset_span hζc), OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj,
      if_neg (fun h => hnoReal hζ h.symm)]
  intro i j
  have h := OddOrder.Peterfalvi.S16.eta_orthogonal_of_norm_one_pair_vanish hyp
    hpsiZ hconjZ hpsi1 hconj1 hcross hvanish i j
  rw [OddOrder.RepresentationTheory.inner_conj_symm, star_eq_zero]
  exact h

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The coherent image of an irreducible `𝒯`-member vanishes on the saturated regular set**
(mirror of `coherentIndS_extension_irr_vanish_regular`; Coq `ortho_cycTIiso_vanish` at `T`):
`c(ξ)` is orthogonal to the whole `η`-grid (`coherentIndT_image_inner_eta_eq_zero`), and the
grid is complete on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` ((3.2.d)
`vanish_of_inner_eta_eq_zero`); conjugacy-invariance of class functions saturates the vanishing
to `Ŵ^G`. -/
theorem Hypothesis.coherentIndT_extension_irr_vanish_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))
    {ξ : ClassFunction ↥hyp.T ℂ} (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hξirr : IsIrreducibleCharacter ξ)
    {x : G} (hx : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))) :
    c.extension ξ x = 0 := by
  classical
  have := hyp.finiteG
  have hcrux := coherentIndT_image_inner_eta_eq_zero hG hnoV hyp hTP Tdata hW1 hW2
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd))
    (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG))
    (fun ζ hζ => by
      rw [show ζ - ζ.conj = -(ζ.conj - ζ) from by abel, ClassFunction.support_neg]
      exact hyp.sSet_member_conjDiff_supported_T hG hvd hζ)
    c hξ hξirr
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  rw [← (c.extension ξ).of_isConj (isConj_iff.mpr ⟨g, hg⟩)]
  exact hyp.vanish_of_inner_eta_eq_zero (c.extension ξ)
    (fun i j => by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux i j, star_zero])
    hw.1 hw.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The coherent image of a reducible ν-row vanishes on the saturated regular set, given an
irreducible member** (the γ-trick, mirror of `coherentIndS_muColumn_vanish_regular`; Coq
`coherent_prDade_TIred`, `PFsection5.v:1371` at `T`): the degree-`0` combination
`γ = ξ(1)·ν_i − ν_i(1)·ξ ∈ ℤ[𝒯]` is `A(T)`-supported, so `c(γ)` is the honest `A₀(T)`-Dade
image (`extends_on_supported` + `tInstance_dade0_eq_induce`), which vanishes on `Ŵ^G`
(`dadeT0_apply_eq_zero_of_regular`); `c(ξ)` also vanishes there
(`coherentIndT_extension_irr_vanish_regular`), and `ξ(1) ≠ 0` divides out. -/
theorem Hypothesis.coherentIndT_nuRow_vanish_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))
    {ξ : ClassFunction ↥hyp.T ℂ} (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hξirr : IsIrreducibleCharacter ξ)
    {i : Fin hyp.q} (hi : i ≠ ⟨0, hyp.q_prime.pos⟩)
    {x : G} (hx : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))) :
    c.extension (∑ j : Fin hyp.p, hyp.nu i j) x = 0 := by
  classical
  have := hyp.finiteG
  set νrow : ClassFunction ↥hyp.T ℂ := ∑ j : Fin hyp.p, hyp.nu i j with hνdef
  have hνmem : νrow ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sOf_subset_sSet _ chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief i hi)
  -- integer degrees: `ξ(1) = nξ > 0`, `ν_i(1) = p·v`
  obtain ⟨nξ, hnξpos, hnξ, -⟩ := hξirr.exists_natDegree_charValue_one_dvd_card
  have hnξne : (nξ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnξpos.ne'
  have hν1 : νrow 1 = ((hyp.p * hyp.v : ℕ) : ℂ) := by
    rw [hνdef]
    have := hyp.nuRow_apply_one hG pins i hi
    push_cast
    exact this
  -- the degree-0 combination `γ ∈ ℤ[𝒯]`
  set γ : ClassFunction ↥hyp.T ℂ := (nξ : ℤ) • νrow - ((hyp.p * hyp.v : ℕ) : ℤ) • ξ with hγdef
  have hγspan : γ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.T)
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hνmem))
      (Submodule.smul_mem _ _ (Submodule.subset_span hξ))
  have hγ1 : γ 1 = 0 := by
    rw [hγdef, ClassFunction.sub_apply, ← Int.cast_smul_eq_zsmul ℂ (nξ : ℤ) νrow,
      ← Int.cast_smul_eq_zsmul ℂ ((hyp.p * hyp.v : ℕ) : ℤ) ξ,
      ClassFunction.smul_apply, ClassFunction.smul_apply, hν1, hnξ]
    push_cast
    ring
  -- `γ` is `A(T)`-supported: members are supported in `A(T) ∪ {1}` and `γ(1) = 0`
  have hγsupp : γ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
    intro z hz
    have hz0 : γ z ≠ 0 := hz
    have hz1 : z ≠ 1 := fun h => hz0 (h ▸ hγ1)
    have hmem : z ∈ νrow.support ∪ ξ.support := by
      by_contra hnot
      rw [Set.mem_union, not_or] at hnot
      apply hz0
      have hνz : νrow z = 0 := by
        by_contra h; exact hnot.1 (ClassFunction.mem_support.mpr h)
      have hξz : ξ z = 0 := by
        by_contra h; exact hnot.2 (ClassFunction.mem_support.mpr h)
      rw [hγdef, ClassFunction.sub_apply, ← Int.cast_smul_eq_zsmul ℂ (nξ : ℤ) νrow,
        ← Int.cast_smul_eq_zsmul ℂ ((hyp.p * hyp.v : ℕ) : ℤ) ξ,
        ClassFunction.smul_apply, ClassFunction.smul_apply, hνz, hξz]
      ring
    rcases hmem with h | h
    · rcases hyp.sSet_member_support_subset_T hG hvd hνmem h with h' | h'
      · exact h'
      · exact absurd (Set.mem_singleton_iff.mp h') hz1
    · rcases hyp.sSet_member_support_subset_T hG hvd hξ h with h' | h'
      · exact h'
      · exact absurd (Set.mem_singleton_iff.mp h') hz1
  have hγA0supp : γ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.T Tdata) hyp.T :=
    hγsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (S10.typePACore_subset_A0Set Tdata))
  -- `c(γ)` is the honest `A₀(T)`-Dade image, vanishing at the regular `x`
  have hcγ : c.extension γ
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
          ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData) γ := by
    rw [c.extends_on_supported γ ⟨hγspan, hγsupp⟩, hyp.indT_apply,
      hyp.tInstance_dade0_eq_induce hG hnoV hTP Tdata hγA0supp]
  have hcγx : c.extension γ x = 0 := by
    rw [hcγ]
    exact hyp.dadeT0_apply_eq_zero_of_regular hG hTP Tdata hW1 hW2 hγsupp hx
  -- expand `c(γ) = nξ·c(ν_i) − (p·v)·c(ξ)` and divide by `nξ`
  have hsplit : c.extension γ
      = (nξ : ℂ) • c.extension νrow - ((hyp.p * hyp.v : ℕ) : ℂ) • c.extension ξ := by
    rw [hγdef, map_sub, map_zsmul, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℂ (nξ : ℤ) (c.extension νrow),
      ← Int.cast_smul_eq_zsmul ℂ ((hyp.p * hyp.v : ℕ) : ℤ) (c.extension ξ)]
    push_cast
    rfl
  have hξx : c.extension ξ x = 0 :=
    hyp.coherentIndT_extension_irr_vanish_regular hG hnoV hvd hTP Tdata hW1 hW2 c hξ hξirr hx
  have h0 : (nξ : ℂ) * c.extension νrow x = 0 := by
    have := hcγx
    rw [hsplit, ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.smul_apply,
      hξx] at this
    calc (nξ : ℂ) * c.extension νrow x
        = (nξ : ℂ) * c.extension νrow x - ((hyp.p * hyp.v : ℕ) : ℂ) * 0 := by ring
      _ = 0 := this
  exact (mul_eq_zero.mp h0).resolve_left hnξne

open scoped FiniteInduce in
/-- **η-row self/cross inner product**: `⟨∑_j η_{rj}, ∑_j η_{sj}⟩ = p·[r = s]`, from the grid
orthonormality `eta_orthonormal`.  Mirror of `etaColumn_inner`. -/
theorem Hypothesis.etaRow_inner [Finite G] (hyp : Hypothesis (G := G)) (r s : Fin hyp.q) :
    ClassFunction.inner (∑ j : Fin hyp.p, hyp.eta r j) (∑ j : Fin hyp.p, hyp.eta s j)
      = if r = s then (hyp.p : ℂ) else 0 := by
  have := hyp.finiteG
  by_cases hrs : r = s
  · subst hrs; rw [if_pos rfl, OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ j : Fin hyp.p, ClassFunction.inner (hyp.eta r j) (∑ j' : Fin hyp.p, hyp.eta r j')
        = ∑ _j : Fin hyp.p, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right,
            Finset.sum_congr rfl
              (fun j' _ => OddOrder.Peterfalvi.S16.eta_orthonormal hyp r r j j')]
          simp
      _ = (hyp.p : ℂ) := by simp
  · rw [if_neg hrs, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [OddOrder.RepresentationTheory.inner_sum_right]
    exact Finset.sum_eq_zero fun j' _ => by
      rw [OddOrder.Peterfalvi.S16.eta_orthonormal hyp r s j j', if_neg (fun h => hrs h.1)]

open scoped FiniteInduce in
/-- **η-row self-norm**: `⟨∑_j η_{rj}, ∑_j η_{rj}⟩ = p`.  Mirror of `etaColumn_inner_self`. -/
theorem Hypothesis.etaRow_inner_self [Finite G] (hyp : Hypothesis (G := G)) (r : Fin hyp.q) :
    ClassFunction.inner (∑ j : Fin hyp.p, hyp.eta r j) (∑ j : Fin hyp.p, hyp.eta r j)
      = (hyp.p : ℂ) := by
  rw [hyp.etaRow_inner r r, if_pos rfl]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c)-at-`T`, the ν-row pin dichotomy given an irreducible member** (mirror
of `coherentIndS_muColumn_pin_of_irr`; Coq `coherent_prDade_TIred`, `PFsection5.v:1371` at `T`):
if `𝒯` contains an irreducible `ξ`, then **any** coherent extension `c` of `𝒯` on `Ind_T^G`
sends the reducible row sum `ν_i = ∑_j ν_{ij}` (`i ≠ 0`) either to the aligned `η`-row
`∑_j η_{ij}`, or to the *negated conjugate* row `−∑_j η_{sj}` (`ν̄_i = ∑_j ν_{sj}`).

Route: the (5.5) `R`-family decomposition gives `c(ν_i) = ∑_{α ∈ E} α` with
`E ⊆ {η_{ij}} ∪ {−η_{sj}}`; the γ-trick vanishing (`coherentIndT_nuRow_vanish_regular`) feeds
the (3.7) exchange relation (`S16.inner_eta_grid_relation` — the rectangle relation is
`S`/`T`-symmetric: here the **row-0** corner entries vanish, giving *column*-uniform membership
indicators along each of the two rows); the isometry norm `‖c(ν_i)‖² = p` then forces `E` to be
exactly one full row. -/
theorem Hypothesis.coherentIndT_nuRow_pin_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))
    {ξ : ClassFunction ↥hyp.T ℂ} (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hξirr : IsIrreducibleCharacter ξ)
    {i : Fin hyp.q} (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    c.extension (∑ j : Fin hyp.p, hyp.nu i j) = ∑ j : Fin hyp.p, hyp.eta i j
    ∨ ∃ s : Fin hyp.q, s ≠ ⟨0, hyp.q_prime.pos⟩ ∧ s ≠ i ∧
        (∑ j : Fin hyp.p, hyp.nu i j : ClassFunction ↥hyp.T ℂ).conj
          = ∑ j : Fin hyp.p, hyp.nu s j ∧
        c.extension (∑ j : Fin hyp.p, hyp.nu i j) = -∑ j : Fin hyp.p, hyp.eta s j := by
  classical
  have := hyp.finiteG
  set νrow : ClassFunction ↥hyp.T ℂ := ∑ j : Fin hyp.p, hyp.nu i j with hνdef
  have hνmem : νrow ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sOf_subset_sSet _ chief.H0 (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief i hi)
  have hνcmem : (νrow : ClassFunction ↥hyp.T ℂ).conj
      ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    sSet_closedUnderConjugate _ hνmem
  have hνred : ¬ IsIrreducibleCharacter νrow := hνdef ▸ hyp.nuRow_not_irreducible pins i
  -- the conjugate row `s`
  obtain ⟨s, hs0, hseq⟩ := hyp.sSet_reducible_eq_nuRowSum hG pins hvd hνcmem
    (hyp.sSet_reducible_conj_not_irr_T hνred)
  have hνrows : ∀ a b : Fin hyp.q,
      ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu a j) (∑ j : Fin hyp.p, hyp.nu b j)
        = if a = b then (hyp.p : ℂ) else 0 := hyp.nuRow_inner pins
  have hpne : (hyp.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne'
  have hsi : s ≠ i := by
    rintro rfl
    exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) hνmem
      (hseq.trans hνdef.symm)
  -- the (5.5) `R`-family decomposition through the Dade-coherence transport
  have hagree : ∀ φ : ClassFunction ↥hyp.T ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T)
        (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) →
      hyp.indT φ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData) φ :=
    fun φ hφ => by
      rw [hyp.indT_apply, hyp.tInstance_dade_eq_induce hG hnoV hTP hφ.2]
  obtain ⟨E, hEsub, hEsum⟩ :=
    hyp.sSet_coherent_extension_eq_sum_memberRFamily_T hG hnoV pins hvd hTP Tdata hU hW1 hW2
      (Set.Subset.refl _) (c.congrMap hagree) hνmem hνcmem
  have hEsum' : c.extension νrow = ∑ α ∈ E, α := hEsum
  -- the `R`-family image set: `{η_{ij}} ∪ {−η_{sj}}`
  obtain ⟨i', s', hi'eq, hs'eq, himg⟩ :=
    hyp.sSet_memberRFamily_T_imageSet_of_red hG hnoV pins hvd hTP Tdata hU hW1 hW2 hνmem hνred
  have hi' : i' = i := by
    by_contra hne
    have h := hνrows i' i
    rw [if_neg hne, ← hi'eq, ← hνdef, hνdef, hνrows i i, if_pos rfl] at h
    exact hpne h
  have hs' : s' = s := by
    by_contra hne
    have h := hνrows s' s
    rw [if_neg hne, ← hs'eq, hseq, hνrows s s, if_pos rfl] at h
    exact hpne h
  rw [hi', hs'] at himg
  have hEsubset : ∀ α ∈ E, (∃ b : Fin hyp.p, α = hyp.eta i b) ∨
      (∃ b : Fin hyp.p, α = -hyp.eta s b) := by
    intro α hα
    have := hEsub hα
    rw [himg, Finset.mem_image] at this
    obtain ⟨x, -, rfl⟩ := this
    rcases x with b | b
    · exact Or.inl ⟨b, rfl⟩
    · exact Or.inr ⟨b, rfl⟩
  -- grid inner products of the members of `E`
  have hη := OddOrder.Peterfalvi.S16.eta_orthonormal hyp
  -- `⟨c(ν_i), η_{ib}⟩` as a membership indicator
  have hcoef_i : ∀ b : Fin hyp.p,
      ClassFunction.inner (c.extension νrow) (hyp.eta i b)
        = if hyp.eta i b ∈ E then 1 else 0 := by
    intro b
    rw [hEsum', OddOrder.RepresentationTheory.inner_sum_left]
    rw [show (∑ α ∈ E, ClassFunction.inner α (hyp.eta i b))
        = ∑ α ∈ E, (if α = hyp.eta i b then (1 : ℂ) else 0) from
      Finset.sum_congr rfl fun α hα => by
        rcases hEsubset α hα with ⟨b', rfl⟩ | ⟨b', rfl⟩
        · rw [hη i i b' b]
          by_cases hbb : b' = b
          · subst hbb; rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
          · rw [if_neg (fun h => hbb h.2), if_neg (fun h => hbb (by
              have := congrArg (fun f => ClassFunction.inner f (hyp.eta i b)) h
              rw [hη i i b' b, hη i i b b, if_pos (⟨rfl, rfl⟩ : i = i ∧ b = b),
                if_neg (fun hh => hbb hh.2)] at this
              exact absurd this zero_ne_one))]
        · rw [ClassFunction.inner_neg_left, hη s i b' b, if_neg (fun h => hsi h.1), neg_zero,
            if_neg (fun h => by
              have := congrArg (fun f => ClassFunction.inner f (hyp.eta i b)) h
              rw [ClassFunction.inner_neg_left, hη s i b' b, if_neg (fun hh => hsi hh.1),
                neg_zero, hη i i b b, if_pos ⟨rfl, rfl⟩] at this
              exact absurd this zero_ne_one)]]
    rw [Finset.sum_ite_eq' E (hyp.eta i b) (fun _ => (1 : ℂ))]
  have hcoef_s : ∀ b : Fin hyp.p,
      ClassFunction.inner (c.extension νrow) (hyp.eta s b)
        = if -hyp.eta s b ∈ E then -1 else 0 := by
    intro b
    rw [hEsum', OddOrder.RepresentationTheory.inner_sum_left]
    rw [show (∑ α ∈ E, ClassFunction.inner α (hyp.eta s b))
        = ∑ α ∈ E, (if α = -hyp.eta s b then (-1 : ℂ) else 0) from
      Finset.sum_congr rfl fun α hα => by
        rcases hEsubset α hα with ⟨b', rfl⟩ | ⟨b', rfl⟩
        · rw [hη i s b' b, if_neg (fun h => hsi h.1.symm), if_neg (fun h => by
            have := congrArg (fun f => ClassFunction.inner f (hyp.eta s b)) h
            rw [hη i s b' b, if_neg (fun hh => hsi hh.1.symm),
              ClassFunction.inner_neg_left, hη s s b b, if_pos ⟨rfl, rfl⟩] at this
            exact absurd this (by norm_num))]
        · rw [ClassFunction.inner_neg_left, hη s s b' b]
          by_cases hbb : b' = b
          · subst hbb; rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
          · rw [if_neg (fun h => hbb h.2), neg_zero, if_neg (fun h => hbb (by
              have := congrArg (fun f => ClassFunction.inner f (hyp.eta s b)) h
              rw [ClassFunction.inner_neg_left, hη s s b' b, if_neg (fun hh => hbb hh.2),
                neg_zero, ClassFunction.inner_neg_left, hη s s b b, if_pos ⟨rfl, rfl⟩] at this
              exact absurd this (by norm_num)))]]
    rw [Finset.sum_ite_eq' E (-hyp.eta s b) (fun _ => (-1 : ℂ))]
  have hcoef_0 : ∀ (a : Fin hyp.q) (b : Fin hyp.p), a ≠ i → a ≠ s →
      ClassFunction.inner (c.extension νrow) (hyp.eta a b) = 0 := by
    intro a b hai has
    rw [hEsum', OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun α hα => ?_
    rcases hEsubset α hα with ⟨b', rfl⟩ | ⟨b', rfl⟩
    · rw [hη i a b' b, if_neg (fun h => hai h.1.symm)]
    · rw [ClassFunction.inner_neg_left, hη s a b' b, if_neg (fun h => has h.1.symm), neg_zero]
  -- column-uniformity of the indicators through the (3.7) exchange relation
  have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      c.extension νrow x = 0 := fun x hx =>
    hyp.coherentIndT_nuRow_vanish_regular hG hnoV pins hvd hTP Tdata hW1 hW2 chief c
      hξ hξirr hi hx
  have hi0' : (⟨0, hyp.q_prime.pos⟩ : Fin hyp.q) ≠ i := fun h => hi h.symm
  have hs0' : (⟨0, hyp.q_prime.pos⟩ : Fin hyp.q) ≠ s := fun h => hs0 h.symm
  have hcol : ∀ (a : Fin hyp.q) (b : Fin hyp.p),
      ClassFunction.inner (c.extension νrow) (hyp.eta a b)
        = ClassFunction.inner (c.extension νrow) (hyp.eta a ⟨0, hyp.p_prime.pos⟩) := by
    intro a b
    have hrel := OddOrder.Peterfalvi.S16.inner_eta_grid_relation hyp hvanish a b
    rw [hcoef_0 ⟨0, hyp.q_prime.pos⟩ b hi0' hs0',
      hcoef_0 ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ hi0' hs0'] at hrel
    linear_combination hrel
  have hcol_i : ∀ b : Fin hyp.p,
      (hyp.eta i b ∈ E ↔ hyp.eta i ⟨0, hyp.p_prime.pos⟩ ∈ E) := by
    intro b
    have h := hcol i b
    rw [hcoef_i b, hcoef_i ⟨0, hyp.p_prime.pos⟩] at h
    by_cases h1 : hyp.eta i b ∈ E <;> by_cases h2 : hyp.eta i ⟨0, hyp.p_prime.pos⟩ ∈ E <;>
      simp only [h1, h2, if_pos, if_false] at h ⊢ <;>
      first
        | exact Iff.rfl
        | exact absurd h one_ne_zero
        | exact absurd h.symm one_ne_zero
  have hcol_s : ∀ b : Fin hyp.p,
      (-hyp.eta s b ∈ E ↔ -hyp.eta s ⟨0, hyp.p_prime.pos⟩ ∈ E) := by
    intro b
    have h := hcol s b
    rw [hcoef_s b, hcoef_s ⟨0, hyp.p_prime.pos⟩] at h
    by_cases h1 : -hyp.eta s b ∈ E <;> by_cases h2 : -hyp.eta s ⟨0, hyp.p_prime.pos⟩ ∈ E <;>
      simp only [h1, h2, if_pos, if_false] at h ⊢ <;>
      first
        | exact Iff.rfl
        | exact absurd h (by norm_num)
  -- the isometry norm `‖c(ν_i)‖² = p`
  have hnorm : ClassFunction.inner (c.extension νrow) (c.extension νrow) = (hyp.p : ℂ) := by
    rw [c.extension_inner_eq νrow νrow (Submodule.subset_span hνmem)
      (Submodule.subset_span hνmem), hνdef, hνrows i i, if_pos rfl]
  -- injectivity of the two row enumerations
  have hinj_i : Function.Injective (fun b : Fin hyp.p => hyp.eta i b) := by
    intro b b' h
    by_contra hne
    have := congrArg (fun f => ClassFunction.inner f (hyp.eta i b')) h
    rw [hη i i b b', hη i i b' b', if_pos (⟨rfl, rfl⟩ : i = i ∧ b' = b'),
      if_neg (fun hh => hne hh.2)] at this
    exact zero_ne_one this
  have hinj_s : Function.Injective (fun b : Fin hyp.p => -hyp.eta s b) := by
    intro b b' h
    by_contra hne
    have := congrArg (fun f => ClassFunction.inner f (-hyp.eta s b')) h
    simp only [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg] at this
    rw [hη s s b b', hη s s b' b', if_pos (⟨rfl, rfl⟩ : s = s ∧ b' = b'),
      if_neg (fun hh => hne hh.2)] at this
    exact zero_ne_one this
  -- endgame: four cases on the two base indicators
  by_cases hsE : hyp.eta i ⟨0, hyp.p_prime.pos⟩ ∈ E <;>
    by_cases htE : -hyp.eta s ⟨0, hyp.p_prime.pos⟩ ∈ E
  · -- both rows in: `‖φ‖² = 2p`, contradiction
    exfalso
    have hEeq : E = Finset.image (Sum.elim (fun j : Fin hyp.p => hyp.eta i j)
        (fun j : Fin hyp.p => -hyp.eta s j)) Finset.univ := by
      apply Finset.Subset.antisymm
      · rw [← himg]; exact hEsub
      · intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨x, -, rfl⟩ := hα
        rcases x with b | b
        · exact (hcol_i b).mpr hsE
        · exact (hcol_s b).mpr htE
    have hφeq : c.extension νrow
        = (∑ b : Fin hyp.p, hyp.eta i b) - ∑ b : Fin hyp.p, hyp.eta s b := by
      rw [hEsum', hEeq]
      rw [show Finset.image (Sum.elim (fun j : Fin hyp.p => hyp.eta i j)
            (fun j : Fin hyp.p => -hyp.eta s j)) Finset.univ
          = Finset.image (fun b : Fin hyp.p => hyp.eta i b) Finset.univ
            ∪ Finset.image (fun b : Fin hyp.p => -hyp.eta s b) Finset.univ from by
        ext α
        simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and,
          Sum.exists, Sum.elim_inl, Sum.elim_inr]]
      rw [Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro α hα hmem
        rw [Finset.mem_image] at hα hmem
        obtain ⟨b, -, rfl⟩ := hα
        obtain ⟨b', -, heq⟩ := hmem
        have := congrArg (fun f => ClassFunction.inner f (hyp.eta i b)) heq
        rw [ClassFunction.inner_neg_left, hη s i b' b, if_neg (fun hh => hsi hh.1), neg_zero,
          hη i i b b, if_pos (⟨rfl, rfl⟩ : i = i ∧ b = b)] at this
        exact zero_ne_one this)]
      rw [Finset.sum_image (fun b _ b' _ h => hinj_i h),
        Finset.sum_image (fun b _ b' _ h => hinj_s h), Finset.sum_neg_distrib]
      abel
    have h2p : ClassFunction.inner (c.extension νrow) (c.extension νrow)
        = (2 : ℂ) * (hyp.p : ℂ) := by
      rw [hφeq]
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hyp.etaRow_inner_self i, hyp.etaRow_inner_self s,
        hyp.etaRow_inner i s, hyp.etaRow_inner s i,
        if_neg (fun h => hsi h.symm), if_neg hsi]
      ring
    rw [hnorm] at h2p
    have : (hyp.p : ℂ) = 0 := by linear_combination -h2p
    exact hpne this
  · -- clean pin: `E` is the full `i`-row
    left
    have hEeq : E = Finset.image (fun b : Fin hyp.p => hyp.eta i b) Finset.univ := by
      apply Finset.Subset.antisymm
      · intro α hα
        rcases hEsubset α hα with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
        · exact absurd ((hcol_s b).mp hα) htE
      · intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨b, -, rfl⟩ := hα
        exact (hcol_i b).mpr hsE
    rw [hEsum', hEeq, Finset.sum_image (fun b _ b' _ h => hinj_i h)]
  · -- flipped pin: `E` is the full negated `s`-row
    right
    refine ⟨s, hs0, hsi, hνdef ▸ hseq, ?_⟩
    have hEeq : E = Finset.image (fun b : Fin hyp.p => -hyp.eta s b) Finset.univ := by
      apply Finset.Subset.antisymm
      · intro α hα
        rcases hEsubset α hα with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact absurd ((hcol_i b).mp hα) hsE
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
      · intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨b, -, rfl⟩ := hα
        exact (hcol_s b).mpr htE
    rw [hEsum', hEeq, Finset.sum_image (fun b _ b' _ h => hinj_s h), Finset.sum_neg_distrib]
  · -- neither: `φ = 0`, contradicting `‖φ‖² = p`
    exfalso
    have hEeq : E = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro α hα
      rcases hEsubset α hα with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact hsE ((hcol_i b).mp hα)
      · exact htE ((hcol_s b).mp hα)
    rw [hEsum', hEeq, Finset.sum_empty, ClassFunction.inner_zero_left] at hnorm
    exact hpne hnorm.symm

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The clean pivot pin propagates to all rows** (mirror of
`coherentIndS_muColumn_eq_etaColumn_of_pivot`, coherence-generic): if `c(ν_1) = ∑_j η_{1j}` at
the pivot row, then `c(ν_i) = ∑_j η_{ij}` for every nonzero `i`, through the row-independence
`coherentIndT_nuRow_diff`. -/
theorem Hypothesis.coherentIndT_nuRow_eq_etaRow_of_pivot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))
    (hpivot : c.extension (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
      = ∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j)
    {i : Fin hyp.q} (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    c.extension (∑ j : Fin hyp.p, hyp.nu i j) = ∑ j : Fin hyp.p, hyp.eta i j := by
  classical
  have := hyp.finiteG
  have hq1 : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  by_cases hiq : i = ⟨1, hyp.q_prime.one_lt⟩
  · subst hiq; exact hpivot
  · have hdiff := hyp.coherentIndT_nuRow_diff hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief c
      hi hq1 hiq
    calc c.extension (∑ j : Fin hyp.p, hyp.nu i j)
        = (c.extension (∑ j : Fin hyp.p, hyp.nu i j)
            - c.extension (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j))
          + c.extension (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j) := by abel
      _ = ((∑ j : Fin hyp.p, hyp.eta i j)
            - (∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j))
          + ∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j := by rw [hdiff, hpivot]
      _ = ∑ j : Fin hyp.p, hyp.eta i j := by abel

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The canonical pinned `𝒯 = sSet(setupT)`-coherence, all-reducible case** (mirror of
`exists_pinned_coherent_sSet_of_all_reducible`).  If every member of `𝒯` is reducible — hence a
ν-row sum (`sSet_reducible_eq_nuRowSum`) — the assignment `ν-row ↦ aligned η-row` extends to a
coherent extension of `𝒯` on `Ind_T^G` (`coherentImageMap` over the orthogonal ν-row family),
*pinned by construction* at the pivot row `1`.

Isometry: ν-rows are pairwise `p·[r=s]`-orthogonal, matched by the η-rows (`nuRow_inner` /
`etaRow_inner`).  τ-agreement: an `A(T)`-supported lattice element vanishes at `1`
(`S10.typePACore_one_not_mem`); since every reducible row shares degree `p·v`
(`nuRow_apply_one`), the residual `ν₀ − Ind_T^G` is `(x 1 / p·v)`-proportional to the
row-independent constant `r = η-row₁ − Ind_T^G(ν-row₁)` (from the per-column prime-`TI`
cross-relation `tauT_nu_cross` through `tInstance_dade0_eq_induce`), hence vanishes there. -/
theorem Hypothesis.exists_pinned_coherent_sSet_of_all_reducible_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hallred : ∀ η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd),
      ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
        (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T),
      c.extension (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
        = ∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j := by
  have := hyp.finiteG
  classical
  -- pivot / second-row index arithmetic
  have hi1_0 : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  have h2lt : 2 < hyp.q := by have := hyp.three_le_q; omega
  have hi2_0 : (⟨2, h2lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) (by norm_num)
  have hne12 : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨2, h2lt⟩ := by
    intro h; exact absurd (congrArg Fin.val h) (by norm_num)
  have hv_ne : hyp.v ≠ 0 := by
    intro h0
    have hcard : 0 < Nat.card ↥hyp.V := Nat.card_pos
    rw [hyp.card_V_eq_vd, h0, zero_mul] at hcard
    exact absurd hcard (lt_irrefl 0)
  have hpne0 : (hyp.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne'
  have hone_notin : (1 : ↥hyp.T) ∉
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    simp
  -- the family, its finiteness, and the per-member row datum (all members reducible)
  set F : Set (ClassFunction ↥hyp.T ℂ) := sSet (hyp.toTypesIIIIIIVSetupT hG hvd) with hFdef
  have hFfin : F.Finite := sSet_finite (hyp.toTypesIIIIIIVSetupT hG hvd)
  have hrowof : ∀ a ∈ F, ∃ r : Fin hyp.q, r ≠ ⟨0, hyp.q_prime.pos⟩ ∧
      a = ∑ j : Fin hyp.p, hyp.nu r j := fun a ha =>
    hyp.sSet_reducible_eq_nuRowSum hG pins hvd ha (hallred a ha)
  -- enumeration of the family
  set n := hFfin.toFinset.card with hndef
  set χ : Fin n → ClassFunction ↥hyp.T ℂ := fun i => ↑(hFfin.toFinset.equivFin.symm i) with hχdef
  have hχmem : ∀ i, χ i ∈ F := fun i =>
    hFfin.mem_toFinset.mp (hFfin.toFinset.equivFin.symm i).2
  have hχinj : Function.Injective χ := fun i j hij =>
    (Equiv.injective _ (Subtype.ext hij) :)
  set rf : Fin n → Fin hyp.q := fun i => (hrowof (χ i) (hχmem i)).choose with hrfdef
  have hrf0 : ∀ i, rf i ≠ ⟨0, hyp.q_prime.pos⟩ := fun i =>
    (hrowof (χ i) (hχmem i)).choose_spec.1
  have hrfeq : ∀ i, χ i = ∑ j : Fin hyp.p, hyp.nu (rf i) j :=
    fun i => (hrowof (χ i) (hχmem i)).choose_spec.2
  -- row inner products: `⟨ν-row_r, ν-row_s⟩ = p·[r=s] = ⟨η-row_r, η-row_s⟩`
  have hνrows : ∀ r s : Fin hyp.q,
      ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu r j) (∑ j : Fin hyp.p, hyp.nu s j)
        = if r = s then (hyp.p : ℂ) else 0 := hyp.nuRow_inner pins
  have hηrows : ∀ r s : Fin hyp.q,
      ClassFunction.inner (∑ j : Fin hyp.p, hyp.eta r j) (∑ j : Fin hyp.p, hyp.eta s j)
        = if r = s then (hyp.p : ℂ) else 0 := hyp.etaRow_inner
  -- distinct members carry distinct rows; member-pair inner products
  have hrfinj : ∀ i i' : Fin n, rf i = rf i' → i = i' := by
    intro i i' hk
    apply hχinj
    rw [hrfeq i, hrfeq i', hk]
  have hχpair : ∀ i i' : Fin n, ClassFunction.inner (χ i) (χ i')
      = if i = i' then (hyp.p : ℂ) else 0 := by
    intro i i'
    rw [hrfeq i, hrfeq i', hνrows]
    by_cases hii : i = i'
    · subst hii; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hii (hrfinj _ _ h)), if_neg hii]
  have hχorth : ∀ i j : Fin n, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0 := by
    intro i j hij; rw [hχpair, if_neg hij]
  have hχnorm : ∀ i : Fin n, ClassFunction.inner (χ i) (χ i) ≠ 0 := by
    intro i; rw [hχpair, if_pos rfl]; exact hpne0
  -- the canonical Fourier map and its member images
  set ν₀ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.coherentImageMap χ
      (fun i => (ClassFunction.inner (χ i) (χ i))⁻¹ • ∑ j' : Fin hyp.p, hyp.eta (rf i) j')
    with hν₀def
  have hν₀apply : ∀ i : Fin n, ν₀ (χ i) = ∑ j' : Fin hyp.p, hyp.eta (rf i) j' := fun i =>
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.coherentImageMap_apply_eq_of_orthogonal
      hχorth hχnorm i
  -- the general-row prime-`TI` cross-relation re-grounded onto `Ind_T^G`
  have hindT_row_diff : ∀ r : Fin hyp.q, r ≠ ⟨0, hyp.q_prime.pos⟩ →
      hyp.indT ((∑ j : Fin hyp.p, hyp.nu r j)
          - (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j))
        = (∑ j : Fin hyp.p, hyp.eta r j)
          - (∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j) := by
    intro r hr0
    by_cases hr1 : r = ⟨1, hyp.q_prime.one_lt⟩
    · subst hr1; rw [sub_self, map_zero, sub_self]
    · have hAsupp := hyp.nuRow_diff_supported hG pins hvd chief hr0 hi1_0
      have hA0supp := hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
        (S10.typePACore_subset_A0Set Tdata))
      rw [hyp.indT_apply, ← hyp.tInstance_dade0_eq_induce hG hnoV hTP Tdata hA0supp,
        show ((∑ j : Fin hyp.p, hyp.nu r j)
            - (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j))
          = ∑ j : Fin hyp.p, (hyp.nu r j - hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j) from by
          rw [Finset.sum_sub_distrib],
        map_sum, Finset.sum_congr rfl (fun j _ =>
          tauT_nu_cross hG hnoV hyp pins hTP Tdata hU hW1 hW2 j hr0 hi1_0 hr1),
        Finset.sum_sub_distrib]
  -- the row-independent residual `r = η-row₁ − Ind_T^G(ν-row₁)`
  set r : ClassFunction G ℂ :=
    (∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j)
      - hyp.indT (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j) with hrdef
  have hrconst : ∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
      (∑ j : Fin hyp.p, hyp.eta i j) - hyp.indT (∑ j : Fin hyp.p, hyp.nu i j) = r := by
    intro i hi0
    have hτdiff : hyp.indT (∑ j : Fin hyp.p, hyp.nu i j)
        - hyp.indT (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
        = (∑ j : Fin hyp.p, hyp.eta i j)
          - (∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j) := by
      rw [← map_sub]; exact hindT_row_diff i hi0
    rw [hrdef, sub_eq_sub_iff_sub_eq_sub]
    exact hτdiff.symm
  -- every reducible member shares the degree `p·v` — via the value-at-1 of the row sum
  have hdegs : ∀ i : Fin n, ((χ i : ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1
      = ((∑ j' : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j' :
          ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1 := by
    intro i
    rw [hrfeq i, hyp.nuRow_apply_one hG pins (rf i) (hrf0 i),
      hyp.nuRow_apply_one hG pins ⟨1, hyp.q_prime.one_lt⟩ hi1_0]
  -- the member-index extraction from a set-membership
  have hidxof : ∀ a ∈ F, ∃ i : Fin n, χ i = a := by
    intro a ha
    exact ⟨hFfin.toFinset.equivFin ⟨a, hFfin.mem_toFinset.mpr ha⟩, by simp [hχdef]⟩
  -- the isometry field
  have hinner : ∀ x y : ClassFunction ↥hyp.T ℂ,
      x ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.T) F →
      y ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.T) F →
      ClassFunction.inner (ν₀ x) (ν₀ y) = ClassFunction.inner x y := by
    intro x y hx hy
    induction hy using Submodule.span_induction with
    | mem b hb =>
        induction hx using Submodule.span_induction with
        | mem a ha =>
            obtain ⟨i, rfl⟩ := hidxof a ha
            obtain ⟨j', rfl⟩ := hidxof b hb
            rw [hν₀apply i, hν₀apply j', hηrows, hχpair]
            by_cases hij : i = j'
            · subst hij; rw [if_pos rfl, if_pos rfl]
            · rw [if_neg (fun h => hij (hrfinj _ _ h)), if_neg hij]
        | zero => rw [map_zero, ClassFunction.inner_zero_left,
            ClassFunction.inner_zero_left]
        | add u v hu hv ihu ihv =>
            rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
              ihu, ihv]
        | smul m u hu ihu =>
            rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ m (ν₀ u),
              ← Int.cast_smul_eq_zsmul ℂ m u, ClassFunction.inner_smul_left,
              ClassFunction.inner_smul_left, ihu]
    | zero => rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
    | add u v hu hv ihu ihv =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ihu, ihv]
    | smul m u hu ihu =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ m (ν₀ u),
          ← Int.cast_smul_eq_zsmul ℂ m u, OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, ihu]
  -- the pivot degree is nonzero (`p·v`)
  have hD1ne : ((∑ j' : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j' :
      ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1 ≠ 0 := by
    rw [hyp.nuRow_apply_one hG pins ⟨1, hyp.q_prime.one_lt⟩ hi1_0]
    exact mul_ne_zero hpne0 (Nat.cast_ne_zero.mpr hv_ne)
  -- the residual identity on the whole lattice
  have hres : ∀ x ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.T) F,
      ν₀ x - hyp.indT x
        = ((x 1) / ((∑ j' : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j' :
            ClassFunction ↥hyp.T ℂ) : ↥hyp.T → ℂ) 1) • r := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := hidxof a ha
        rw [hν₀apply i, hdegs i, div_self hD1ne, one_smul]
        have h1 : (∑ j' : Fin hyp.p, hyp.eta (rf i) j') - hyp.indT (χ i) = r := by
          conv_lhs => rw [hrfeq i]
          exact hrconst (rf i) (hrf0 i)
        exact h1
    | zero => rw [map_zero, map_zero, ClassFunction.zero_apply, zero_div, zero_smul, sub_zero]
    | add u v hu hv ihu ihv =>
        rw [map_add, map_add, ClassFunction.add_apply, add_div, add_smul]
        rw [show ν₀ u + ν₀ v - (hyp.indT u + hyp.indT v)
            = (ν₀ u - hyp.indT u) + (ν₀ v - hyp.indT v) from by abel, ihu, ihv]
    | smul m u hu ihu =>
        rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ m (ν₀ u),
          ← Int.cast_smul_eq_zsmul ℂ m (hyp.indT u), ← Int.cast_smul_eq_zsmul ℂ m u,
          ClassFunction.smul_apply, ← smul_sub, ihu, smul_smul, mul_div_assoc]
  -- the supported-agreement field
  have hextends : ∀ x : ClassFunction ↥hyp.T ℂ,
      x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T) F
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) →
      ν₀ x = hyp.indT x := by
    rintro x ⟨hxspan, hxsupp⟩
    have hx1 : x 1 = 0 := by
      by_contra h
      exact hone_notin (hxsupp (ClassFunction.mem_support.mpr h))
    have h := hres x hxspan
    rw [hx1, zero_div, zero_smul, sub_eq_zero] at h
    exact h
  -- the ZIrr-codomain field
  have hZIrr : ∀ x : ClassFunction ↥hyp.T ℂ,
      x ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.T) F → ν₀ x ∈ ZIrr G := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := hidxof a ha
        rw [hν₀apply i]
        exact Submodule.sum_mem _ fun j' _ =>
          OddOrder.Peterfalvi.S16.eta_mem_ZIrr hyp (rf i) j'
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
    | smul m u hu ihu => rw [map_zsmul]; exact Submodule.smul_mem _ m ihu
  -- the nonzero supported witness `ν-row₁ − ν-row₂`
  have hnonzero : ∃ φ : ClassFunction ↥hyp.T ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T) F
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) ∧
        φ ≠ 0 := by
    refine ⟨(∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
        - (∑ j : Fin hyp.p, hyp.nu ⟨2, h2lt⟩ j), ?_, ?_⟩
    · rw [OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff]
      refine ⟨Submodule.sub_mem _ (Submodule.subset_span ?_) (Submodule.subset_span ?_),
        hyp.nuRow_diff_supported hG pins hvd chief hi1_0 hi2_0⟩
      · rw [hFdef]
        exact sOf_subset_sSet _ chief.H0
          (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief ⟨1, hyp.q_prime.one_lt⟩ hi1_0)
      · rw [hFdef]
        exact sOf_subset_sSet _ chief.H0
          (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief ⟨2, h2lt⟩ hi2_0)
    · intro heq
      have hce : (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
          = ∑ j : Fin hyp.p, hyp.nu ⟨2, h2lt⟩ j := sub_eq_zero.mp heq
      have hcontra := hνrows ⟨1, hyp.q_prime.one_lt⟩ ⟨2, h2lt⟩
      rw [if_neg hne12, ← hce, hνrows ⟨1, hyp.q_prime.one_lt⟩ ⟨1, hyp.q_prime.one_lt⟩,
        if_pos rfl] at hcontra
      exact hpne0 hcontra
  -- assemble; the pin is `hν₀apply` at the `ν-row₁`-member index
  have hν1mem : (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j) ∈ F := by
    rw [hFdef]
    exact sOf_subset_sSet _ chief.H0
      (hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief ⟨1, hyp.q_prime.one_lt⟩ hi1_0)
  set i₁ : Fin n := hFfin.toFinset.equivFin ⟨_, hFfin.mem_toFinset.mpr hν1mem⟩ with hi₁def
  have hχi₁ : χ i₁ = ∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j := by
    rw [hχdef, hi₁def]; simp
  have hrfi₁ : rf i₁ = ⟨1, hyp.q_prime.one_lt⟩ := by
    have hrows_eq : (∑ j' : Fin hyp.p, hyp.nu (rf i₁) j')
        = ∑ j' : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j' := by
      rw [← hrfeq i₁, hχi₁]
    have h2 : (if rf i₁ = (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) then (hyp.p : ℂ) else 0)
        = (hyp.p : ℂ) := by
      rw [← hνrows, hrows_eq, hνrows, if_pos rfl]
    by_contra hne
    rw [if_neg hne] at h2
    exact hpne0 h2.symm
  refine ⟨{ nonzero := hnonzero
            extension := ν₀
            extension_inner_eq := hinner
            extends_on_supported := hextends
            extension_mem_ZIrr := hZIrr }, ?_⟩
  change ν₀ (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
    = ∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j
  rw [← hχi₁, hν₀apply i₁, hrfi₁]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The (9.11)-`T` coherence of `𝒯 = sSet(setupT)`, pinned by the (13.3.c)-`T` ν-row
formula** (mirror of `sSet_coherent_indS_A_pinned`): there is a coherent extension of `𝒯` on
`Ind_T^G` whose values on the reducible ν-row sums are the aligned `η`-row sums — either
uniformly, or (the `q = 3` sign-flip exception) with a global negative sign and the two nonzero
rows swapped.

By-cases on an irreducible member of `𝒯`:

* **has-irr**: *any* inhabitant (`sSet_coherent_indT_A`) is pinned by the γ-trick dichotomy
  `coherentIndT_nuRow_pin_of_irr`.  A clean pivot propagates by row-independence; a flipped
  pivot forces `q = 3` (for `q ≥ 5` a third row `i₂ ∉ {0, 1, s}` makes the row-difference
  identity contradict the flip) and the rows swap.
* **all-reducible**: the constructed glue `exists_pinned_coherent_sSet_of_all_reducible_T`
  supplies a clean-pinned inhabitant. -/
theorem Hypothesis.sSet_coherent_indT_A_pinned [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    ∃ c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T),
      (∀ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
        c.extension (∑ j : Fin hyp.p, hyp.nu i j) = ∑ j : Fin hyp.p, hyp.eta i j) ∨
      (hyp.q = 3 ∧ ∀ i i' : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ →
        i' ≠ ⟨0, hyp.q_prime.pos⟩ → i ≠ i' →
        c.extension (∑ j : Fin hyp.p, hyp.nu i j) = -∑ j : Fin hyp.p, hyp.eta i' j) := by
  classical
  have := hyp.finiteG
  have hq1 : (⟨1, hyp.q_prime.one_lt⟩ : Fin hyp.q) ≠ ⟨0, hyp.q_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  have hpne0 : (hyp.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.p_prime.pos.ne'
  by_cases hirr : ∃ ξ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd), IsIrreducibleCharacter ξ
  · -- has-irr: any inhabitant is pinned by the γ-trick dichotomy
    obtain ⟨ξ, hξ, hξirr⟩ := hirr
    obtain ⟨c⟩ := hyp.sSet_coherent_indT_A hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
    refine ⟨c, ?_⟩
    rcases hyp.coherentIndT_nuRow_pin_of_irr hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief c
        hξ hξirr hq1 with
      hclean | ⟨s, hs0, hs1, hsconj, hflip⟩
    · exact Or.inl fun i hi =>
        hyp.coherentIndT_nuRow_eq_etaRow_of_pivot hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          c hclean hi
    · -- flipped pivot: `q = 3` is forced, and the two nonzero rows swap
      right
      have hνrows := hyp.nuRow_inner pins
      have hηrows := hyp.etaRow_inner
      -- a flipped pivot with a third nonzero row `i₂ ∉ {0, 1, s}` is contradictory
      have hno3rd : ∀ i₂ : Fin hyp.q, i₂ ≠ ⟨0, hyp.q_prime.pos⟩ →
          i₂ ≠ ⟨1, hyp.q_prime.one_lt⟩ → i₂ ≠ s → False := by
        intro i₂ hi₂0 hi₂1 hi₂s
        have hdiff := hyp.coherentIndT_nuRow_diff hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          c hq1 hi₂0 (fun h => hi₂1 h.symm)
        -- inner the difference identity with the pivot `η`-row
        have hinner := congrArg (fun f => ClassFunction.inner f
          (∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j)) hdiff
        simp only [ClassFunction.inner_sub_left] at hinner
        rw [hflip, ClassFunction.inner_neg_left,
          hηrows s ⟨1, hyp.q_prime.one_lt⟩, if_neg hs1, neg_zero,
          hηrows ⟨1, hyp.q_prime.one_lt⟩ ⟨1, hyp.q_prime.one_lt⟩, if_pos rfl,
          hηrows i₂ ⟨1, hyp.q_prime.one_lt⟩, if_neg hi₂1] at hinner
        -- so `⟨c(ν_{i₂}), η-row₁⟩ = −p`; but the dichotomy at `i₂` gives `0`
        rcases hyp.coherentIndT_nuRow_pin_of_irr hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief c
            hξ hξirr hi₂0 with
          hc2 | ⟨s₂, hs₂0, hs₂i₂, hs₂conj, hc2⟩
        · rw [hc2, hηrows i₂ ⟨1, hyp.q_prime.one_lt⟩, if_neg hi₂1] at hinner
          rw [sub_zero] at hinner
          exact hpne0 (by linear_combination -hinner)
        · have hs₂1 : s₂ ≠ ⟨1, hyp.q_prime.one_lt⟩ := by
            rintro rfl
            -- `s₂ = 1` would give `conj(ν_{i₂}) = ν_1`, i.e. `ν_{i₂} = conj(ν_1) = ν_s`
            have h1 : (∑ j : Fin hyp.p, hyp.nu i₂ j : ClassFunction ↥hyp.T ℂ)
                = (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j :
                    ClassFunction ↥hyp.T ℂ).conj := by
              rw [← hs₂conj, ClassFunction.conj_conj]
            rw [hsconj] at h1
            have h2 := hνrows i₂ s
            rw [if_neg hi₂s, h1, hνrows s s, if_pos rfl] at h2
            exact hpne0 h2
          rw [hc2, ClassFunction.inner_neg_left,
            hηrows s₂ ⟨1, hyp.q_prime.one_lt⟩, if_neg hs₂1, neg_zero, sub_zero] at hinner
          exact hpne0 (by linear_combination -hinner)
      -- `q = 3`: otherwise `q ≥ 5` and a third row exists
      have hq3 : hyp.q = 3 := by
        by_contra hq3ne
        have h3q := hyp.three_le_q
        have hq4 : hyp.q ≠ 4 := fun h => by
          have := hyp.q_prime; rw [h] at this; norm_num at this
        have hq5 : 5 ≤ hyp.q := by omega
        have h2lt : 2 < hyp.q := by omega
        have h3lt : 3 < hyp.q := by omega
        by_cases hs2 : s = ⟨2, h2lt⟩
        · refine hno3rd ⟨3, h3lt⟩ ?_ ?_ ?_
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · rw [hs2]; intro h; exact absurd (congrArg Fin.val h) (by norm_num)
        · refine hno3rd ⟨2, h2lt⟩ ?_ ?_ ?_
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · intro h; exact absurd (congrArg Fin.val h) (by norm_num)
          · intro h; exact hs2 h.symm
      refine ⟨hq3, ?_⟩
      -- with `q = 3` the nonzero rows are `1` and `s = 2`
      have hsval : (s : Fin hyp.q).val = 2 := by
        have hslt := s.isLt
        have hs0' : s.val ≠ 0 := fun h => hs0 (Fin.ext h)
        have hs1' : s.val ≠ 1 := fun h => hs1 (Fin.ext h)
        omega
      intro i i' hi hi' hii'
      have hilt := i.isLt; have hi'lt := i'.isLt
      have hi0' : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have hi'0 : i'.val ≠ 0 := fun h => hi' (Fin.ext h)
      have hii'' : i.val ≠ i'.val := fun h => hii' (Fin.ext h)
      rcases show i.val = 1 ∧ i'.val = 2 ∨ i.val = 2 ∧ i'.val = 1 by omega with
        ⟨hiv, hi'v⟩ | ⟨hiv, hi'v⟩
      · -- `i` is the pivot, `i' = s`: the flip itself
        have hip : i = ⟨1, hyp.q_prime.one_lt⟩ := Fin.ext hiv
        have hi's : i' = s := Fin.ext (hi'v.trans hsval.symm)
        rw [hip, hi's]
        exact hflip
      · -- `i = s`, `i'` the pivot: transport the flip through the row difference
        have his : i = s := Fin.ext (hiv.trans hsval.symm)
        have hi'p : i' = ⟨1, hyp.q_prime.one_lt⟩ := Fin.ext hi'v
        rw [his, hi'p]
        have hdiff := hyp.coherentIndT_nuRow_diff hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
          c hq1 hs0 hs1.symm
        have : c.extension (∑ j : Fin hyp.p, hyp.nu s j)
            = c.extension (∑ j : Fin hyp.p, hyp.nu ⟨1, hyp.q_prime.one_lt⟩ j)
              - ((∑ j : Fin hyp.p, hyp.eta ⟨1, hyp.q_prime.one_lt⟩ j)
                - ∑ j : Fin hyp.p, hyp.eta s j) := by
          rw [← hdiff]; abel
        rw [this, hflip]
        abel
  · -- all-reducible: the constructed glue supplies the clean pin
    push Not at hirr
    obtain ⟨c, hpivot⟩ := hyp.exists_pinned_coherent_sSet_of_all_reducible_T hG hnoV pins hvd
      hTP Tdata hU hW1 hW2 chief hirr
    exact ⟨c, Or.inl fun i hi =>
      hyp.coherentIndT_nuRow_eq_etaRow_of_pivot hG hnoV pins hvd hTP Tdata hU hW1 hW2 chief
        c hpivot hi⟩

end OddOrder.Peterfalvi.S15


