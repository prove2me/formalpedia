-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_MuColumnPin
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_MuColumnPin
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:31:20.326184+00:00
-- url     : https://prove2.me/theorems/e2288a1d-2334-478e-821a-90b57f6809bf
-- title:
--   Peterfalvi (13.3.c): the $\mu$-column pin machinery
-- statement:
--   Formalizes the main part of (13.3.c): a (9.11)-coherent extension $\tau_1$ of the honest §9 family on $\tau=\mathrm{Ind}_S^G$ sends the reducible prime-TI column sums to prescribed values.
--
--   Main declarations: `Hypothesis.muColumn_not_irreducible` (A `μ`-column sum is not irreducible); `Hypothesis.coherentIndS_muColumn_diff` (`τ₁` column-difference identity, coherence-generic); `Hypothesis.coherentIndS_extension_irr_vanish_regular` (The coherent image of an irreducible `𝒮`-member vanishes on the saturated regular set); `Hypothesis.coherentIndS_muColumn_vanish_regular` (The coherent image of a reducible `μ`-column vanishes on the saturated regular set, given an…).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/MuColumnPin.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/MuColumnPin.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseBReducibleCoherence
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CoherenceEtaOrthogonality

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **A `μ`-column sum is not irreducible**: `⟨μ_j, μ_j⟩ = q ≠ 1` (`muColumn_inner_self`), while
irreducible characters have norm `1`. -/
theorem Hypothesis.muColumn_not_irreducible [Finite G] (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) :
    ¬ IsIrreducibleCharacter (∑ i : Fin hyp.q, hyp.mu i j) := by
  have := hyp.finiteG
  intro hirr
  have h1 := hirr.inner_self_eq_one
  rw [hyp.muColumn_inner_self j] at h1
  have : hyp.q = 1 := by exact_mod_cast h1
  exact absurd (this ▸ hyp.q_prime) Nat.not_prime_one

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`τ₁` column-difference identity, coherence-generic** (issue 2035 更新 #11/#17, the (13.3.c)
column-independence): *any* coherent extension `c` of `𝒮 = sSet` on `Ind_S^G` sends the reducible
column difference to the aligned `η`-column difference,
`c(∑ᵢ μ_{ij}) − c(∑ᵢ μ_{ik}) = (∑ᵢ η_{ij}) − (∑ᵢ η_{ik})`, for distinct nonzero `j ≠ k`.
`c` agrees with `Ind_S^G` on the `A(S)`-supported column difference (`extends_on_supported`),
which is the honest Dade image (`sInstance_dade_eq_induce`), evaluated by
`dadeHypS_muColumn_diff`. -/
theorem Hypothesis.coherentIndS_muColumn_diff [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    {j k : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) (hk : k ≠ ⟨0, hyp.p_prime.pos⟩)
    (hjk : j ≠ k) :
    c.extension (∑ i : Fin hyp.q, hyp.mu i j) - c.extension (∑ i : Fin hyp.q, hyp.mu i k)
      = (∑ i : Fin hyp.q, hyp.eta i j) - (∑ i : Fin hyp.q, hyp.eta i k) := by
  classical
  have := hyp.finiteG
  have hmemSpan : ((∑ i : Fin hyp.q, hyp.mu i j) - (∑ i : Fin hyp.q, hyp.mu i k)) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (sSet (hyp.toTypesIIIIIIVSetupS hG))
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S) :=
    ⟨Submodule.sub_mem _
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)))
      (Submodule.subset_span (sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief k hk))),
      hyp.muColumn_diff_supported hG chief hj hk⟩
  rw [← map_sub, c.extends_on_supported _ hmemSpan, hyp.indS_apply,
    ← hyp.sInstance_dade_eq_induce hG hnoV (hyp.muColumn_diff_supported hG chief hj hk),
    hyp.dadeHypS_muColumn_diff hG hnoV chief hj hk hjk, Finset.sum_sub_distrib]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The coherent image of an irreducible `𝒮`-member vanishes on the saturated regular set**
(Coq `ortho_cycTIiso_vanish`, the `zetaV0` step of `coherent_prDade_TIred`): `c(ξ)` is orthogonal
to the whole `η`-grid (`coherentIndS_image_inner_eta_eq_zero`), and the grid is complete on the
regular set `Ŵ = W ∖ (W₁ ∪ W₂)` ((3.2.d) `vanish_of_inner_eta_eq_zero`); conjugacy-invariance of
class functions saturates the vanishing to `Ŵ^G`. -/
theorem Hypothesis.coherentIndS_extension_irr_vanish_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    {ξ : ClassFunction ↥hyp.S ℂ} (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hξirr : IsIrreducibleCharacter ξ)
    {x : G} (hx : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))) :
    c.extension ξ x = 0 := by
  classical
  have := hyp.finiteG
  have hcrux := coherentIndS_image_inner_eta_eq_zero hG hnoV hyp
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG))
    (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG))
    (fun ζ hζ => by
      rw [show ζ - ζ.conj = -(ζ.conj - ζ) from by abel, ClassFunction.support_neg]
      exact hyp.sSet_member_conjDiff_supported hG hζ)
    c hξ hξirr
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  rw [← (c.extension ξ).of_isConj (isConj_iff.mpr ⟨g, hg⟩)]
  exact hyp.vanish_of_inner_eta_eq_zero (c.extension ξ)
    (fun i j => by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux i j, star_zero])
    hw.1 hw.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The coherent image of a reducible `μ`-column vanishes on the saturated regular set, given an
irreducible member** (the γ-trick of Coq `coherent_prDade_TIred`, `PFsection5.v:1371`): the
degree-`0` combination `γ = ξ(1)·μ_j − μ_j(1)·ξ ∈ ℤ[𝒮]` is `A(S)`-supported, so `c(γ)` is the
honest `A₀`-Dade image (`extends_on_supported` + `sInstance_dade0_eq_induce`), which vanishes on
`Ŵ^G` (`dadeS0_apply_eq_zero_of_regular`); `c(ξ)` also vanishes there
(`coherentIndS_extension_irr_vanish_regular`), and `ξ(1) ≠ 0` divides out. -/
theorem Hypothesis.coherentIndS_muColumn_vanish_regular [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    {ξ : ClassFunction ↥hyp.S ℂ} (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hξirr : IsIrreducibleCharacter ξ)
    {j : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩)
    {x : G} (hx : x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G)))) :
    c.extension (∑ i : Fin hyp.q, hyp.mu i j) x = 0 := by
  classical
  have := hyp.finiteG
  set μcol : ClassFunction ↥hyp.S ℂ := ∑ i : Fin hyp.q, hyp.mu i j with hμdef
  have hμmem : μcol ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
  -- integer degrees: `ξ(1) = nξ > 0`, `μ_j(1) = q·u`
  obtain ⟨nξ, hnξpos, hnξ, -⟩ := hξirr.exists_natDegree_charValue_one_dvd_card
  have hnξne : (nξ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnξpos.ne'
  have hμ1 : μcol 1 = ((hyp.q * hyp.u : ℕ) : ℂ) := by
    rw [hμdef]
    have := hyp.muColumn_apply_one hG j hj
    push_cast
    exact this
  -- the degree-0 combination `γ ∈ ℤ[𝒮]`
  set γ : ClassFunction ↥hyp.S ℂ := (nξ : ℤ) • μcol - ((hyp.q * hyp.u : ℕ) : ℤ) • ξ with hγdef
  have hγspan : γ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥hyp.S)
      (sSet (hyp.toTypesIIIIIIVSetupS hG)) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span hμmem))
      (Submodule.smul_mem _ _ (Submodule.subset_span hξ))
  have hγ1 : γ 1 = 0 := by
    rw [hγdef, ClassFunction.sub_apply, ← Int.cast_smul_eq_zsmul ℂ (nξ : ℤ) μcol,
      ← Int.cast_smul_eq_zsmul ℂ ((hyp.q * hyp.u : ℕ) : ℤ) ξ,
      ClassFunction.smul_apply, ClassFunction.smul_apply, hμ1, hnξ]
    push_cast
    ring
  -- `γ` is `A(S)`-supported: members are supported in `A(S) ∪ {1}` and `γ(1) = 0`
  have hγsupp : γ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
    intro z hz
    have hz0 : γ z ≠ 0 := hz
    have hz1 : z ≠ 1 := fun h => hz0 (h ▸ hγ1)
    have hmem : z ∈ μcol.support ∪ ξ.support := by
      by_contra hnot
      rw [Set.mem_union, not_or] at hnot
      apply hz0
      have hμz : μcol z = 0 := by
        by_contra h; exact hnot.1 (ClassFunction.mem_support.mpr h)
      have hξz : ξ z = 0 := by
        by_contra h; exact hnot.2 (ClassFunction.mem_support.mpr h)
      rw [hγdef, ClassFunction.sub_apply, ← Int.cast_smul_eq_zsmul ℂ (nξ : ℤ) μcol,
        ← Int.cast_smul_eq_zsmul ℂ ((hyp.q * hyp.u : ℕ) : ℤ) ξ,
        ClassFunction.smul_apply, ClassFunction.smul_apply, hμz, hξz]
      ring
    rcases hmem with h | h
    · rcases hyp.sSet_member_support_subset hG hμmem h with h' | h'
      · exact h'
      · exact absurd (Set.mem_singleton_iff.mp h') hz1
    · rcases hyp.sSet_member_support_subset hG hξ h with h' | h'
      · exact h'
      · exact absurd (Set.mem_singleton_iff.mp h') hz1
  have hγA0supp : γ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
    hγsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (S10.typePACore_subset_A0Set hyp.Sdata))
  -- `c(γ)` is the honest `A₀`-Dade image, vanishing at the regular `x`
  have hcγ : c.extension γ
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData) γ := by
    rw [c.extends_on_supported γ ⟨hγspan, hγsupp⟩, hyp.indS_apply,
      hyp.sInstance_dade0_eq_induce hG hnoV hγA0supp]
  have hcγx : c.extension γ x = 0 := by
    rw [hcγ]
    exact hyp.dadeS0_apply_eq_zero_of_regular hG hγsupp hx
  -- expand `c(γ) = nξ·c(μ_j) − (q·u)·c(ξ)` and divide by `nξ`
  have hsplit : c.extension γ
      = (nξ : ℂ) • c.extension μcol - ((hyp.q * hyp.u : ℕ) : ℂ) • c.extension ξ := by
    rw [hγdef, map_sub, map_zsmul, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℂ (nξ : ℤ) (c.extension μcol),
      ← Int.cast_smul_eq_zsmul ℂ ((hyp.q * hyp.u : ℕ) : ℤ) (c.extension ξ)]
    push_cast
    rfl
  have hξx : c.extension ξ x = 0 :=
    hyp.coherentIndS_extension_irr_vanish_regular hG hnoV c hξ hξirr hx
  have h0 : (nξ : ℂ) * c.extension μcol x = 0 := by
    have := hcγx
    rw [hsplit, ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.smul_apply,
      hξx] at this
    calc (nξ : ℂ) * c.extension μcol x
        = (nξ : ℂ) * c.extension μcol x - ((hyp.q * hyp.u : ℕ) : ℂ) * 0 := by ring
      _ = 0 := this
  exact (mul_eq_zero.mp h0).resolve_left hnξne

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (13.3.c), the `μ`-column pin dichotomy given an irreducible member** (Coq
`coherent_prDade_TIred`, `PFsection5.v:1371`; issue 2035 更新 #17): if `𝒮` contains an irreducible
`ξ`, then **any** coherent extension `c` of `𝒮` on `Ind_S^G` sends the reducible column sum
`μ_j = ∑_i μ_{ij}` (`j ≠ 0`) either to the aligned `η`-column `∑_i η_{ij}`, or to the *negated
conjugate* column `−∑_i η_{ik}` (`μ̄_j = ∑_i μ_{ik}`).

Route: the (5.5) `R`-family decomposition gives `c(μ_j) = ∑_{α ∈ E} α` with
`E ⊆ {η_{ij}} ∪ {−η_{ik}}`; the γ-trick vanishing (`coherentIndS_muColumn_vanish_regular`) feeds
the (3.7) exchange relation (`S16.inner_eta_grid_relation`), making the membership indicators
row-uniform; the isometry norm `‖c(μ_j)‖² = q` then forces `E` to be exactly one full column. -/
theorem Hypothesis.coherentIndS_muColumn_pin_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    {ξ : ClassFunction ↥hyp.S ℂ} (hξ : ξ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hξirr : IsIrreducibleCharacter ξ)
    {j : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    c.extension (∑ i : Fin hyp.q, hyp.mu i j) = ∑ i : Fin hyp.q, hyp.eta i j
    ∨ ∃ k : Fin hyp.p, k ≠ ⟨0, hyp.p_prime.pos⟩ ∧ k ≠ j ∧
        (∑ i : Fin hyp.q, hyp.mu i j : ClassFunction ↥hyp.S ℂ).conj
          = ∑ i : Fin hyp.q, hyp.mu i k ∧
        c.extension (∑ i : Fin hyp.q, hyp.mu i j) = -∑ i : Fin hyp.q, hyp.eta i k := by
  classical
  have := hyp.finiteG
  set μcol : ClassFunction ↥hyp.S ℂ := ∑ i : Fin hyp.q, hyp.mu i j with hμdef
  have hμmem : μcol ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sOf_subset_sSet _ chief.H0 (hyp.mu_colSum_mem_sOf_H0 hG chief j hj)
  have hμcmem : (μcol : ClassFunction ↥hyp.S ℂ).conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
    sSet_closedUnderConjugate _ hμmem
  have hμred : ¬ IsIrreducibleCharacter μcol := hμdef ▸ hyp.muColumn_not_irreducible j
  -- the conjugate column `k`
  obtain ⟨k, hk0, hkeq⟩ :=
    hyp.sSet_reducible_eq_muColumnSum hG hμcmem (hyp.sSet_reducible_conj_not_irr hμred)
  have hμcols : ∀ a b : Fin hyp.p,
      ClassFunction.inner (∑ i : Fin hyp.q, hyp.mu i a) (∑ i : Fin hyp.q, hyp.mu i b)
        = if a = b then (hyp.q : ℂ) else 0 := hyp.muColumn_inner
  have hqne : (hyp.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hyp.q_prime.pos.ne'
  have hkj : k ≠ j := by
    rintro rfl
    exact sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) hμmem
      (hkeq.trans hμdef.symm)
  -- the (5.5) `R`-family decomposition through the Dade-coherence transport
  have hagree : ∀ φ : ClassFunction ↥hyp.S ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.S)
        (sSet (hyp.toTypesIIIIIIVSetupS hG))
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S) →
      hyp.indS φ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData) φ := fun φ hφ => by
    rw [hyp.indS_apply, hyp.sInstance_dade_eq_induce hG hnoV hφ.2]
  obtain ⟨E, hEsub, hEsum⟩ :=
    hyp.sSet_coherent_extension_eq_sum_memberRFamily hG hnoV
      (Set.Subset.refl _) (c.congrMap hagree) hμmem hμcmem
  have hEsum' : c.extension μcol = ∑ α ∈ E, α := hEsum
  -- the `R`-family image set: `{η_{ij}} ∪ {−η_{ik}}`
  obtain ⟨j', k', hj'eq, hk'eq, himg⟩ :=
    hyp.sSet_memberRFamily_imageSet_of_red hG hnoV hμmem hμred
  have hj' : j' = j := by
    by_contra hne
    have h := hμcols j' j
    rw [if_neg hne, ← hj'eq, ← hμdef, hμdef, hμcols j j, if_pos rfl] at h
    exact hqne h
  have hk' : k' = k := by
    by_contra hne
    have h := hμcols k' k
    rw [if_neg hne, ← hk'eq, hkeq, hμcols k k, if_pos rfl] at h
    exact hqne h
  rw [hj', hk'] at himg
  have hEsubset : ∀ α ∈ E, (∃ a : Fin hyp.q, α = hyp.eta a j) ∨
      (∃ a : Fin hyp.q, α = -hyp.eta a k) := by
    intro α hα
    have := hEsub hα
    rw [himg, Finset.mem_image] at this
    obtain ⟨x, -, rfl⟩ := this
    rcases x with a | a
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨a, rfl⟩
  -- grid inner products of the members of `E`
  have hη := OddOrder.Peterfalvi.S16.eta_orthonormal hyp
  -- `⟨c(μ_j), η_{ab}⟩` as a membership indicator
  have hcoef_j : ∀ a : Fin hyp.q,
      ClassFunction.inner (c.extension μcol) (hyp.eta a j)
        = if hyp.eta a j ∈ E then 1 else 0 := by
    intro a
    rw [hEsum', OddOrder.RepresentationTheory.inner_sum_left]
    rw [show (∑ α ∈ E, ClassFunction.inner α (hyp.eta a j))
        = ∑ α ∈ E, (if α = hyp.eta a j then (1 : ℂ) else 0) from
      Finset.sum_congr rfl fun α hα => by
        rcases hEsubset α hα with ⟨a', rfl⟩ | ⟨a', rfl⟩
        · rw [hη a' a j j]
          by_cases haa : a' = a
          · subst haa; rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
          · rw [if_neg (fun h => haa h.1), if_neg (fun h => haa (by
              have := congrArg (fun f => ClassFunction.inner f (hyp.eta a j)) h
              rw [hη a' a j j, hη a a j j, if_pos (⟨rfl, rfl⟩ : a = a ∧ j = j),
                if_neg (fun hh => haa hh.1)] at this
              exact absurd this zero_ne_one))]
        · rw [ClassFunction.inner_neg_left, hη a' a k j, if_neg (fun h => hkj h.2), neg_zero,
            if_neg (fun h => by
              have := congrArg (fun f => ClassFunction.inner f (hyp.eta a j)) h
              rw [ClassFunction.inner_neg_left, hη a' a k j, if_neg (fun hh => hkj hh.2),
                neg_zero, hη a a j j, if_pos ⟨rfl, rfl⟩] at this
              exact absurd this zero_ne_one)]]
    rw [Finset.sum_ite_eq' E (hyp.eta a j) (fun _ => (1 : ℂ))]
  have hcoef_k : ∀ a : Fin hyp.q,
      ClassFunction.inner (c.extension μcol) (hyp.eta a k)
        = if -hyp.eta a k ∈ E then -1 else 0 := by
    intro a
    rw [hEsum', OddOrder.RepresentationTheory.inner_sum_left]
    rw [show (∑ α ∈ E, ClassFunction.inner α (hyp.eta a k))
        = ∑ α ∈ E, (if α = -hyp.eta a k then (-1 : ℂ) else 0) from
      Finset.sum_congr rfl fun α hα => by
        rcases hEsubset α hα with ⟨a', rfl⟩ | ⟨a', rfl⟩
        · rw [hη a' a j k, if_neg (fun h => hkj h.2.symm), if_neg (fun h => by
            have := congrArg (fun f => ClassFunction.inner f (hyp.eta a k)) h
            rw [hη a' a j k, if_neg (fun hh => hkj hh.2.symm),
              ClassFunction.inner_neg_left, hη a a k k, if_pos ⟨rfl, rfl⟩] at this
            exact absurd this (by norm_num))]
        · rw [ClassFunction.inner_neg_left, hη a' a k k]
          by_cases haa : a' = a
          · subst haa; rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
          · rw [if_neg (fun h => haa h.1), neg_zero, if_neg (fun h => haa (by
              have := congrArg (fun f => ClassFunction.inner f (hyp.eta a k)) h
              rw [ClassFunction.inner_neg_left, hη a' a k k, if_neg (fun hh => haa hh.1),
                neg_zero, ClassFunction.inner_neg_left, hη a a k k, if_pos ⟨rfl, rfl⟩] at this
              exact absurd this (by norm_num)))]]
    rw [Finset.sum_ite_eq' E (-hyp.eta a k) (fun _ => (-1 : ℂ))]
  have hcoef_0 : ∀ (a : Fin hyp.q) (b : Fin hyp.p), b ≠ j → b ≠ k →
      ClassFunction.inner (c.extension μcol) (hyp.eta a b) = 0 := by
    intro a b hbj hbk
    rw [hEsum', OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun α hα => ?_
    rcases hEsubset α hα with ⟨a', rfl⟩ | ⟨a', rfl⟩
    · rw [hη a' a j b, if_neg (fun h => hbj h.2.symm)]
    · rw [ClassFunction.inner_neg_left, hη a' a k b, if_neg (fun h => hbk h.2.symm), neg_zero]
  -- row-uniformity of the indicators through the (3.7) exchange relation
  have hvanish : ∀ x ∈ OddOrder.GroupTheory.conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      c.extension μcol x = 0 := fun x hx =>
    hyp.coherentIndS_muColumn_vanish_regular hG hnoV chief c hξ hξirr hj hx
  have hj0 : (⟨0, hyp.p_prime.pos⟩ : Fin hyp.p) ≠ j := fun h => hj h.symm
  have hk0' : (⟨0, hyp.p_prime.pos⟩ : Fin hyp.p) ≠ k := fun h => hk0 h.symm
  have hrow : ∀ (a : Fin hyp.q) (b : Fin hyp.p),
      ClassFunction.inner (c.extension μcol) (hyp.eta a b)
        = ClassFunction.inner (c.extension μcol) (hyp.eta ⟨0, hyp.q_prime.pos⟩ b) := by
    intro a b
    have hrel := OddOrder.Peterfalvi.S16.inner_eta_grid_relation hyp hvanish a b
    rw [hcoef_0 a ⟨0, hyp.p_prime.pos⟩ hj0 hk0',
      hcoef_0 ⟨0, hyp.q_prime.pos⟩ ⟨0, hyp.p_prime.pos⟩ hj0 hk0'] at hrel
    linear_combination hrel
  have hrow_j : ∀ a : Fin hyp.q,
      (hyp.eta a j ∈ E ↔ hyp.eta ⟨0, hyp.q_prime.pos⟩ j ∈ E) := by
    intro a
    have h := hrow a j
    rw [hcoef_j a, hcoef_j ⟨0, hyp.q_prime.pos⟩] at h
    by_cases h1 : hyp.eta a j ∈ E <;> by_cases h2 : hyp.eta ⟨0, hyp.q_prime.pos⟩ j ∈ E <;>
      simp only [h1, h2, if_pos, if_false] at h ⊢ <;>
      first
        | exact Iff.rfl
        | exact absurd h one_ne_zero
        | exact absurd h.symm one_ne_zero
  have hrow_k : ∀ a : Fin hyp.q,
      (-hyp.eta a k ∈ E ↔ -hyp.eta ⟨0, hyp.q_prime.pos⟩ k ∈ E) := by
    intro a
    have h := hrow a k
    rw [hcoef_k a, hcoef_k ⟨0, hyp.q_prime.pos⟩] at h
    by_cases h1 : -hyp.eta a k ∈ E <;> by_cases h2 : -hyp.eta ⟨0, hyp.q_prime.pos⟩ k ∈ E <;>
      simp only [h1, h2, if_pos, if_false] at h ⊢ <;>
      first
        | exact Iff.rfl
        | exact absurd h (by norm_num)
  -- the isometry norm `‖c(μ_j)‖² = q`
  have hnorm : ClassFunction.inner (c.extension μcol) (c.extension μcol) = (hyp.q : ℂ) := by
    rw [c.extension_inner_eq μcol μcol (Submodule.subset_span hμmem)
      (Submodule.subset_span hμmem), hμdef, hyp.muColumn_inner_self j]
  -- injectivity of the two column enumerations
  have hinj_j : Function.Injective (fun a : Fin hyp.q => hyp.eta a j) := by
    intro a a' h
    by_contra hne
    have := congrArg (fun f => ClassFunction.inner f (hyp.eta a' j)) h
    rw [hη a a' j j, hη a' a' j j, if_pos (⟨rfl, rfl⟩ : a' = a' ∧ j = j),
      if_neg (fun hh => hne hh.1)] at this
    exact zero_ne_one this
  have hinj_k : Function.Injective (fun a : Fin hyp.q => -hyp.eta a k) := by
    intro a a' h
    by_contra hne
    have := congrArg (fun f => ClassFunction.inner f (-hyp.eta a' k)) h
    simp only [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg] at this
    rw [hη a a' k k, hη a' a' k k, if_pos (⟨rfl, rfl⟩ : a' = a' ∧ k = k),
      if_neg (fun hh => hne hh.1)] at this
    exact zero_ne_one this
  -- endgame: four cases on the two base indicators
  by_cases hs : hyp.eta ⟨0, hyp.q_prime.pos⟩ j ∈ E <;>
    by_cases ht : -hyp.eta ⟨0, hyp.q_prime.pos⟩ k ∈ E
  · -- both columns in: `‖φ‖² = 2q`, contradiction
    exfalso
    have hEeq : E = Finset.image (Sum.elim (fun i : Fin hyp.q => hyp.eta i j)
        (fun i : Fin hyp.q => -hyp.eta i k)) Finset.univ := by
      apply Finset.Subset.antisymm
      · rw [← himg]; exact hEsub
      · intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨x, -, rfl⟩ := hα
        rcases x with a | a
        · exact (hrow_j a).mpr hs
        · exact (hrow_k a).mpr ht
    have hφeq : c.extension μcol
        = (∑ a : Fin hyp.q, hyp.eta a j) - ∑ a : Fin hyp.q, hyp.eta a k := by
      rw [hEsum', hEeq]
      rw [show Finset.image (Sum.elim (fun i : Fin hyp.q => hyp.eta i j)
            (fun i : Fin hyp.q => -hyp.eta i k)) Finset.univ
          = Finset.image (fun a : Fin hyp.q => hyp.eta a j) Finset.univ
            ∪ Finset.image (fun a : Fin hyp.q => -hyp.eta a k) Finset.univ from by
        ext α
        simp only [Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and,
          Sum.exists, Sum.elim_inl, Sum.elim_inr]]
      rw [Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro α hα hmem
        rw [Finset.mem_image] at hα hmem
        obtain ⟨a, -, rfl⟩ := hα
        obtain ⟨a', -, heq⟩ := hmem
        have := congrArg (fun f => ClassFunction.inner f (hyp.eta a j)) heq
        rw [ClassFunction.inner_neg_left, hη a' a k j, if_neg (fun hh => hkj hh.2), neg_zero,
          hη a a j j, if_pos (⟨rfl, rfl⟩ : a = a ∧ j = j)] at this
        exact zero_ne_one this)]
      rw [Finset.sum_image (fun a _ a' _ h => hinj_j h),
        Finset.sum_image (fun a _ a' _ h => hinj_k h), Finset.sum_neg_distrib]
      abel
    have h2q : ClassFunction.inner (c.extension μcol) (c.extension μcol)
        = (2 : ℂ) * (hyp.q : ℂ) := by
      rw [hφeq]
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hyp.etaColumn_inner_self j, hyp.etaColumn_inner_self k,
        hyp.etaColumn_inner j k, hyp.etaColumn_inner k j,
        if_neg (fun h => hkj h.symm), if_neg hkj]
      ring
    rw [hnorm] at h2q
    have : (hyp.q : ℂ) = 0 := by linear_combination -h2q
    exact hqne this
  · -- clean pin: `E` is the full `j`-column
    left
    have hEeq : E = Finset.image (fun a : Fin hyp.q => hyp.eta a j) Finset.univ := by
      apply Finset.Subset.antisymm
      · intro α hα
        rcases hEsubset α hα with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
        · exact absurd ((hrow_k a).mp hα) ht
      · intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨a, -, rfl⟩ := hα
        exact (hrow_j a).mpr hs
    rw [hEsum', hEeq, Finset.sum_image (fun a _ a' _ h => hinj_j h)]
  · -- flipped pin: `E` is the full negated `k`-column
    right
    refine ⟨k, hk0, hkj, hμdef ▸ hkeq, ?_⟩
    have hEeq : E = Finset.image (fun a : Fin hyp.q => -hyp.eta a k) Finset.univ := by
      apply Finset.Subset.antisymm
      · intro α hα
        rcases hEsubset α hα with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact absurd ((hrow_j a).mp hα) hs
        · exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      · intro α hα
        rw [Finset.mem_image] at hα
        obtain ⟨a, -, rfl⟩ := hα
        exact (hrow_k a).mpr ht
    rw [hEsum', hEeq, Finset.sum_image (fun a _ a' _ h => hinj_k h), Finset.sum_neg_distrib]
  · -- neither: `φ = 0`, contradicting `‖φ‖² = q`
    exfalso
    have hEeq : E = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro α hα
      rcases hEsubset α hα with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact hs ((hrow_j a).mp hα)
      · exact ht ((hrow_k a).mp hα)
    rw [hEsum', hEeq, Finset.sum_empty, ClassFunction.inner_zero_left] at hnorm
    exact hqne hnorm.symm

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The clean pivot pin propagates to all columns** (issue 2035 更新 #11, coherence-generic):
if `c(μ_1) = ∑_i η_{i1}` at the pivot column, then `c(μ_j) = ∑_i η_{ij}` for every nonzero `j`,
through the column-independence `coherentIndS_muColumn_diff`. -/
theorem Hypothesis.coherentIndS_muColumn_eq_etaColumn_of_pivot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (sSet (hyp.toTypesIIIIIIVSetupS hG))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    (hpivot : c.extension (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩)
      = ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩)
    {j : Fin hyp.p} (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    c.extension (∑ i : Fin hyp.q, hyp.mu i j) = ∑ i : Fin hyp.q, hyp.eta i j := by
  classical
  have := hyp.finiteG
  have hp1 : (⟨1, hyp.p_prime.one_lt⟩ : Fin hyp.p) ≠ ⟨0, hyp.p_prime.pos⟩ := by
    intro h; exact absurd (congrArg Fin.val h) one_ne_zero
  by_cases hjp : j = ⟨1, hyp.p_prime.one_lt⟩
  · subst hjp; exact hpivot
  · have hdiff := hyp.coherentIndS_muColumn_diff hG hnoV chief c hj hp1 hjp
    calc c.extension (∑ i : Fin hyp.q, hyp.mu i j)
        = (c.extension (∑ i : Fin hyp.q, hyp.mu i j)
            - c.extension (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩))
          + c.extension (∑ i : Fin hyp.q, hyp.mu i ⟨1, hyp.p_prime.one_lt⟩) := by abel
      _ = ((∑ i : Fin hyp.q, hyp.eta i j) - (∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩))
          + ∑ i : Fin hyp.q, hyp.eta i ⟨1, hyp.p_prime.one_lt⟩ := by rw [hdiff, hpivot]
      _ = ∑ i : Fin hyp.q, hyp.eta i j := by abel

end OddOrder.Peterfalvi.S15


