-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_MaximalIII_IV
-- name    : OddOrder_Peterfalvi_S13_MaximalIII_IV
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:41:29.865553+00:00
-- url     : https://prove2.me/theorems/17ca26f6-6d5f-4e63-96e1-0cab81cebda0
-- title:
--   Peterfalvi §13: maximal types III and IV (continuation)
-- statement:
--   A continuation file for the §13 analysis of maximal subgroups of types III and IV, with the vanishing of Dade images on the exceptional set, a cross-orthogonality of certain-type columns, and the dichotomy for case (b) members.
--
--   Main declarations: `tau_apply_eq_zero_of_mem_typePV` (The §12 Dade image of an `A(M)`-supported function vanishes on the exceptional set `V`); `certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP` ((5.2.e) certain-type column vs irreducible break cross-orthogonality, §12 form); `caseB_sOf_member_dichotomy` (caseB member dichotomy); `caseB_sOf_memberRFamily` (Per-member orthonormal `R`-family over `𝒮(H₀C′)`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_MaximalIII_IV.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_MaximalIII_IV.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeSubcoherent
import Definitions.Def_OddOrder_Peterfalvi_S08_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S13_Lemmas113To115

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The §12 Dade image of an `A(M)`-supported function vanishes on the exceptional set `V`**
(the §12 analogue of `tau_apply_eq_zero_of_mem_ticVdiffV`, by a *different* route — issue 1019
update⁷³/⁷⁴): for `α` supported on `A(M) = (M')^#` and `v ∈ (ticVdiff h46).V = W ∖ (W₁ ∪ W₂) =
typePV M`, the image `α^τ` vanishes at `v`.

Unlike the Sibley case (where `V` avoids the Dade support and the image vanishes for lack of a
base point), here `V^M ⊆ A₀(M)` — `v` **is** a Dade base point.  The explicit (2.5) evaluation
(`dadeValue_eq` with the witness `a = v`, `h = 1`) gives `α^τ(v) = α(v)`, which vanishes because
`v ∉ M'` (`typePData_typePV_not_mem_derived`) while `α` is supported on `(M')^# ⊆ M'`.  This is
the anchor of the §12 cross-orthogonality `R(μ_j) ⊥ R(χ)` (the `hortho_mem` input of the (9.11)
column-pair adjunction). -/
theorem tau_apply_eq_zero_of_mem_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    {α : ClassFunction ↥M ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.GroupTheory.typePA M hyp.typeP) M)
    {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).V) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) α v = 0 := by
  have := hyp.finiteG
  classical
  refine OddOrder.Peterfalvi.S06.dadeICM_apply_eq_zero_of_mem_ticVdiffV
    (hyp.toHypothesis46 hG hG.odd) ?_ ?_ hv
  · exact hαsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  · intro z hz
    by_contra hne
    have hmem := hαsupp (ClassFunction.mem_support.mpr hne)
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
      OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG] at hmem
    exact hz (Subgroup.mem_subgroupOf.mpr hmem.1)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) certain-type column vs irreducible break cross-orthogonality, §12 form**
`R(μ_j) ⊥ R(χ)` — the §12 (`A₀(M)`-Dade) analogue of
`certainTypeR_imageSet_orthogonal_dadeOfDiff` (S08_CaseBHortho, Sibley world).  The proof is a
mirror: the disjointness machine (`inner_smul_chiFam_eq_zero_of_diff_vanishOnV` on
`ticVdiff (toHypothesis46 …)`) and the two-element `R(χ)` capture are `h46`-generic; the single
Sibley-specific anchor — vanishing of `(χ − χ̄)^τ` on the exceptional `V` — is replaced by the
§12 anchor `tau_apply_eq_zero_of_mem_typePV` (base-point evaluation, `V^M ⊆ A₀`).  The conjugate
difference is `A(M)`-supported (`hdiffsuppχA`, feeding the anchor) and `A₀(M)`-supported
(`hdiffsuppχ`, defining the Dade image family `R(χ)`).  This is the `hortho_mem` core of the
(9.11) column-pair adjunction. -/
theorem certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    {χ₂ : ((hyp.toHypothesis46 hG hG.odd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hG.odd).W1 ⊔ (hyp.toHypothesis46 hG hG.odd).W2)) →* ℂˣ}
    (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, (((hyp.toHypothesis46 hG hG.odd).columnFamily χ₂).mu i
        : ClassFunction ↥M ℂ) 1)
      = (∑ i, (((hyp.toHypothesis46 hG hG.odd).columnFamily χ₂⁻¹).mu i
        : ClassFunction ↥M ℂ) 1))
    (χ : IrreducibleCharacter ↥M)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥M ℂ))
    (hdiffsuppχA : (((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)
      : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.GroupTheory.typePA M hyp.typeP) M)
    (hdiffsuppχ : (((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)
      : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.GroupTheory.typePA0 M hyp.typeP) M) :
    ∀ α ∈ (OddOrder.Peterfalvi.S06.certainTypeR (hyp.toHypothesis46 hG hG.odd)
        hχ₂ hdeg).imageSet,
    ∀ β ∈ (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
      χ hrealχ hdiffsuppχ).imageSet,
      ClassFunction.inner α β = 0 := by
  have := hyp.finiteG
  classical
  -- The whole argument is now the general (5.2.e) mixed-stratum theorem
  -- (`S08_CrossOrthogonality`); the only §12-specific input is the anchor: `(χ − χ̄)^τ` vanishes
  -- on the `ticVdiff`-exceptional set `V` (base-point evaluation, `V^M ⊆ A₀`).
  have hsuppsub : (((χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj
      : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (OddOrder.GroupTheory.typePA M hyp.typeP) M := by
    rw [show (χ : ClassFunction ↥M ℂ) - (χ : ClassFunction ↥M ℂ).conj =
        -((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)) by abel,
      ClassFunction.support_neg]
    exact hdiffsuppχA
  exact OddOrder.Peterfalvi.S08.certainTypeR_imageSet_orthogonal_dadeOfDiff_of_vanishOnV
    (hyp.toHypothesis46 hG hG.odd) hχ₂ hdeg hyp.dadeData.dade χ hrealχ hdiffsuppχ
    (fun v hv => tau_apply_eq_zero_of_mem_typePV hG hyp hsuppsub hv)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **caseB member dichotomy** (the `hcover` core of the (9.11) chain fold): under the caseB
uniform degree (`hunif`, every `𝒮(H₀C′)`-member has degree `d`), each member either lies in the
degree-`d` irreducible cut, or is a nontrivial μ-grid column sum
(`reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` + the world-join
`muGrid_columnSum_eq_columnSum`). -/
theorem caseB_sOf_member_dichotomy [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    φ ∈ {ψ : ClassFunction ↥M ℂ | ψ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime ∧
        IsIrreducibleCharacter ψ ∧ ((ψ : ↥M → ℂ) 1 = (d : ℂ))} ∨
      ∃ k : Fin hyp.base.w2, k ≠ 0 ∧
        φ = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) := by
  have := hyp.base.finiteG
  classical
  by_cases hirr : IsIrreducibleCharacter φ
  · exact Or.inl ⟨hφ, hirr, hunif φ hφ⟩
  · right
    have hφIKF : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.H0Cprime.subgroupOf M) := by
      have h := hyp.sOf_subset_SOf hyp.H0Cprime hφ
      rwa [hyp.SOf_eq] at h
    obtain ⟨k, hk0, hkeq⟩ := hyp.base.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum hG
      hφIKF hirr
    exact ⟨k, hk0, hkeq.trans (hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k)⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Per-member orthonormal `R`-family over `𝒮(H₀C′)`** (the raw (5.2.d) datum for the
norm-general (5.7) engine `uniform_degree_coherence_of_families`).  The caseB member dichotomy
(`caseB_sOf_member_dichotomy`) splits every member into an irreducible (degree `d`) or a
certain-type
column sum `μ_k`; the `R`-family is dispatched accordingly:

* **irreducible `η`** — the 2-element signed Dade family `dadeOrthonormalCharacterImageFamilyOfDiff`
  (`hyp.base.tau (η − η̄) = ε·(μ − ν)`);
* **column `η = μ_k`** — the `2q`-element certain-type family `S06.certainTypeR` at
  `χ₂ = muColumnChar k` (`hyp.base.tau (μ_k − μ̄_k) = ∑ R(μ_k)`).

Both land *definitionally* on `hyp.base.tau = dadeIntegralCharacterMap h.dade0 h.tau` (the
`toHypothesis46` unfolding), so no `congrMap` seam.  The column case rebuilds the family at the
abstract member `η` (rather than `▸`-transporting) by reusing the `η`-independent
`imageSet`/`orthonormal`/`mem_ZIrr` fields of `certainTypeR` and re-proving `image_eq` through the
dichotomy equality `η = columnSum h χ₂` — so `(caseB_sOf_memberRFamily …).imageSet` is
*definitionally* `certainTypeR.imageSet`, the form the (5.2.e) cross-orthogonality lemmas
consume. -/
noncomputable def caseB_sOf_memberRFamily [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily hyp.base.tau η := by
  haveI := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- bridge to the `⊥`-kernel induced family (for support / no-real facts)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hη
    rw [hyp.SOf_eq] at h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  by_cases hirr : IsIrreducibleCharacter η
  · -- irreducible: the signed Dade family
    have hreal : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
        (⊥ : Subgroup ↥M) hηIKF0
    have hdiffsupp := OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0
    exact OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
      hyp.base.dadeData.dade ⟨η, hirr⟩ hreal hdiffsupp
  · -- column: rebuild `certainTypeR` at the abstract member `η` (data extracted by choice)
    have hex := (caseB_sOf_member_dichotomy hG hyp d hunif hη).resolve_left
      (fun h => hirr h.2.1)
    let k := hex.choose
    have hk0 : k ≠ 0 := hex.choose_spec.1
    have hkeq : η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k) := hex.choose_spec.2
    exact OddOrder.Peterfalvi.S06.columnR (hyp.base.toHypothesis46 hG hG.odd)
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0) hkeq

set_option backward.isDefEq.respectTransparency false in
/-- **`caseB_sOf_memberRFamily` reduction, irreducible case**: for an irreducible member `η`, the
dispatched `R`-family *is* `dadeOrthonormalCharacterImageFamilyOfDiff` (imageSet form).  The
realness and support proofs are existential (proof-irrelevant inputs to a proof-independent
`imageSet`), so the (5.2.e) `dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` lemma applies to
`(caseB_sOf_memberRFamily …).imageSet` after rewriting. -/
theorem caseB_sOf_memberRFamily_imageSet_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hirr : IsIrreducibleCharacter η) :
    ∃ (hr : ¬ ClassFunction.IsReal (η : ClassFunction ↥M ℂ))
      (hs : ((η : ClassFunction ↥M ℂ).conj - (η : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typePA0 M hyp.base.typeP) M),
      (caseB_sOf_memberRFamily hG hyp d hunif hη).imageSet =
        (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.base.dadeData.dade ⟨η, hirr⟩ hr hs).imageSet := by
  have := hyp.base.finiteG
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hηIKF0 : η ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hη)
  refine ⟨OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd
      (⊥ : Subgroup ↥M) hηIKF0,
    OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hηIKF0, ?_⟩
  unfold caseB_sOf_memberRFamily
  rw [dif_pos hirr]

set_option backward.isDefEq.respectTransparency false in
/-- **`caseB_sOf_memberRFamily` reduction, column case**: for a reducible member `η`, the dispatched
`R`-family *is* `certainTypeR` at the certain-type column `χ₂ = muColumnChar k` (imageSet form),
for the internally-chosen column index `k` (exposed existentially together with the membership
equation `η = columnSum h χ₂`, which supplies the `≠`-side conditions of the μ×μ / μ×irr
cross-orthogonality). -/
theorem caseB_sOf_memberRFamily_imageSet_of_col [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {η : ClassFunction ↥M ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hcol : ¬ IsIrreducibleCharacter η) :
    ∃ (k : Fin hyp.base.w2) (hk0 : k ≠ 0),
      η = OddOrder.Peterfalvi.S06.columnSum (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar hG hG.odd k) ∧
      (caseB_sOf_memberRFamily hG hyp d hunif hη).imageSet =
        (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd k)).symm).imageSet := by
  have := hyp.base.finiteG
  have hex := (caseB_sOf_member_dichotomy hG hyp d hunif hη).resolve_left (fun h => hcol h.2.1)
  refine ⟨hex.choose, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold caseB_sOf_memberRFamily
  rw [dif_neg hcol]
  rfl

set_option maxHeartbeats 1600000 in
-- the `dadeData.dade`-support defeq (`supportInSubgroup A L =?= typePA0`) is feasible but
-- expensive; discharging it once here keeps it out of the larger `hRorth` proof
/-- **irr × irr `R`-family orthogonality, typeP form**: the §12/§13 specialization of the generic
`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal` to `hyp.dadeData.dade` with the typePA0
supports, isolating the (feasible-but-expensive) `dadeData.dade`-support defeq in one focused lemma
(so the (5.2.e) `hRorth` case split does not re-pay it under its large local context). -/
theorem dadeOfDiff_orthogonal_dadeOfDiff_typeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (x χ : IrreducibleCharacter ↥M)
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction ↥M ℂ))
    (hxdiffsupp : ((x : ClassFunction ↥M ℂ).conj - (x : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA0 M hyp.typeP) M)
    (hχreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥M ℂ))
    (hχdiffsupp : ((χ : ClassFunction ↥M ℂ).conj - (χ : ClassFunction ↥M ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA0 M hyp.typeP) M)
    (hxχ : ClassFunction.inner (x : ClassFunction ↥M ℂ) (χ : ClassFunction ↥M ℂ) = 0)
    (hxχbar : ClassFunction.inner (x : ClassFunction ↥M ℂ) (χ : ClassFunction ↥M ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner (x : ClassFunction ↥M ℂ).conj (χ : ClassFunction ↥M ℂ) = 0)
    (hxbarχbar :
      ClassFunction.inner (x : ClassFunction ↥M ℂ).conj (χ : ClassFunction ↥M ℂ).conj = 0) :
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
      x hxreal hxdiffsupp).Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp.dadeData.dade
        χ hχreal hχdiffsupp) :=
  OddOrder.Peterfalvi.S08.dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
    hyp.dadeData.dade hxreal hxdiffsupp hχreal hχdiffsupp
    hxχ hxχbar hxbarχ hxbarχbar

set_option maxHeartbeats 1600000 in
-- the `2×2` dichotomy case split repeatedly matches the reduced dispatched families against the
-- (5.2.e) lemmas through the `hyp.base.tau = dadeIntegralCharacterMap` defeq
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.2.e) cross-orthogonality of the dispatched `R`-families over `𝒮(H₀C′)`** (the `hRorth`
input of the norm-general (5.7) engine).  For members `φ, ξ` with `⟨φ, ξ⟩ = ⟨φ, ξ̄⟩ = 0`, the
`R`-families `R(φ) ⊥ R(ξ)` — a `2×2` case split on the member dichotomy (irreducible / column):

* **irr × irr** — `dadeOfDiff_orthogonal_dadeOfDiff_typeP`; the two extra scalars
  `⟨φ̄, ξ⟩`, `⟨φ̄, ξ̄⟩` are `star`-conjugates of `⟨φ, ξ̄⟩`, `⟨φ, ξ⟩` (`inner_conj_conj`), so `0`;
* **irr × column** / **column × irr** — `certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP`
  (the irr-on-left order via an `inner_conj_symm` swap);
* **column × column** — `certainTypeR_imageSet_orthogonal_certainTypeR`, whose `χ₂ ≠ χ₂'` and
  `χ₂ ≠ χ₂'⁻¹` side conditions come from `⟨φ, ξ⟩ = 0` and `⟨φ, ξ̄⟩ = 0`: if `χ₂ = χ₂'` then `φ = ξ`
  and `⟨φ, φ⟩ = w₁ ≠ 0`; if `χ₂ = χ₂'⁻¹` then `φ = ξ̄` (`columnSum_conj_eq`) and `⟨φ, ξ̄⟩ = w₁`. -/
theorem caseB_sOf_memberRFamily_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {φ ξ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (hξ : ξ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (h1 : ClassFunction.inner φ ξ = 0) (h2 : ClassFunction.inner φ ξ.conj = 0) :
    (caseB_sOf_memberRFamily hG hyp d hunif hφ).Orthogonal
      (caseB_sOf_memberRFamily hG hyp d hunif hξ) := by
  have := hyp.base.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- typePA support for an irreducible member (needed by the μ×irr cross-orthogonality)
  have hIrrPA : ∀ {ζ : ClassFunction ↥M ℂ},
      ζ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      ((ζ.conj - ζ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.GroupTheory.typePA M hyp.base.typeP) M) := by
    intro ζ hζ
    have hζIKF0 : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
        (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hζ)
    refine OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support ?_ hζIKF0
    intro y hyK hy1
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
      OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG]
    exact ⟨Subgroup.mem_subgroupOf.mp hyK,
      fun h => hy1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h))⟩
  -- self-norm `w₁ ≠ 0` of a column sum (for the μ×μ `≠`-conditions)
  have hw1ne : (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (NeZero.ne _)
  intro α hα β hβ
  by_cases hφirr : IsIrreducibleCharacter φ <;> by_cases hξirr : IsIrreducibleCharacter ξ
  · -- irr × irr
    obtain ⟨hrφ, hsφ, hφeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    have hbarχ : ClassFunction.inner φ.conj ξ = 0 := by
      rw [← ClassFunction.conj_conj ξ, inner_conj_conj, h2, star_zero]
    have hbarχbar : ClassFunction.inner φ.conj ξ.conj = 0 := by
      rw [inner_conj_conj, h1, star_zero]
    exact dadeOfDiff_orthogonal_dadeOfDiff_typeP hG hyp.base ⟨φ, hφirr⟩ ⟨ξ, hξirr⟩
      hrφ hsφ hrξ hsξ h1 h2 hbarχ hbarχbar α hα β hβ
  · -- irr × column
    obtain ⟨hrφ, hsφ, hφeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hφ hφirr
    obtain ⟨k, hk0, hkeq, hξeq⟩ := caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    rw [inner_conj_symm β α]
    rw [certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨φ, hφirr⟩ hrφ (hIrrPA hφ) hsφ β hβ α hα, star_zero]
  · -- column × irr
    obtain ⟨k, hk0, hkeq, hφeq⟩ := caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hφ hφirr
    obtain ⟨hrξ, hsξ, hξeq⟩ := caseB_sOf_memberRFamily_imageSet_of_irr hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    exact certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd k)).symm
      ⟨ξ, hξirr⟩ hrξ (hIrrPA hξ) hsξ α hα β hβ
  · -- column × column
    obtain ⟨kφ, hkφ0, hkφeq, hφeq⟩ :=
      caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hφ hφirr
    obtain ⟨kξ, hkξ0, hkξeq, hξeq⟩ :=
      caseB_sOf_memberRFamily_imageSet_of_col hG hyp d hunif hξ hξirr
    rw [hφeq] at hα
    rw [hξeq] at hβ
    set h46 := hyp.base.toHypothesis46 hG hG.odd with hh46
    -- `χ₂ ≠ χ₂'`: else `φ = ξ` and `⟨φ, φ⟩ = w₁ ≠ 0` contradicts `h1`
    have hne1 : hyp.base.muColumnChar hG hG.odd kφ ≠ hyp.base.muColumnChar hG hG.odd kξ := by
      intro heq
      have hφξ : φ = ξ := by rw [hkφeq, hkξeq, heq]
      rw [hφξ, hkξeq, OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h1
      exact hw1ne h1
    -- `χ₂ ≠ χ₂'⁻¹`: else `φ = ξ̄` and `⟨φ, ξ̄⟩ = w₁ ≠ 0` contradicts `h2`
    have hne2 : hyp.base.muColumnChar hG hG.odd kφ ≠ (hyp.base.muColumnChar hG hG.odd kξ)⁻¹ := by
      intro heq
      have hφξc : φ = ξ.conj := by
        rw [hkφeq, heq, ← OddOrder.Peterfalvi.S06.columnSum_conj_eq, hkξeq]
      rw [hφξc, hkξeq, OddOrder.Peterfalvi.S06.columnSum_conj_eq,
        OddOrder.Peterfalvi.S06.columnSum_def,
        OddOrder.Peterfalvi.S06.columnFamily_mu_sum_inner, if_pos rfl] at h2
      exact hw1ne h2
    exact OddOrder.Peterfalvi.S06.certainTypeR_imageSet_orthogonal_certainTypeR h46
      (hyp.base.muColumnChar_ne_one hG hG.odd hkφ0) (hyp.base.muColumnChar_ne_one hG hG.odd hkξ0)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46
        (hyp.base.muColumnChar hG hG.odd kφ)).symm
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one h46
        (hyp.base.muColumnChar hG hG.odd kξ)).symm
      hne1 hne2 α hα β hβ

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Uniform anchor-difference support over `𝒮(H₀C′)`** (the `hdegS₁diff` supply of every (9.11)
chain step, uniform over the whole family): under the caseB uniform degree (`hunif`), the
difference of any member against the anchor `χ₁ ∈ 𝒮(H₀C′)` is `A₀`-supported — both are
`S(⊥)`-members of equal degree, so `inducedKernelFamily_scaledDiff_support` applies at `d = 1`.
Since every chain accumulator `S₁ = pairUnion S₀ pair i` is a subfamily of `𝒮(H₀C′)`, this one
lemma feeds `hdegS₁diff` at every step. -/
theorem sOf_anchor_diff_support [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (d : ℕ)
    (hunif : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      (φ : ClassFunction ↥M ℂ) 1 = (d : ℂ))
    {χ₁ : ClassFunction ↥M ℂ}
    (hχ₁mem : χ₁ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    {x : ClassFunction ↥M ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) :
    ((x - χ₁ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
  have := hyp.base.finiteG
  classical
  have hIKF : ∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime,
      y ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun y hy => by
    have h := hyp.sOf_subset_SOf hyp.H0Cprime hy
    rw [hyp.SOf_eq] at h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h
  have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
    hyp.base.mderivSharp_subset_A0 (hIKF x hx) (hIKF χ₁ hχ₁mem) (d := 1)
    (by rw [Nat.cast_one, one_mul, hunif x hx, hunif χ₁ hχ₁mem])
  rwa [one_smul] at h

end OddOrder.Peterfalvi.S13


