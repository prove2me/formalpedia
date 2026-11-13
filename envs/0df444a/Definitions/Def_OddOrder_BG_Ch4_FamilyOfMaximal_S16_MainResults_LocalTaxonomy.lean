-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_LocalTaxonomy
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_LocalTaxonomy
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:47:42.803668+00:00
-- url     : https://prove2.me/theorems/3bad0b04-bc56-4002-a82f-5b7bacdf46bb
-- title:
--   BG §16: Proposition 16.1, the local taxonomy predicates
-- statement:
--   The shared type I–V predicates and the Proposition 16.1 taxonomy layer of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §16, consumed by the Theorem I/II output file. It consists of lemmas only, including `proposition_type_classification_of_inputs`.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/LocalTaxonomy.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/LocalTaxonomy.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **§14/§15-independent assembly engine for BG Proposition 16.1** (mmd L4478; the source proof
runs over Theorems A(8)/B(1)(2)(3)(4)/C(1)(2)(3)(10)/D(1), Theorem 15.2(a), and Theorem 15.7(c)).
Proposition 16.1 is the bridge from the BG-local `κ`/`σ`/`M_F` taxonomy to the shared, bundled
Type I--V predicates; the genuinely gated content is the *construction* of each `TypeXData`
structure from the local classification.  This engine isolates those constructions (and the few
structural facts the source proof uses to combine them) as named hypotheses and discharges the full
six-clause conjunction `sorry`-free.  The §15--§16 structural theory has since landed, and the
wrapper `proposition_type_classification` cites it and applies this skeleton (the gated-endpoint
pattern, cf. `theoremD_msigma_conjugacy_and_centralizers_of_inputs`).

The named obligations, with their BG sources:

* the four **forward bridges** `hFI`/`hP2II`/`hP1neIIIIV`/`hP1eqV` — construct the Type
  I/II/III--IV/V data from the local classification (Theorem A(8)+B(1)(2)(3)+15.7(c) for I;
  C(1)(10)+B(1)(4)+A(8) for II; A(8)+Frattini for III/IV; 15.7(c) for V).  These are exactly the
  directions that `theoremI_nilpotentHall_conjugacy_and_type_dichotomy` and
  `theoremII_tame_embedding` consume;
* the four **reverse classifications** `hIF`/`hIIP2`/`hIIIIVP1`/`hVP1` — read off the local type
  from the Peterfalvi data (the `π(W₁) ⊆ κ(M)` argument for `→ M_P`, plus the `κ`/`M_F` refinement;
  Theorem C(2) for `I → M_F`);
* `hP_derived` (**Theorem C(3)**: `M' = U M_σ` for `M ∈ M_P`) and `hF_not_derived` (**Theorem
  A(3)**: `M = U M_σ ⊋ M'` for `M ∈ M_F`), which power clause (e);
* `h152a` (**Theorem 15.2(a)**: `M_F ≠ M_σ ⟹ M ∈ M_P₁`), used for clause (f).

The genuinely *derived* content (not a renamed hypothesis) is clauses (e) and (f), assembled from
the `κ`-trichotomy (`isTypeP_iff_isTypeP1_or_isTypeP2`, `isTypeF_iff_not_isTypeP`,
`not_isTypeP1_and_isTypeP2`) together with the bridges. -/
theorem proposition_type_classification_of_inputs {M : Subgroup G}
    (hFI : S14.IsTypeF M → OddOrder.GroupTheory.IsTypeI M)
    (hP2II : S14.IsTypeP2 M → OddOrder.GroupTheory.IsTypeII M)
    (hP1neIIIIV : S14.IsTypeP1 M → S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M →
      OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M)
    (hP1eqV : S14.IsTypeP1 M → S15.MF M = OddOrder.BG.Ch3.S10.Msigma M →
      OddOrder.GroupTheory.IsTypeV M)
    (hIF : OddOrder.GroupTheory.IsTypeI M → S14.IsTypeF M)
    (hIIP2 : OddOrder.GroupTheory.IsTypeII M → S14.IsTypeP2 M)
    (hIIIIVP1 : (OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) →
      S14.IsTypeP1 M ∧ S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hVP1 : OddOrder.GroupTheory.IsTypeV M →
      S14.IsTypeP1 M ∧ S15.MF M = OddOrder.BG.Ch3.S10.Msigma M)
    (hP_derived : S14.IsTypeP M →
      ∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M)
    (hF_not_derived : S14.IsTypeF M →
      ¬ ∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M)
    (h152a : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M → S14.IsTypeP1 M) :
    (OddOrder.GroupTheory.IsTypeI M ↔ S14.IsTypeF M) ∧
      (OddOrder.GroupTheory.IsTypeII M ↔ S14.IsTypeP2 M) ∧
      ((OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) ↔
        S14.IsTypeP1 M ∧ S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) ∧
      (OddOrder.GroupTheory.IsTypeV M ↔
        S14.IsTypeP1 M ∧ S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) ∧
      ((∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
          (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M) ↔
          ¬ OddOrder.GroupTheory.IsTypeI M) ∧
      (S15.MF M = OddOrder.BG.Ch3.S10.Msigma M ↔
        OddOrder.GroupTheory.IsTypeI M ∨ OddOrder.GroupTheory.IsTypeII M ∨
          OddOrder.GroupTheory.IsTypeV M) := by
  -- `¬ M_P₁ ⟹ M_F = M_σ`, the contrapositive of Theorem 15.2(a).
  have mf_eq_of_not_typeP1 :
      ¬ S14.IsTypeP1 M → S15.MF M = OddOrder.BG.Ch3.S10.Msigma M := by
    intro hnP1
    by_contra hne
    exact hnP1 (h152a hne)
  refine ⟨⟨hIF, hFI⟩, ⟨hIIP2, hP2II⟩, ⟨hIIIIVP1, fun h => hP1neIIIIV h.1 h.2⟩,
    ⟨hVP1, fun h => hP1eqV h.1 h.2⟩, ?_, ?_⟩
  · -- **(e)** `M' = U M_σ ⟺ ¬ Type I`.  Via (a) (`Type I ⟺ M_F`), this is `(∃U …) ⟺ M_P`.
    constructor
    · -- `→`: a Type I `M` would be `M_F` (`hIF`), contradicting Theorem A(3) (`hF_not_derived`).
      intro hex hI
      exact hF_not_derived (hIF hI) hex
    · -- `←`: `¬ Type I ⟹ ¬ M_F ⟹ M_P`, and Theorem C(3) (`hP_derived`) supplies the decomposition.
      intro hnI
      have hnF : ¬ S14.IsTypeF M := fun hF => hnI (hFI hF)
      have hP : S14.IsTypeP M := not_not.mp (by rwa [S14.isTypeF_iff_not_isTypeP] at hnF)
      exact hP_derived hP
  · -- **(f)** `M_F = M_σ ⟺ M` is Type I, II, or V.
    constructor
    · -- `→`: case on the `κ`-trichotomy.  `M_F` (`κ = ∅`) ⟹ I; `M_P₂` ⟹ II; `M_P₁`+`M_F = M_σ` ⟹ V.
      intro heq
      by_cases hP : S14.IsTypeP M
      · rcases S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
        · exact Or.inr (Or.inr (hP1eqV hP1 heq))
        · exact Or.inr (Or.inl (hP2II hP2))
      · exact Or.inl (hFI (S14.isTypeF_iff_not_isTypeP.mpr hP))
    · -- `←`: Type I ⟹ `M_F` ⟹ `¬ M_P₁` ⟹ `M_F = M_σ`; Type II ⟹ `M_P₂` ⟹ `¬ M_P₁` ⟹ `M_F = M_σ`;
      -- Type V carries `M_F = M_σ` directly (`hVP1`).
      rintro (hI | hII | hV)
      · have hnP : ¬ S14.IsTypeP M := S14.isTypeF_iff_not_isTypeP.mp (hIF hI)
        exact mf_eq_of_not_typeP1 (fun hP1 => hnP (S14.isTypeP_of_isTypeP1 hP1))
      · have hP2 := hIIP2 hII
        exact mf_eq_of_not_typeP1 (fun hP1 => S14.not_isTypeP1_and_isTypeP2 ⟨hP1, hP2⟩)
      · exact (hVP1 hV).2

/-- **Proposition 16.1 input `hF_not_derived` / BG Theorem A(3) contrapositive** (mmd L4290): a
type-`F` maximal subgroup `M` (`κ(M) = ∅`) has **no** `(κ ∪ σ)'`-Hall `U` with `M' = U M_σ`.
For type-`F`, `M = U M_σ` for *every* such `U` (`typeP_maximal_eq_kappaHall_sup_U_sup_Msigma` with
`K = ⊥`: the `⊥`-`κ`-Hall witness exists since `κ(M) = ∅`), so `M' = U M_σ` would force `M' = M`,
contradicting the proper derived subgroup `M' < M` of the nontrivial solvable `M`
(`Group.IsSolvable.commutator_lt_top_of_nontrivial`).  This is the `M ∈ ℳ_𝓕 ⟹ M' ⊊ M = U M_σ` half
powering Proposition 16.1 clause (e) (`M' = U M_σ ⟺ ¬ Type I`). -/
theorem typeF_not_exists_hall_derived_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hF : S14.IsTypeF M) :
    ¬ ∃ U : Subgroup G,
      Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
      derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
  rintro ⟨U, hUhall, hM'eq⟩
  have hkappa : S14.kappa M = ∅ := hF
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `U ≤ M' ≤ M`.
  have hUM : U ≤ M := by
    have h : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
    exact h.trans (Subgroup.map_subtype_le _)
  -- `⊥` is a `κ(M)`-Hall subgroup of `M` (type-`F`: `κ(M) = ∅`).
  have hK_bot : Ch03.IsHallSubgroup (S14.kappa M) ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
    intro p _
    rw [hkappa]; exact Set.notMem_empty p
  -- type-`F` decomposition `M = ⊥ ⊔ U ⊔ M_σ = U ⊔ M_σ`.
  have hMeq : M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
    have h := typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM bot_le hUM hK_bot hUhall
    rwa [bot_sup_eq] at h
  -- but `M' < M` (proper derived subgroup of the nontrivial solvable `M`).
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
      (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  have hlt : derivedInG M < M := by
    rw [derivedInG]
    conv_rhs => rw [← Subgroup.range_subtype M, MonoidHom.range_eq_map]
    rw [Subgroup.map_lt_map_iff_of_injective M.subtype_injective]
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥M)
  exact (ne_of_lt hlt) (hM'eq.trans hMeq.symm)

/-- **Proposition 16.1 input `hP_derived` / BG Theorem C(3)** (mmd L4307): a type-`P` maximal
subgroup `M` has a `(κ ∪ σ)'`-Hall `U` with `M' = U M_σ`.  Construct a `κ(M)`-Hall `K` and a
`(κ ∪ σ)'`-Hall `U` of the solvable `M` (Hall's theorem); `K ≠ ⊥` since `M` is type-`P`
(`isTypeF_of_isHall_kappa_eq_bot` would force `κ(M) = ∅`); then `typeP_hall_derived_eq_and_abelian`
(Theorem 14.7(h) + the three-Hall partition) gives `M' = U M_σ`.  Together with
`typeF_not_exists_hall_derived_eq` this supplies both directions of Proposition 16.1 clause (e)
(`M' = U M_σ ⟺ ¬ Type I`). -/
theorem typeP_exists_hall_derived_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : S14.IsTypeP M) :
    ∃ U : Subgroup G,
      Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) ∧
      derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- A `κ(M)`-Hall subgroup `K` of `M` (Hall's theorem in the solvable `M`).
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := hKdef ▸ Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    hKdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hKeq ▸ hK'
  -- A `(κ ∪ σ)'`-Hall subgroup `U` of `M`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    hUdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hUeq ▸ hU'
  -- `K ≠ ⊥`: else `M` would be type-`F` (`κ(M) = ∅`), contradicting `IsTypeP M`.
  have hKne : K ≠ ⊥ := fun h =>
    (S14.isTypeF_iff_not_isTypeP.mp (isTypeF_of_isHall_kappa_eq_bot hKM hK h)) hP
  exact ⟨U, hU, (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1⟩

/--
**Type-`F` Frobenius FPF against a `U₀`-element** (mmd L4486, the engine of `isTypeF_of_isTypeI`,
following the Coq `BGsection16` argument): a nontrivial `X ≤ U₀` of the Frobenius complement has
trivial `M_F`-centralizer, `M_F ⊓ C_G(X) = ⊥`. Any `M_F`-element `y` centralizing some
`x ∈ X# ⊆ U₀#`
lifts to `↥(M_F ⊔ U₀)`, where `frobenius_HU0` (kernel `M_F = H`, complement `U₀`) and
`centralizer_complement_le` place it in `U₀`; then `y ∈ M_F ⊓ U₀ = ⊥` (the `complement` field with
`U₀ ≤ U`). This is the `C_H(K) = 1` half of the BG argument, applied to a `U₀`-element `X ⊆ K`
rather
than to the `κ`-Hall `K` itself (which need not lie in `H ⊔ U₀`). -/
theorem typeFData_fitting_inf_centralizer_eq_bot [Finite G]
    {M : Subgroup G} (td : OddOrder.GroupTheory.TypeFData M) {X : Subgroup G}
    (hXU0 : X ≤ td.U0) (hXne : X ≠ ⊥) :
    td.H ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  classical
  -- `M_F ⊓ U₀ = ⊥` from the complement (`U₀ ≤ U`, `M_F.subgroupOf M ⊓ U.subgroupOf M = ⊥`).
  have hHU0 : td.H ⊓ td.U0 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzH, hzU0⟩ := Subgroup.mem_inf.mp hz
    have hzM : z ∈ M := td.H_le hzH
    have hmem : (⟨z, hzM⟩ : ↥M) ∈ (td.H.subgroupOf M) ⊓ (td.U.subgroupOf M) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_subgroupOf).mpr hzH,
        (Subgroup.mem_subgroupOf).mpr (td.U0_le hzU0)⟩
    rw [td.complement.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val hmem
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨x, hxX, hxne⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hXne (eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hc z hz))
  have hxU0 : x ∈ td.U0 := hXU0 hxX
  have hyHU0 : y ∈ td.H ⊔ td.U0 := Subgroup.mem_sup_left hyH
  have hxHU0 : x ∈ td.H ⊔ td.U0 := Subgroup.mem_sup_right hxU0
  -- `y` and `x` commute in `G` (`y ∈ C_G(X)`, `x ∈ X`).
  have hcomm : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hyC x hxX).symm
  -- lift to `↥(M_F ⊔ U₀)` and apply `centralizer_complement_le`.
  have hxmem : (⟨x, hxHU0⟩ : ↥(td.H ⊔ td.U0)) ∈ (td.U0).subgroupOf (td.H ⊔ td.U0) :=
    (Subgroup.mem_subgroupOf).mpr hxU0
  have hxne' : (⟨x, hxHU0⟩ : ↥(td.H ⊔ td.U0)) ≠ 1 := by
    rw [ne_eq, Subtype.ext_iff]; simpa using hxne
  have hymem : (⟨y, hyHU0⟩ : ↥(td.H ⊔ td.U0)) ∈
      Subgroup.centralizer ({(⟨x, hxHU0⟩ : ↥(td.H ⊔ td.U0))} : Set ↥(td.H ⊔ td.U0)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcomm
  have hyU0' := td.frobenius_HU0.centralizer_complement_le _ hxmem hxne' hymem
  have hyU0 : y ∈ td.U0 := (Subgroup.mem_subgroupOf).mp hyU0'
  rw [← hHU0]
  exact Subgroup.mem_inf.mpr ⟨hyH, hyU0⟩

/-- **Type-`F` `κ`-element placement** (mmd L4486, the Coq `Hall_superset` + `kappa_pi` step; the
last residual of `isTypeF_of_isTypeI`): from `p ∈ κ(M)` and the type-`F` datum, produce a nontrivial
`p`-subgroup `X ≤ U₀` (inside the Frobenius complement, where
`typeFData_fitting_inf_centralizer_eq_bot` applies) together with a `κ(M)`-Hall `K ⊇ X`.

The construction (Coq `BGsection16.v:1031`): `p ∈ κ(M) ⟹ p ∉ σ(M)` (`kappa_subset_sigmaCompl`) and
`p ∈ π(M)`, so `p ∤ |M_F|` (`M_F ⊆ M_σ`) and `p ∣ |U| = [M : M_F]`; since
`exponent U₀ = exponent U`,
`p ∈ π(U₀)`, giving a Sylow `p`-subgroup `X ≤ U₀`, `X ≠ ⊥`.  Then `X` is a `κ`-group, so Hall's
theorem in the solvable `M` (`hall_E_exists` + Hall conjugacy) places it in a `κ(M)`-Hall `K`.  This
was the last residual of `isTypeF_of_isTypeI`, which is now `sorry`-free throughout. -/
theorem typeFData_exists_kappaElement_le_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (td : OddOrder.GroupTheory.TypeFData M)
    {p : ℕ} (hp : p ∈ S14.kappa M) :
    ∃ X K : Subgroup G, X ≤ td.U0 ∧ X ≠ ⊥ ∧ X ≤ K ∧ K ≤ M ∧
      Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨hp_prime, hp_tau, P, hP_elem, hP_le, hP_centr⟩ := hp
  have : Fact p.Prime := ⟨hp_prime⟩
  -- `p ∈ π(M)`: `|P| = p` and `P ≤ M`.
  obtain ⟨_, hPcard⟩ := mem_elemAbelianOfRank.mp hP_elem
  rw [pow_one] at hPcard
  have hp_dvd_M : p ∣ Nat.card ↥M := hPcard ▸ Subgroup.card_dvd_of_le hP_le
  -- `p ∉ σ(M)`.
  have hp_not_sigma : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
    hp_tau.elim (fun h => tau1_subset_sigma_compl M h) (fun h => tau3_subset_sigma_compl M h)
  -- `p ∤ |M_F|` (`M_F ≤ M_σ`, and `M_σ` is `σ`-Hall).
  have hMFMσ : td.H ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    td.H_eq ▸ maxNilpotentNormalHall_le_Msigma hG hM
  have hp_not_dvd_MF : ¬ p ∣ Nat.card ↥td.H := fun hdvd =>
    hp_not_sigma ((OddOrder.BG.Ch3.S10.Msigma_isHall hG hM).primeFactors_card_subset p
      (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd.trans (Subgroup.card_dvd_of_le hMFMσ),
        Nat.card_pos.ne'⟩))
  -- `p ∣ |U|`: `|M_F| · |U| = |M|`.
  have hcard : Nat.card ↥td.H * Nat.card ↥td.U = Nat.card ↥M := by
    have h := td.complement.card_mul_card
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe td.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe td.U_le).toEquiv] at h
  have hp_dvd_U : p ∣ Nat.card ↥td.U :=
    (hp_prime.dvd_mul.mp (hcard ▸ hp_dvd_M)).resolve_left hp_not_dvd_MF
  -- `p ∣ |U₀|`: a `p`-element of `U` gives `p ∣ exponent U = exponent U₀ ∣ |U₀|`.
  have hp_dvd_U0 : p ∣ Nat.card ↥td.U0 := by
    have : Fintype ↥td.U := Fintype.ofFinite _
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥td.U) p
      (by rwa [Nat.card_eq_fintype_card] at hp_dvd_U)
    exact (td.exponent_eq ▸ (hg ▸ Monoid.order_dvd_exponent g : p ∣ Monoid.exponent ↥td.U)).trans
      Group.exponent_dvd_nat_card
  -- A `p`-element `g ∈ U₀` generates a nontrivial `p`-subgroup `X = ⟨g⟩ ≤ U₀`.
  have : Fintype ↥td.U0 := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥td.U0) p
    (by rwa [Nat.card_eq_fintype_card] at hp_dvd_U0)
  have hXMle : (Subgroup.zpowers g).map td.U0.subtype ≤ M :=
    (Subgroup.map_subtype_le _).trans (td.U0_le.trans td.U_le)
  have hXcard : Nat.card ↥((Subgroup.zpowers g).map td.U0.subtype) = p := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ td.U0.subtype_injective).symm.toEquiv,
      Nat.card_zpowers, hg]
  -- `X` is a `κ(M)`-group (`|X| = p ∈ κ`), so Hall-D places it in a `κ(M)`-Hall `K`.
  have hX_kappa :
      ∀ q ∈ (Nat.card ↥(((Subgroup.zpowers g).map td.U0.subtype).subgroupOf M)).primeFactors,
      q ∈ S14.kappa M := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXMle).toEquiv, hXcard,
      hp_prime.primeFactors, Finset.mem_singleton] at hq
    rw [hq]; exact ⟨hp_prime, hp_tau, P, hP_elem, hP_le, hP_centr⟩
  obtain ⟨K', hK'_hall, hXK'⟩ := Ch03.hall_D (G := ↥M) hX_kappa
  refine ⟨(Subgroup.zpowers g).map td.U0.subtype, K'.map M.subtype,
    Subgroup.map_subtype_le _, ?_, ?_, Subgroup.map_subtype_le _, ?_⟩
  · -- `X ≠ ⊥` (`|X| = p ≠ 1`).
    intro hbot
    rw [hbot, Subgroup.card_bot] at hXcard
    exact hp_prime.ne_one hXcard.symm
  · -- `X ≤ K'.map subtype` from `X.subgroupOf M ≤ K'`.
    rw [← Subgroup.map_subgroupOf_eq_of_le hXMle]
    exact Subgroup.map_mono hXK'
  · -- `IsHallSubgroup κ ((K'.map subtype).subgroupOf M)` reduces to `hK'_hall` on `K'`.
    change Ch03.IsHallSubgroup (S14.kappa M) ((K'.map M.subtype).comap M.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hK'_hall

/-- **Proposition 16.1(a), reverse direction — type I ⟹ type `F`** (mmd L4486): a Type I maximal
subgroup `M` has `κ(M) = ∅`.  This is the `hIF` bridge of `proposition_type_classification`, and
together with `isTypeP_of_isTypeNonI` it is everything the FT-critical `not_isTypeI_of_isTypeNonI`
consumes (it lets a non-Type-I `M` be placed in `ℳ_𝓟`, which a Type I `M` cannot also be).

**Proof** (BG L4486, by contradiction): suppose `κ(M) ≠ ∅`, witnessed by `p ∈ κ(M)`.
`typeFData_exists_kappaElement_le_kappaHall` produces a nontrivial `p`-subgroup `X ≤ U₀` and a
`κ(M)`-Hall `K ⊇ X`.  Theorem C(2) (`theoremC_paired_structure`) gives `K* = M_σ ⊓ C_G(K) ≠ ⊥` with
`K* ≤ M_F`.  But `typeFData_fitting_inf_centralizer_eq_bot` forces `M_F ⊓ C_G(X) = ⊥`, and since
`X ≤ K`, `K* ≤ C_G(K) ≤ C_G(X)` together with `K* ≤ M_F` place `K* ≤ M_F ⊓ C_G(X) = ⊥`,
contradicting
`K* ≠ ⊥`. -/
theorem isTypeF_of_isTypeI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hI : OddOrder.GroupTheory.IsTypeI M) :
    S14.IsTypeF M := by
  rw [S14.isTypeF_iff_not_isTypeP]
  intro hP
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨td⟩ := hI
  obtain ⟨p, hp⟩ := hP
  -- A nontrivial `p`-subgroup `X ≤ U₀` and a `κ(M)`-Hall `K ⊇ X`.
  obtain ⟨X, K, hXU0, hXne, hXK, hKM, hK⟩ :=
    typeFData_exists_kappaElement_le_kappaHall hG hM td.typeF hp
  -- A `(κ ∪ σ)'`-Hall subgroup `U` of `M`.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    hUdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hUeq ▸ hU'
  -- `K ≠ ⊥` (since `X ≠ ⊥` and `X ≤ K`).
  have hKne : K ≠ ⊥ := fun h => hXne (le_bot_iff.mp (hXK.trans h.le))
  -- Theorem C(2): `K* = M_σ ⊓ C_G(K)` is nonempty and contained in `M_F`.
  obtain ⟨_, _, hKsne, _, hKsMF, _, _, _, _, _, _, _⟩ :=
    theoremC_paired_structure hG hM hKne hKM hUM hK rfl hU
  -- The type-`F` Frobenius structure gives `M_F ⊓ C_G(X) = ⊥`; with `X ≤ K`, `K* ≤ M_F ⊓ C_G(X)`.
  have hAX := typeFData_fitting_inf_centralizer_eq_bot td.typeF hXU0 hXne
  apply hKsne
  rw [← le_bot_iff, ← hAX, td.typeF.H_eq]
  refine le_inf hKsMF (inf_le_right.trans ?_)
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  exact fun x hx => hg x (hXK hx)

/-- **BG Proposition 16.1** (mmd L4478): the §14--§15 local families are exactly
the shared Type I--V maximal-subgroup predicates consumed downstream by Peterfalvi.
Six clauses = mmd (a)-(f): (a) Type I ⟺ `M ∈ ℳ_𝓕`, (b) Type II ⟺ `M ∈ ℳ_𝓟₂`,
(c) Type III/IV ⟺ `M ∈ ℳ_𝓟₁ ∧ M_F ≠ M_σ`, (d) Type V ⟺ `M ∈ ℳ_𝓟₁ ∧ M_F = M_σ`,
(e) `M' = U M_σ ⟺ M` not Type I, (f) `M_F = M_σ ⟺ M` Type I/II/V. -/
theorem proposition_type_classification [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    (OddOrder.GroupTheory.IsTypeI M ↔ S14.IsTypeF M) ∧
      (OddOrder.GroupTheory.IsTypeII M ↔ S14.IsTypeP2 M) ∧
      ((OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) ↔
        S14.IsTypeP1 M ∧ S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) ∧
      (OddOrder.GroupTheory.IsTypeV M ↔
        S14.IsTypeP1 M ∧ S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) ∧
      ((∃ U : Subgroup G,
        Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
          (U.subgroupOf M) ∧
        derivedInG M = U ⊔ OddOrder.BG.Ch3.S10.Msigma M) ↔
          ¬ OddOrder.GroupTheory.IsTypeI M) ∧
      (S15.MF M = OddOrder.BG.Ch3.S10.Msigma M ↔
        OddOrder.GroupTheory.IsTypeI M ∨ OddOrder.GroupTheory.IsTypeII M ∨
          OddOrder.GroupTheory.IsTypeV M) := by
  -- Apply the `§14`/`§15`-independent assembly engine.  The proved inputs: `hFI` =
  -- `isTypeI_of_isTypeF` (axiom-clean), `hP2II` = `isTypeII_of_isTypeP2` (axiom-clean), `hIF` =
  -- `isTypeF_of_isTypeI` (BG L4486 reverse, modulo the Frobenius FPF crux), `hP_derived` /
  -- `hF_not_derived` = Theorem C(3)/A(3), `h152a` = Theorem 15.2(a).  The 5 residual bridges
  -- (issue 8015) bottom out on the carrier `W₁`/`U`-Hall characterization (reverse `hIIP2` /
  -- `hIIIIVP1` / `hVP1`) or the type-`P₁` data construction (`hP1neIIIIV` / `hP1eqV` = Peterfalvi
  -- (8.3)/(8.8)).
  refine proposition_type_classification_of_inputs
    ?hFI (fun hP2 => isTypeII_of_isTypeP2 hG hM hP2) ?hP1neIIIIV ?hP1eqV ?hIF ?hIIP2 ?hIIIIVP1 ?hVP1
    (typeP_exists_hall_derived_eq hG hM) (typeF_not_exists_hall_derived_eq hG hM)
    (fun hne => isTypeP1_of_mf_ne_msigma hG hM hne)
  -- `hFI` (Type F ⟹ Type I): the `TypeFData` is built (`isTypeF_groupTheory_of_isTypeF`) and the
  -- `alternative` TI case is proved; only the `¬FittingIsTI` trichotomy (BG 15.7(e)) is residual.
  case hFI => exact isTypeI_of_isTypeF hG hM
  -- `hP1neIIIIV` (Type P₁, `M_F ≠ M_σ` ⟹ Type III/IV): the `TypePData` is fully constructed
  -- (`typePData_of_isTypeP1_mf_ne_msigma`, BG Cor 15.5, `U ≠ ⊥` nilpotent); the sole residual is
  -- the
  -- Peterfalvi (8.7) normalizer `N_G(U) ⊆ M` (isolated in
  -- `isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma`).
  case hP1neIIIIV => exact isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma hG hM
  -- `hP1eqV` (Type P₁, `M_F = M_σ` ⟹ Type V): the type-V `TypePData` is fully constructed
  -- (`typePData_of_isTypeP1_mf_eq_msigma`, `U = ⊥`); the sole residual is the Peterfalvi (8.8)
  -- trichotomy on `M_F` (isolated in `isTypeV_of_isTypeP1_mf_eq_msigma`).
  case hP1eqV => exact isTypeV_of_isTypeP1_mf_eq_msigma hG hM
  -- `hIF` (Type I ⟹ Type F): `isTypeF_of_isTypeI` (BG L4486 reverse direction), modulo the
  -- type-`F` Frobenius FPF crux.
  case hIF => exact isTypeF_of_isTypeI hG hM
  -- `hIIP2` (Type II ⟹ Type P₂): Type II is non-Type-I, so `IsTypeP` (`= P₁ ∨ P₂`,
  -- `isTypeP_of_isTypeNonI`).  The `P₁` branch is excluded: with `M_F = M_σ` it is Type V
  -- (`hP1eqV`, contradicting II via `not_isTypeII_of_isTypeV`); with `M_F ≠ M_σ` it is Type III/IV
  -- (`hP1neIIIIV`, contradicting II via `not_isTypeII_of_isTypeIII_or_IV`).  Hence `P₂`.
  case hIIP2 =>
    intro hII
    rcases isTypeP_iff_isTypeP1_or_isTypeP2.mp (isTypeP_of_isTypeNonI hG hM (Or.inl hII))
      with hP1 | hP2
    · by_cases hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M
      · exact absurd hII
          (not_isTypeII_of_isTypeV (isTypeV_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf))
      · exact absurd hII (not_isTypeII_of_isTypeIII_or_IV hG hM
          (isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma hG hM hP1 hmf))
    · exact hP2
  -- `hIIIIVP1` (Type III/IV ⟹ Type P₁ ∧ `M_F ≠ M_σ`): Type III/IV is non-Type-I, so `IsTypeP`.
  -- The `P₂` branch is excluded (`P₂ ⟹ II`, contradicting III/IV via
  -- `not_isTypeII_of_isTypeIII_or_IV`), giving `P₁`; and `M_F = M_σ` would make it Type V
  -- (`hP1eqV`,
  -- contradicting III/IV via `not_isTypeV_of_isTypeIII_or_IV`), so `M_F ≠ M_σ`.
  case hIIIIVP1 =>
    intro h34
    have hP : S14.IsTypeP M := isTypeP_of_isTypeNonI hG hM
      (h34.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))
    have hP1 : S14.IsTypeP1 M := by
      rcases isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
      · exact hP1
      · exact absurd (isTypeII_of_isTypeP2 hG hM hP2) (not_isTypeII_of_isTypeIII_or_IV hG hM h34)
    exact ⟨hP1, fun hmf =>
      not_isTypeV_of_isTypeIII_or_IV h34 (isTypeV_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf)⟩
  -- `hVP1` (Type V ⟹ Type P₁ ∧ `M_F = M_σ`): `M_F = M_σ` from `U = ⊥`
  -- (`mf_eq_msigma_of_typePData_U_eq_bot`); `IsTypeP1` (not `P₂`) because `P₂ ⟹ Type II`
  -- (`isTypeII_of_isTypeP2`) contradicts `Type V` (`not_isTypeII_of_isTypeV`).
  case hVP1 =>
    intro hV
    obtain ⟨dV⟩ := hV
    refine ⟨?_, mf_eq_msigma_of_typePData_U_eq_bot hG hM dV.typeP dV.U_eq_bot⟩
    rcases isTypeP_iff_isTypeP1_or_isTypeP2.mp (isTypeP_of_isTypeV hG hM ⟨dV⟩) with h1 | h2
    · exact h1
    · exact absurd (isTypeII_of_isTypeP2 hG hM h2) (not_isTypeII_of_isTypeV ⟨dV⟩)

/-- **Peterfalvi (8.10)/(8.11), the full `M_s = M_σ` identity** (mmd 04.10:123: "M_s is the group
denoted by M_σ in [BG]"): for a maximal subgroup `M` of its classified Peterfalvi type `τ`, the
"main subgroup" `M_s` (`mainSubgroup`, `= M_F` for I/II/V, `= M'` for III/IV) coincides with BG's
σ-Hall subgroup `M_σ`. Assembled from `proposition_type_classification` (BG Prop 16.1): for I/II/V
it
is clause (f) (`M_F = M_σ ⟺ τ ∈ {I,II,V}`); for III/IV it is clause (c) (`τ ∈ {III,IV} ⟹ M` is type
`P₁`) followed by `isTypeP1_derivedInG_eq_Msigma` (`M' = M_σ`).  The linchpin bridge turning BG's
`M_σ`-stated Theorem E (`sigmaConjugacySaturation_Mtilde_ncard`, `sigma_reps_prime_cover`) into the
`mainSubgroup`-stated `BGTheoremECoverData` (issue 8020). -/
theorem mainSubgroup_eq_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {tau : PeterfalviType} (htau : HasPeterfalviType tau M) :
    mainSubgroup M tau = OddOrder.BG.Ch3.S10.Msigma M := by
  have hcls := proposition_type_classification hG hM
  cases tau with
  | I => exact hcls.2.2.2.2.2.mpr (Or.inl htau)
  | II => exact hcls.2.2.2.2.2.mpr (Or.inr (Or.inl htau))
  | V => exact hcls.2.2.2.2.2.mpr (Or.inr (Or.inr htau))
  | III => exact isTypeP1_derivedInG_eq_Msigma hG hM (hcls.2.2.1.mp (Or.inl htau)).1
  | IV => exact isTypeP1_derivedInG_eq_Msigma hG hM (hcls.2.2.1.mp (Or.inr htau)).1

/-- **Every maximal subgroup has a Peterfalvi type** (exhaustiveness of the I–V classification): a
maximal subgroup `M` of a minimal simple group of odd order has `HasPeterfalviType τ M` for some
`τ ∈ {I,II,III,IV,V}`. Reads off `proposition_type_classification` (BG Prop 16.1) over the
exhaustive
BG trichotomy `F`/`P₁`/`P₂` (`isTypeF_iff_not_isTypeP`, `isTypeP_iff_isTypeP1_or_isTypeP2`): type
`F`
is I (clause a), `P₂` is II (clause b), `P₁` splits as V if `M_F = M_σ` (clause d) else III/IV
(clause c).  Supplies the `tau`/`typed` fields of `BGTheoremECoverData` (issue 8020). -/
theorem exists_peterfalviType [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ tau : PeterfalviType, HasPeterfalviType tau M := by
  have hcls := proposition_type_classification hG hM
  by_cases hF : S14.IsTypeF M
  · exact ⟨.I, hcls.1.mpr hF⟩
  · have hP : S14.IsTypeP M := by
      by_contra hnP
      exact hF (S14.isTypeF_iff_not_isTypeP.mpr hnP)
    rcases S14.isTypeP_iff_isTypeP1_or_isTypeP2.mp hP with hP1 | hP2
    · by_cases hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M
      · exact ⟨.V, hcls.2.2.2.1.mpr ⟨hP1, hmf⟩⟩
      · rcases hcls.2.2.1.mpr ⟨hP1, hmf⟩ with hIII | hIV
        · exact ⟨.III, hIII⟩
        · exact ⟨.IV, hIV⟩
    · exact ⟨.II, hcls.2.1.mpr hP2⟩

/-- **The signalizer maximal's Fitting equals its `σ`-core** (`M_F = M_σ` for type-`F`/`P₂`
maximals): a maximal subgroup that is BG type `F` or `P₂` has `maxNilpotentNormalHall N = M_σ(N)`.
Type `F` is Peterfalvi I and type `P₂` is Peterfalvi II (`proposition_type_classification` clauses
(a)/(b)), both of which satisfy `M_F = M_σ` (clause (f)).  This is exactly the identity making
Peterfalvi's (8.14) signalizer `R(x) = C_{(N[x])_F}(x)` (Coq `FTsignalizer`, Fitting of the
signalizer
maximal `N[x]`, which is type `F`/`P₂` by `signalizer_structure_of_mem_sigmaSharp`) coincide with
BG's
`R(x) = (N[x])_σ ⊓ C_G(x)` (`Rsub`): `(N[x])_F = (N[x])_σ` (issue 8020). -/
theorem maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {N : Subgroup G} (hN : N ∈ maximalSubgroups G)
    (h : S14.IsTypeF N ∨ S14.IsTypeP2 N) :
    maxNilpotentNormalHall N = OddOrder.BG.Ch3.S10.Msigma N := by
  have hcls := proposition_type_classification hG hN
  rcases h with hF | hP2
  · exact hcls.2.2.2.2.2.mpr (Or.inl (hcls.1.mpr hF))
  · exact hcls.2.2.2.2.2.mpr (Or.inr (Or.inl (hcls.2.1.mpr hP2)))

/-- **Type `F` with no `τ₂`-primes is Frobenius over `M_σ`** (the `∃ U` conclusion of BG
Lemma 14.13(a)): if `κ(M) = ∅`, no prime lies in `τ₂(M)`, and some prime of `π(M)` is
outside `σ(M)` (so the complement is nontrivial), then `M = M_σ ⋊ E` is a Frobenius group.

A fixed point `n ∈ M_σ^#` of `e ∈ E^#` would give a prime `r` of `orderOf e` — necessarily
in `τ₁(M) ∪ τ₃(M)` by the `π(E)`-partition (Lemma 12.1) and `τ₂`-freeness — a rank-one
subgroup `X ≤ ⟨e⟩` with `C_{M_σ}(X) ≠ 1`, i.e. `r ∈ κ(M)` — contradiction. -/
theorem typeF_frobenius_of_esetup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M)
    (ht2 : ∀ p : ℕ, p.Prime → p ∉ tau2 M)
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃)
    (hEne : E.subgroupOf M ≠ ⊥) :
    Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) ∧
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
        ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) := by
  classical
  have hcompl : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).IsComplement'
      (E.subgroupOf M) := hsetup.isComplement'_subgroupOf
  have hMσhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM)
  have hcardE : Nat.card ↥(E.subgroupOf M) =
      ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := (hcompl.symm.index_eq_card).symm
  -- `π(E) ⊆ σ(M)ᶜ` (the complement realizes the `σ'`-index).
  have hEpi : ∀ r ∈ (Nat.card ↥(E.subgroupOf M)).primeFactors,
      r ∉ OddOrder.BG.Ch3.S10.sigma M := by
    intro r hr
    rw [hcardE] at hr
    exact hMσhall.2 r hr
  refine ⟨hcompl, ?_⟩
  refine
    { isNormal := ?_
      isComplement := hcompl
      ne_bot_kernel := ?_
      ne_bot_complement := hEne
      conj_frobenius := ?_ }
  · rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  · intro hbot
    have hMσne : OddOrder.BG.Ch3.S10.Msigma M ≠ ⊥ :=
      OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    exact hMσne (by
      have := congrArg (Subgroup.map M.subtype) hbot
      rwa [Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le M),
        Subgroup.map_bot] at this)
  · -- Frobenius action: no nontrivial fixed points.
    intro a haE ha1 n hnMσ hn1 hfix
    -- `n` commutes with `a` (as elements of `↥M`, hence of `G`).
    have hcomm : Commute (a : G) (n : G) := by
      have hcM : a * n = n * a := mul_inv_eq_iff_eq_mul.mp hfix
      have h2 := congrArg (fun z : ↥M => (z : G)) hcM
      simpa [commute_iff_eq] using h2
    -- a prime `r ∣ orderOf (a : G)`, with an order-`r` power `c` of `a`.
    have haG1 : (a : G) ≠ 1 := fun h => ha1 (by
      apply Subtype.ext
      simpa using h)
    have hordne : orderOf (a : G) ≠ 1 := fun h => haG1 (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr_prime, hr_dvd⟩ := (orderOf (a : G)).exists_prime_and_dvd hordne
    have : Fact r.Prime := ⟨hr_prime⟩
    have hrcard : r ∣ Nat.card ↥(Subgroup.zpowers (a : G)) := by
      rwa [Nat.card_zpowers]
    obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers (a : G))) r
      hrcard
    have hcz : (c : G) ∈ Subgroup.zpowers (a : G) := c.2
    have hc_ordG : orderOf (c : G) = r := by
      rw [← hc_ord]
      exact (orderOf_injective (Subgroup.zpowers (a : G)).subtype
        (Subgroup.zpowers (a : G)).subtype_injective c).symm ▸ rfl
    -- `X = ⟨c⟩ ∈ ℰ_r¹(M)`.
    set X : Subgroup G := Subgroup.zpowers (c : G) with hXdef
    have hXcard : Nat.card ↥X = r := by rw [hXdef, Nat.card_zpowers, hc_ordG]
    have hXelem : X ∈ elemAbelianOfRank G r 1 :=
      mem_elemAbelianOfRank.mpr
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
    have haM : (a : G) ∈ E := by
      have := haE
      rwa [Subgroup.mem_subgroupOf] at this
    have hXE : X ≤ E := by
      rw [hXdef, Subgroup.zpowers_le]
      exact (Subgroup.zpowers_le.mpr haM) hcz
    have hXM : X ≤ M := hXE.trans hsetup.E_le
    -- `r ∈ π(E) ∖ σ(M) ∖ τ₂(M) ⊆ τ₁(M) ∪ τ₃(M)`.
    have hrE : r ∈ (Nat.card ↥E).primeFactors := by
      refine Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, Nat.card_pos.ne'⟩
      calc r = Nat.card ↥X := hXcard.symm
        _ ∣ Nat.card ↥E := Subgroup.card_dvd_of_le hXE
    have hrτ : r ∈ tau1 M ∪ tau2 M ∪ tau3 M :=
      hsetup.mem_tau_union_of_mem_primeFactors hG hrE
    have hrτ13 : r ∈ tau1 M ∪ tau3 M := by
      rcases hrτ with (h1 | h2) | h3
      · exact Or.inl h1
      · exact absurd h2 (ht2 r hr_prime)
      · exact Or.inr h3
    -- `n` centralizes `X` and lies in `M_σ`, so `r ∈ κ(M)` — against type `F`.
    have hnG : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := by
      have := hnMσ
      rwa [Subgroup.mem_subgroupOf] at this
    have hcn : Commute (c : G) (n : G) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
      rw [← hk]; exact hcomm.zpow_left k
    have hnX : (n : G) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hXdef] at hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (hcn.zpow_left m).eq
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
      intro hbot
      have hnG1 : (n : G) ≠ 1 := fun h => hn1 (by
        apply Subtype.ext
        simpa using h)
      exact hnG1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hnG, hnX⟩))
    have hrκ : r ∈ S14.kappa M := ⟨hr_prime, hrτ13, X, hXelem, hXM, hne⟩
    rw [hF] at hrκ
    exact Set.notMem_empty r hrκ

/-- **BG Corollary 15.9** (mmd L4240; Coq `nonFtype_signalizer_base`, BGsection15.v:1399, parts
(a)(b), due to Sibley and Feit--Thompson): the final local landing point for a centralizer escaping
`M`.  Given `x ∈ M_σ^#` with `C_G(x) ⊄ M` and the signalizer neighbour `N ⊇ C_G(x)` that is *not*
type-`F`, then `M` is type-`F`, `F(M)` is not `TI`, `N` is type-`P₂`, and `M = M_σ ⋊ E` is a
Frobenius group with cyclic `σ(M)′`-Hall complement `E`.  The Sibley/Feit--Thompson package used
by §16.

⚠ **Statement corrected (2026-07-07, issue 9017 更新 #19)**: an earlier draft over-specified an
`∃ r prime ∈ τ₂(N), N_G(⟨x⟩) ≤ E ⊓ N` localization conjunct.  That is **unsound** — `x ∈ ⟨x⟩ ≤
N_G(⟨x⟩)` but `x ∈ M_σ` is disjoint from the complement `E` (`M_σ ⊓ E = 1`), so `N_G(⟨x⟩) ⊄ E` —
and it is neither part of Coq 15.9(a)(b) nor consumed downstream (`exists_RData_escape_structure`
discards it).  Dropped.

**Proof plan** (Coq `nonFtype_signalizer_base`): `IsTypeP2 N` from the signalizer dichotomy
`IsTypeF N ∨ IsTypeP2 N` (`signalizer_structure_of_mem_sigmaSharp`) with `¬IsTypeF N`.  Fix a prime
`r ∣ ord(x)` (so `r ∈ τ₂(N)`, signalizer conjunct); the matched `κ(N)` / `(κ∪σ)(N)′`-Hall pair
`K, U` (`typeP2_exists_matched_kappa_hall_pair`) has an `r`-Sylow `R ≤ U` of `r`-rank 2 (noncyclic),
and `N_G(R) ≤ M` (`norm_noncyclic_sigma`, since `r ∈ σ(M)` via `τ₂(N) ∩ π(N) ⊆ σ(M)`).  Then
`typeP2_neighbor_is_typeF_of_mem` (Coq `P2type_signalizer`) with `H := M` gives `IsTypeF M`;
`tau2_transfer_constraint` (Thm 15.8) forces `τ₂(M) = ∅` (else its first conjunct gives `τ₂(N) = ∅`,
contradicting `r ∈ τ₂(N)`); `typeF_frobenius_of_tau2_prime_free` builds the Frobenius `E`; and
`¬FittingIsTI M` follows from `not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le`
(`x ∈ M_σ^# ⊆ F(M)^#`, `M_σ` nilpotent for type-`F`). -/
theorem centralizer_escape_final_local [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M N : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G) {x : G}
    (hx : x ∈ sigmaSharp M) (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M)
    (hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)))
    (hNnotF : ¬ S14.IsTypeF N) :
    S14.IsTypeF M ∧ ¬ FittingIsTI M ∧ S14.IsTypeP2 N ∧
      ∃ E : Subgroup G,
        E ≤ M ∧ Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
          (E.subgroupOf M) ∧ IsCyclic ↥E ∧
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M) := by
  classical
  have hx1 : x ≠ 1 := hx.2
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hx.1
  -- The escape gives `1 < |𝓜_σ(x)|`, and the signalizer structure yields the unique neighbour `N'`.
  have hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    push Not at h
    exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxMσ hx1 h)
  obtain ⟨N', hNstruct, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hx hgt
  obtain ⟨hNmax', hCN', hRne', hRhall', hxtau2', hNtype', hforall'⟩ := hNstruct
  have hxN' : x ∈ N' := hCN' (Subgroup.mem_centralizer_iff.mpr
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]))
  -- Our given `N ⊇ C_G(x)` is that unique neighbour (`ℳ(C_G(x)) = {N'}`).
  have hNeq : N = N' := Set.mem_singleton_iff.mp
    ((maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax' hxN' hx1 hxtau2' hRne')
      ▸ hNmem)
  subst hNeq
  -- `N` is type-`P₂` (signalizer dichotomy `IsTypeF N ∨ IsTypeP2 N` with `¬IsTypeF N`).
  have hP2N : S14.IsTypeP2 N := hNtype'.resolve_left hNnotF
  -- `IsTypeF M` via `typeP2_neighbor_is_typeF_of_mem` (Coq `P2type_signalizer`); issue 9017 #19.
  -- **Hoisted R-localization setup** (shared by `hFM`, `τ₂(M)=∅`, and the cyclic complement):
  -- `M ∈ 𝓜_σ(x)`; the signalizer structure gives `M ⊓ N` as a `σ(N)'`-complement of `N_σ`.
  have hMσx : M ∈ S14.maximalSigmaSubgroupsOfElement x := ⟨hM, hxMσ⟩
  obtain ⟨-, -, hcompl, -⟩ := hforall' M hMσx
  have hEleN : M ⊓ N ≤ N := inf_le_right
  have hinf : OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N) = ⊥ := by
    have hd : Disjoint (OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N)) N := by
      rw [← Subgroup.subgroupOf_eq_bot]
      change (OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N)).comap N.subtype = ⊥
      rw [Subgroup.comap_inf]; exact disjoint_iff.mp hcompl.disjoint
    have hle : OddOrder.BG.Ch3.S10.Msigma N ⊓ (M ⊓ N) ≤ N := inf_le_right.trans inf_le_right
    rw [← inf_of_le_left hle]; exact disjoint_iff.mp hd
  have hsup : OddOrder.BG.Ch3.S10.Msigma N ⊔ (M ⊓ N) = N := by
    refine le_antisymm (sup_le (OddOrder.BG.Ch3.S10.Msigma_le N) inf_le_right) ?_
    rw [← Subgroup.subgroupOf_eq_top,
      Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le N) inf_le_right]
    exact hcompl.sup_eq_top
  obtain ⟨E₁, E₂, E₃, hsetup⟩ := subgroupESetup_of_complement hG hN hEleN hinf hsup
  obtain ⟨hE1N, hU0E, -, hK₀, hU₀, hU₀ab, hK₀NU₀⟩ :=
    typeP2_matched_kappa_hall_pair_of_esetup hG hN hP2N hsetup
  set U₀ : Subgroup G := E₂ ⊔ E₃ with hU₀def
  have hU0N : U₀ ≤ N := hU0E.trans hEleN
  have hU0M : U₀ ≤ M := hU0E.trans inf_le_left
  -- A prime `r ∣ ord(x)` is a `τ₂(N)`-element (signalizer conjunct) and a `σ(M)`-prime.
  have hcard_eq : Nat.card ↥(Subgroup.closure ({x} : Set G)) = orderOf x := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hclosne : Nat.card ↥(Subgroup.closure ({x} : Set G)) ≠ 1 := by
    rw [hcard_eq]; exact fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd hclosne
  have : Fact r.Prime := ⟨hrp⟩
  have hr_pi : r ∈ S14.piSet (Subgroup.closure ({x} : Set G)) :=
    Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, Nat.card_pos.ne'⟩
  have hrτ2 : r ∈ tau2 N := hxtau2' r hr_pi
  have hrσM : r ∈ OddOrder.BG.Ch3.S10.sigma M :=
    S14.isPiElement_sigma_of_mem_Msigma hxMσ r
      (by rw [← hcard_eq]; exact Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, Nat.card_pos.ne'⟩)
  have hr2 : pRank ↥N r = 2 := tau2_pRank_eq_two hrτ2
  have hrσ'N : r ∉ OddOrder.BG.Ch3.S10.sigma N := hrτ2.1
  have hrκ'N : r ∉ S14.kappa N := by
    intro hrκ
    have hru : r ∈ tau1 N ∨ r ∈ tau3 N := S14.kappa_subset_tau1_union_tau3 hrκ
    rcases hru with h | h
    · exact absurd (hr2.symm.trans (tau1_pRank_eq_one h)) (by norm_num)
    · exact absurd (hr2.symm.trans (tau3_pRank_eq_one h)) (by norm_num)
  have hrκσ'N : r ∈ (S14.kappa N ∪ OddOrder.BG.Ch3.S10.sigma N)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_union, not_or]; exact ⟨hrκ'N, hrσ'N⟩
  -- `r ∤ [N : U₀]`, `r ∣ |N|` ⟹ `r ∣ |U₀|` and `pRank_{U₀} r = pRank_N r = 2`.
  have hridx : ¬ r ∣ (U₀.subgroupOf N).index := fun hd =>
    hU₀.2 r (Nat.mem_primeFactors.mpr ⟨hrp, hd, Subgroup.index_ne_zero_of_finite⟩) hrκσ'N
  have hrN : r ∣ Nat.card ↥N :=
    hrdvd.trans (Subgroup.card_dvd_of_le
      (by rw [← Subgroup.zpowers_eq_closure]; exact Subgroup.zpowers_le.mpr hxN'))
  have hrU₀ : r ∈ S14.piSet U₀ := by
    have hlag : Nat.card ↥(U₀.subgroupOf N) * (U₀.subgroupOf N).index = Nat.card ↥N :=
      Subgroup.card_mul_index _
    have hrsub : r ∣ Nat.card ↥(U₀.subgroupOf N) :=
      ((Nat.Prime.dvd_mul hrp).mp (hlag ▸ hrN)).resolve_right hridx
    refine Nat.mem_primeFactors.mpr ⟨hrp, ?_, Nat.card_pos.ne'⟩
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU0N).toEquiv] at hrsub
  -- `R := O_r(U₀)`, a Sylow `r`-subgroup of `U₀`: `≤ M`, an `r`-group, noncyclic (`pRank = 2`).
  have := hU₀ab
  have : Group.IsSolvable ↥N := hG.isSolvable_of_mem_maximalSubgroups hN
  have : Group.IsSolvable ↥U₀ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hU0N)
  obtain ⟨R', hR'⟩ := Ch03.hall_E_exists (G := ↥U₀) ({r} : Set ℕ)
  set R : Subgroup G := R'.map U₀.subtype with hRdef
  have hRU₀ : R ≤ U₀ := Subgroup.map_subtype_le _
  have hRsubOf : R.subgroupOf U₀ = R' := by
    rw [hRdef]; exact Subgroup.comap_map_eq_self_of_injective U₀.subtype_injective R'
  have hRhall : Ch03.IsHallSubgroup ({r} : Set ℕ) (R.subgroupOf U₀) := by
    rw [hRsubOf]; exact hR'
  have hRM : R ≤ M := hRU₀.trans hU0M
  have hRpi : Subgroup.IsPiSubgroup ({r} : Set ℕ) R := by
    intro p hp
    rw [hRdef, Subgroup.card_map_of_injective U₀.subtype_injective] at hp
    exact hR'.1 p hp
  have hRpg : IsPGroup r ↥R := isPGroup_of_isPiSubgroup_singleton hRpi
  have hridxR : ¬ r ∣ (R.subgroupOf U₀).index := fun hd =>
    hRhall.2 r (Nat.mem_primeFactors.mpr ⟨hrp, hd, Subgroup.index_ne_zero_of_finite⟩) rfl
  have hpR2 : pRank ↥R r = 2 := by
    rw [OddOrder.GroupTheory.pRank_eq_of_le_of_not_dvd_index hRU₀ hridxR,
      OddOrder.GroupTheory.pRank_eq_of_le_of_not_dvd_index hU0N hridx, hr2]
  have hRnc : ¬ IsCyclic ↥R := by
    obtain ⟨A, -, hAnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_of_two_le_pRank (G := ↥R) (p := r) hpR2.ge
    exact fun hRcyc => hAnc (by have := hRcyc; infer_instance)
  have hNRM : Subgroup.normalizer (R : Set G) ≤ M :=
    norm_noncyclic_sigma hG hM hrσM hRpg hRM hRnc
  have hHmem : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hNRM⟩
  -- Corollary 14.12 (`P2type_signalizer`) with the `P₂` neighbour `N` and `H := M`.
  have hUab : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥U₀) (⟨b, hb⟩ : ↥U₀))
  have hFM : S14.IsTypeF M :=
    (S14.typeP2_neighbor_is_typeF_of_mem hG hN hP2N hE1N hU0N hK₀ hU₀ hUab
      hrU₀ hRU₀ hRhall hK₀NU₀ hHmem).1
  -- `¬FittingIsTI M`: `x ∈ M_σ^# ⊆ F(M)^#` (type-`F` ⟹ `M_σ = M_F` nilpotent normal `⊆ F(M)`).
  have hnotTI : ¬ FittingIsTI M := by
    have : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp
        (maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG hM (Or.inl hFM))
    have hMσF : OddOrder.BG.Ch3.S10.Msigma M ≤ fittingInAmbient M :=
      le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent
        (OddOrder.BG.Ch3.S10.Msigma_le M)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M))
    exact not_fittingIsTI_of_mem_fittingSharp_of_centralizer_not_le hG hM ⟨hMσF hx.1, hx.2⟩ hesc
  -- **`τ₂(M) = ∅`** (Theorem 15.8, `tau2_transfer_constraint` with `H := M`): a prime `p ∈ τ₂(M)`
  -- forces `τ₂(N) = ∅`, contradicting `r ∈ τ₂(N)`.  `Mstar ∈ 𝓜(C_G(E₁))` exists (`E₁ ≠ ⊥`).
  have hE1ne : E₁ ≠ ⊥ := fun h =>
    S14.card_kappaHall_ne_one hP2N.1 hE1N hK₀ (by rw [h, Subgroup.card_bot])
  obtain ⟨Mstar, hMstarmem⟩ :
      (maximalSubgroupsContaining (Subgroup.centralizer (E₁ : Set G))).Nonempty := by
    have : Nontrivial ↥E₁ := (Subgroup.nontrivial_iff_ne_bot E₁).mpr hE1ne
    obtain ⟨⟨e, he⟩, heNe⟩ := exists_ne (1 : ↥E₁)
    have heNe1 : e ≠ 1 := fun h => heNe (by apply Subtype.ext; simpa using h)
    have hlt : Subgroup.centralizer (E₁ : Set G) < ⊤ :=
      lt_of_le_of_lt (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr he))
        (OddOrder.BG.Ch2.S09.centralizer_singleton_lt_top hG heNe1)
    obtain ⟨Mstar, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hlt.ne
    exact ⟨Mstar, mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩⟩
  have htau2M : ∀ p : ℕ, p.Prime → p ∉ tau2 M := fun p hpp hpM =>
    (S15.tau2_transfer_constraint hG hN hP2N hE1N hU0N hK₀ hU₀ hUab hMstarmem
      hrU₀ hRU₀ hRhall hK₀NU₀ hHmem ⟨p, hpp, hpM⟩).1 r hrp hrτ2
  refine ⟨hFM, hnotTI, hP2N, ?_⟩
  -- **Cyclic Frobenius complement** `M = M_σ ⋊ E`, `E = E₁` cyclic: `τ₂(M)=∅ ⟹ E₂=1`
  -- (`E2_eq_bot_of_tau2_eq_empty`), `¬FittingIsTI ⟹ E₃=1` (`E3_eq_bot_of_not_fittingIsTI`),
  -- `E₁` cyclic (`E1_isCyclic`); `E ≠ ⊥` is free (`SubgroupESetup.E_ne_bot`), Frobenius via
  -- `typeF_frobenius_of_esetup`.  BG Corollary 15.9(b) (Coq `nonFtype_signalizer_base` `cycE`).
  obtain ⟨EM, EM₁, EM₂, EM₃, hsetupM⟩ := exists_subgroupESetup hG hM
  have hEM2 : EM₂ = ⊥ := S15.E2_eq_bot_of_tau2_eq_empty hsetupM htau2M
  have hEM3 : EM₃ = ⊥ := S15.E3_eq_bot_of_not_fittingIsTI hG hM hnotTI hsetupM
  have hEMeq : EM = EM₁ := by rw [hsetupM.eq_sup hG, hEM2, hEM3, sup_bot_eq, sup_bot_eq]
  have hEMcyc : IsCyclic ↥EM := by rw [hEMeq]; exact hsetupM.E1_isCyclic hG
  have hEMne : EM.subgroupOf M ≠ ⊥ := fun hbot =>
    OddOrder.BG.Ch3.S12.SubgroupESetup.E_ne_bot hG hsetupM
      (by rw [← inf_of_le_left hsetupM.E_le]
          exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot))
  obtain ⟨hIsCompl, hFrob⟩ := typeF_frobenius_of_esetup hG hM hFM htau2M hsetupM hEMne
  exact ⟨EM, hsetupM.E_le, hIsCompl, hEMcyc, hFrob⟩

/-- **A `τ₂(N)`-element lies outside `N_σ`.**  Every prime of `π(⟨x⟩)` is a `τ₂(N)`-prime, hence a
`σ(N)′`-prime (`mem_tau2_iff`), while `N_σ` is a `σ(N)`-group.  Extracted from the Theorem D(4)
proof, which needs it for the `∖ N_σ` half of its fourth component. -/
theorem notMem_Msigma_of_forall_mem_tau2 [Finite G] {N : Subgroup G} {x : G} (hx1 : x ≠ 1)
    (hxtau2 : ∀ p ∈ S14.piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N) :
    x ∉ (OddOrder.BG.Ch3.S10.Msigma N : Set G) := by
  intro hxMσN
  obtain ⟨p, hpp, hpdvd⟩ := (orderOf x).exists_prime_and_dvd
    (fun h => hx1 (orderOf_eq_one_iff.mp h))
  have hpπx : p ∈ S14.piSet (Subgroup.closure ({x} : Set G)) := by
    rw [S14.piSet, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, (orderOf_pos x).ne'⟩
  have hpτ2 : p ∈ tau2 N := hxtau2 p hpπx
  have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr ⟨hpp,
      hpdvd.trans ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard
        (SetLike.mem_coe.mp hxMσN)), Nat.card_pos.ne'⟩)
  exact ((mem_tau2_iff N p).mp hpτ2).1 hpσN

/-- **BG Theorem D(4), the escape structure** (the `hD4` conjunct of
`theoremD_msigma_conjugacy_and_centralizers`): for `x ∈ M_σ^#` whose centralizer escapes `M`, the
normal-complement data `R(x)` exists and is attached to a *unique* maximal `N ⊇ C_G(x)` of type `F`
or `P₂`.  Assembled from the signalizer structure (`signalizer_structure_of_mem_sigmaSharp`), the
`τ₂`-element centralizer uniqueness (`maximalContaining_centralizer_eq_singleton_of_tau2_element`,
giving `ℳ(C_G(x)) = {N}`), `RData_of_inputs`,
`maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2`,
and the `P₂`-escape package (`centralizer_escape_final_local`). -/
theorem exists_RData_escape_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hx : x ∈ sigmaSharp M) (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∃ R : Subgroup G,
      RData M x R ∧
      ∃! N : Subgroup G,
        N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
        R = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
        S15.MF N = OddOrder.BG.Ch3.S10.Msigma N ∧
        x ∈ ASet N ⊤ \ (OddOrder.BG.Ch3.S10.Msigma N : Set G) ∧
        (S14.IsTypeF N ∨ S14.IsTypeP2 N) ∧
        Subgroup.IsComplement' ((M ⊓ N).subgroupOf N)
          ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) ∧
        (S14.IsTypeP2 N →
          S14.IsTypeF M ∧ ¬ S15.FittingIsTI M ∧
            ∃ E : Subgroup G,
              E ≤ M ∧ IsCyclic ↥E ∧
              Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
                (E.subgroupOf M) ∧
              OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
                ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M)) := by
  have hx1 : x ≠ 1 := hx.2
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hx.1
  -- `|𝓜_σ(x)| > 1` from the escape.
  have hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    push Not at h
    exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxMσ hx1 h)
  -- The signalizer neighbour `N`.
  obtain ⟨N, hNstruct, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hx hgt
  obtain ⟨hNmax, hCN, hRne, hRhall, hxtau2, hNtype, hforall⟩ := hNstruct
  have hxN : x ∈ N := hCN (Subgroup.mem_centralizer_iff.mpr
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]))
  -- Uniqueness: `ℳ(C_G(x)) = {N}` (Cor 14.3 τ₂-uniqueness applied to `N`).
  have hMC : maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} :=
    maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax hxN hx1 hxtau2 hRne
  have hxM_mem : x ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hxMσ
  obtain ⟨-, -, hMcompl, hMsharp⟩ := hforall M ⟨hM, hxMσ⟩
  -- `x ∉ M_σ(N)` since `x` is a `τ₂(N)`-element (`σ(N)′`).
  have hxnotMσN : x ∉ (OddOrder.BG.Ch3.S10.Msigma N : Set G) :=
    notMem_Msigma_of_forall_mem_tau2 hx1 hxtau2
  refine ⟨OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G),
    RData_of_inputs hG hM hxMσ hx1 hCN hMsharp hRhall
      (signalizer_centralizer_isComplement hMcompl hCN hxM_mem),
    N, ⟨?_, rfl, ?_, ⟨?_, hxnotMσN⟩, hNtype, hMcompl.symm, ?_⟩, ?_⟩
  · rw [hMC]; rfl
  · exact maxNilpotentNormalHall_eq_Msigma_of_isTypeF_or_isTypeP2 hG hNmax hNtype
  · -- `x ∈ ASet N ⊤ = hatMsigma N`.
    show x ∈ ASet N ⊤
    refine ⟨⟨hxN, hRne⟩, ?_⟩
    simp
  · -- `IsTypeP2 N → IsTypeF M ∧ ¬FittingIsTI M ∧ Frobenius`.
    intro hP2
    have hNnotF : ¬ S14.IsTypeF N := fun hF => S14.not_isTypeP_and_isTypeF ⟨hP2.1, hF⟩
    have hNmem : N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) := by
      rw [hMC]; rfl
    obtain ⟨hFM, hnotTI, -, E, hEM, hEcompl, hEcyc, hEfrob⟩ :=
      centralizer_escape_final_local hG hM hNmax hx hesc hNmem hNnotF
    exact ⟨hFM, hnotTI, E, hEM, hEcyc, hEcompl, hEfrob⟩
  · rintro N' ⟨hN'mem, -⟩
    rw [hMC] at hN'mem
    exact hN'mem

/-- **BG Theorem D** (mmd L4317, recovered tail L4368): conjugacy and centralizer
control for `M_sigma`, including the `R(x)` normal complement, its sharply transitive
action, and the unique maximal subgroup attached to escaping centralizers.

The final conjunct is the recovered BG D(4) tail: `M ∩ N` complements `N_sigma` in
`N`, and if `N` is type `P2` then `M` is type `F`, Frobenius with cyclic complement,
and `M_F` is not TI. -/
theorem theoremD_msigma_conjugacy_and_centralizers [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    (∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      (∀ g : G, g ∉ M → IsCyclic ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓ (MulAut.conj g • M))) ∧
      (∀ x : G, x ∈ sigmaSharp M → ∃ R : Subgroup G, RData M x R) ∧
      (∀ x : G, x ∈ sigmaSharp M → ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∃ R : Subgroup G,
          RData M x R ∧
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            R = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
            S15.MF N = OddOrder.BG.Ch3.S10.Msigma N ∧
            x ∈ ASet N ⊤ \ (OddOrder.BG.Ch3.S10.Msigma N : Set G) ∧
            (S14.IsTypeF N ∨ S14.IsTypeP2 N) ∧
            Subgroup.IsComplement' ((M ⊓ N).subgroupOf N)
              ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) ∧
            (S14.IsTypeP2 N →
              S14.IsTypeF M ∧ ¬ S15.FittingIsTI M ∧
                ∃ E : Subgroup G,
                  E ≤ M ∧ IsCyclic ↥E ∧
                  Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
                    (E.subgroupOf M) ∧
                  OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M
                    ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (E.subgroupOf M))) := by
  refine ⟨msigma_fusion_control hG hM, fun g hg => Msigma_inf_conj_isCyclic hG hM hg, ?_, ?_⟩
  · exact exists_RData_of_mem_sigmaSharp hG hM
  · exact fun x hx hesc => exists_RData_escape_structure hG hM hx hesc

/-- **Type I and non-Type-I are mutually exclusive** (corollary of Proposition
16.1(a)–(d)).  A maximal subgroup of a minimal simple group of odd order that is
Type I cannot also be one of Types II–V.

The proof reads the type dictionary of `proposition_type_classification`: clause
(a) says Type I `⟺ M ∈ ℳ_𝓕` (`S14.IsTypeF`), while clauses (b)–(d) place each of
Types II–V in `ℳ_𝓟` (`S14.IsTypeP`) — Type II in `ℳ_𝓟₂`, Types III/IV/V in
`ℳ_𝓟₁`.  Since `ℳ_𝓕` and `ℳ_𝓟` are complementary
(`S14.isTypeF_iff_not_isTypeP`), the two cannot coincide.

Used by `OddOrder.section16MaximalPair_of_isMinimalSimpleOdd` to discharge the
all-Type-I branch of Peterfalvi (8.8): the case-(b) witness of (12.17) is a
non-Type-I maximal subgroup, contradicting "every maximal subgroup is Type I". -/
theorem not_isTypeI_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hNonI : OddOrder.GroupTheory.IsTypeNonI M) :
    ¬ OddOrder.GroupTheory.IsTypeI M := by
  intro hI
  -- Type I forces `κ(M) = ∅` (`isTypeF_of_isTypeI`), i.e. `M ∉ ℳ_𝓟`; but every non-Type-I `M` is
  -- type `P` (`isTypeP_of_isTypeNonI`).  This routes around the other five
  -- `proposition_type_classification` bridges, leaving the FT-critical surface gated on the single
  -- `hIF` crux (`typeF_mf_inf_centralizer_kappaHall_eq_bot`).
  exact (S14.isTypeF_iff_not_isTypeP.mp (isTypeF_of_isTypeI hG hM hI))
    (isTypeP_of_isTypeNonI hG hM hNonI)

end OddOrder.BG.Ch4.S16


