-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_InducedKernelFamily
-- name    : OddOrder_Peterfalvi_S08_InducedKernelFamily
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:10:41.354274+00:00
-- url     : https://prove2.me/theorems/98382956-e0c5-4a6f-bd0a-87df04ef1958
-- title:
--   Peterfalvi (6.1): the induced family $S(X)$ for a general kernel, and the (6.6) $X$-set
-- statement:
--   Formalizes the induced family of Peterfalvi §6, Hypothesis (6.1) and Theorem (6.6). Hypothesis (6.1) fixes a solvable normal $K\trianglelefteq L$ and sets $\mathcal{S}=\{\mathrm{Ind}_K^L\theta\mid\theta\in\mathrm{Irr}\,K,\theta\ne1\}$, with the filtration $\mathcal{S}(X)$ cutting down to sources whose kernel contains $X$. The family is defined in this leaf because two independent §8 developments need it and sit on opposite sides of an import boundary.
--
--   The main definition is `inducedKernelFamily` (Peterfalvi (6.1) filtration $S(X)$ for a general kernel $K\le L$).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_InducedKernelFamily.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_InducedKernelFamily.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_YsetInner_CharacterBreaks

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

variable {L : Subgroup G} [Fintype ↥L]

section InducedKernelFamily

variable (K : Subgroup ↥L) [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (6.1) filtration `S(X)` for a general kernel `K ≤ L`** (Coq `seqIndD K L K X`):
the induced characters `Ind_K^L θ` of nontrivial irreducible sources `θ ∈ Irr K` whose kernel
contains `X`.  `S(⊥) = S` is the full induced family; the §11 consumer instantiates `K = M'`
(solvable), where members can be *reducible* (the μ-columns), unlike the Sibley `SsubFiltration`
(`K = H` with a Frobenius action making every member irreducible). -/
def inducedKernelFamily (X : Subgroup ↥L) : Set (ClassFunction ↥L ℂ) :=
  {φ : ClassFunction ↥L ℂ | ∃ θ : IrreducibleCharacter ↥K,
    θ ≠ trivialIrreducibleCharacter ↥K ∧
    (X.subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) ∧
    φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ)}

variable {K}

theorem mem_inducedKernelFamily {X : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} :
    φ ∈ inducedKernelFamily K X ↔ ∃ θ : IrreducibleCharacter ↥K,
      θ ≠ trivialIrreducibleCharacter ↥K ∧
      (X.subgroupOf K : Set ↥K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) ∧
      φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ) :=
  Iff.rfl

/-- `S(X)` is antitone in the kernel demand `X`. -/
theorem inducedKernelFamily_antitone {X Y : Subgroup ↥L} (hXY : X ≤ Y) :
    inducedKernelFamily K Y ⊆ inducedKernelFamily K X := by
  intro φ hφ
  obtain ⟨θ, hθne, hker, hφeq⟩ := hφ
  refine ⟨θ, hθne, ?_, hφeq⟩
  intro x hxX
  exact hker (Subgroup.mem_subgroupOf.mpr (hXY (Subgroup.mem_subgroupOf.mp hxX)))

/-- Every filtration layer lies in the full family `S = S(⊥)`. -/
theorem inducedKernelFamily_subset_bot (X : Subgroup ↥L) :
    inducedKernelFamily K X ⊆ inducedKernelFamily K ⊥ :=
  inducedKernelFamily_antitone bot_le

end InducedKernelFamily

section XCharacterization

variable [Invertible (Nat.card ↥L : ℂ)]

variable {K : Subgroup ↥L} [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (6.6) `X`-characterization, general kernel** (mmd 04.8 L74-76).

For a normal `Z ≤ K` such that every member of `X = 𝒮 − 𝒮(Z)` is irreducible (the (6.8)
Frobenius/case-A side condition `hX`), `X` is exactly the set of irreducible characters of `L`
whose kernel does not contain `Z`:
`𝒮 − 𝒮(Z) = {χ ∈ Irr L | Z ⊄ Ker χ}`.

Nothing about the Feit–Thompson/Sibley setting enters: the argument uses only the *shape* of the
induced family — in fact `K` need not even be **normal** in `L` (the book has `K ⊴ L` from
Hypothesis (6.1), but this identity never uses it), so the statement is slightly stronger
than (6.6).  The Sibley `K = H` instance is
`SibleyDadeHypothesis.Xset_eq_irreducible_not_subset_characterKernel`
(`S08_DegreeSums/CoherenceGlue`), which is this theorem transported along
`SsubFiltration = inducedKernelFamily H`. -/
theorem inducedKernelFamily_sdiff_eq_irreducible_not_subset_characterKernel
    {Z : Subgroup ↥L} [Z.Normal] (hZK : Z ≤ K)
    (hX : ∀ φ ∈ inducedKernelFamily K ⊥ \ inducedKernelFamily K Z, IsIrreducibleCharacter φ) :
    inducedKernelFamily K ⊥ \ inducedKernelFamily K Z =
      {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
        ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} := by
  have : Fintype ↥K := Fintype.ofFinite _
  ext φ
  constructor
  · -- (⊆): `φ ∈ X` is irreducible (`hX`); if `Z ⊆ Ker φ` then `φ ∈ 𝒮(Z)`, contradiction.
    intro hφX
    have hφirr : IsIrreducibleCharacter φ := hX φ hφX
    refine ⟨hφirr, ?_⟩
    obtain ⟨hφS, hφnotSZ⟩ := hφX
    obtain ⟨θ, hθ_ne, -, hφeq⟩ := hφS
    intro hZker
    refine hφnotSZ ⟨θ, hθ_ne, ?_, hφeq⟩
    -- `Z.subgroupOf K ⊆ Ker θ`: read off from `Res_K φ` (a genuine character with `θ` a
    -- constituent).
    have hRes : IsCharacter (ClassFunction.restrict K φ) := isCharacter_restrict hφirr.isCharacter K
    have hθirr : IsIrreducibleCharacter (θ : ClassFunction ↥K ℂ) := θ.property
    have hnorm : ClassFunction.inner φ φ = 1 := by
      have h := irreducibleCharacter_inner_eq_ite (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hφirr⟩ : IrreducibleCharacter ↥L)
      simpa using h
    have hinner_ne : ClassFunction.inner (ClassFunction.restrict K φ)
        (θ : ClassFunction ↥K ℂ) ≠ 0 := by
      have hfrob := ClassFunction.inner_induce_eq_inner_restrict K (θ : ClassFunction ↥K ℂ) φ
      rw [← hφeq, hnorm] at hfrob
      rw [inner_conj_symm θ (ClassFunction.restrict K φ), ← hfrob]
      simp
    intro n hn
    refine characterKernel_subset_of_isCharacter_of_inner_ne_zero hRes hθirr hinner_ne ?_
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    simp only [ClassFunction.restrict_apply]
    have hnZ : ((n : ↥L)) ∈ Z := Subgroup.mem_subgroupOf.mp hn
    have hker := hZker hnZ
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hker
    rw [hker, OneMemClass.coe_one]
  · -- (⊇): `χ` irreducible with `Z ⊄ Ker χ`.  Take a source `θ` of `χ`; show `Ind θ ∈ X`, hence
    -- irreducible (`hX`), hence `= χ` by orthonormality.
    rintro ⟨hχirr, hχZ⟩
    obtain ⟨θ, hθinner⟩ := OddOrder.Peterfalvi.S03.exists_inner_induce_ne_zero (H := K)
      (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
    -- A source `θ'` of `χ` with `Z.subgroupOf K ⊆ Ker θ'` would force `Z ⊆ Ker χ` (contradiction).
    have hkey : ∀ θ' : IrreducibleCharacter ↥K,
        ClassFunction.inner (ClassFunction.induce K (θ' : ClassFunction ↥K ℂ)) φ ≠ 0 →
        ((Z.subgroupOf K : Set ↥K) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (θ' : ClassFunction ↥K ℂ)) → False := by
      intro θ' hθ'inner hθ'ker
      apply hχZ
      have hZind := OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
        (G := ↥L) hZK (θ' : ClassFunction ↥K ℂ) hθ'ker
      intro z hz
      exact characterKernel_subset_of_inner_induce_ne_zero
        θ'.property.isCharacter hχirr hθ'inner (hZind hz)
    have hθ_ne : θ ≠ trivialIrreducibleCharacter ↥K := by
      intro hθtriv
      refine hkey θ hθinner (fun n _ => ?_)
      rw [hθtriv]
      simp [OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    have hIndnotSZ : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∉
        inducedKernelFamily K Z := by
      intro hmem
      obtain ⟨θ', _, hθ'ker, hθ'eq⟩ := hmem
      exact hkey θ' (by rw [← hθ'eq]; exact hθinner) hθ'ker
    have hIndX : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) ∈
        inducedKernelFamily K ⊥ \ inducedKernelFamily K Z := by
      refine ⟨⟨θ, hθ_ne, ?_, rfl⟩, hIndnotSZ⟩
      rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
    have hIndirr : IsIrreducibleCharacter (ClassFunction.induce K (θ : ClassFunction ↥K ℂ)) :=
      hX _ hIndX
    have heq : ClassFunction.induce K (θ : ClassFunction ↥K ℂ) = φ := by
      have hite := irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce K (θ : ClassFunction ↥K ℂ), hIndirr⟩ : IrreducibleCharacter ↥L)
        (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      by_cases hAB : (⟨ClassFunction.induce K (θ : ClassFunction ↥K ℂ), hIndirr⟩ :
          IrreducibleCharacter ↥L) = (⟨φ, hχirr⟩ : IrreducibleCharacter ↥L)
      · exact congrArg Subtype.val hAB
      · rw [if_neg hAB] at hite
        exact absurd hite hθinner
    rw [← heq]; exact hIndX

end XCharacterization

end OddOrder.Peterfalvi.S08


