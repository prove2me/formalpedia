-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherenceT
-- name    : OddOrder_Peterfalvi_S15_CaseACoherenceT
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:41:39.993264+00:00
-- url     : https://prove2.me/theorems/2f323422-7418-4aea-9e15-6374e92959b0
-- title:
--   Peterfalvi (9.11) at $T$: norm bound and equality refutation
-- statement:
--   The $T$-side mirrors of the (9.11.5)–(9.11.8) endgame (Peterfalvi, pp. 87-91): the norm bound and the equality-configuration refutation.
--
--   Main declarations: `Hypothesis.nineElevenNormBoundT` (Peterfalvi (9.11.4)–(9.11.8), the norm bound — `T`-instance residual); `Hypothesis.nineElevenEqualityRefutationT` (Peterfalvi (9.11.2)–(9.11.8), the `T`-instance equality-configuration refutation); `Hypothesis.sSet_caseA_nineElevenRefutation_T` (Peterfalvi (9.11.1)–(9.11.8), the `T`-instance equality-configuration refutation); `Hypothesis.sSet_coherent_indT_caseA` ((9.11) non-Galois-branch coherence of the full family `𝒯 = sSet(setupT)` on `Ind_T^G`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseACoherenceT.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_CaseACoherenceT.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenSevenEightT

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4)–(9.11.8), the norm bound — `T`-instance residual** (mirror; issue 2035;
the
`T`-mirror of the M-side `S13.NineElevenNormBound` discharge
(`nineElevenNormBound_of_sevenEightRefutation` + `nineElevenSevenEightRefutation`, issue 9083
Phases D/E, both landed M-side)).  **(9.11.4)**: `α = Ind_{HU₁}^T 1 − ψ₁` is an `A(T)`-supported
virtual character with the cleared Mackey norm `N·u = (a+1)·u + (q−1)·a²` (mirror of
`caseA_nineElevenFour_norm_inputs`: the (9.11.2) TI-witness from
`S11.nineElevenTwoTIWitness_of_degree_dichotomy` at the `T`-instance degree dichotomy, the
double-coset count `S11.nineElevenGamma_inner_self_mul_u`, and `‖α‖² = ‖γ‖² + 1` via
`S11.cfnorm_sub_irreducible_orthogonal`).  **(9.11.5)–(9.11.8)**: `|𝒮₄| ≤ N = ‖α^τ‖²` — in the
orthogonal branch of the (9.11.6) dichotomy the projection budget
(`S07.exists_bridge_target_of_budget`) plus the union-pair extension
(`S07.isCoherent_union_pair_of_bridge`, suppliable via the case-agnostic `sSet_memberRFamily`)
would coherently adjoin a conjugate pair from `𝒮₄`, contradicting `hnopair`; in the
non-orthogonal branch distinct `𝒮₄`-members consume orthogonal integral slices of `α^τ` (Bessel,
`card_le_inner_self_re_of_orthonormal_inner_int_ne`).  Here `𝒮₄` is the irreducible part of the
`𝒮(H₀C)` stratum outside `𝒮₂` (the `T`-instance `nineElevenSFour`), whose `ncard` is exactly the
`S4` of the (9.11.3) class equation. -/
theorem Hypothesis.nineElevenNormBoundT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.T ℂ))
    (hS₁S₂ : hyp.sSetIrrDegT hG hvd (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)))
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      (χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * chars.u : ℕ) : ℂ))
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.T ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ))
    (hS2deg : ∀ χ ∈ S₂,
      (χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)) :
    ∃ N : ℕ,
      N * chars.u = (caseA.a + 1) * chars.u
        + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 ∧
      {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard ≤ N := by
  classical
  have := hyp.finiteG
  -- ── `indT` → honest-Dade conversions for the coherence clauses (as in `nineElevenPairBoundT`)
  obtain ⟨cohS₂_indS⟩ := hS₂coh
  have hindS_dade : ∀ f : ClassFunction ↥hyp.T ℂ,
      f ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥hyp.T) S₂
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) →
      hyp.indT f = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData) f := fun f hf => by
    rw [hyp.indT_apply, ← hyp.tInstance_dade_eq_induce hG hnoV hTP
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2]
  have hS₂cohD : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData)) S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) :=
    ⟨cohS₂_indS.congrMap hindS_dade⟩
  have hnopairD : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData))
        (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) := by
    intro χ hχ
    rintro ⟨c⟩
    refine hnopair χ hχ ⟨c.congrMap (fun f hf => ?_)⟩
    rw [hyp.tInstance_dade_eq_induce hG hnoV hTP
      (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hf).2, hyp.indT_apply]
  -- ── `τ₃` = the (9.11.6) `𝒮₃`-coherence on the honest Dade
  obtain ⟨c₃⟩ := hyp.sSet_sThree_coherent_dade_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 chars hS₂conj
      hS₃ne hS3deg
  -- ── the `𝒮(H₀C)`-stratum dictionary and degree dichotomy (as in the equality assembler)
  have hsubC : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
      ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := by
    rw [hyp.sSet_eq_sOf_H0Cprime_T hG hvd chars]
    exact OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupT hG hvd)
      (sup_le_sup_left chars.Cprime_le_C chief.H0)
  have hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief),
      (φ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) := by
    intro φ hφ
    by_cases hφS₂ : φ ∈ S₂
    · exact Or.inr (hS2deg φ hφS₂)
    · exact Or.inl (hS3deg φ ⟨hsubC hφ, hφS₂⟩)
  -- ── the (9.11.4) `α = γ − ψ₁` context at the explicit TI-witness (as in the Phase-D bundle)
  have hq0 : 0 < (hyp.toTypesIIIIIIVSetupT hG hvd).q :=
    (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1.pos
  have hTI := cuSubOf_zero_tiWitness caseA hdich
  have hCU₁ : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief
      ≤ cuSubOf caseA ⟨0, hq0⟩ := cSub_le_cuSubOf caseA ⟨0, hq0⟩
  have hU₁U : cuSubOf caseA ⟨0, hq0⟩ ≤ (hyp.toTypesIIIIIIVSetupT hG hvd).U :=
    cuSubOf_le_U caseA ⟨0, hq0⟩
  have hU₁a : (cuSubOf caseA ⟨0, hq0⟩).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U = caseA.a :=
    relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩
  have hUpU₁ : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)
      ≤ cuSubOf caseA ⟨0, hq0⟩ := by
    have hUpC : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)
        = OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief := hCUprime.symm
    rw [hUpC]; exact hCU₁
  have hrelne : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex
      (hyp.toTypesIIIIIIVSetupT hG hvd).U ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < chief.p := chief.p_prime.one_lt
    have hrpos := Nat.pos_of_ne_zero hrelne
    have : 0 < (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
        (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U) :=
      Nat.mul_pos (by omega) hrpos
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  have hψ₁sSet : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    hyp.sOf_H0Uprime_subset_sSet_T hG hvd chars hψ₁sOf
  have hψ₁S₂ : ψ₁ ∈ S₂ := hS₁S₂ ⟨hψ₁sSet, hψ₁irr, hψ₁deg⟩
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  -- `γ = Ind_{HU₁}^T 1` and its (9.11.4) facts
  set K : Subgroup ↥hyp.T := (hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
    ⊔ (cuSubOf caseA ⟨0, hq0⟩).subgroupOf hyp.T with hKdef
  set γ : ClassFunction ↥hyp.T ℂ :=
    ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.T :=
    nineElevenGamma_mem_ZIrr (hyp.toTypesIIIIIIVSetupT hG hvd) (cuSubOf caseA ⟨0, hq0⟩)
  have hγ1 : γ (1 : ↥hyp.T) = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one (hyp.toTypesIIIIIIVSetupT hG hvd) hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ * (chars.u : ℂ)
      = ((caseA.a * chars.u
          + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    nineElevenGamma_inner_self_mul_u chars hU₁U hUpU₁ hU₁a hTI
  -- `γ ⊥` every `𝒮`-member (`H ⊆ Ker γ` at the source, `H ⊄ Ker ξ` on `𝒳`)
  have hγorth : ∀ φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd),
      ClassFunction.inner γ φ = 0 := by
    intro φ hφ
    obtain ⟨ξ, hξ, rfl⟩ := hφ
    have hindEqξ : induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
        = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ) := rfl
    rw [hindEqξ]
    exact nineElevenGamma_inner_induceHU (hyp.toTypesIIIIIIVSetupT hG hvd) hU₁U hξ
  -- `α = γ − ψ₁`: norm split, integrality, `‖α‖² = N`, the cleared identity, support
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := hγorth ψ₁ hψ₁sSet
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.T := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact induceHU_mem_ZIrr (hyp.toTypesIIIIIIVSetupT hG hvd) ζ
  obtain ⟨c, -, -, hcsum⟩ :=
    OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hαZIrr
  have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmval : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
      = ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hcsum]
    push_cast
    rfl
  set N : ℕ := (∑ x ∈ c.support, (c x) ^ 2).toNat with hNdef
  have hNval : ((N : ℕ) : ℂ) = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) := by
    rw [hmval, hNdef]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)
  have hNu : N * chars.u = (caseA.a + 1) * chars.u
      + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 := by
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) * (chars.u : ℂ)
        = ((caseA.a * chars.u
            + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 : ℕ) : ℂ)
          + (chars.u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * chars.u : ℕ) : ℂ)
        = (((caseA.a + 1) * chars.u
            + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  have hαsupp : ((γ - ψ₁ : ClassFunction ↥hyp.T ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T :=
    hyp.nineElevenAlphaSupportT hG hvd chars caseA ⟨0, hq0⟩ hψ₁sSet hψ₁deg
  -- `α^τ ∈ ℤ[Irr G]`, norm preservation
  have hταZIrr : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
      ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁)
      ∈ OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypT hG hTP) hαsupp hαZIrr
  have hταnorm : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
      = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypT hG hTP) hαsupp hαsupp
  -- ── `α ⊥ 𝒮₃` at the source
  have hαorthS₃ : ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ClassFunction.inner (γ - ψ₁) lam = 0 := by
    intro lam hlam
    have hψlam : ClassFunction.inner ψ₁ lam = 0 :=
      sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) hψ₁sSet hlam.1
        (fun h => hlam.2 (h ▸ hψ₁S₂))
    rw [ClassFunction.inner_sub_left, hγorth lam hlam.1, hψlam, sub_zero]
  -- ── the (9.11.6) constancy of `⟨α^τ, λ^{τ₃}⟩` over `λ ∈ 𝒮₃`
  have hconst : ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ∀ lam' ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
        (c₃.extension lam)
      = ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
            ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
          (c₃.extension lam') := by
    intro lam hlam lam' hlam'
    have hdiffsupp : ((lam - lam' : ClassFunction ↥hyp.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
      have h := hyp.sSet_scaledDiff_support_T hG hvd hlam.1 hlam'.1 (c := 1)
        (by rw [hS3deg lam hlam, hS3deg lam' hlam', Nat.cast_one, one_mul])
      rwa [one_smul] at h
    have hzss : (lam - lam' : ClassFunction ↥hyp.T ℂ)
        ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
          (sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂)
          (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) :=
      OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
        ⟨Submodule.sub_mem _ (Submodule.subset_span hlam) (Submodule.subset_span hlam'),
          hdiffsupp⟩
    have hagree : c₃.extension (lam - lam')
        = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (lam - lam') :=
      c₃.extends_on_supported _ hzss
    have hiso : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (lam - lam'))
        = ClassFunction.inner (γ - ψ₁) (lam - lam') :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypT hG hTP) hαsupp hdiffsupp
    have hz : ClassFunction.inner (γ - ψ₁) (lam - lam') = 0 := by
      rw [ClassFunction.inner_sub_right, hαorthS₃ lam hlam, hαorthS₃ lam' hlam', sub_zero]
    have hsub : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
        (c₃.extension lam)
        - ClassFunction.inner
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
              ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
            (c₃.extension lam') = 0 := by
      rw [← ClassFunction.inner_sub_right, ← map_sub, hagree, hiso, hz]
    exact sub_eq_zero.mp hsub
  -- ── the (9.11.6) dichotomy
  by_cases hc : ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
        (c₃.extension lam) = 0
  · -- orthogonal branch — the (9.11.7)–(9.11.8) residual refutes
    exact (hyp.nineElevenSevenEightRefutationT hG hnoV pins hvd hTP Tdata hU hW1 hW2 chars caseA S₂
        hS₁S₂ hS₂S hS₂conj hS₂cohD
      hS₃ne hnopairD h2a hCUprime hS3deg hcount hFboundU hS2deg c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg
      hγZIrr hγ1 hγorth hαsupp hc).elim
  · -- non-orthogonal branch — the Bessel count `|𝒮₄| ≤ ‖α^τ‖² = N`
    push Not at hc
    obtain ⟨lam₀, hlam₀, hlam₀ne⟩ := hc
    have hS4sub : {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}
        ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂ := fun ξ hξ => ⟨hsubC hξ.1, hξ.2.2⟩
    have hS4fin : ({φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂} : Set (ClassFunction ↥hyp.T ℂ)).Finite :=
      (sSet_finite (hyp.toTypesIIIIIIVSetupT hG hvd)).subset (fun ξ hξ => (hS4sub hξ).1)
    refine ⟨N, hNu, ?_⟩
    have hON1 : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ) = 1 := by
      intro ξ hξT
      have hξ := hS4fin.mem_toFinset.mp hξT
      have hξ3 := hS4sub hξ
      rw [c₃.extension_inner_eq ξ ξ (Submodule.subset_span hξ3)
        (Submodule.subset_span hξ3)]
      have h := irreducibleCharacter_inner_eq_ite
        (⟨ξ, hξ.2.1⟩ : IrreducibleCharacter ↥hyp.T) ⟨ξ, hξ.2.1⟩
      rwa [if_pos rfl] at h
    have hON2 : ∀ ξ ∈ hS4fin.toFinset, ∀ ξ' ∈ hS4fin.toFinset, ξ ≠ ξ' →
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ') = 0 := by
      intro ξ hξT ξ' hξ'T hne
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      have hξ'3 := hS4sub (hS4fin.mem_toFinset.mp hξ'T)
      rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ3)
        (Submodule.subset_span hξ'3)]
      exact sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) hξ3.1 hξ'3.1 hne
    have hint : ∀ ξ ∈ hS4fin.toFinset, ∃ m : ℤ,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
            ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
          (c₃.extension ξ) = (m : ℂ) := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      exact ClassFunction.inner_mem_ZIrr_int hταZIrr
        (c₃.extension_mem_ZIrr ξ (Submodule.subset_span hξ3))
    have hnec : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
            ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
          (c₃.extension ξ) ≠ 0 := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      rw [hconst ξ hξ3 lam₀ hlam₀]
      exact hlam₀ne
    have hcount4 := OddOrder.Peterfalvi.S07.card_le_inner_self_re_of_orthonormal_inner_int_ne
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
      hS4fin.toFinset (fun ξ => c₃.extension ξ) hON1 hON2 hint hnec
    have hNre : (ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
          ((hyp.dadeHypT hG hTP).fullDadeIsometryData) (γ - ψ₁))).re
        = (N : ℝ) := by
      rw [hταnorm, ← hNval, Complex.natCast_re]
    rw [hNre] at hcount4
    have hcard : (({φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂}.ncard : ℝ)) ≤ (N : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hS4fin]
      exact hcount4
    exact_mod_cast hcard

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.2)–(9.11.8), the `T`-instance equality-configuration refutation**
(mirror; issue 2035 step (c); the `T`-mirror of the M-side assembler
`S13.nineElevenEqualityRefutation_of_sTwoExtraction_normBound`).  The (9.11.1) squeeze in
`sSet_caseA_nineElevenRefutation` forces the *equality configuration* at any pair-refuted maximal
`𝒮₂` — `2a = p−1`, `C = U′`, every `𝒮₃ = 𝒮 ∖ 𝒮₂`-member of degree `q·u`, the count equality
`|𝒮₁(q·a)|·a² = (p−1)·[U:U′]`, and the saturated subfamily bound `sumnS F ≤ 2q²a·u`.  This
theorem refutes that configuration.

**Assembly (no `htype`/`hncH0C` gate).**  The generic (9.11) apparatus fires directly at
`data := toTypesIIIIIIVSetupT hG hvd`: the `𝒮(H₀C)`-stratum degree dichotomy — from `hS3deg` and the
(9.11.1) `𝒮₂ = 𝒮₁` extraction `nineElevenSTwoExtractionT` through the `sSet = 𝒮(H₀C′)`
dictionary `sSet_eq_sOf_H0Cprime` — feeds the (9.11.2) inertia identity
`S11.nineElevenTwo_two_summand_inertia` and the (9.11.3) class equation
`S11.nineElevenThree_orbit_split`; the (9.11.4)–(9.11.8) norm bound `nineElevenNormBoundT`
supplies `hnorm`/`hle`; the tau-free arithmetic core `S11.nineElevenCaseA_equality_refutation`
closes.  The M-side `htype`/`hncH0C` inputs existed only to identify the `Hypothesis M`
packaging's `H₀C′` with the generic `cprimeSub` stratum (`C_eq_cSub_of_noncoherent`); the
`T`-instance dictionary is definitional, so they vanish.  Remaining named residuals:
`nineElevenSTwoExtractionT` and `nineElevenNormBoundT`. -/
theorem Hypothesis.nineElevenEqualityRefutationT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.T ℂ))
    (hS₁S₂ : hyp.sSetIrrDegT hG hvd (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)))
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      (χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * chars.u : ℕ) : ℂ))
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.T ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ)) :
    False := by
  classical
  -- ── (9.11.1) `𝒮₂ = 𝒮₁`: the saturated-bound extraction (residual)
  have hS₂cut := hyp.nineElevenSTwoExtractionT hG hvd chars caseA S₂ hS₁S₂ hS₂S h2a hCUprime
    hcount hFboundU
  have hS2deg : ∀ χ ∈ S₂,
      (χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) :=
    fun χ hχ => (hS₂cut hχ).2.2
  -- ── dictionary: the `𝒮(H₀C)` stratum sits inside `𝒮 = 𝒮(H₀C′)` (`C′ ≤ C`)
  have hsubC : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
      ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := by
    rw [hyp.sSet_eq_sOf_H0Cprime_T hG hvd chars]
    exact OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupT hG hvd)
      (sup_le_sup_left chars.Cprime_le_C chief.H0)
  -- ── the `𝒮(H₀C)`-stratum degree dichotomy (`qu` outside `𝒮₂`, `qa` inside)
  have hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief),
      (φ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) := by
    intro φ hφ
    by_cases hφS₂ : φ ∈ S₂
    · exact Or.inr (hS2deg φ hφS₂)
    · exact Or.inl (hS3deg φ ⟨hsubC hφ, hφS₂⟩)
  -- ── (9.11.2): the two-summand inertia identity `C = K₁ ⊓ K₂`, `[U:Kᵢ] = a`
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    OddOrder.Peterfalvi.S11.nineElevenTwo_two_summand_inertia caseA hdich
  -- ── (9.11.3): the class equation at `n = |𝒮₄|·q + (p−1)`
  have hS₁'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁S₂ ⟨hyp.sOf_H0Uprime_subset_sSet_T hG hvd chars hχ.1, hχ.2.1, hχ.2.2⟩
  have hCU : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief
      = OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd) := hCUprime
  have hclass := OddOrder.Peterfalvi.S11.nineElevenThree_orbit_split hG caseA hS₁'sub
    (fun χ hχ hn => hS3deg χ ⟨hsubC hχ, hn⟩) hS2deg hCU hcount
  -- ── (9.11.4)–(9.11.8): the norm bound `|𝒮₄| ≤ N` (residual)
  obtain ⟨N, hnorm, hleN⟩ := hyp.nineElevenNormBoundT hG hnoV pins hvd hTP Tdata hU hW1 hW2
    chars caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne hnopair h2a hCUprime hS3deg hcount hFboundU
    hS2deg
  -- ── numerics: `q ≥ 3` odd prime, `u ≥ 1`, `p = 2a+1`
  have hqp : ((hyp.toTypesIIIIIIVSetupT hG hvd).q).Prime :=
    (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1
  have hqodd : Odd (hyp.toTypesIIIIIIVSetupT hG hvd).q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1)
  have hq3 : 3 ≤ (hyp.toTypesIIIIIIVSetupT hG hvd).q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu : 1 ≤ chars.u := (OddOrder.Peterfalvi.S11.u_odd hG chars).pos
  have hp1 : 1 < chief.p := chief.p_prime.one_lt
  have hpeq : chief.p = 2 * caseA.a + 1 := by omega
  -- ── the tau-free arithmetic core closes
  exact OddOrder.Peterfalvi.S11.nineElevenCaseA_equality_refutation caseA hq3 hu hpeq
    hK₁ hK₂ hCinf hclass rfl hnorm hleN

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.1)–(9.11.8), the `T`-instance equality-configuration refutation** (mirror;
issue 2035,
consumed by `sSet_coherent_indT_caseA`, mirroring the M-instance
`nineElevenSevenEightRefutation` / `nineElevenEqualityRefutation_of_sevenEightRefutation`).

Given a maximal proper coherent conjugation-closed `𝒮₂` with the degree-`q·a` base cut
`S₁(q·a) ⊆ 𝒮₂ ⊊ 𝒮 = sSet`, `𝒮₃ = 𝒮 ∖ 𝒮₂ ≠ ∅` and *no* conjugate pair `{χ, χ̄}` (`χ ∈ 𝒮₃`)
coherently adjoinable, derive `False`.

**Reuse map (verified STEP-1 for the assembly, issue 1017 hub note).**  Via
`sSet_eq_sOf_H0Cprime` the full family `𝒮` *is* the `H₀C′` stratum
`sOf data (chief.H₀ ⊔ chars.Cprime)`,
so the entire generic (9.11) apparatus — all phrased over `sOf data (chief.H₀ ⊔ …)`,
`{data}{chief}{chars}(caseA)`-parametrized, hence directly instantiable at `data :=
toTypesIIIIIIVSetupT hG hvd` — applies:
* the (9.11.2)–(9.11.5) arithmetic contradiction `S11.nineElevenCaseA_equality_refutation`;
* the (9.11.1) squeeze `S11.nineElevenOne_configuration` + `S11.sumnS_irreducible_constant_degree`;
* the world-facts *from the degree dichotomy*: `S11.nineElevenTwoTIWitness_of_degree_dichotomy`
  (TI-witness), `S11.nineElevenTwo_two_summand_inertia` (inertia `C = K₁ ⊓ K₂`),
  `S11.nineElevenGamma_inner_self_mul_u` (Mackey norm), `S11.nineElevenThree_orbit_split` (class
  eq);
* the abstract projection budget `S07.exists_bridge_target_of_budget` and the (5.6.3) union-pair
  extension `S07.isCoherent_union_pair_of_bridge` for the (9.11.7)–(9.11.8) coherent-pair
  adjunction.
The genuinely `S`-specific pieces still to build are the caseA per-member Dade `R`-family (the
analogue of the M-side `sOf_H0Cprime_memberRFamily`, feeding `𝒮₃`-coherence and the coherent-image
cross-orthogonality) and the (5.6) pair-bound producer for the `indS`/`A(S)` world; the (9.11.7)–
(9.11.8) orthogonal branch is itself a residual on the M-side (issue 9083 Phase E). -/
theorem Hypothesis.sSet_caseA_nineElevenRefutation_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.T ℂ))
    (hS₁S₂ : hyp.sSetIrrDegT hG hvd (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂coh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)))
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂).Nonempty)
    (hnopair : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T))) :
    False := by
  classical
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- numeric positivity inputs of the (9.11.1) squeeze
  have hq : 0 < (hyp.toTypesIIIIIIVSetupT hG hvd).q :=
    (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1.pos
  have hu : 0 < chars.u := (OddOrder.Peterfalvi.S11.u_odd hG chars).pos
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  -- strata collapse (mirror; issue 2035 step (a)): the generic (9.11) `U′`-anchor stratum is the
  -- full family
  have hcollapse : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd))
      = sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := hyp.sOf_H0_uprime_eq_sSet_T hG hvd chief
  -- the degree-`qa` anchor cut over the `U′`-stratum sits inside `𝒮₂` (it is `S₁(qa) ⊆ 𝒮₂`)
  have hS1'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
        IsIrreducibleCharacter χ ∧
          χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)} ⊆ S₂ :=
    fun χ hχ => hS₁S₂ ⟨hcollapse ▸ hχ.1, hχ.2.1, hχ.2.2⟩
  have hS1'fin : ({χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
        IsIrreducibleCharacter χ ∧
          χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}).Finite :=
    (sSet_finite (hyp.toTypesIIIIIIVSetupT hG hvd)).subset (fun χ hχ => hcollapse ▸ hχ.1)
  -- (9.11.5) left endpoint: `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one uniform degree-`qa` irreducibles)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ)
        * (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℝ) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  have hs1' : (({χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard : ℝ))
        * (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℝ) ^ 2
      ≤ OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset :=
    le_of_eq (by rw [Set.ncard_eq_toFinset_card _ hS1'fin, hsum1'])
  -- per-`χ` (9.11.1) squeeze: the (5.6) pair-bound + squeeze force the equality configuration
  have hconfig : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ∃ d : ℕ, ((χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * d : ℕ) : ℂ)) ∧
        (2 * caseA.a = chief.p - 1 ∧ chars.C = chars.Uprime ∧ d = chars.u ∧
          {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
              (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
              IsIrreducibleCharacter χ ∧
                χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard
            * (caseA.a * caseA.a)
            = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
              (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U)) ∧
        (∀ F : Finset (ClassFunction ↥hyp.T ℂ), ↑F ⊆ S₂ →
          OddOrder.Peterfalvi.S07.sumnS F
            ≤ 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ)) := by
    intro χ hχ
    obtain ⟨d, hχdeg, hdu, hFbound⟩ :=
      hyp.nineElevenPairBoundT hG hnoV pins hvd hTP Tdata hU hW1 hW2 chars caseA S₂ hS₁S₂ hS₂S
          hS₂conj hS₂coh χ hχ (hnopair χ hχ)
    have hpair : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
        ≤ 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2 * (caseA.a : ℝ) * (d : ℝ) :=
      hFbound hS1'fin.toFinset (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
    exact ⟨d, hχdeg,
      OddOrder.Peterfalvi.S11.nineElevenOne_configuration hG caseA hq hu hp1 hdu hs1' hpair,
      hFbound⟩
  -- extract the global equality-configuration facts from a `𝒮₃`-witness
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  obtain ⟨d₀, -, ⟨h2a, hCUprime, hd₀u, hcount⟩, hFbound₀⟩ := hconfig χ₀ hχ₀
  -- every `𝒮₃`-member has the uniform degree `qu` (the squeeze run per member)
  have hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      (χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * chars.u : ℕ) : ℂ) := by
    intro χ hχ
    obtain ⟨d, hχdeg, ⟨-, -, hdu, -⟩, -⟩ := hconfig χ hχ
    rwa [hdu] at hχdeg
  -- the saturated subfamily bound `sumnS F ≤ 2q²au`
  have hFboundU : ∀ F : Finset (ClassFunction ↥hyp.T ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F
        ≤ 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    intro F hF
    have h := hFbound₀ F hF
    rwa [hd₀u] at h
  -- hand the equality configuration to the (9.11.2)–(9.11.8) refutation residual
  exact hyp.nineElevenEqualityRefutationT hG hnoV pins hvd hTP Tdata hU hW1 hW2 chars caseA S₂ hS₁S₂
      hS₂S hS₂conj hS₂coh
    ⟨χ₀, hχ₀⟩ hnopair h2a hCUprime hS3deg hcount hFboundU

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) non-Galois-branch coherence of the full family `𝒯 = sSet(setupT)` on `Ind_T^G`**
(mirror of `sSet_coherent_indS_caseA`; caseA-`T` of Peterfalvi (9.11) `Ptype_core_coherence`).
In the non-Galois case the honest `T`-instance §9 family is genuinely mixed-degree, so this is
the (9.11) maximal-coherent-subfamily refutation, not the uniform Galois route
(`sSet_coherent_dade_caseB_T`).

Honest route via the generic `coherent_of_maximal_coherent_pair_refuted`:
* **base** = the degree-`p·a` irreducible cut `S₁(p·a)` is the coherent conjugation-closed
  prefix (`sSetIrrDegT_pa_coherent_indT_caseA`, landed sorry-free);
* **reduction** = `𝒯` is finite (`sSet_finite`) and conjugation-closed
  (`sSet_closedUnderConjugate`), so a maximal proper coherent conj-closed intermediate either
  equals `𝒯` (done) or is the (9.11) refutation target;
* **refuter** = `sSet_caseA_nineElevenRefutation_T` (now a real proof — the assembled
  `T`-mirror of the discharged `S`-side chain). -/
theorem Hypothesis.sSet_coherent_indT_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) := by
  classical
  refine OddOrder.Peterfalvi.S07.coherent_of_maximal_coherent_pair_refuted
    (sSet_finite _)
    (sSet_closedUnderConjugate _)
    (hyp.sSetIrrDegT_subset_sSet hG hvd
      (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ))
    (hyp.sSetIrrDegT_closedUnderConjugate hG hvd
      (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) (star_natCast _))
    (hyp.sSetIrrDegT_pa_coherent_indT_caseA hG hnoV hvd hTP chars caseA)
    ?_
  intro S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne hnopair
  exact hyp.sSet_caseA_nineElevenRefutation_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 chars
    caseA S₂ hS₁S₂ hS₂S hS₂conj hS₂coh hS₃ne hnopair

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) coherence of the full honest `T`-instance §9 family `𝒯 = sSet(setupT)` on
`Ind_T^G`** (mirror of `sSet_coherent_indS_A` — the `T`-instance Peterfalvi (9.11)
`Ptype_core_coherence`).  Case-splits the Clifford dichotomy (9.7) (`clifford_dichotomy` at
`mkSection11CharacterDataT`) and dispatches: the non-Galois branch is
`sSet_coherent_indT_caseA`; the Galois branch is the landed uniform-degree Dade coherence
`sSet_coherent_dade_caseB_T`, re-grounded from the honest `T`-Dade map onto plain induction by
`tInstance_dade_eq_induce` (the (13.2.e)-at-`T` trivial-stabilizer computation) via
`IsCoherent.congrMap`.  The map is the genuine induction `τ = Ind_T^G` (`indT`) and the support
is the honest Dade support `A(T)`. -/
theorem Hypothesis.sSet_coherent_indT_A [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indT
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) := by
  rcases clifford_dichotomy hG (hyp.mkSection11CharacterDataT hG hvd chief) with hA | hB
  · exact hyp.sSet_coherent_indT_caseA hG hnoV pins hvd hTP Tdata hU hW1 hW2
      (hyp.mkSection11CharacterDataT hG hvd chief) hA.some
  · exact (hyp.sSet_coherent_dade_caseB_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 hB.some).map
      fun c => c.congrMap fun φ hφ => by
        rw [hyp.indT_apply]
        exact hyp.tInstance_dade_eq_induce hG hnoV hTP hφ.2

end OddOrder.Peterfalvi.S15


