-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenSevenEight
-- name    : OddOrder_Peterfalvi_S15_NineElevenSevenEight
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:34:56.594242+00:00
-- url     : https://prove2.me/theorems/176622b6-0425-4605-b46c-9313eb2acf62
-- title:
--   Peterfalvi (9.11.7)–(9.11.8): the $S$-instance orthogonal-branch refutation
-- statement:
--   Formalizes the budget refutation of (9.11.7)–(9.11.8) for the honest $S$-instance.
--
--   Main declarations: `Hypothesis.nineElevenSevenEightRefutationS` (Peterfalvi (9.11.7)–(9.11.8), the orthogonal-branch refutation — `S`-instance residual).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_NineElevenSevenEight.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_NineElevenSevenEight.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenSteps

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.7)–(9.11.8), the orthogonal-branch refutation — `S`-instance residual**
(issue 1017; the `S`-mirror of the M-side `S13.NineElevenSevenEightRefutation`, **discharged**
M-side by `nineElevenSevenEightRefutation`, Coq `PFsection9.v:2048-2227`).  In the orthogonal
branch `α^τ ⊥ 𝒮₃^{τ₃}` of the (9.11.6) dichotomy: `𝒮₄ ≠ ∅` (else the (9.11.2)–(9.11.5)
arithmetic spine already refutes), pick `λ₁ ∈ 𝒮₄`, put `e = u/a` and `β = λ₁ − e·ψ₁`; the
projection budget (`S07.exists_bridge_target_of_budget`) over the orthonormal families
`𝒮₂^{τ₁}` and `𝒮₄^{τ₃}` — cross-orthogonal via the case-agnostic `sSet_memberRFamily` —
produces `Γ ∈ ℤ[Irr G]` with `‖Γ‖² = 1` and the bridge `β^τ = Γ − e·τ₁ψ₁`; the union-pair
extension (`S07.isCoherent_union_pair_of_bridge`) then adjoins `{λ₁, λ̄₁}` coherently to `𝒮₂`,
contradicting the pair clause `hnopairD`.  All coherence clauses on the honest `'A`-Dade
(`dadeHypS`/`A(S)`), converted from `indS` by the caller. -/
theorem Hypothesis.nineElevenSevenEightRefutationS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.S ℂ))
    (hS₁S₂ : hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₂cohD : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData)) S₂
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)))
    (_hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hnopairD : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData))
        (S₂ ∪ {χ, χ.conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ))
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ))
    (hS2deg : ∀ χ ∈ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
    (c₃ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData))
      (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S))
    (γ ψ₁ : ClassFunction ↥hyp.S ℂ)
    (hψ₁S₂ : ψ₁ ∈ S₂)
    (_hψ₁irr : IsIrreducibleCharacter ψ₁)
    (hψ₁deg : (ψ₁ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
    (hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S)
    (_hγ1 : (γ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
    (hγorth : ∀ φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG), ClassFunction.inner γ φ = 0)
    (hαsupp : ((γ - ψ₁ : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)
    (hc : ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
          ((hyp.dadeHypS hG).fullDadeIsometryData) (γ - ψ₁))
        (c₃.extension lam) = 0) :
    False := by
  classical
  have := hyp.finiteG
  obtain ⟨c₁⟩ := hS₂cohD
  -- ── ambient family facts
  have hSfin : (sSet (hyp.toTypesIIIIIIVSetupS hG)).Finite :=
    sSet_finite (hyp.toTypesIIIIIIVSetupS hG)
  have hS₂fin : S₂.Finite := hSfin.subset hS₂S
  have hS₂cut := hyp.nineElevenSTwoExtractionS hG chars caseA S₂ hS₁S₂ hS₂S h2a hCUprime
    hcount hFboundU
  have hψ₁sSet : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) := hS₂S hψ₁S₂
  have hselfone : ∀ {χ : ClassFunction ↥hyp.S ℂ}, IsIrreducibleCharacter χ →
      ClassFunction.inner χ χ = 1 := by
    intro χ hχ
    have h := irreducibleCharacter_inner_eq_ite
      (⟨χ, hχ⟩ : IrreducibleCharacter ↥hyp.S) ⟨χ, hχ⟩
    rwa [if_pos rfl] at h
  -- ── the explicit (9.11.2) TI-witness `U₁ = cuSubOf caseA 0`: `C ≤ U₁ ≤ U`, `[U:U₁] = a`
  have hq0 : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  have hCU₁ : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
      ≤ cuSubOf caseA ⟨0, hq0⟩ := cSub_le_cuSubOf caseA ⟨0, hq0⟩
  have hU₁U : cuSubOf caseA ⟨0, hq0⟩ ≤ (hyp.toTypesIIIIIIVSetupS hG).U :=
    cuSubOf_le_U caseA ⟨0, hq0⟩
  have hU₁a : (cuSubOf caseA ⟨0, hq0⟩).relIndex (hyp.toTypesIIIIIIVSetupS hG).U = caseA.a :=
    relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩
  obtain ⟨e, hedef⟩ : ∃ e : ℕ,
      e = (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief).relIndex
        (cuSubOf caseA ⟨0, hq0⟩) := ⟨_, rfl⟩
  have hue : e * caseA.a = chars.u := by
    rw [hedef]
    have h := Subgroup.relIndex_mul_relIndex
      (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      (cuSubOf caseA ⟨0, hq0⟩) (hyp.toTypesIIIIIIVSetupS hG).U hCU₁ hU₁U
    rwa [hU₁a, relIndex_cSub_U_eq_u chars] at h
  -- ── the `𝒮(H₀C)`-stratum dictionary and degree dichotomy
  have hsubC : OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := by
    rw [hyp.sSet_eq_sOf_H0Cprime hG chars]
    exact OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupS hG)
      (sup_le_sup_left chars.Cprime_le_C chief.H0)
  have hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) := by
    intro φ hφ
    by_cases hφS₂ : φ ∈ S₂
    · exact Or.inr (hS2deg φ hφS₂)
    · exact Or.inl (hS3deg φ ⟨hsubC hφ, hφS₂⟩)
  -- ── `𝒮₄ ≠ ∅`: else the (9.11.2)–(9.11.5) arithmetic spine already refutes
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ :=
    OddOrder.Peterfalvi.S11.nineElevenTwo_two_summand_inertia caseA hdich
  have hS₁'sub : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} ⊆ S₂ := fun χ hχ =>
    hS₁S₂ ⟨hyp.sOf_H0Uprime_subset_sSet hG chars hχ.1, hχ.2.1, hχ.2.2⟩
  have hCU : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
      = OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG) := hCUprime
  have hclass := OddOrder.Peterfalvi.S11.nineElevenThree_orbit_split hG caseA hS₁'sub
    (fun χ hχ hn => hS3deg χ ⟨hsubC hχ, hn⟩) hS2deg hCU hcount
  obtain ⟨N, hnormN, -⟩ := hyp.nineElevenFourNormInputsS hG chars caseA hdich hCUprime hcount
  have hqp : ((hyp.toTypesIIIIIIVSetupS hG).q).Prime :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1
  have hqodd : Odd (hyp.toTypesIIIIIIVSetupS hG).q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)
  have hq3 : 3 ≤ (hyp.toTypesIIIIIIVSetupS hG).q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu1 : 1 ≤ chars.u := (OddOrder.Peterfalvi.S11.u_odd hG chars).pos
  have hp1 : 1 < chief.p := chief.p_prime.one_lt
  have hpeq : chief.p = 2 * caseA.a + 1 := by omega
  have hS4ne : ({φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
      IsIrreducibleCharacter φ ∧ φ ∉ S₂} : Set (ClassFunction ↥hyp.S ℂ)).Nonempty := by
    rcases Set.eq_empty_or_nonempty
      ({φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
        IsIrreducibleCharacter φ ∧ φ ∉ S₂} : Set (ClassFunction ↥hyp.S ℂ)) with hemp | hne
    · exact absurd
        (OddOrder.Peterfalvi.S11.nineElevenCaseA_equality_refutation caseA hq3 hu1 hpeq
          hK₁ hK₂ hCinf hclass rfl hnormN
          (by rw [hemp, Set.ncard_empty]; exact Nat.zero_le N))
        not_false
    · exact hne
  obtain ⟨lam₁, hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩ := hS4ne
  -- ── `𝒮₄ ⊆ 𝒮₃` along `H₀C′ ≤ H₀C`; the pair `{λ₁, λ̄₁}` lives in `𝒮₄`
  have hS4sub : {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
      IsIrreducibleCharacter φ ∧ φ ∉ S₂}
      ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂ := fun ξ hξ => ⟨hsubC hξ.1, hξ.2.2⟩
  have hlam₁S₃ : lam₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂ :=
    hS4sub ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩
  have hlam₁c_S₄ : lam₁.conj ∈ {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
      IsIrreducibleCharacter φ ∧ φ ∉ S₂} := by
    refine ⟨OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate
      (hyp.toTypesIIIIIIVSetupS hG) _ hlam₁sOfC, hlam₁irr.conj, ?_⟩
    intro hmem
    apply hlam₁nS₂
    have h := hS₂conj hmem
    rwa [ClassFunction.conj_conj] at h
  have hlam₁cS₃ : lam₁.conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂ := hS4sub hlam₁c_S₄
  have hlam₁ne : lam₁ ≠ lam₁.conj := fun h =>
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG)
      hlam₁S₃.1 h.symm
  have hlam₁deg : (lam₁ : ↥hyp.S → ℂ)
      1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) := hS3deg lam₁ hlam₁S₃
  -- ── `e ≥ 2`: `u ≠ a` since a degree-`qa` irreducible member would lie in `𝒮₁ ⊆ 𝒮₂`
  have hune : chars.u ≠ caseA.a := by
    intro huea
    apply hlam₁nS₂
    apply hS₁S₂
    refine ⟨hlam₁S₃.1, hlam₁irr, ?_⟩
    rw [hlam₁deg, huea]
  have he2 : 2 ≤ e := by
    have ha1 : 1 ≤ caseA.a := caseA.a_pos
    rcases Nat.lt_or_ge e 2 with h | h
    · exfalso
      interval_cases e
      · rw [zero_mul] at hue
        omega
      · rw [one_mul] at hue
        exact hune hue.symm
    · exact h
  -- ── `|𝒮₂| = 2e` from the (9.8.d) count at the equality configuration
  have hS₂eq : S₂ = {φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter φ ∧
      φ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} :=
    Set.Subset.antisymm hS₂cut hS₁'sub
  have hcardS₂ : hS₂fin.toFinset.card = 2 * e := by
    have hrelu : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)).relIndex
        (hyp.toTypesIIIIIIVSetupS hG).U = chars.u := by
      rw [← hCU]
      exact relIndex_cSub_U_eq_u chars
    have hcount' : S₂.ncard * (caseA.a * caseA.a) = 2 * e * (caseA.a * caseA.a) := by
      rw [hS₂eq, hcount, hrelu, ← h2a, ← hue]
      ring
    have ha0 : 0 < caseA.a * caseA.a := Nat.mul_pos caseA.a_pos caseA.a_pos
    have hncard : S₂.ncard = 2 * e := Nat.eq_of_mul_eq_mul_right ha0 hcount'
    rw [← Set.ncard_eq_toFinset_card _ hS₂fin]
    exact hncard
  -- ── orthonormality of the source families
  have hON1 : ∀ φ ∈ S₂, ClassFunction.inner φ φ = 1 := fun φ hφ =>
    hselfone (hS₂cut hφ).2.1
  have hON2 : ∀ φ ∈ S₂, ∀ ξ ∈ S₂, φ ≠ ξ → ClassFunction.inner φ ξ = 0 :=
    fun φ hφ ξ hξ hne =>
      sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) (hS₂S hφ) (hS₂S hξ) hne
  -- ── `𝒮₃` is conjugation-closed; cross-orthogonality of the coherent images
  have hS₃conj : ∀ x ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      x.conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂ := by
    intro x hx
    refine ⟨sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hx.1, ?_⟩
    intro hcmem
    apply hx.2
    have h := hS₂conj hcmem
    rwa [ClassFunction.conj_conj] at h
  have hcross : ∀ φ ∈ S₂,
      ∀ lam ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ClassFunction.inner (c₁.extension φ) (c₃.extension lam) = 0 := by
    intro φ hφ lam hlam
    exact hyp.sSet_coherent_extension_cross_orthogonal hG hnoV hS₂S Set.sdiff_subset c₁ c₃
      hφ (hS₂conj hφ) hlam (hS₃conj lam hlam)
      (fun h => hlam.2 (h ▸ hφ)) (fun h => (hS₃conj lam hlam).2 (h ▸ hφ))
  -- ── `β = λ₁ − e·ψ₁`: support, integrality, `τ`-image
  have hβdegℂ : (lam₁ : ↥hyp.S → ℂ) 1 = ((e : ℕ) : ℂ) * (ψ₁ : ↥hyp.S → ℂ) 1 := by
    rw [hlam₁deg, hψ₁deg, ← hue]
    push_cast
    ring
  have hβsupp : ((lam₁ - e • ψ₁ : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S :=
    hyp.sSet_scaledDiff_support hG hlam₁S₃.1 hψ₁sSet hβdegℂ
  have hβsmul : (lam₁ - e • ψ₁ : ClassFunction ↥hyp.S ℂ) = lam₁ - ((e : ℕ) : ℂ) • ψ₁ := by
    rw [Nat.cast_smul_eq_nsmul]
  have hβZIrr : (lam₁ - e • ψ₁ : ClassFunction ↥hyp.S ℂ)
      ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
    Submodule.sub_mem _ (sSet_subset_ZIrr (hyp.toTypesIIIIIIVSetupS hG) hlam₁S₃.1)
      (nsmul_mem (sSet_subset_ZIrr (hyp.toTypesIIIIIIVSetupS hG) hψ₁sSet) e)
  have hτβZ : (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁) ∈
          OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS hG) hβsupp hβZIrr
  have hαZIrr : (γ - ψ₁ : ClassFunction ↥hyp.S ℂ)
      ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
    Submodule.sub_mem _ hγZIrr (sSet_subset_ZIrr (hyp.toTypesIIIIIIVSetupS hG) hψ₁sSet)
  have hταZ : (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (γ - ψ₁) ∈
          OddOrder.RepresentationTheory.ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS hG) hαsupp hαZIrr
  -- ── supported differences and their `τ₁`/`τ₃` images
  have hψdiffsupp : ∀ φ ∈ S₂,
      ((φ - ψ₁ : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
    intro φ hφ
    have h := hyp.sSet_scaledDiff_support hG (hS₂S hφ) hψ₁sSet (c := 1)
      (by rw [hS2deg φ hφ, hψ₁deg, Nat.cast_one, one_mul])
    rwa [one_smul] at h
  have hτ₁diff : ∀ φ ∈ S₂,
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (φ - ψ₁) = c₁.extension φ -
          c₁.extension ψ₁ := by
    intro φ hφ
    rw [← map_sub]
    exact (c₁.extends_on_supported (φ - ψ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hφ) (Submodule.subset_span hψ₁S₂),
        hψdiffsupp φ hφ⟩).symm
  have hDsupp : ((lam₁ - lam₁.conj : ClassFunction ↥hyp.S ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
    rw [show (lam₁ - lam₁.conj : ClassFunction ↥hyp.S ℂ) = -(lam₁.conj - lam₁) from by abel,
      ClassFunction.support_neg]
    exact hyp.sSet_member_conjDiff_supported hG hlam₁S₃.1
  have hτD : (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj) =
          c₃.extension lam₁ - c₃.extension lam₁.conj := by
    rw [← map_sub]
    exact (c₃.extends_on_supported (lam₁ - lam₁.conj)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hlam₁S₃)
        (Submodule.subset_span hlam₁cS₃), hDsupp⟩).symm
  -- ── scalar values at the source
  have hll1 : ClassFunction.inner lam₁ lam₁ = 1 := hselfone hlam₁irr
  have hlclc : ClassFunction.inner lam₁.conj lam₁.conj = 1 := hselfone hlam₁irr.conj
  have hllc : ClassFunction.inner lam₁ lam₁.conj = 0 :=
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hlam₁S₃.1 hlam₁cS₃.1 hlam₁ne
  have hψψ : ClassFunction.inner ψ₁ ψ₁ = 1 := hON1 ψ₁ hψ₁S₂
  have hψl : ClassFunction.inner ψ₁ lam₁ = 0 :=
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hψ₁sSet hlam₁S₃.1
      (fun h => hlam₁nS₂ (h ▸ hψ₁S₂))
  have hψlc : ClassFunction.inner ψ₁ lam₁.conj = 0 :=
    sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hψ₁sSet hlam₁cS₃.1
      (fun h => hlam₁cS₃.2 (h ▸ hψ₁S₂))
  have hlψ : ClassFunction.inner lam₁ ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁, hψl, star_zero]
  have hlcψ : ClassFunction.inner lam₁.conj ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁.conj, hψlc, star_zero]
  have hlcl : ClassFunction.inner lam₁.conj lam₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm lam₁ lam₁.conj, hllc, star_zero]
  -- ── the budget inputs
  have hS4fin : ({φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) |
      IsIrreducibleCharacter φ ∧ φ ∉ S₂} : Set (ClassFunction ↥hyp.S ℂ)).Finite :=
    hSfin.subset (fun ξ hξ => (hS4sub hξ).1)
  have hτβnorm : ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁))
          ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁))
      = ((e : ℕ) : ℂ) ^ 2 + 1 := by
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) hβsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hll1, hlψ, hψl, hψψ, star_natCast, mul_zero, mul_one, sub_zero, zero_sub]
    ring
  have hτβconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁))
          (c₁.extension φ)
        = ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁))
          (c₁.extension ψ₁)
          + ((e : ℕ) : ℂ) := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hβφ : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥hyp.S ℂ) (φ - ψ₁)
        = ((e : ℕ) : ℂ) := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hlψ, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm),
        show ClassFunction.inner lam₁ φ = 0 from by
          rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam₁,
            sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) (hS₂S hφ) hlam₁S₃.1
              (fun h => hlam₁nS₂ (h ▸ hφ)),
            star_zero],
        mul_zero, mul_one, sub_zero, zero_sub, sub_neg_eq_add, zero_add]
    have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) hβsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hβφ] at hiso
    linear_combination hiso
  have hτβD : ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS
      hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁))
          (c₃.extension lam₁)
      - ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁))
          (c₃.extension lam₁.conj) = 1 := by
    have hβD : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥hyp.S ℂ)
        (lam₁ - lam₁.conj) = 1 := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hll1, hllc, hψl, hψlc, mul_zero, sub_zero]
    have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) hβsupp hDsupp
    rw [hτD, ClassFunction.inner_sub_right, hβD] at hiso
    exact hiso
  have hτατβ : ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS
      hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (γ - ψ₁))
          ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁))
      = ((e : ℕ) : ℂ) := by
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) hαsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right, hγorth lam₁ hlam₁S₃.1,
      hγorth ψ₁ hψ₁sSet, hψl, hψψ, star_natCast, mul_zero, mul_one, zero_sub, sub_zero,
      sub_neg_eq_add, zero_add]
  have hταconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (γ - ψ₁)) (c₁.extension φ)
        = ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (γ - ψ₁)) (c₁.extension ψ₁)
          + 1 := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hαφ : ClassFunction.inner (γ - ψ₁ : ClassFunction ↥hyp.S ℂ) (φ - ψ₁) = 1 := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        hγorth φ (hS₂S hφ), hγorth ψ₁ hψ₁sSet, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm), zero_sub, sub_neg_eq_add,
        zero_add, sub_self]
    have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) hαsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hαφ] at hiso
    linear_combination hiso
  -- ── run the projection budget
  obtain ⟨Γ0, hΓZ, hΓ1, hθ₁Γ, hΓD, hTBeq⟩ :=
    OddOrder.Peterfalvi.S07.exists_bridge_target_of_budget (Γ' := G)
      (SF := hS₂fin.toFinset) (S4F := hS4fin.toFinset)
      (fun φ => c₁.extension φ) (fun ξ => c₃.extension ξ)
      (TB := (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - e • ψ₁)) (TA :=
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (γ - ψ₁))
      (ψ₁ := ψ₁) (l₁ := lam₁) (l₂ := lam₁.conj) (e := e)
      (hS₂fin.mem_toFinset.mpr hψ₁S₂)
      (hS4fin.mem_toFinset.mpr ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩)
      (hS4fin.mem_toFinset.mpr hlam₁c_S₄)
      he2 hcardS₂
      (by
        intro φ hφF ξ hξF
        have hφ := hS₂fin.mem_toFinset.mp hφF
        have hξ := hS₂fin.mem_toFinset.mp hξF
        rw [c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ)
          (Submodule.subset_span hξ)]
        by_cases h : φ = ξ
        · subst h; rw [if_pos rfl]; exact hON1 φ hφ
        · rw [if_neg h]; exact hON2 φ hφ ξ hξ h)
      (by
        intro ξ hξF ξ' hξ'F
        have hξ := hS4sub (hS4fin.mem_toFinset.mp hξF)
        have hξ' := hS4sub (hS4fin.mem_toFinset.mp hξ'F)
        rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ)
          (Submodule.subset_span hξ')]
        by_cases h : ξ = ξ'
        · subst h
          rw [if_pos rfl]
          exact hselfone (hS4fin.mem_toFinset.mp hξF).2.1
        · rw [if_neg h]
          exact sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hξ.1 hξ'.1 h)
      (fun φ hφF ξ hξF => hcross φ (hS₂fin.mem_toFinset.mp hφF)
        ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      (fun ξ hξF => c₃.extension_mem_ZIrr ξ
        (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF))))
      (fun φ hφF => c₁.extension_mem_ZIrr φ
        (Submodule.subset_span (hS₂fin.mem_toFinset.mp hφF)))
      hτβZ hτβnorm hτβconst hτβD hτατβ
      (fun ξ hξF => hc ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      hταconst
      (ClassFunction.inner_mem_ZIrr_int hταZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (fun ξ hξF => ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₃.extension_mem_ZIrr ξ
          (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF)))))
  -- ── the pair targets `X = Γ0`, `Xc = Γ0 − (λ₁ − λ̄₁)^τ`
  have hΓτD : ClassFunction.inner Γ0 ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj)) = 1 :=
          by
    rw [hτD, ClassFunction.inner_sub_right, hΓD]
  have hτDΓ : ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS
      hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj)) Γ0 =
          1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Γ0
        ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj)),
      hΓτD, star_one]
  have hτDτD : ClassFunction.inner ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS
      hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj))
          ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj)) = 2 :=
          by
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) hDsupp hDsupp]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hll1, hllc, hlcl, hlclc, sub_zero, zero_sub, sub_neg_eq_add]
    norm_num
  have hτDZ : (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj) ∈
          OddOrder.RepresentationTheory.ZIrr G := by
    rw [hτD]
    exact Submodule.sub_mem _
      (c₃.extension_mem_ZIrr lam₁ (Submodule.subset_span hlam₁S₃))
      (c₃.extension_mem_ZIrr lam₁.conj (Submodule.subset_span hlam₁cS₃))
  -- ── adjoin the pair `{λ₁, λ̄₁}` coherently to `𝒮₂` (the (5.6.3) union-pair extension)
  have hunion : OddOrder.Peterfalvi.S07.IsCoherent (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
      (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (S₂ ∪ {lam₁, lam₁.conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S) := by
    refine OddOrder.Peterfalvi.S07.isCoherent_union_pair_of_bridge (E := ((e : ℕ) : ℤ))
      hS₂fin hON1 hON2
      (fun φ hφ ξ hξ => c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ)
        (Submodule.subset_span hξ))
      (fun φ hφ => c₁.extends_on_supported φ hφ)
      (fun φ hφ => c₁.extension_mem_ZIrr φ (Submodule.subset_span hφ))
      hlam₁ne hll1 hlclc hllc
      (fun φ hφ => sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG)
        (hS₂S hφ) hlam₁S₃.1 (fun h => hlam₁nS₂ (h ▸ hφ)))
      (fun φ hφ => sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG)
        (hS₂S hφ) hlam₁cS₃.1 (fun h => hlam₁cS₃.2 (h ▸ hφ)))
      hΓ1 ?_ ?_ hΓZ
      (Submodule.sub_mem _ hΓZ hτDZ)
      (fun φ hφ => hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ)) ?_ ?_ hDsupp hψ₁S₂ ?_ ?_
    · -- `‖Xc‖² = 1`
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hΓ1, hΓτD, hτDΓ, hτDτD]
      norm_num
    · -- `⟨X, Xc⟩ = 0`
      rw [ClassFunction.inner_sub_right, hΓ1, hΓτD]
      norm_num
    · -- `τ₁𝒮₂ ⊥ Xc`
      intro φ hφ
      rw [ClassFunction.inner_sub_right, hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ), hτD,
        ClassFunction.inner_sub_right,
        hcross φ hφ lam₁ hlam₁S₃, hcross φ hφ lam₁.conj hlam₁cS₃]
      norm_num
    · -- `(λ₁ − λ̄₁)^τ = X − Xc`
      exact (sub_sub_cancel Γ0 ((OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - lam₁.conj))).symm
    · -- the bridge `(λ₁ − e·ψ₁)^τ = X − e·τ₁ψ₁` (`ℤ`-scalar form)
      change (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData)) (lam₁ - ((e : ℕ) : ℤ) • ψ₁)
          = Γ0 - ((e : ℕ) : ℤ) • c₁.extension ψ₁
      simp only [natCast_zsmul]
      rw [← Nat.cast_smul_eq_nsmul ℂ e (c₁.extension ψ₁)]
      exact hTBeq
    · -- the bridge support (`ℤ`-scalar form)
      show ((lam₁ - ((e : ℕ) : ℤ) • ψ₁ : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S
      simp only [natCast_zsmul]
      exact hβsupp
  exact hnopairD lam₁ hlam₁S₃ ⟨hunion⟩

end OddOrder.Peterfalvi.S15


