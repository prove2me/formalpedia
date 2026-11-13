-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_SixFiveGeneral
-- name    : OddOrder_Peterfalvi_S08_SixFiveGeneral
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:28:42.819197+00:00
-- url     : https://prove2.me/theorems/cb8a5cfb-1c1c-4d97-9667-8bc057b85c31
-- title:
--   Peterfalvi (6.5) for a general kernel: the (6.3.b) coherence input
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.5). The proof of (6.5)(a) opens by observing that hypothesis (a) of Theorem (6.3) holds with $H=K$, since $K/H_1$ is abelian and nontrivial, so that (6.3.b) holds by (5.7). The general-kernel (6.5) therefore needs the general-kernel (5.2) hypothesis for subfamilies.
--
--   Main definitions: `characterDifferenceImage_of_irreducible` (the (5.3.a) two-element image datum of an irreducible member) and `InducedFamilyTauData.hypothesisOfSubfamily` (Hypothesis (5.2) for a conjugation-closed subfamily with irreducible members), with lemmas such as `signedDifference_eq` and `orthogonal_of_tau_conjDiff_inner_eq_zero`.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_SixFiveGeneral.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_SixFiveGeneral.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoThreeFromImageFamilies
import Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceConstantDegree
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_GroupTheory_NilpotentAbelianization

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {A₀ : Set ↥L} {K : Subgroup ↥L} [K.Normal] [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (5.3.a) for an arbitrary `τ`.**  If `χ` is an irreducible non-real character and
`τ` is a (5.2.b) map — an isometry at `χ − χ̄`, landing in `ℤ[Irr G]` and vanishing at `1` (the
book's codomain `ℤ[Irr G, G^#]`) — then `τ(χ − χ̄) = ε·(μ − ν)` for distinct irreducible `μ, ν`
and a sign `ε`.

*Proof.*  `‖χ − χ̄‖² = 2` since `χ` is irreducible and `χ̄ ≠ χ`, so `‖τ(χ − χ̄)‖² = 2`; a virtual
character of norm-square `2` is a signed pair `ε_α·α + ε_β·β` of distinct irreducibles
(`exists_signed_pair_of_mem_ZIrr_inner_self_eq_two`, mathcomp `dirr_small_norm`).  Evaluating at
`1` gives `ε_α·α(1) + ε_β·β(1) = 0` with `α(1), β(1) > 0`, so the signs are opposite.

This is the book's "for `χ ∈ 𝒮`, `‖(χ − χ̄)^τ‖² = 2` and so (5.2.d) holds with `|R(χ)| = 2`"
(p. 25), made explicit in the signed shape that this repository's `S07.Hypothesis` takes. -/
theorem nonempty_characterDifferenceImage_of_irreducible
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G} {χ : ClassFunction ↥L ℂ}
    (hirr : IsIrreducibleCharacter χ) (hreal : ¬ ClassFunction.IsReal χ)
    (hisom : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) =
      ClassFunction.inner (χ - χ.conj) (χ - χ.conj))
    (hZ : τ (χ - χ.conj) ∈ ZIrr G) (h1 : τ (χ - χ.conj) (1 : G) = 0) :
    Nonempty (OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ) := by
  classical
  -- `‖χ − χ̄‖² = ⟨χ,χ⟩ − ⟨χ,χ̄⟩ − ⟨χ̄,χ⟩ + ⟨χ̄,χ̄⟩ = 1 − 0 − 0 + 1 = 2`.
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  have hne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  have hcross : ClassFunction.inner χ χ.conj = 0 := by
    simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ.conj, hconjirr⟩ |>.trans (if_neg (Ne.symm hne))
  have hcross' : ClassFunction.inner χ.conj χ = 0 := by
    simpa using irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hirr⟩ |>.trans (if_neg hne)
  have hnorm2 : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = 2 := by
    rw [hisom, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hirr.inner_self_eq_one, hconjirr.inner_self_eq_one,
      hcross, hcross']
    ring
  obtain ⟨α, β, εα, εβ, hαirr, hβirr, hαβ, hεα, hεβ, hsum⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hZ hnorm2
  -- degrees are positive naturals
  obtain ⟨a, hapos, ha⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨α, hαirr⟩ : IrreducibleCharacter G)
  obtain ⟨b, hbpos, hb⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨β, hβirr⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at ha hb
  -- evaluating at `1`: `εα·a + εβ·b = 0`, so the signs are opposite.
  have heval : (εα : ℂ) * (a : ℂ) + (εβ : ℂ) * (b : ℂ) = 0 := by
    have := congrArg (fun f : ClassFunction G ℂ => f (1 : G)) hsum
    simp only [ClassFunction.add_apply, ClassFunction.smul_apply] at this
    rw [h1, ha, hb] at this
    exact this.symm
  have hopp : εβ = -εα := by
    rcases hεα with rfl | rfl <;> rcases hεβ with rfl | rfl
    · exfalso
      have hz : ((a + b : ℕ) : ℂ) = 0 := by push_cast at heval ⊢; linear_combination heval
      have : a + b = 0 := by exact_mod_cast hz
      omega
    · rfl
    · rfl
    · exfalso
      have hz : ((a + b : ℕ) : ℂ) = 0 := by push_cast at heval ⊢; linear_combination -heval
      have : a + b = 0 := by exact_mod_cast hz
      omega
  exact ⟨
    { mu := ⟨α, hαirr⟩
      nu := ⟨β, hβirr⟩
      distinct := fun h => hαβ (congrArg Subtype.val h)
      sign := εα
      sign_eq := hεα
      image_eq := by
        rw [hsum, hopp]
        push_cast
        module }⟩

/-- The chosen (5.3.a) two-element image datum of an irreducible member — see
`nonempty_characterDifferenceImage_of_irreducible`.  Only its `image_eq` is ever used downstream
(through `signedDifference_eq`), so the choice is harmless. -/
noncomputable def characterDifferenceImage_of_irreducible
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G} {χ : ClassFunction ↥L ℂ}
    (hirr : IsIrreducibleCharacter χ) (hreal : ¬ ClassFunction.IsReal χ)
    (hisom : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) =
      ClassFunction.inner (χ - χ.conj) (χ - χ.conj))
    (hZ : τ (χ - χ.conj) ∈ ZIrr G) (h1 : τ (χ - χ.conj) (1 : G) = 0) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ :=
  (nonempty_characterDifferenceImage_of_irreducible hirr hreal hisom hZ h1).some

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [K.Normal] [Invertible (Nat.card ↥K : ℂ)] in
/-- `R(χ)`'s signed difference **is** `τ(χ − χ̄)` — `image_eq` read backwards.  Holds for *any*
`CharacterDifferenceImage`, so it is insensitive to the choice above. -/
theorem signedDifference_eq {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G}
    {χ : ClassFunction ↥L ℂ}
    (R : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ) :
    R.signedDifference = τ (χ - χ.conj) := R.image_eq.symm

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **A member's conjugate difference lies in `ℤ[𝒮, A₀]`.**  `χ̄ ∈ 𝒮(X)` by conjugation closure
and has the same degree as `χ` (`ClassFunction.conj` preserves the value at `1` up to complex
conjugation and degrees are real), so `χ − χ̄` is `K^#`-supported. -/
theorem conjDiff_mem_zSupportedSpan
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {X : Subgroup ↥L} {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ inducedKernelFamily K X) :
    (χ - χ.conj : ClassFunction ↥L ℂ) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) (inducedKernelFamily K ⊥) A₀ := by
  have hconj : χ.conj ∈ inducedKernelFamily K X :=
    inducedKernelFamily_closedUnderConjugate (K := K) X hχ
  refine ⟨Submodule.sub_mem _
    (Submodule.subset_span (inducedKernelFamily_subset_bot X hχ))
    (Submodule.subset_span (inducedKernelFamily_subset_bot X hconj)), ?_⟩
  have hneg : (χ - χ.conj : ClassFunction ↥L ℂ) = -(χ.conj - χ) := by abel
  rw [hneg, ClassFunction.support_neg]
  exact inducedKernelFamily_conjDiff_support hKsupp hχ

/-- **Peterfalvi (5.2.e) for irreducible members, derived** (the book's (5.3.a) argument): if
`φ ⊥ {χ, χ̄}` then `⟨(φ − φ̄)^τ, (χ − χ̄)^τ⟩ = ⟨φ − φ̄, χ − χ̄⟩ = 0`, because all four cross terms
vanish — two by hypothesis and two because `φ̄ ≠ χ`, `φ̄ ≠ χ̄` (else the hypothesis would read
`⟨φ, φ⟩ = 0` or `⟨φ, χ⟩ = ⟨χ, χ⟩ = 0`), so `inducedKernelFamily_pairwise_orthogonal` applies.

Stated for an arbitrary conjugation-closed subfamily `T ⊆ 𝒮` so that both the (6.5) filtrations
`𝒮(X)` and the (6.6) set `𝒳 = 𝒮 − 𝒮(Z)` can use it. -/
theorem tau_conjDiff_inner_eq_zero_of_orthogonal
    (RD : InducedFamilyTauData (G := G) A₀ K)
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {T : Set (ClassFunction ↥L ℂ)} (hTsub : T ⊆ inducedKernelFamily K ⊥)
    (hTconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate T)
    (hirr : ∀ φ ∈ T, IsIrreducibleCharacter φ)
    {φ χ : ClassFunction ↥L ℂ} (hφ : φ ∈ T) (hχ : χ ∈ T)
    (h1 : ClassFunction.inner φ χ = 0) (h2 : ClassFunction.inner φ χ.conj = 0) :
    ClassFunction.inner (RD.tau (φ - φ.conj)) (RD.tau (χ - χ.conj)) = 0 := by
  have hφc : φ.conj ∈ T := hTconj hφ
  have hχc : χ.conj ∈ T := hTconj hχ
  -- `φ ≠ χ` and `φ̄ ≠ χ`, else the two hypotheses would read `⟨φ, φ⟩ = 0`.
  have hne : φ ≠ χ := fun h => by
    rw [h, (hirr χ hχ).inner_self_eq_one] at h1; exact one_ne_zero h1
  have hcne : φ.conj ≠ χ := fun h => by
    rw [← h, ClassFunction.conj_conj, (hirr φ hφ).inner_self_eq_one] at h2
    exact one_ne_zero h2
  have hccne : φ.conj ≠ χ.conj := fun h => hne (by
    rw [← ClassFunction.conj_conj φ, h, ClassFunction.conj_conj])
  rw [RD.tau_isometry (conjDiff_mem_zSupportedSpan hKsupp (hTsub hφ))
      (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)),
    ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, h1, h2,
    inducedKernelFamily_pairwise_orthogonal (hTsub hφc) (hTsub hχ) hcne,
    inducedKernelFamily_pairwise_orthogonal (hTsub hφc) (hTsub hχc) hccne]
  ring

omit [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] [K.Normal]
  [Invertible (Nat.card ↥K : ℂ)] in
/-- **(5.2.e) in the two-element shape**: once the two signed differences `τ(φ − φ̄)` and
`τ(χ − χ̄)` are orthogonal, the image sets `R(φ)`, `R(χ)` share no irreducible — Peterfalvi (4.1)
at `u = v = 1` (`inner_eq_zero_of_signedDifference_inner_zero_of_mem`). -/
theorem orthogonal_of_tau_conjDiff_inner_eq_zero
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G} {φ χ : ClassFunction ↥L ℂ}
    (Rφ : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ φ)
    (Rχ : OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G) τ χ)
    (h : ClassFunction.inner (τ (φ - φ.conj)) (τ (χ - χ.conj)) = 0) :
    Rφ.Orthogonal Rχ := fun _a _b ha hb =>
  S07.CharacterDifferenceImage.inner_eq_zero_of_signedDifference_inner_zero_of_mem Rφ Rχ
    (by rw [signedDifference_eq, signedDifference_eq]; exact h) ha hb

/-- **Hypothesis (5.2) for a conjugation-closed subfamily `T ⊆ 𝒮` with irreducible members.**
Every clause is inherited: (5.2.a) from `hTconj` plus non-reality on `𝒮` (`|L|` odd — Peterfalvi
(1.1)), (5.2.b) from the `InducedFamilyImageData` isometry restricted along `T ⊆ 𝒮`, (5.2.c) from
`inducedKernelFamily_pairwise_orthogonal`, (5.2.d) from the (5.3.a) two-element shape
`characterDifferenceImage_of_irreducible` — which is why the irreducibility `hirr` is required
here (it is *not* a hypothesis of the book's (5.2); see the module docstring) — and (5.2.e) from
`tau_conjDiff_inner_eq_zero_of_orthogonal`. -/
noncomputable def InducedFamilyTauData.hypothesisOfSubfamily
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {T : Set (ClassFunction ↥L ℂ)} (hTsub : T ⊆ inducedKernelFamily K ⊥)
    (hTconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate T)
    (hirr : ∀ φ ∈ T, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥L) (G := G) T A₀ where
  tau := RD.tau
  tau_isometry_diff _ _ hφ hζ :=
    RD.tau_isometry ⟨Submodule.span_mono hTsub hφ.1, hφ.2⟩
      ⟨Submodule.span_mono hTsub hζ.1, hζ.2⟩
  conjugate_closed := hTconj
  no_real_characters := (inducedKernelFamily_hasNoRealCharacters (K := K) hodd ⊥).mono hTsub
  pairwise_orthogonal _ _ hφ hφ' hne :=
    inducedKernelFamily_pairwise_orthogonal (hTsub hφ) (hTsub hφ') hne
  difference_image χ hχ :=
    characterDifferenceImage_of_irreducible (hirr χ hχ)
      ((inducedKernelFamily_hasNoRealCharacters (K := K) hodd ⊥).mono hTsub hχ)
      (RD.tau_isometry (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ))
        (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)))
      (RD.tau_mem_ZIrr (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)))
      (RD.tau_apply_one (conjDiff_mem_zSupportedSpan hKsupp (hTsub hχ)))
  difference_images_orthogonal _φ _χ hφ hχ h1 h2 :=
    orthogonal_of_tau_conjDiff_inner_eq_zero _ _
      (tau_conjDiff_inner_eq_zero_of_orthogonal RD hKsupp hTsub hTconj hirr hφ hχ h1 h2)

@[simp] theorem InducedFamilyTauData.hypothesisOfSubfamily_tau
    (RD : InducedFamilyTauData (G := G) A₀ K) (hodd : Odd (Nat.card ↥L))
    (hKsupp : ∀ x : ↥L, x ∈ K → x ≠ 1 → x ∈ A₀)
    {T : Set (ClassFunction ↥L ℂ)} (hTsub : T ⊆ inducedKernelFamily K ⊥)
    (hTconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate T)
    (hirr : ∀ φ ∈ T, IsIrreducibleCharacter φ) :
    (RD.hypothesisOfSubfamily hodd hKsupp hTsub hTconj hirr).tau = RD.tau := rfl

end OddOrder.Peterfalvi.S08


