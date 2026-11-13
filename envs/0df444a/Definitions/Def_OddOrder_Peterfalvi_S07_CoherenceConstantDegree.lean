-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceConstantDegree
-- name    : OddOrder_Peterfalvi_S07_CoherenceConstantDegree
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:54.232491+00:00
-- url     : https://prove2.me/theorems/a0349d4b-3803-4ad4-ba05-578db25a83a2
-- title:
--   Peterfalvi (5.7): the standalone constant-degree coherence theorem
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5, (5.7): assume Hypothesis (5.2) and that $\chi(1)$ is independent of $\chi\in S$; then $S$ is coherent. This is the version used in the maximal-subgroup analysis.
--
--   Main definitions: `pairExtension` (the base-case coherent extension for an orthonormal break pair), `imageFam` (the orthonormal image family of a member), `pairDecomp` (the (5.7) per-pair decomposition) and `DiffPair` (members lying in different conjugate pairs); `isCoherent_pair_of_orthonormalImage` handles the base case $|\mathcal{S}|=2$.
--
--   The bundle also proves 21 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_CoherenceConstantDegree.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_CoherenceConstantDegree.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

variable [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

variable {S : Set (ClassFunction L ℂ)} {A : Set L}

/-- The base-case coherent extension for an orthonormal break pair `{χ, χ̄}`: the projection
`φ ↦ ⟨φ,χ⟩·(ε·μ) + ⟨φ,χ̄⟩·(ε·ν)` onto the orthonormal image pair `{μ, ν}` of (5.2.d) (with
`ε = sign`).  A `ℤ`-linear map since `⟨·,χ⟩` is (`IntegralCharacterMap.innerLeftℤ`). -/
noncomputable def pairExtension {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ) : IntegralCharacterMap L G :=
  (IntegralCharacterMap.innerLeftℤ χ).smulRight (hχ.sign • (hχ.mu : ClassFunction G ℂ))
    + (IntegralCharacterMap.innerLeftℤ χ.conj).smulRight (hχ.sign • (hχ.nu : ClassFunction G ℂ))

omit [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] in
@[simp] theorem pairExtension_apply {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ}
    (hχ : CharacterDifferenceImage (L := L) (G := G) τ χ) (φ : ClassFunction L ℂ) :
    pairExtension hχ φ =
      ClassFunction.inner φ χ • (hχ.sign • (hχ.mu : ClassFunction G ℂ))
        + ClassFunction.inner φ χ.conj • (hχ.sign • (hχ.nu : ClassFunction G ℂ)) := by
  simp [pairExtension]

open scoped Classical in
/-- **Peterfalvi (5.7), base case `|𝒮| = 2`, for an arbitrary member norm.**

The book's "if `|𝒮| = 2`, this follows from (5.2.d)" with no irreducibility assumed.  Write
`m = ‖χ‖²`.  The (5.2.b) isometry gives `‖τ(χ − χ̄)‖² = ‖χ − χ̄‖² = 2m` (using `χ ⊥ χ̄` and
`‖χ̄‖² = ‖χ‖²`), while orthonormality of `R(χ)` gives `‖∑_{α ∈ R(χ)} α‖² = |R(χ)|` — so
**`|R(χ)| = 2m`**.  Splitting off any `E ⊆ R(χ)` with `|E| = m` and setting

* `X₀ = ∑_{α ∈ E} α`,  `X₁ = X₀ − τ(χ − χ̄)  (= −∑_{α ∉ E} α)`

makes the Gram matrix of `(X₀, X₁)` equal to that of `(χ, χ̄)`: `‖X₀‖² = |E| = m = ‖χ‖²`,
`⟨X₀, X₁⟩ = m − |E| = 0 = ⟨χ, χ̄⟩`, and `‖X₁‖² = |R(χ)| − m = m = ‖χ̄‖²`.  Feeding that to
`coherentEqualDegreeW` (which asks for Gram agreement, not orthonormality) gives coherence.

At `m = 1` this is `isCoherent_pair_of_differenceImage`, whose two-element `R(χ) = {ε·μ, −ε·ν}`
is the `|E| = 1` split.  The naturality of `m` is a genuine hypothesis here because
`GeneralHypothesis` does not record that members are characters; in Peterfalvi's (5.2) they are,
so `‖χ‖² ∈ ℕ` (issue 0157). -/
noncomputable def isCoherent_pair_of_orthonormalImage
    {τ : IntegralCharacterMap L G} {χ : ClassFunction L ℂ} {A : Set L}
    (R : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    {m : ℕ} (hm : ClassFunction.inner χ χ = (m : ℂ))
    (hisom : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj))
      = ClassFunction.inner (χ - χ.conj) (χ - χ.conj))
    (hortho : ClassFunction.inner χ χ.conj = 0) (hortho' : ClassFunction.inner χ.conj χ = 0)
    (hne : χ ≠ χ.conj)
    (hdeg : (χ.conj : ClassFunction L ℂ) 1 = (χ : ClassFunction L ℂ) 1)
    (hdeg0 : (χ : ClassFunction L ℂ) 1 ≠ 0)
    (hdiff_supp : ((χ - χ.conj : ClassFunction L ℂ)).support ⊆ A) (h1A : (1 : L) ∉ A)
    (hZ : τ (χ - χ.conj) ∈ ZIrr G) :
    IsCoherent τ ({χ, χ.conj} : Set (ClassFunction L ℂ)) A := by
  classical
  -- `‖χ̄‖² = ‖χ‖²`
  have hconjnorm : ClassFunction.inner χ.conj χ.conj = ClassFunction.inner χ χ := by
    rw [inner_conj_conj, hm, star_natCast]
  -- `|R(χ)| = 2m`
  have hcard : R.imageSet.card = 2 * m := by
    rw [R.image_eq, inner_sum_sum_of_orthonormal R.orthonormal (Finset.Subset.refl _)
        (Finset.Subset.refl _), Finset.inter_self,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hortho, hortho', hconjnorm, hm] at hisom
    have h2 : ((R.imageSet.card : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) := by
      rw [hisom]; push_cast; ring
    exact_mod_cast h2
  -- `m > 0`: otherwise `χ = 0`, contradicting `χ(1) ≠ 0`
  have hmpos : m ≠ 0 := by
    intro h0
    have hzero : ClassFunction.inner χ χ = 0 := by rw [hm, h0]; simp
    have hz : χ = 0 := eq_zero_of_inner_self_re_eq_zero (by rw [hzero]; simp)
    exact hdeg0 (by rw [hz]; simp)
  choose E hEsub hEcard using
    Finset.exists_subset_card_eq (s := R.imageSet) (n := m) (by rw [hcard]; omega)
  set X₀ : ClassFunction G ℂ := ∑ α ∈ E, α with hX₀
  set X₁ : ClassFunction G ℂ := X₀ - τ (χ - χ.conj) with hX₁
  have hsumR : τ (χ - χ.conj) = ∑ α ∈ R.imageSet, α := R.image_eq
  -- the four Gram entries
  have hg00 : ClassFunction.inner X₀ X₀ = ClassFunction.inner χ χ := by
    rw [hX₀, inner_sum_sum_of_orthonormal R.orthonormal hEsub hEsub, Finset.inter_self, hEcard, hm]
  have hgER : ClassFunction.inner X₀ (τ (χ - χ.conj)) = (m : ℂ) := by
    rw [hX₀, hsumR, inner_sum_sum_of_orthonormal R.orthonormal hEsub (Finset.Subset.refl _),
      Finset.inter_eq_left.mpr hEsub, hEcard]
  have hgRE : ClassFunction.inner (τ (χ - χ.conj)) X₀ = (m : ℂ) := by
    rw [hX₀, hsumR, inner_sum_sum_of_orthonormal R.orthonormal (Finset.Subset.refl _) hEsub,
      Finset.inter_eq_right.mpr hEsub, hEcard]
  have hgRR : ClassFunction.inner (τ (χ - χ.conj)) (τ (χ - χ.conj)) = ((2 * m : ℕ) : ℂ) := by
    rw [hsumR, inner_sum_sum_of_orthonormal R.orthonormal (Finset.Subset.refl _)
      (Finset.Subset.refl _), Finset.inter_self, hcard]
  have hg01 : ClassFunction.inner X₀ X₁ = ClassFunction.inner χ χ.conj := by
    rw [hX₁, ClassFunction.inner_sub_right, hg00, hgER, hm, hortho]; ring
  have hg10 : ClassFunction.inner X₁ X₀ = ClassFunction.inner χ.conj χ := by
    rw [hX₁, ClassFunction.inner_sub_left, hg00, hgRE, hm, hortho']; ring
  have hg11 : ClassFunction.inner X₁ X₁ = ClassFunction.inner χ.conj χ.conj := by
    rw [hX₁, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hg00, hgER, hgRE, hgRR, hconjnorm, hm]
    push_cast; ring
  -- feed the weighted equal-degree builder at `n = 2`
  have hrange : Set.range ![χ, χ.conj] = ({χ, χ.conj} : Set (ClassFunction L ℂ)) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · intro hz
      rcases hz with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hcoh : IsCoherent τ (Set.range ![χ, χ.conj]) A := by
    refine coherentEqualDegreeW (χ := ![χ, χ.conj]) (X := ![X₀, X₁]) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
      (by simpa using hdeg0) h1A ?_
    · -- pairwise orthogonality
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hortho
      · exact hortho'
      · exact absurd rfl hij
    · -- nonzero norms
      intro j
      fin_cases j
      · change ClassFunction.inner χ χ ≠ 0
        rw [hm]; exact_mod_cast hmpos
      · change ClassFunction.inner χ.conj χ.conj ≠ 0
        rw [hconjnorm, hm]; exact_mod_cast hmpos
    · -- Gram agreement
      intro i j
      fin_cases i <;> fin_cases j
      · exact hg00
      · exact hg01
      · exact hg10
      · exact hg11
    · -- `τ (χⱼ − χ₀) = Xⱼ − X₀`
      intro j
      fin_cases j
      · change τ (χ - χ) = X₀ - X₀
        rw [sub_self, map_zero, sub_self]
      · change τ (χ.conj - χ) = X₁ - X₀
        rw [show χ.conj - χ = -(χ - χ.conj) from by abel, map_neg, hX₁]
        abel
    · -- `Xⱼ ∈ ℤ[Irr G]`
      intro j
      fin_cases j
      · change X₀ ∈ ZIrr G
        exact Submodule.sum_mem _ fun α hα => R.mem_ZIrr α (hEsub hα)
      · change X₁ ∈ ZIrr G
        exact Submodule.sub_mem _
          (Submodule.sum_mem _ fun α hα => R.mem_ZIrr α (hEsub hα)) hZ
    · -- equal degree
      intro j
      fin_cases j
      · rfl
      · exact hdeg
    · -- supported differences
      intro j
      fin_cases j
      · change ((χ - χ : ClassFunction L ℂ)).support ⊆ A
        rw [sub_self]
        simp
      · change ((χ.conj - χ : ClassFunction L ℂ)).support ⊆ A
        rw [show χ.conj - χ = -(χ - χ.conj) from by abel, ClassFunction.support_neg]
        exact hdiff_supp
  rwa [hrange] at hcoh

open OddOrder.RepresentationTheory

/-- The orthonormal image family `R(χ) = {ε·μ, −ε·ν}` of a member `χ ∈ S`, from the (5.2.d)
difference image carried by the hypothesis. -/
noncomputable abbrev imageFam (hyp : GeneralHypothesis (L := L) (G := G) S A)
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    OrthonormalCharacterImageFamily (L := L) (G := G) hyp.tau χ :=
  hyp.difference_image hχ

/-- **Difference-isometry extends to the `zSpan` of two differences.**  From the four generator
inner-product equalities `⟨τ dᵢ, τ dⱼ⟩ = ⟨dᵢ, dⱼ⟩` (`i, j ∈ {1, 2}`), the isometry holds on every
`ℤ`-combination `φ, ψ ∈ zSpan {d₁, d₂}`, by bilinear expansion (`τ` is `ℤ`-linear, `⟨·,·⟩` is
`ℤ`-sesquilinear).  This feeds the lattice-relative `ofProjection` isometry input from the
member-difference isometry `Hypothesis.tau_isometry_memberDiff` (issues 9001, 0099), replacing the
former global `IsIntegralIsometry`. -/
theorem inner_eq_on_zSpan_pair {τ : IntegralCharacterMap L G} {d₁ d₂ : ClassFunction L ℂ}
    (h₁₁ : ClassFunction.inner (τ d₁) (τ d₁) = ClassFunction.inner d₁ d₁)
    (h₁₂ : ClassFunction.inner (τ d₁) (τ d₂) = ClassFunction.inner d₁ d₂)
    (h₂₁ : ClassFunction.inner (τ d₂) (τ d₁) = ClassFunction.inner d₂ d₁)
    (h₂₂ : ClassFunction.inner (τ d₂) (τ d₂) = ClassFunction.inner d₂ d₂)
    {φ ψ : ClassFunction L ℂ}
    (hφ : φ ∈ zSpan (L := L) ({d₁, d₂} : Set (ClassFunction L ℂ)))
    (hψ : ψ ∈ zSpan (L := L) ({d₁, d₂} : Set (ClassFunction L ℂ))) :
    ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hφ
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hψ
  -- push `τ` through the `ℤ`-combinations first (keeping `zsmul`, before the scalar cast).
  simp only [map_add, map_zsmul]
  -- expand both bilinear forms and apply the four generator equalities.
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ← Int.cast_smul_eq_zsmul ℂ, ClassFunction.inner_smul_left, ClassFunction.inner_smul_right,
    star_intCast, h₁₁, h₁₂, h₂₁, h₂₂]

/-- **(5.7) per-pair decomposition.**  For members `χ, ζ ∈ S` with `⟨χ,ζ⟩ = ⟨χ̄,ζ⟩ = 0` and the
supported-difference virtual-character fact `(χ − ζ)^τ ∈ ℤ[Irr G]`, the (5.4) decomposition of
`(χ − ζ)^τ` against `R(χ)`, built against the fixed Dade isometry `τ` (`tau1 := τ`).  The
`ofProjection` isometry input on `zSpan {χ − χ̄, χ − ζ}` comes from the lattice-relative
difference-isometry `hyp.tau_isometry_memberDiff` (issues 9001, 0099; the member-difference support
inputs come from `hsuppdiff`) via `inner_eq_on_zSpan_pair` — no global `IsIntegralIsometry` is
needed, so this applies to the Feit–Thompson Dade map. -/
noncomputable def pairDecomp (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ ζ : ClassFunction L ℂ} (hχ : χ ∈ S) (hζ : ζ ∈ S)
    (hχζ : ClassFunction.inner χ ζ = 0) (hχbarζ : ClassFunction.inner χ.conj ζ = 0)
    (hZ : hyp.tau (χ - ζ) ∈ ZIrr G) :
    CharacterPsiDecomposition (L := L) (G := G) hyp.tau χ ζ :=
  have hs1 : ((χ - χ.conj : ClassFunction L ℂ)).support ⊆ A :=
    hsuppdiff _ hχ _ (hyp.conjugate_mem hχ)
  have hs2 : ((χ - ζ : ClassFunction L ℂ)).support ⊆ A := hsuppdiff _ hχ _ hζ
  CharacterPsiDecomposition.ofProjection (imageFam hyp hχ) hyp.tau
    (fun _ _ hφ hψ =>
      inner_eq_on_zSpan_pair
        (hyp.tau_isometry_memberDiff hχ (hyp.conjugate_mem hχ) hχ (hyp.conjugate_mem hχ) hs1 hs1)
        (hyp.tau_isometry_memberDiff hχ (hyp.conjugate_mem hχ) hχ hζ hs1 hs2)
        (hyp.tau_isometry_memberDiff hχ hζ hχ (hyp.conjugate_mem hχ) hs2 hs1)
        (hyp.tau_isometry_memberDiff hχ hζ hχ hζ hs2 hs2)
        hφ hψ)
    rfl hZ hχζ hχbarζ
    (hyp.pairwise_orthogonal hχ (hyp.conjugate_mem hχ) (hyp.ne_conj hχ))

/-- `⟨D.X, D'.X⟩ = 0` when the image families are orthogonal (`R(χ) ⊥ R(χ')`, the (5.2.e) input):
lift the per-element orthogonality `⟨D.X, α⟩ = 0` (`α ∈ R(χ')`) to the `ℤ`-combination
`D'.X = ∑_{α ∈ R(χ')} coeff α • α`. -/
theorem inner_X_X'_eq_zero {τ : IntegralCharacterMap L G}
    {χ χ' ψ ψ' : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (D' : CharacterPsiDecomposition (L := L) (G := G) τ χ' ψ')
    (hortho : D.imageFamily.Orthogonal D'.imageFamily) :
    ClassFunction.inner D.X D'.X = 0 := by
  rw [D'.X_eq, inner_sum_right]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_smul_right,
    D.inner_X_orthogonal_imageSet_of_orthogonal D'.imageFamily hortho hα, mul_zero]

/-- Inner-self products are real: `⟨φ,φ⟩ = (⟨φ,φ⟩.re : ℂ)`. -/
theorem inner_self_re_cast (φ : ClassFunction G ℂ) :
    ClassFunction.inner φ φ = ((ClassFunction.inner φ φ).re : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, inner_self_eq_realCast, Complex.ofReal_im]

/-- **Peterfalvi (5.7) two-sided norm core.**  For two members `χ, ζ` in *different* conjugate
pairs (so `R(χ) ⊥ R(ζ)`, both norm-one, both differences supported and virtual), the (5.4)
decomposition `D` of `(χ − ζ)^τ` against `R(χ)` and the symmetric `D'` of `(ζ − χ)^τ` against `R(ζ)`
satisfy `‖D.X‖² = 1` and `D.Y = D'.X`.

This is Peterfalvi's "`‖X‖² = ‖χ‖²`" and "`Y = 0`" combined: the (5.4.b) hypothesis `‖Y‖² ≥ ‖ζ‖²`
is supplied by the symmetric `D'` through `‖D.Y − D'.X‖² ≥ 0` together with the identity
`⟨D.Y, D'.X⟩ = ‖D'.X‖² ≥ ‖ζ‖²` (which holds because `D.Y = D.X − (χ − ζ)^τ`,
`(χ − ζ)^τ = D'.Y − D'.X`,
`⟨D.X, D'.X⟩ = 0` and `⟨D'.X, D'.Y⟩ = 0`).  Once `‖D.Y‖² = ‖ζ‖²` is forced, `‖D.Y − D'.X‖² = 0`. -/
theorem pairDecomp_two_sided
    {τ : IntegralCharacterMap L G} {χ ζ : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ζ)
    (D' : CharacterPsiDecomposition (L := L) (G := G) τ ζ χ)
    (hortho : D.imageFamily.Orthogonal D'.imageFamily)
    (himgD : τ (χ - ζ) = D.X - D.Y) (himgD' : τ (ζ - χ) = D'.X - D'.Y) :
    ClassFunction.inner D.X D.X = ClassFunction.inner χ χ ∧ D.Y = D'.X := by
  -- `⟨D.X, D'.X⟩ = 0` (cross-family) and `⟨D'.Y, D'.X⟩ = 0` (image ⊥ residual).
  have hXX' : ClassFunction.inner D.X D'.X = 0 := inner_X_X'_eq_zero D D' hortho
  have hYX' : ClassFunction.inner D'.Y D'.X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D'.inner_X_Y, star_zero]
  -- `D.Y = D.X − (χ−ζ)^τ`, and `(χ−ζ)^τ = D'.Y − D'.X`.
  have hDYval : D.Y = D.X - τ (χ - ζ) := by rw [himgD]; abel
  have hτχζ : τ (χ - ζ) = D'.Y - D'.X := by
    have hneg : χ - ζ = -(ζ - χ) := by abel
    rw [hneg, map_neg, himgD']; abel
  -- `⟨D.Y, D'.X⟩ = ‖D'.X‖²`.
  have hYX'_eq : ClassFunction.inner D.Y D'.X = ClassFunction.inner D'.X D'.X := by
    rw [hDYval, ClassFunction.inner_sub_left, hXX', hτχζ, ClassFunction.inner_sub_left, hYX']
    ring
  -- `‖D'.X‖².re ≥ ‖ζ‖².re` from (5.4.a) on `D'`.
  have hD'Xge : (ClassFunction.inner ζ ζ).re ≤ (ClassFunction.inner D'.X D'.X).re :=
    D'.inner_self_chi_re_le_inner_self_X
  -- `‖D.Y − D'.X‖².re = ‖D.Y‖².re − ‖D'.X‖².re`.
  have hdiffre : (ClassFunction.inner (D.Y - D'.X) (D.Y - D'.X)).re
      = (ClassFunction.inner D.Y D.Y).re - (ClassFunction.inner D'.X D'.X).re := by
    have hexp : ClassFunction.inner (D.Y - D'.X) (D.Y - D'.X)
        = ClassFunction.inner D.Y D.Y - ClassFunction.inner D.Y D'.X
          - ClassFunction.inner D'.X D.Y + ClassFunction.inner D'.X D'.X := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right]; ring
    rw [hexp, hYX'_eq, OddOrder.RepresentationTheory.inner_conj_symm D.Y D'.X, hYX'_eq]
    simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re]; ring
  have hDXle : (ClassFunction.inner D'.X D'.X).re ≤ (ClassFunction.inner D.Y D.Y).re := by
    have hnn := inner_self_re_nonneg (D.Y - D'.X)
    rw [hdiffre] at hnn; linarith
  -- (5.4.b) on `D` with `‖ζ‖².re ≤ ‖D'.X‖².re ≤ ‖D.Y‖².re`.
  have hY : (ClassFunction.inner ζ ζ).re ≤ (ClassFunction.inner D.Y D.Y).re := by
    linarith
  obtain ⟨hXnorm, hYnorm, _⟩ := D.norm_eq_and_X_eq_sum_of_norm_Y_ge hY
  refine ⟨?_, ?_⟩
  · -- `‖D.X‖² = ‖χ‖²` (ℂ): the real parts agree and both inner products are real.
    rw [inner_self_re_cast D.X, ← hXnorm]
    exact (inner_self_re_cast χ).symm
  · -- `D.Y = D'.X`: `‖ζ‖².re = ‖D.Y‖².re` and `‖ζ‖².re ≤ ‖D'.X‖².re ≤ ‖D.Y‖².re` pin all three
    -- equal, so `‖D.Y − D'.X‖².re = 0`.
    have hdz : D.Y - D'.X = 0 := by
      apply eq_zero_of_inner_self_re_eq_zero
      rw [hdiffre]; linarith
    exact sub_eq_zero.mp hdz

/-- `⟨D.X, w⟩ = 0` when `w ⊥ R(χ)` (`w` orthogonal to every member of the image family).  The
`X`-side companion of `Y_orthogonal`. -/
theorem inner_X_perp {τ : IntegralCharacterMap L G} {χ ψ : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) {w : ClassFunction G ℂ}
    (hw : ∀ α ∈ D.imageFamily.imageSet, ClassFunction.inner w α = 0) :
    ClassFunction.inner D.X w = 0 := by
  rw [D.X_eq, inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_conj_symm, hw α hα,
    star_zero, mul_zero]

/-- `χ`, `ζ` lie in *different* conjugate pairs: `χ ∉ {ζ, ζ̄}`.  (Then also `χ̄ ∉ {ζ, ζ̄}`, and the
relation is symmetric.) -/
def DiffPair (χ ζ : ClassFunction L ℂ) : Prop := χ ≠ ζ ∧ χ ≠ ζ.conj

omit [Fintype L] in
omit [Invertible (Nat.card L : ℂ)] in
theorem DiffPair.conj_ne {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) : χ.conj ≠ ζ :=
  fun he => h.2 (by rw [← ClassFunction.conj_conj χ, he])

omit [Fintype L] in
omit [Invertible (Nat.card L : ℂ)] in
theorem DiffPair.symm {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) : DiffPair ζ χ :=
  ⟨h.1.symm, fun he => h.2 (by rw [he, ClassFunction.conj_conj])⟩

theorem DiffPair.inner_eq_zero (hyp : GeneralHypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    ClassFunction.inner χ ζ = 0 :=
  hyp.pairwise_orthogonal hχ hζ h.1

theorem DiffPair.inner_conj_eq_zero (hyp : GeneralHypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    ClassFunction.inner χ ζ.conj = 0 :=
  hyp.pairwise_orthogonal hχ (hyp.conjugate_mem hζ) h.2

/-- The image families of two members in different conjugate pairs are orthogonal (the (5.2.e) input
lifted through `toOrthonormalImage`). -/
theorem DiffPair.imageFam_orthogonal (hyp : GeneralHypothesis (L := L) (G := G) S A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    (imageFam hyp hχ).Orthogonal (imageFam hyp hζ) :=
  hyp.difference_images_orthogonal hχ hζ
    (h.inner_eq_zero hyp hχ hζ) (h.inner_conj_eq_zero hyp hχ hζ)

/-- The per-pair decomposition `pairDecomp` for two members `χ, ζ` in *different* conjugate pairs.
-/
noncomputable def pairDecomp' (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S)
    (hZ : hyp.tau (χ - ζ) ∈ ZIrr G) :
    CharacterPsiDecomposition (L := L) (G := G) hyp.tau χ ζ :=
  pairDecomp hyp hsuppdiff hχ hζ (hyp.pairwise_orthogonal hχ hζ h.1)
    (hyp.pairwise_orthogonal (hyp.conjugate_mem hχ) hζ h.conj_ne) hZ

/-- The defining image equation `(χ − ζ)^τ = D.X − D.Y` for `D = pairDecomp' …` (the `tau1_image`
field of `ofProjection`, with the fixed `tau1 = τ`). -/
theorem pairDecomp'_image (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S)
    (hZ : hyp.tau (χ - ζ) ∈ ZIrr G) :
    hyp.tau (χ - ζ) = (pairDecomp' hyp hsuppdiff h hχ hζ hZ).X
      - (pairDecomp' hyp hsuppdiff h hχ hζ hZ).Y :=
  (pairDecomp' hyp hsuppdiff h hχ hζ hZ).tau1_image

/-- `⟨D.X, ∑_{β ∈ R'} β⟩ = 0` for an orthogonal second family `R'` (`R(χ) ⊥ R'`). -/
theorem inner_X_sum_imageFam_eq_zero {τ : IntegralCharacterMap L G} {χ χ' ψ : ClassFunction L ℂ}
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (R' : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ')
    (hortho : D.imageFamily.Orthogonal R') :
    ClassFunction.inner D.X (∑ β ∈ R'.imageSet, β) = 0 := by
  refine inner_X_perp D fun α hα => ?_
  rw [inner_sum_left]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [OddOrder.RepresentationTheory.inner_conj_symm, hortho α hα β hβ, star_zero]

/-- **Peterfalvi (5.7) common image `β = χ₀^{τ₁}`.**  The `R(χ₀)`-projection of `(χ₀ − ζ₀)^τ` for a
fixed reference member `ζ₀` in a different conjugate pair from `χ₀`.  By `pairDecomp_two_sided` this
is a single element of `R(χ₀)` of norm one; Peterfalvi (5.7) shows it is *independent* of `ζ₀`. -/
noncomputable def commonImage (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction G ℂ :=
  (pairDecomp' hyp hsuppdiff hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀)).X

/-- The two-sided norm facts for `pairDecomp'`: `‖D.X‖² = 1` and `D.Y = D'.X` (the symmetric
decomposition), from `pairDecomp_two_sided`. -/
theorem pairDecomp'_two_sided (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ ζ : ClassFunction L ℂ} (h : DiffPair χ ζ) (hχ : χ ∈ S) (hζ : ζ ∈ S) :
    ClassFunction.inner (pairDecomp' hyp hsuppdiff h hχ hζ (hZIrr χ hχ ζ hζ)).X
        (pairDecomp' hyp hsuppdiff h hχ hζ (hZIrr χ hχ ζ hζ)).X = ClassFunction.inner χ χ ∧
      (pairDecomp' hyp hsuppdiff h hχ hζ (hZIrr χ hχ ζ hζ)).Y =
        (pairDecomp' hyp hsuppdiff h.symm hζ hχ (hZIrr ζ hζ χ hχ)).X :=
  pairDecomp_two_sided (pairDecomp' hyp hsuppdiff h hχ hζ (hZIrr χ hχ ζ hζ))
    (pairDecomp' hyp hsuppdiff h.symm hζ hχ (hZIrr ζ hζ χ hχ))
    (h.imageFam_orthogonal hyp hχ hζ)
    (pairDecomp'_image hyp hsuppdiff h hχ hζ (hZIrr χ hχ ζ hζ))
    (pairDecomp'_image hyp hsuppdiff h.symm hζ hχ (hZIrr ζ hζ χ hχ))

/-- **(5.7) fact (A): `‖β‖² = 1`.** -/
theorem commonImage_self (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hsuppdiff hdp hχ₀ hζ₀)
      (commonImage hyp hZIrr hsuppdiff hdp hχ₀ hζ₀) = ClassFunction.inner χ₀ χ₀ :=
  (pairDecomp'_two_sided hyp hZIrr hsuppdiff hdp hχ₀ hζ₀).1

/-- **(5.7) fact (B) at the reference `ζ₀`: `⟨β, (χ₀ − ζ₀)^τ⟩ = 1`.**  `= ⟨D₀.X, D₀.X − D₀.Y⟩ =
‖D₀.X‖² − 0`. -/
theorem commonImage_inner_ref (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hsuppdiff hdp hχ₀ hζ₀) (hyp.tau (χ₀ - ζ₀)) =
      ClassFunction.inner χ₀ χ₀ := by
  rw [commonImage, pairDecomp'_image hyp hsuppdiff hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀),
    ClassFunction.inner_sub_right,
    (pairDecomp' hyp hsuppdiff hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀)).inner_X_Y,
    sub_zero, (pairDecomp'_two_sided hyp hZIrr hsuppdiff hdp hχ₀ hζ₀).1]

/-- **(5.7) fact (B) at `χ̄₀`: `⟨β, (χ₀ − χ̄₀)^τ⟩ = 1`.**  `(χ₀ − χ̄₀)^τ = ∑_{R(χ₀)} α`, and
`⟨β, ∑ α⟩ = ∑ coeff = ‖χ₀‖² = 1` (the keystone). -/
theorem commonImage_inner_conj (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hsuppdiff hdp hχ₀ hζ₀)
      (hyp.tau (χ₀ - χ₀.conj)) = ClassFunction.inner χ₀ χ₀ := by
  rw [commonImage]
  set D₀ := pairDecomp' hyp hsuppdiff hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀) with hD₀
  rw [D₀.imageFamily.image_eq, D₀.inner_X_sum, ← D₀.inner_self_chi_eq_sum_coeff]

/-- **(5.7) fact (B) at `ζ̄₀`: `⟨β, (χ₀ − ζ̄₀)^τ⟩ = 1`.**
`(χ₀ − ζ̄₀)^τ = (χ₀ − ζ₀)^τ + (ζ₀ − ζ̄₀)^τ`;
the first gives `1` (reference), the second is `∑_{R(ζ₀)} α ⊥ R(χ₀)`. -/
theorem commonImage_inner_refconj (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S) :
    ClassFunction.inner (commonImage hyp hZIrr hsuppdiff hdp hχ₀ hζ₀)
      (hyp.tau (χ₀ - ζ₀.conj)) = ClassFunction.inner χ₀ χ₀ := by
  have hsplit : χ₀ - ζ₀.conj = (χ₀ - ζ₀) + (ζ₀ - ζ₀.conj) := by abel
  rw [hsplit, map_add, ClassFunction.inner_add_right,
    commonImage_inner_ref hyp hZIrr hsuppdiff hdp hχ₀ hζ₀, commonImage,
    (imageFam hyp hζ₀).image_eq,
    inner_X_sum_imageFam_eq_zero (pairDecomp' hyp hsuppdiff hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀))
      (imageFam hyp hζ₀) (hdp.imageFam_orthogonal hyp hχ₀ hζ₀), add_zero]

/-- **(5.7) fact (B) at a member `ζ` in a *third* pair: `⟨β, (χ₀ − ζ)^τ⟩ = 1`.**  The independence
of `β` from the auxiliary member: `⟨β, (χ₀−ζ)^τ⟩ = ⟨D₀.X, Dζ.X⟩ = ⟨χ₀−ζ₀, χ₀−ζ⟩ = 1`, the cross
terms
vanishing because `R(χ₀) ⊥ R(ζ)`, `R(χ₀) ⊥ R(ζ₀)` and `D₀.Y, Dζ.Y` lie in `R(ζ₀)`, `R(ζ)` (different
pairs, `pairDecomp_two_sided`). -/
theorem commonImage_inner_other (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ₀ ζ₀ ζ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S)
    (hζ : ζ ∈ S) (hdpχ : DiffPair χ₀ ζ) (hdpζ : DiffPair ζ₀ ζ) :
    ClassFunction.inner (commonImage hyp hZIrr hsuppdiff hdp hχ₀ hζ₀)
      (hyp.tau (χ₀ - ζ)) = ClassFunction.inner χ₀ χ₀ := by
  rw [commonImage, pairDecomp'_image hyp hsuppdiff hdpχ hχ₀ hζ (hZIrr χ₀ hχ₀ ζ hζ),
    ClassFunction.inner_sub_right]
  set D₀ := pairDecomp' hyp hsuppdiff hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀) with hD₀
  set Dζ := pairDecomp' hyp hsuppdiff hdpχ hχ₀ hζ (hZIrr χ₀ hχ₀ ζ hζ) with hDζ
  -- `⟨D₀.X, Dζ.Y⟩ = 0` (`Dζ.Y ⊥ R(χ₀)`), so the goal is `⟨D₀.X, Dζ.X⟩ = 1`.
  rw [inner_X_perp D₀ Dζ.Y_orthogonal, sub_zero]
  -- isometry: `⟨(χ₀−ζ₀)^τ, (χ₀−ζ)^τ⟩ = ⟨χ₀−ζ₀, χ₀−ζ⟩`.
  have hiso : ClassFunction.inner (hyp.tau (χ₀ - ζ₀)) (hyp.tau (χ₀ - ζ))
      = ClassFunction.inner (χ₀ - ζ₀) (χ₀ - ζ) :=
    hyp.tau_isometry_memberDiff hχ₀ hζ₀ hχ₀ hζ
      (hsuppdiff _ hχ₀ _ hζ₀) (hsuppdiff _ hχ₀ _ hζ)
  rw [pairDecomp'_image hyp hsuppdiff hdp hχ₀ hζ₀ (hZIrr χ₀ hχ₀ ζ₀ hζ₀),
    pairDecomp'_image hyp hsuppdiff hdpχ hχ₀ hζ (hZIrr χ₀ hχ₀ ζ hζ)] at hiso
  -- the cross terms.
  have hXY : ClassFunction.inner D₀.X Dζ.Y = 0 := inner_X_perp D₀ Dζ.Y_orthogonal
  have hYX : ClassFunction.inner D₀.Y Dζ.X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, inner_X_perp Dζ D₀.Y_orthogonal, star_zero]
  have hYY : ClassFunction.inner D₀.Y Dζ.Y = 0 := by
    rw [(pairDecomp'_two_sided hyp hZIrr hsuppdiff hdp hχ₀ hζ₀).2,
      (pairDecomp'_two_sided hyp hZIrr hsuppdiff hdpχ hχ₀ hζ).2]
    exact inner_X_X'_eq_zero _ _ (hdpζ.imageFam_orthogonal hyp hζ₀ hζ)
  -- the right-hand side `⟨χ₀−ζ₀, χ₀−ζ⟩ = 1`.
  have hLHS : ClassFunction.inner (χ₀ - ζ₀) (χ₀ - ζ) = ClassFunction.inner χ₀ χ₀ := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      hdpχ.inner_eq_zero hyp hχ₀ hζ, hdp.symm.inner_eq_zero hyp hζ₀ hχ₀,
      hdpζ.inner_eq_zero hyp hζ₀ hζ]
    ring
  rw [hLHS, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, hXY, hYX, hYY] at hiso
  linear_combination hiso

/-- **Peterfalvi (5.7) fact (B), dispatcher: `⟨β, (χ₀ − ζ)^τ⟩ = 1` for every member `ζ ≠ χ₀`.** -/
theorem commonImage_inner (hyp : GeneralHypothesis (L := L) (G := G) S A)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {χ₀ ζ₀ : ClassFunction L ℂ} (hdp : DiffPair χ₀ ζ₀) (hχ₀ : χ₀ ∈ S) (hζ₀ : ζ₀ ∈ S)
    {ζ : ClassFunction L ℂ} (hζ : ζ ∈ S) (hζne : ζ ≠ χ₀) :
    ClassFunction.inner (commonImage hyp hZIrr hsuppdiff hdp hχ₀ hζ₀)
      (hyp.tau (χ₀ - ζ)) = ClassFunction.inner χ₀ χ₀ := by
  by_cases hc1 : ζ = χ₀.conj
  · rw [hc1]; exact commonImage_inner_conj hyp hZIrr hsuppdiff hdp hχ₀ hζ₀
  have hdpχ : DiffPair χ₀ ζ :=
    ⟨hζne.symm, fun h => hc1 (by rw [← ClassFunction.conj_conj ζ, ← h])⟩
  by_cases hc2 : ζ = ζ₀
  · rw [hc2]; exact commonImage_inner_ref hyp hZIrr hsuppdiff hdp hχ₀ hζ₀
  by_cases hc3 : ζ = ζ₀.conj
  · rw [hc3]; exact commonImage_inner_refconj hyp hZIrr hsuppdiff hdp hχ₀ hζ₀
  have hdpζ : DiffPair ζ₀ ζ :=
    ⟨fun h => hc2 h.symm, fun h => hc3 (by rw [h, ClassFunction.conj_conj] : ζ₀.conj = ζ).symm⟩
  exact commonImage_inner_other hyp hZIrr hsuppdiff hdp hχ₀ hζ₀ hζ hdpχ hdpζ

/-- **(5.7) the retargeted family is an isometric image of the source.**  For the auxiliary isometry
`τ₁` of (5.7) given by `χⱼ^{τ₁} = X j := β − (χ₀ − χⱼ)^τ` (`χ₀ := χ 0`, `β = χ₀^{τ₁}`), one has
`⟨Xᵢ, Xⱼ⟩ = ⟨χᵢ, χⱼ⟩`, from `‖β‖² = 1` (A), the uniform fact `⟨β, (χ₀ − χⱼ)^τ⟩ = 1 − ⟨χ₀, χⱼ⟩`
(B), and the **lattice-relative** difference-isometry `hdiff`
(`⟨(χ₀−χᵢ)^τ, (χ₀−χⱼ)^τ⟩ = ⟨χ₀−χᵢ, χ₀−χⱼ⟩`). This is the *only* place (5.7) used the isometry, and
it
uses it solely on supported differences (issue 9001), so **no global `IsIntegralIsometry` is
needed**
— the theorem applies directly to the Feit–Thompson Dade map (`dim CF(L) > dim CF(G)`, isometric
only
on `A(L)`-supported functions).  (Hence `τ₁` is an isometry — Peterfalvi's closing remark.) -/
theorem xFamily_inner {τ : IntegralCharacterMap L G} {n : ℕ} [NeZero n]
    (χ : Fin n → ClassFunction L ℂ)
    (β : ClassFunction G ℂ)
    (hdiff : ∀ i j, ClassFunction.inner (τ (χ 0 - χ i)) (τ (χ 0 - χ j))
      = ClassFunction.inner (χ 0 - χ i) (χ 0 - χ j))
    (hββ : ClassFunction.inner β β = ClassFunction.inner (χ 0) (χ 0))
    (hB : ∀ j, ClassFunction.inner β (τ (χ 0 - χ j))
      = ClassFunction.inner (χ 0) (χ 0) - ClassFunction.inner (χ 0) (χ j))
    (i j : Fin n) :
    ClassFunction.inner (β - τ (χ 0 - χ i)) (β - τ (χ 0 - χ j))
      = ClassFunction.inner (χ i) (χ j) := by
  have hcstar : star (ClassFunction.inner (χ 0) (χ 0)) = ClassFunction.inner (χ 0) (χ 0) :=
    (OddOrder.RepresentationTheory.inner_conj_symm (χ 0) (χ 0)).symm
  have hai : ClassFunction.inner (τ (χ 0 - χ i)) β
      = ClassFunction.inner (χ 0) (χ 0) - ClassFunction.inner (χ i) (χ 0) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hB i, star_sub, hcstar,
      ← OddOrder.RepresentationTheory.inner_conj_symm]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hββ, hB j, hai, hdiff i j, ClassFunction.inner_sub_left,
    ClassFunction.inner_sub_right, ClassFunction.inner_sub_right]
  ring

/-- `D.X ∈ ℤ[Irr G]` (`X = ∑_{R(χ)} coeff α • α`, each `α ∈ ℤ[Irr G]`). -/
theorem CharacterPsiDecomposition_X_mem_ZIrr {τ : IntegralCharacterMap L G}
    {χ ψ : ClassFunction L ℂ} (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    D.X ∈ ZIrr G := by
  rw [D.X_eq]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (D.imageFamily.mem_ZIrr α hα)

/-- **Peterfalvi (5.7), standalone form**: under the (5.2) coherence hypotheses, if every member of
`S` has the same degree, then `(S, A, τ)` is coherent.

Faithful to Peterfalvi: `hirr` (`S ⊆ Irr L`, the (5.3.a) setting), `hconst` (equal degree), and the
Dade-side facts `hZIrr` (`τ` maps supported member differences into `ℤ[Irr G]`), `h1A` (`1 ∉ A`,
i.e. `A = L^#`) and `hsuppdiff` (member differences are `A`-supported) are discharged by the §13
consumer from the Dade isometry.  The proof follows (5.7) directly: if `S` is a single conjugate
pair
it is the (5.2.d) base case; otherwise the auxiliary isometry `χⱼ ↦ β − (χ₀ − χⱼ)^τ` (with
`β = χ₀^{τ₁}` the common `R(χ₀)`-projection, independent of the auxiliary member) is an orthonormal
retargeting, fed to the equal-degree coherence builder `coherentEqualDegree`.

This is the producer that `S13_MaximalIII_IV.HC_le_secondDerived` (Peterfalvi (11.5)) will cite,
once
a `Hypothesis (5.2)` instance for `S(M'')` is constructed on the §13 Dade side. -/
theorem coherent_of_constant_degree_general
    (hyp : GeneralHypothesis (L := L) (G := G) S A) (hSfin : S.Finite) (hcard : 2 ≤ S.ncard)
    (hnat : ∀ ζ ∈ S, ∃ m : ℕ, ClassFunction.inner ζ ζ = (m : ℂ))
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hconst : ∀ a ∈ S, ∀ b ∈ S,
      ((a : ClassFunction L ℂ) : L → ℂ) 1 = ((b : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ∀ a ∈ S, ((a : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0) (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A) :
    Nonempty (IsCoherent hyp.tau S A) := by
  classical
  by_cases hex : ∃ a ∈ S, ∃ b ∈ S, DiffPair a b
  · -- `|S| ≥ 4`: retargeting via `commonImage` + `coherentEqualDegree`.
    obtain ⟨a, ha, b, hb, hdpab⟩ := hex
    -- enumerate `S` as `χ : Fin n → CF(L)`.
    set n := hSfin.toFinset.card with hndef
    set χ : Fin n → ClassFunction L ℂ := fun i => ↑(hSfin.toFinset.equivFin.symm i) with hχdef
    have hmem : ∀ i, χ i ∈ S := fun i => hSfin.mem_toFinset.mp (hSfin.toFinset.equivFin.symm i).2
    have hinj : Function.Injective χ := fun i j hij =>
      hSfin.toFinset.equivFin.symm.injective (Subtype.ext hij)
    have hn2 : 2 ≤ n := by
      have hne : n = S.ncard := by rw [hndef]; exact (Set.ncard_eq_toFinset_card S hSfin).symm
      omega
    have : NeZero n := ⟨by omega⟩
    have hrange : Set.range χ = S := by
      apply Set.eq_of_subset_of_subset
      · rintro _ ⟨i, rfl⟩; exact hmem i
      · intro x hx
        exact ⟨hSfin.toFinset.equivFin ⟨x, hSfin.mem_toFinset.mpr hx⟩, by simp [hχdef]⟩
    -- a reference `ζ₀` in a different conjugate pair from `χ 0`.
    obtain ⟨ζ₀, hζ₀S, hdp0⟩ : ∃ ζ₀ ∈ S, DiffPair (χ 0) ζ₀ := by
      by_cases ha0 : DiffPair (χ 0) a
      · exact ⟨a, ha, ha0⟩
      by_cases hb0 : DiffPair (χ 0) b
      · exact ⟨b, hb, hb0⟩
      exfalso
      simp only [DiffPair, not_and_or, not_not] at ha0 hb0
      rcases ha0 with h1 | h1 <;> rcases hb0 with h2 | h2
      · exact hdpab.1 (h1 ▸ h2)
      · exact hdpab.2 (h1 ▸ h2)
      · exact hdpab.2 (by rw [← ClassFunction.conj_conj a, ← h1, h2])
      · exact hdpab.1 (by rw [← ClassFunction.conj_conj a, ← h1, h2, ClassFunction.conj_conj])
    set β := commonImage hyp hZIrr hsuppdiff hdp0 (hmem 0) hζ₀S with hβdef
    set X : Fin n → ClassFunction G ℂ := fun j => β - hyp.tau (χ 0 - χ j) with hXdef
    -- the uniform form of (B): `⟨β, (χ₀ − χⱼ)^τ⟩ = 1 − ⟨χ₀, χⱼ⟩`.
    have hB : ∀ j, ClassFunction.inner β (hyp.tau (χ 0 - χ j))
        = ClassFunction.inner (χ 0) (χ 0) - ClassFunction.inner (χ 0) (χ j) := by
      intro j
      by_cases hj : χ j = χ 0
      · rw [hj, sub_self, map_zero, ClassFunction.inner_zero_right]; ring
      · rw [hβdef, commonImage_inner hyp hZIrr hsuppdiff hdp0
            (hmem 0) hζ₀S (hmem j) hj,
          hyp.pairwise_orthogonal (hmem 0) (hmem j) (Ne.symm hj)]; ring
    -- pairwise orthogonality and nonzero norms — **no unit norm needed**: the weighted builder
    -- `coherentEqualDegreeW` asks only that the target family match the Gram matrix of `χ`.
    have horthχ : ∀ i j, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0 :=
      fun i j hij => hyp.pairwise_orthogonal (hmem i) (hmem j) (fun h => hij (hinj h))
    have hnorm : ∀ j, ClassFunction.inner (χ j) (χ j) ≠ 0 := by
      intro j hzero
      have hz : χ j = 0 := eq_zero_of_inner_self_re_eq_zero (by rw [hzero]; simp)
      exact hdeg0 (χ j) (hmem j) (by rw [hz]; simp)
    have hcoh : IsCoherent hyp.tau (Set.range χ) A := by
      refine coherentEqualDegreeW (χ := χ) (X := X) hn2 horthχ hnorm ?_ ?_ ?_ ?_
        (hdeg0 (χ 0) (hmem 0)) h1A ?_
      · -- `hgram`: `⟨Xᵢ, Xⱼ⟩ = ⟨χᵢ, χⱼ⟩` — exactly `xFamily_inner`.
        intro i j
        rw [hXdef]
        exact xFamily_inner χ β (fun p q =>
            hyp.tau_isometry_memberDiff (hmem 0) (hmem p) (hmem 0) (hmem q)
              (hsuppdiff _ (hmem 0) _ (hmem p)) (hsuppdiff _ (hmem 0) _ (hmem q)))
          (commonImage_self hyp hZIrr hsuppdiff hdp0 (hmem 0) hζ₀S) hB i j
      · -- `himg`: `(χⱼ − χ₀)^τ = Xⱼ − X₀`.
        intro j
        simp only [hXdef, sub_self, map_zero, sub_zero]
        rw [show χ j - χ 0 = -(χ 0 - χ j) from by abel, map_neg]; abel
      · -- `hXZ`: `Xⱼ ∈ ℤ[Irr G]`.
        intro j
        exact Submodule.sub_mem _ (CharacterPsiDecomposition_X_mem_ZIrr _)
          (hZIrr (χ 0) (hmem 0) (χ j) (hmem j))
      · -- `hdeg`: equal degree.
        intro j; exact hconst (χ j) (hmem j) (χ 0) (hmem 0)
      · -- `hsuppdiff`.
        intro j; exact hsuppdiff (χ j) (hmem j) (χ 0) (hmem 0)
    rw [hrange] at hcoh
    exact ⟨hcoh⟩
  · -- `S` is a single conjugate pair `{χ₀, χ̄₀}`: the (5.2.d) base case.
    obtain ⟨χ₀, hχ₀⟩ : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    have hcm : χ₀.conj ∈ S := hyp.conjugate_mem hχ₀
    have hSeq : S = {χ₀, χ₀.conj} := by
      apply Set.eq_of_subset_of_subset
      · intro z hz
        by_contra hzn
        rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzn
        exact hex ⟨χ₀, hχ₀, z, hz, fun h => hzn.1 h.symm,
          fun h => hzn.2 (by rw [h, ClassFunction.conj_conj])⟩
      · intro z hz
        rcases hz with rfl | rfl
        · exact hχ₀
        · exact hcm
    obtain ⟨m, hm⟩ := hnat χ₀ hχ₀
    have hbase : IsCoherent hyp.tau ({χ₀, χ₀.conj} : Set (ClassFunction L ℂ)) A :=
      isCoherent_pair_of_orthonormalImage (hyp.difference_image hχ₀) hm
        (hyp.tau_isometry_memberDiff hχ₀ hcm hχ₀ hcm
          (hsuppdiff χ₀ hχ₀ χ₀.conj hcm) (hsuppdiff χ₀ hχ₀ χ₀.conj hcm))
        (hyp.pairwise_orthogonal hχ₀ hcm (hyp.ne_conj hχ₀))
        (hyp.pairwise_orthogonal hcm hχ₀ (Ne.symm (hyp.ne_conj hχ₀))) (hyp.ne_conj hχ₀)
        (hconst χ₀.conj hcm χ₀ hχ₀) (hdeg0 χ₀ hχ₀)
        (hsuppdiff χ₀ hχ₀ χ₀.conj hcm) h1A (hZIrr χ₀ hχ₀ χ₀.conj hcm)
    rw [← hSeq] at hbase
    exact ⟨hbase⟩

/-- **Peterfalvi (5.7)** for the two-element (5.2.d) carrier — the `‖χ‖² = 1` specialization of
`coherent_of_constant_degree_general`.

`Hypothesis` stores `R(χ)` as a signed pair, which already forces every member irreducible, so
`hirr` is discharged by the general statement's integrality hypothesis at `m = 1`. -/
theorem coherent_of_constant_degree
    (hyp : Hypothesis (L := L) (G := G) S A) (hSfin : S.Finite) (hcard : 2 ≤ S.ncard)
    (hirr : ∀ ζ ∈ S, ClassFunction.inner ζ ζ = 1)
    (hZIrr : ∀ a ∈ S, ∀ b ∈ S, hyp.tau (a - b) ∈ ZIrr G)
    (hconst : ∀ a ∈ S, ∀ b ∈ S,
      ((a : ClassFunction L ℂ) : L → ℂ) 1 = ((b : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ∀ a ∈ S, ((a : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0) (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A) :
    Nonempty (IsCoherent hyp.tau S A) :=
  coherent_of_constant_degree_general hyp.toGeneralHypothesis hSfin hcard
    (fun ζ hζ => ⟨1, by rw [hirr ζ hζ]; norm_num⟩) hZIrr hconst hdeg0 h1A hsuppdiff

end OddOrder.Peterfalvi.S07


