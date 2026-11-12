-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
-- name    : OddOrder_Peterfalvi_S07_Coherence_NormInequalities
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:09.057204+00:00
-- url     : https://prove2.me/theorems/5fdb000d-a467-4ffc-9d30-7e4ca35fb862
-- title:
--   Peterfalvi (5.4)–(5.6)/(6.6): norm inequalities, $\psi$-decomposition, coherence, degree gap
-- statement:
--   Part of the coherence development of Peterfalvi §7 (first half of (5.4)–(5.6) and (6.6)): norm inequalities, the $\psi$-decomposition, the definition of coherence, and the degree gap.
--
--   Main definitions: `CharacterPsiDecomposition` (the setup of (5.4): bundles its hypotheses, with smart constructor `ofProjection` via integral projection), `IsCoherent` (Peterfalvi (5.1): $\tau$ is coherent for $(S,A)$ if it admits an integral extension) and `GeneralHypothesis` (Peterfalvi Hypothesis (5.2), the book-faithful carrier, p. 25), with lemmas that the difference sublattice contains $\chi-\bar\chi$ and $\chi-\psi$.
--
--   The bundle also proves 31 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_Coherence/NormInequalities.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_Coherence/NormInequalities.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

open OddOrder.RepresentationTheory in
/-- **Peterfalvi (5.4) setup.**  Bundles the hypotheses of (5.4): the orthonormal
image family `R(χ)`, the auxiliary isometry `τ₁` agreeing with `τ` on `χ - χ̄`, the
decomposition `(χ - ψ)^{τ₁} = X - Y` with `X ∈ ℤ[R(χ)]` (recorded via integer
coefficients `coeff`) and `Y ⊥ R(χ)`, and the orthogonality relations
`(χ,ψ) = (χ̄,ψ) = (χ,χ̄) = 0`. -/
structure CharacterPsiDecomposition (τ : IntegralCharacterMap L G)
    (χ ψ : ClassFunction L ℂ)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- The orthonormal image family `R(χ)` with `(χ - χ̄)^τ = ∑_{α ∈ R(χ)} α`. -/
  imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ
  /-- The auxiliary isometry `τ₁` on `ℤ[χ - ψ, χ - χ̄]`. -/
  tau1 : IntegralCharacterMap L G
  /-- `τ₁` preserves the inner product on the sponsoring lattice `ℤ[χ, χ̄, ψ]`.

  This is **lattice-relative**, not a global `IsIntegralIsometry` on all of `CF(L)`:
  it is the same Round-13 weakening already applied to `IsCoherent.extension_inner_eq`.
  In Feit–Thompson `dim CF(L) > dim CF(G)`, so a global isometry of the
  character-difference lattice into `CF(G)` generically does not exist, but the Dade
  isometry / running extension *does* preserve the inner product on the supported
  sublattice `ℤ[χ, χ̄, ψ]` — which is all the (5.4.b)/(5.5)/(5.6.2) proofs use (every
  access is on `χ - ψ` or `χ - χ̄`, both in `ℤ[χ, χ̄, ψ]`). -/
  tau1_inner_eq_on_support :
    ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} → ζ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} →
      ClassFunction.inner (tau1 φ) (tau1 ζ) = ClassFunction.inner φ ζ
  /-- `τ₁` coincides with `τ` on `χ - χ̄`. -/
  tau1_agrees : tau1 (χ - χ.conj) = τ (χ - χ.conj)
  /-- The image side `X` of `(χ - ψ)^{τ₁} = X - Y`. -/
  X : ClassFunction G ℂ
  /-- The orthogonal side `Y` of `(χ - ψ)^{τ₁} = X - Y`. -/
  Y : ClassFunction G ℂ
  /-- The decomposition `(χ - ψ)^{τ₁} = X - Y`. -/
  tau1_image : tau1 (χ - ψ) = X - Y
  /-- The integer coefficients of `X ∈ ℤ[R(χ)]`. -/
  coeff : ClassFunction G ℂ → ℤ
  /-- `X = ∑_{α ∈ R(χ)} (coeff α) • α`, i.e. `X ∈ ℤ[R(χ)]`. -/
  X_eq : X = ∑ α ∈ imageFamily.imageSet, (coeff α : ℂ) • α
  /-- `Y` is orthogonal to `R(χ)`. -/
  Y_orthogonal : ∀ α ∈ imageFamily.imageSet, ClassFunction.inner Y α = 0
  /-- `(χ, ψ) = 0`. -/
  chi_psi_orthogonal : ClassFunction.inner χ ψ = 0
  /-- `(χ̄, ψ) = 0`. -/
  chiConj_psi_orthogonal : ClassFunction.inner χ.conj ψ = 0
  /-- `(χ, χ̄) = 0` (the distinct elements `χ`, `χ̄ ∈ S` are orthogonal by (5.2.c)). -/
  chi_chiConj_orthogonal : ClassFunction.inner χ χ.conj = 0

namespace CharacterPsiDecomposition

open OddOrder.RepresentationTheory

variable {τ : IntegralCharacterMap L G} {χ ψ : ClassFunction L ℂ}

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Smart constructor for `CharacterPsiDecomposition` via integral projection.**

The hard `X`/`Y`/`coeff` content of the (5.4) decomposition `(χ − ψ)^{τ₁} = X − Y` — the
integral `R(χ)`-projection `X = ∑_{α ∈ R(χ)} (coeff α)•α ∈ ℤ[R(χ)]` and the orthogonal residual
`Y ⊥ R(χ)` — is *computed*, not posited, from the single number-theoretic input
`htau1_mem : (χ − ψ)^{τ₁} ∈ ZIrr G` (the τ₁-image is a virtual character of `G`).  This is the
orthogonal projection of `(χ − ψ)^{τ₁}` onto the ZIrr-orthonormal family `R(χ)`
(`exists_intProjection_of_orthonormal_ZIrr`, integer coefficients because `R(χ) ⊆ ZIrr G`); the
residual `Y` is its orthogonal complement.

The remaining inputs are exactly the *structural* data a per-step (5.4)/(5.5)/(5.6.1) construction
must still supply:
* `imageFamily` — the signed-irreducible family `R(χ)` with `(χ − χ̄)^τ = ∑_{α} α` (from the Dade
  data / §3 keystone, `OrthonormalCharacterImageFamily`);
* `tau1`, `htau1_inner_eq`, `htau1_agrees` — the (5.4) auxiliary isometry `τ₁`, supplied as
  **lattice-relative** inner-preservation on the sponsoring lattice `ℤ[χ, χ̄, ψ]` (the Round-13
  weakening: the Dade isometry / running extension preserves `⟨·,·⟩` only on the supported
  sublattice, *not* globally on `CF(L)`), agreeing with `τ` on `χ − χ̄`;
* the three (5.2.c)/(5.4) orthogonality scalars `⟨χ, ψ⟩ = ⟨χ̄, ψ⟩ = ⟨χ, χ̄⟩ = 0`.

This isolates the genuinely missing primitives (the Dade `R(χ)` extractor and the `τ₁`
isometry-extension) as the only residual: once those are built, this constructor delivers the full
`CharacterPsiDecomposition` with its `X`/`Y`/`coeff`/`X_eq`/`Y_orthogonal` fields populated by the
projection. -/
noncomputable def ofProjection
    (imageFamily : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (tau1 : IntegralCharacterMap L G)
    (htau1_inner_eq : ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} → ζ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} →
      ClassFunction.inner (tau1 φ) (tau1 ζ) = ClassFunction.inner φ ζ)
    (htau1_agrees : tau1 (χ - χ.conj) = τ (χ - χ.conj))
    (htau1_mem : tau1 (χ - ψ) ∈ ZIrr G)
    (hχψ : ClassFunction.inner χ ψ = 0)
    (hχbarψ : ClassFunction.inner χ.conj ψ = 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0) :
    CharacterPsiDecomposition (L := L) (G := G) τ χ ψ :=
  let proj := ClassFunction.exists_intProjection_of_orthonormal_ZIrr htau1_mem
    imageFamily.mem_ZIrr imageFamily.orthonormal
  { imageFamily := imageFamily
    tau1 := tau1
    tau1_inner_eq_on_support := htau1_inner_eq
    tau1_agrees := htau1_agrees
    X := ∑ α ∈ imageFamily.imageSet, (proj.choose α : ℂ) • α
    Y := -(tau1 (χ - ψ) - ∑ α ∈ imageFamily.imageSet, (proj.choose α : ℂ) • α)
    tau1_image := by
      -- `X − Y = X − (−(τ₁(χ−ψ) − X)) = τ₁(χ−ψ)`, pure algebra.
      rw [sub_neg_eq_add]; abel
    coeff := proj.choose
    X_eq := rfl
    Y_orthogonal := by
      -- `⟨Y, α⟩ = −⟨τ₁(χ−ψ) − X, α⟩ = −(⟨τ₁(χ−ψ), α⟩ − coeff α) = −(coeff α − coeff α) = 0`.
      intro α hα
      have hcoeff : ClassFunction.inner (tau1 (χ - ψ)) α = (proj.choose α : ℂ) :=
        proj.choose_spec.choose_spec.1 α hα
      rw [ClassFunction.inner_neg_left, ClassFunction.inner_sub_left,
        inner_orthonormalSum_eq_coeff imageFamily.orthonormal hα, hcoeff, sub_self, neg_zero]
    chi_psi_orthogonal := hχψ
    chiConj_psi_orthogonal := hχbarψ
    chi_chiConj_orthogonal := hχχbar }

omit [Fintype L] in
omit [Invertible (Nat.card L : ℂ)] in
/-- `χ - χ̄ ∈ ℤ[χ−χ̄, χ−ψ]`: the difference sublattice contains the conjugate difference (it is a
generator). -/
theorem chi_sub_conj_mem_zSpan_support :
    χ - χ.conj ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} :=
  Submodule.subset_span (by simp)

omit [Fintype L] in
omit [Invertible (Nat.card L : ℂ)] in
/-- `χ - ψ ∈ ℤ[χ−χ̄, χ−ψ]`: the difference sublattice contains the `ψ`-difference (it is a
generator). -/
theorem chi_sub_psi_mem_zSpan_support :
    χ - ψ ∈ zSpan (L := L) {χ - χ.conj, χ - ψ} :=
  Submodule.subset_span (by simp)

/-- `‖X‖² = ∑_{α ∈ R(χ)} (coeff α)²` (Parseval). -/
theorem inner_self_X (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X D.X = ∑ α ∈ D.imageFamily.imageSet, (D.coeff α : ℂ) ^ 2 := by
  rw [D.X_eq]
  exact inner_self_orthonormalSum_eq_sum_sq D.imageFamily.orthonormal

/-- `⟨X, ∑_{α ∈ R(χ)} α⟩ = ∑_{α ∈ R(χ)} coeff α`. -/
theorem inner_X_sum (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X (∑ α ∈ D.imageFamily.imageSet, α) =
      ∑ α ∈ D.imageFamily.imageSet, (D.coeff α : ℂ) := by
  rw [D.X_eq]
  exact inner_orthonormalSum_sum_eq_sum_coeff D.imageFamily.orthonormal

/-- `Y ⊥ R(χ)` extends to the sum: `⟨Y, ∑_{α ∈ R(χ)} α⟩ = 0`. -/
theorem inner_Y_sum (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.Y (∑ α ∈ D.imageFamily.imageSet, α) = 0 := by
  rw [inner_sum_right]
  exact Finset.sum_eq_zero fun α hα => D.Y_orthogonal α hα

/-- **The keystone identity of (5.4.a).**  `‖χ‖² = ∑_{α ∈ R(χ)} coeff α`.

`‖χ‖² = ⟨χ - ψ, χ - χ̄⟩` (using the three orthogonality relations), `= ⟨X - Y, ∑ α⟩`
(by the isometry of `τ₁` and `τ₁ = τ` on `χ - χ̄`), `= ⟨X, ∑ α⟩` (since `Y ⊥ R(χ)`),
`= ∑ coeff α`. -/
theorem inner_self_chi_eq_sum_coeff
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner χ χ = ∑ α ∈ D.imageFamily.imageSet, (D.coeff α : ℂ) := by
  -- Step 1: `⟨χ, χ⟩ = ⟨χ - ψ, χ - χ̄⟩`.
  have hpsi_chi : ClassFunction.inner ψ χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.chi_psi_orthogonal, star_zero]
  have hpsi_chiConj : ClassFunction.inner ψ χ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.chiConj_psi_orthogonal, star_zero]
  have hsrc : ClassFunction.inner χ χ =
      ClassFunction.inner (χ - ψ) (χ - χ.conj) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, D.chi_chiConj_orthogonal, hpsi_chi, hpsi_chiConj]
    ring
  -- Step 2: transport across `τ₁` (isometry, agreeing with `τ` on `χ - χ̄`).
  have himg : ClassFunction.inner (χ - ψ) (χ - χ.conj) =
      ClassFunction.inner (D.X - D.Y) (∑ α ∈ D.imageFamily.imageSet, α) := by
    rw [← D.tau1_inner_eq_on_support (χ - ψ) (χ - χ.conj)
        chi_sub_psi_mem_zSpan_support chi_sub_conj_mem_zSpan_support,
      D.tau1_image, D.tau1_agrees, D.imageFamily.image_eq]
  -- Step 3: `Y ⊥ R(χ)` drops `Y`; coefficient recovery finishes.
  rw [hsrc, himg, ClassFunction.inner_sub_left, D.inner_Y_sum, sub_zero, D.inner_X_sum]

/-- **Peterfalvi (5.4.a):** `‖X‖² ≥ ‖χ‖²`.

By the keystone identity `‖χ‖² = ∑ coeff α` and Parseval `‖X‖² = ∑ (coeff α)²`, the
integer Cauchy–Schwarz `∑ coeff α ≤ ∑ (coeff α)²` gives the inequality. -/
theorem inner_self_chi_re_le_inner_self_X
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    (ClassFunction.inner χ χ).re ≤ (ClassFunction.inner D.X D.X).re := by
  classical
  have hχ : ClassFunction.inner χ χ =
      ((∑ α ∈ D.imageFamily.imageSet, D.coeff α : ℤ) : ℂ) := by
    rw [D.inner_self_chi_eq_sum_coeff]; push_cast; ring
  have hX : ClassFunction.inner D.X D.X =
      ((∑ α ∈ D.imageFamily.imageSet, (D.coeff α) ^ 2 : ℤ) : ℂ) := by
    rw [D.inner_self_X]; push_cast; ring
  rw [hχ, hX, Complex.intCast_re, Complex.intCast_re]
  exact_mod_cast finset_sum_le_sum_sq D.imageFamily.imageSet D.coeff

/-- `⟨χ, χ⟩` is the integer cast `(∑ coeff α : ℤ)`. -/
theorem inner_self_chi_eq_intCast
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner χ χ = ((∑ α ∈ D.imageFamily.imageSet, D.coeff α : ℤ) : ℂ) := by
  rw [D.inner_self_chi_eq_sum_coeff]; push_cast; ring

/-- `⟨X, X⟩` is the integer cast `(∑ (coeff α)² : ℤ)`. -/
theorem inner_self_X_eq_intCast
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X D.X = ((∑ α ∈ D.imageFamily.imageSet, (D.coeff α) ^ 2 : ℤ) : ℂ) := by
  rw [D.inner_self_X]; push_cast; ring

/-- `X ⊥ Y`: `⟨X, Y⟩ = 0` (since `X ∈ ℤ[R(χ)]` and `Y ⊥ R(χ)`). -/
theorem inner_X_Y (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner D.X D.Y = 0 := by
  rw [D.X_eq, inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [ClassFunction.inner_smul_left,
    OddOrder.RepresentationTheory.inner_conj_symm, D.Y_orthogonal α hα, star_zero, mul_zero]

/-- `‖X - Y‖² = ‖X‖² + ‖Y‖²` (Pythagoras, since `X ⊥ Y`). -/
theorem inner_self_X_sub_Y (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner (D.X - D.Y) (D.X - D.Y) =
      ClassFunction.inner D.X D.X + ClassFunction.inner D.Y D.Y := by
  have hYX : ClassFunction.inner D.Y D.X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.inner_X_Y, star_zero]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, D.inner_X_Y, hYX]
  ring

/-- `‖χ - ψ‖² = ‖χ‖² + ‖ψ‖²` (Pythagoras, since `(χ, ψ) = (ψ, χ) = 0`). -/
theorem inner_self_chi_sub_psi (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner (χ - ψ) (χ - ψ) =
      ClassFunction.inner χ χ + ClassFunction.inner ψ ψ := by
  have hpsi_chi : ClassFunction.inner ψ χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, D.chi_psi_orthogonal, star_zero]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right, D.chi_psi_orthogonal, hpsi_chi]
  ring

/-- The total-norm identity `‖χ‖² + ‖ψ‖² = ‖X‖² + ‖Y‖²` from the isometry of `τ₁`. -/
theorem inner_self_chi_add_psi_eq
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    ClassFunction.inner χ χ + ClassFunction.inner ψ ψ =
      ClassFunction.inner D.X D.X + ClassFunction.inner D.Y D.Y := by
  rw [← D.inner_self_chi_sub_psi, ← D.inner_self_X_sub_Y, ← D.tau1_image,
    D.tau1_inner_eq_on_support (χ - ψ) (χ - ψ)
      chi_sub_psi_mem_zSpan_support chi_sub_psi_mem_zSpan_support]

/-- **Peterfalvi (5.6.2) opening bound:** `‖Y‖² ≤ ‖ψ‖²`.

This is the first step of (5.6.2) ("We note first that `‖χ‖² + a²‖χ₁‖² = ‖X‖² + ‖Y‖²`;
by (5.4.a) `‖X‖² ≥ ‖χ‖²`, so `‖Y‖² ≤ a²‖χ₁‖²`").  It follows directly from the total-norm
identity `‖χ‖² + ‖ψ‖² = ‖X‖² + ‖Y‖²` and (5.4.a) `‖χ‖² ≤ ‖X‖²`, with `ψ = a·χ₁` in the
application.  Stated for the general `ψ` of the (5.4) decomposition. -/
theorem inner_self_Y_re_le_inner_self_psi
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    (ClassFunction.inner D.Y D.Y).re ≤ (ClassFunction.inner ψ ψ).re := by
  have htotal : (ClassFunction.inner χ χ).re + (ClassFunction.inner ψ ψ).re =
      (ClassFunction.inner D.X D.X).re + (ClassFunction.inner D.Y D.Y).re := by
    have := congrArg Complex.re D.inner_self_chi_add_psi_eq
    simpa [Complex.add_re] using this
  have hXge := D.inner_self_chi_re_le_inner_self_X
  linarith

/-- **Peterfalvi (5.4.b).**  If `‖Y‖² ≥ ‖ψ‖²`, then `‖X‖² = ‖χ‖²`, `‖Y‖² = ‖ψ‖²`
and `X = ∑_{α ∈ E} α` for some `E ⊆ R(χ)` with `|E| = ‖χ‖²`.

The total-norm identity `‖χ‖² + ‖ψ‖² = ‖X‖² + ‖Y‖²` together with `‖X‖² ≥ ‖χ‖²`
(5.4.a) and the hypothesis `‖Y‖² ≥ ‖ψ‖²` forces both inequalities to be equalities.
The norm equality `‖χ‖² = ‖X‖²` reads `∑ coeff α = ∑ (coeff α)²`, so by the tightness
of integer Cauchy–Schwarz each `coeff α ∈ {0, 1}`; then `E = {α | coeff α = 1}` and
`X = ∑_{α ∈ E} α`.  The cardinality `|E| = ∑ coeff α = ‖χ‖²` is the form used in
(5.6.3) to compute `‖χ̄^{τ₂}‖² = |R(χ)| - |E| = ‖χ - χ̄‖² - ‖χ‖² = ‖χ̄‖²`. -/
theorem norm_eq_and_X_eq_sum_of_norm_Y_ge
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (hY : (ClassFunction.inner ψ ψ).re ≤ (ClassFunction.inner D.Y D.Y).re) :
    (ClassFunction.inner χ χ).re = (ClassFunction.inner D.X D.X).re ∧
      (ClassFunction.inner ψ ψ).re = (ClassFunction.inner D.Y D.Y).re ∧
      ∃ E ⊆ D.imageFamily.imageSet, D.X = ∑ α ∈ E, α ∧
        (E.card : ℂ) = ClassFunction.inner χ χ := by
  classical
  -- The `.re` total-norm identity.
  have htotal : (ClassFunction.inner χ χ).re + (ClassFunction.inner ψ ψ).re =
      (ClassFunction.inner D.X D.X).re + (ClassFunction.inner D.Y D.Y).re := by
    have := congrArg Complex.re D.inner_self_chi_add_psi_eq
    simpa [Complex.add_re] using this
  have hXge := D.inner_self_chi_re_le_inner_self_X
  -- Both inequalities are forced to equalities.
  have hχX : (ClassFunction.inner χ χ).re = (ClassFunction.inner D.X D.X).re := by linarith
  have hψY : (ClassFunction.inner ψ ψ).re = (ClassFunction.inner D.Y D.Y).re := by linarith
  refine ⟨hχX, hψY, ?_⟩
  -- Tightness: `∑ coeff = ∑ coeff²` as integers.
  have hsum_eq : (∑ α ∈ D.imageFamily.imageSet, D.coeff α) =
      ∑ α ∈ D.imageFamily.imageSet, (D.coeff α) ^ 2 := by
    have h1 := hχX
    rw [D.inner_self_chi_eq_intCast, D.inner_self_X_eq_intCast,
      Complex.intCast_re, Complex.intCast_re] at h1
    exact_mod_cast h1
  have hcoeff01 : ∀ α ∈ D.imageFamily.imageSet, D.coeff α = 0 ∨ D.coeff α = 1 :=
    (finset_sum_eq_sum_sq_iff D.imageFamily.imageSet D.coeff).mp hsum_eq
  -- `E = {α | coeff α = 1}`.
  set E := D.imageFamily.imageSet.filter (fun α => D.coeff α = 1) with hE
  refine ⟨E, Finset.filter_subset _ _, ?_, ?_⟩
  · -- `X = ∑_{α ∈ E} α`.
    rw [D.X_eq, hE, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α hα => ?_
    rcases hcoeff01 α hα with h0 | h1
    · rw [h0, if_neg (by norm_num), Int.cast_zero, zero_smul]
    · rw [h1, if_pos rfl, Int.cast_one, one_smul]
  · -- `|E| = ∑ coeff α = ‖χ‖²`: on `R(χ)`, `coeff α = (if coeff α = 1 then 1 else 0)`.
    have hcard : (E.card : ℤ) = ∑ α ∈ D.imageFamily.imageSet, D.coeff α := by
      rw [hE, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rcases hcoeff01 α hα with h0 | h1
      · rw [h0, if_neg (by norm_num), Nat.cast_zero]
      · rw [h1, if_pos rfl, Nat.cast_one]
    rw [D.inner_self_chi_eq_intCast]
    exact_mod_cast hcard

/-- **Peterfalvi (5.5).**  Applying (5.4) with `ψ = 0`: the hypothesis `‖Y‖² ≥ ‖ψ‖² = 0`
of (5.4.b) holds automatically (the inner product is positive semidefinite), so `Y = 0`
and `χ^{τ₁} = X = ∑_{α ∈ E} α` for some `E ⊆ R(χ)` with `|E| = ‖χ‖²`.

`‖ψ‖² = ⟨0, 0⟩ = 0 ≤ ‖Y‖²` feeds (5.4.b), whose norm equality `‖Y‖² = ‖ψ‖² = 0` forces
`Y = 0` by positive definiteness of `ClassFunction.inner`.  Then
`χ^{τ₁} = (χ - 0)^{τ₁} = X - Y = X`. -/
theorem eq_sum_of_psi_eq_zero
    (D : CharacterPsiDecomposition (L := L) (G := G) τ χ 0) :
    D.Y = 0 ∧ D.tau1 χ = D.X ∧
      ∃ E ⊆ D.imageFamily.imageSet, D.X = ∑ α ∈ E, α ∧
        (E.card : ℂ) = ClassFunction.inner χ χ := by
  -- `‖ψ‖² = ‖0‖² = 0 ≤ ‖Y‖²` by positive semidefiniteness.
  have hψY : (ClassFunction.inner (0 : ClassFunction L ℂ) 0).re ≤
      (ClassFunction.inner D.Y D.Y).re := by
    rw [ClassFunction.inner_zero_left, Complex.zero_re]
    exact inner_self_re_nonneg D.Y
  obtain ⟨_, hYnorm, E, hEsub, hXsum, hEcard⟩ := D.norm_eq_and_X_eq_sum_of_norm_Y_ge hψY
  -- `‖Y‖² = ‖0‖² = 0`, so `Y = 0` by positive definiteness.
  have hY0 : D.Y = 0 := by
    apply eq_zero_of_inner_self_re_eq_zero
    rw [← hYnorm, ClassFunction.inner_zero_left, Complex.zero_re]
  -- `χ^{τ₁} = (χ - 0)^{τ₁} = X - Y = X`.
  have hτ1χ : D.tau1 χ = D.X := by
    have := D.tau1_image
    rw [sub_zero] at this
    rw [this, hY0, sub_zero]
  exact ⟨hY0, hτ1χ, E, hEsub, hXsum, hEcard⟩

end CharacterPsiDecomposition

/-- Peterfalvi (5.1): `τ` is coherent for `(S,A)` if it admits an integral
extension on `Z[S]` that is **isometric on the lattice `Z[S]`** and agrees with
`τ` on `Z[S,A]`.

The isometry hypothesis is **lattice-relative** (`extension_inner_eq`, restricted
to `φ, ψ ∈ Z[S] = zSpan S`), not a global `IsIntegralIsometry` on all of `CF(L)`.
This is the object Peterfalvi actually constructs in (5.6): in Feit–Thompson
`dim CF(L) > dim CF(G)`, so a global isometry of the character-difference lattice
into `CF(G)` generically does not exist, but the lattice-relative one
(`retarget_inner_eq_on`) does.  Every downstream consumer uses only the
inner-product preservation on lattice elements `ζ ∈ S ⊆ Z[S]`. -/
structure IsCoherent (τ : IntegralCharacterMap L G)
    (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  nonzero : ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A ∧ φ ≠ 0
  extension : IntegralCharacterMap L G
  extension_inner_eq :
    ∀ φ ψ : ClassFunction L ℂ, φ ∈ zSpan (L := L) S → ψ ∈ zSpan (L := L) S →
      ClassFunction.inner (extension φ) (extension ψ) = ClassFunction.inner φ ψ
  extends_on_supported :
    ∀ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A → extension φ = τ φ
  /-- The coherent extension sends the **coherent lattice** `ℤ[S]` into `ℤ[Irr G]`.

  Peterfalvi's coherent isometries are genuine virtual-character maps *on the coherent set*: the
  (5.6.3) running extension is built by `retarget` from virtual-character target pairs
  `{X, X̄} ⊂ ℤ[Irr G]`, sending each member of `S` to a virtual character.  (It is *not* claimed on
  all of `ℤ[Irr L]` — the base Dade map is only an isometry on the supported lattice, not a global
  `ℤ[Irr]`-endomorphism.)  This is the **ZIrr-codomain** the (6.6)/(6.8) `X`-chain needs: for an
  irreducible member `χⱼ ∈ S`, `χⱼ ∈ ℤ[S]` gives `ν χⱼ ∈ ZIrr`, the load-bearing input of
  `crux1_of_memberFamily`. -/
  extension_mem_ZIrr : ∀ φ : ClassFunction L ℂ, φ ∈ zSpan (L := L) S → extension φ ∈ ZIrr G

/-- **Peterfalvi Hypothesis (5.2), verbatim** (p. 25) — the book-faithful carrier.

Identical to `Hypothesis` except in clause **(5.2.d)**, where the difference image `R(χ)` is an
arbitrary finite orthonormal family (`τ(χ − χ̄) = ∑_{α ∈ R(χ)} α`) rather than the *two-element*
signed pair `ε·(μ − ν)` of `CharacterDifferenceImage`.

That difference is not cosmetic.  Taking norms in the two-element form gives
`‖τ(χ − χ̄)‖² = 2`, while the (5.2.b) isometry gives `‖χ − χ̄‖² = 2‖χ‖²` (using `⟨χ, χ̄⟩ = 0` and
`‖χ̄‖² = ‖χ‖²`) — so `Hypothesis` silently forces **every member to be irreducible**.  The book
imposes no such thing: a reducible member has `‖χ‖² > 1` and `|R(χ)| = 2‖χ‖²`.  This is exactly
what stops (5.7) from being provable at book strength over `Hypothesis` (issue 0157).

`Hypothesis.toGeneralHypothesis` exhibits the two-element carrier as the special case, via
`CharacterDifferenceImage.toOrthonormalImage`. -/
structure GeneralHypothesis (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  /-- **(5.2.b)**: the linear map `τ`. -/
  tau : IntegralCharacterMap L G
  /-- **(5.2.b)**: `τ` is an isometry on the `A`-supported sublattice `ℤ[S, A]`. -/
  tau_isometry_diff : ∀ ⦃φ ψ : ClassFunction L ℂ⦄,
    φ ∈ zSupportedSpan (L := L) S A → ψ ∈ zSupportedSpan (L := L) S A →
    ClassFunction.inner (tau φ) (tau ψ) = ClassFunction.inner φ ψ
  /-- **(5.2.a)**: `S` is closed under complex conjugation. -/
  conjugate_closed : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S
  /-- **(5.2.a)**: no member is real. -/
  no_real_characters : OddOrder.Peterfalvi.S03.HasNoRealCharacters S
  /-- **(5.2.c)**: distinct members are orthogonal. -/
  pairwise_orthogonal : OddOrder.Peterfalvi.S03.PairwiseOrthogonal S
  /-- **(5.2.d)**: `τ(χ − χ̄) = ∑_{α ∈ R(χ)} α` for an orthonormal `R(χ) ⊆ ℤ[Irr G]` of
  **arbitrary size** — the book's clause, with no irreducibility of `χ` implied. -/
  difference_image :
    ∀ ⦃χ : ClassFunction L ℂ⦄, χ ∈ S → OrthonormalCharacterImageFamily (L := L) (G := G) tau χ
  /-- **(5.2.e)**: `φ ⊥ {χ, χ̄}` forces `R(φ) ⊥ R(χ)`. -/
  difference_images_orthogonal :
    ∀ ⦃φ χ : ClassFunction L ℂ⦄ (hφ : φ ∈ S) (hχ : χ ∈ S),
      ClassFunction.inner φ χ = 0 → ClassFunction.inner φ χ.conj = 0 →
        (difference_image hφ).Orthogonal (difference_image hχ)

/-- Peterfalvi (5.2)-style hypotheses for coherence applications.  This is a
carrier for later theorems, not a proof that the hypotheses hold in any
particular Dade situation.

⚠ The `difference_image` field is the **two-element** (5.3.a) shape, which forces every member of
`S` to be irreducible (see `GeneralHypothesis`, the book-faithful carrier, for the derivation).
Results that do not need that refinement should be stated over `GeneralHypothesis` and reached
from here through `toGeneralHypothesis`. -/
structure Hypothesis (S : Set (ClassFunction L ℂ)) (A : Set L)
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)] where
  tau : IntegralCharacterMap L G
  /-- **Lattice-relative (5.2)(b) isometry on the `A`-supported sublattice** (issues 9001, 0099):
  `τ` preserves inner products on `ℤ[S, A] = {f ∈ ℤ[S] | supp f ⊆ A}` — Coq `subcoherent`
  clause (b) `{in 'Z[S, L^#], isometry tau}` (`PFsection5.v:488`).  A *global* `IsIntegralIsometry`
  does **not** exist for the Feit–Thompson Dade map (`dim CF(L) > dim CF(G)`), and the pre-0099
  all-member-difference form is **false** for mixed-degree families (`a − b` with `a(1) ≠ b(1)` is
  not `A`-supported) — while every extension mechanism ((5.4)/(5.6)/(5.7)/(5.9a)) only ever
  consumes `A`-supported `ℤ`-combinations.  The Dade witnesses supply this field *unconditionally*
  (any family, mixed degrees included) via `dadeIntegralCharacterMap_inner_eq_of_supported`;
  member-difference consumers use the derived `tau_isometry_memberDiff`. -/
  tau_isometry_diff : ∀ ⦃φ ψ : ClassFunction L ℂ⦄,
    φ ∈ zSupportedSpan (L := L) S A → ψ ∈ zSupportedSpan (L := L) S A →
    ClassFunction.inner (tau φ) (tau ψ) = ClassFunction.inner φ ψ
  conjugate_closed : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S
  no_real_characters : OddOrder.Peterfalvi.S03.HasNoRealCharacters S
  pairwise_orthogonal : OddOrder.Peterfalvi.S03.PairwiseOrthogonal S
  difference_image :
    ∀ ⦃χ : ClassFunction L ℂ⦄, χ ∈ S → CharacterDifferenceImage (L := L) (G := G) tau χ
  difference_images_orthogonal :
    ∀ ⦃φ χ : ClassFunction L ℂ⦄ (hφ : φ ∈ S) (hχ : χ ∈ S),
      ClassFunction.inner φ χ = 0 → ClassFunction.inner φ χ.conj = 0 →
        (difference_image hφ).Orthogonal (difference_image hχ)

/-- **The two-element carrier is the special case of the book's (5.2).**

Every clause of `GeneralHypothesis` is a field of `Hypothesis` except (5.2.d)/(5.2.e), which are
obtained by putting the signed pair `τ(χ − χ̄) = ε·(μ − ν)` into the orthonormal-family shape
`R(χ) = {ε·μ, −ε·ν}` (`CharacterDifferenceImage.toOrthonormalImage`) and transporting the
disjoint-pair orthogonality along it (`toOrthonormalImage_orthogonal`).

So results proved over `GeneralHypothesis` apply verbatim to every existing `Hypothesis` consumer,
while being available for families with reducible members — which the book's (5.2) allows and
`Hypothesis` silently forbids (issue 0157). -/
noncomputable def Hypothesis.toGeneralHypothesis {S : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis (L := L) (G := G) S A) :
    GeneralHypothesis (L := L) (G := G) S A where
  tau := hyp.tau
  tau_isometry_diff := hyp.tau_isometry_diff
  conjugate_closed := hyp.conjugate_closed
  no_real_characters := hyp.no_real_characters
  pairwise_orthogonal := hyp.pairwise_orthogonal
  difference_image := fun _χ hχ => (hyp.difference_image hχ).toOrthonormalImage
  difference_images_orthogonal := by
    intro _φ _χ hφ hχ h1 h2
    exact CharacterDifferenceImage.toOrthonormalImage_orthogonal _ _
      (hyp.difference_images_orthogonal hφ hχ h1 h2)

namespace GeneralHypothesis

variable {S : Set (ClassFunction L ℂ)} {A : Set L}

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- (5.2.a): `S` contains the conjugate of each member. -/
theorem conjugate_mem {hyp : GeneralHypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    χ.conj ∈ S :=
  hyp.conjugate_closed hχ

/-- (5.2.a): no member is real. -/
theorem not_isReal {hyp : GeneralHypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    ¬ χ.IsReal :=
  hyp.no_real_characters hχ

/-- (5.2.a): a member differs from its conjugate. -/
theorem ne_conj {hyp : GeneralHypothesis (L := L) (G := G) S A}
    {χ : ClassFunction L ℂ} (hχ : χ ∈ S) :
    χ ≠ χ.conj := by
  intro hχ_eq
  exact hyp.not_isReal hχ hχ_eq.symm

/-- **Member-difference form of the (5.2.b) lattice isometry** — the `GeneralHypothesis` copy of
`Hypothesis.tau_isometry_memberDiff`.  Both read off `tau_isometry_diff`, which is a shared
field; only (5.2.d)/(5.2.e) differ between the two carriers. -/
theorem tau_isometry_memberDiff (hyp : GeneralHypothesis (L := L) (G := G) S A)
    ⦃a b c d : ClassFunction L ℂ⦄ (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : ((a - b : ClassFunction L ℂ)).support ⊆ A)
    (hcd : ((c - d : ClassFunction L ℂ)).support ⊆ A) :
    ClassFunction.inner (hyp.tau (a - b)) (hyp.tau (c - d))
      = ClassFunction.inner (a - b) (c - d) :=
  hyp.tau_isometry_diff
    ⟨Submodule.sub_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb), hab⟩
    ⟨Submodule.sub_mem _ (Submodule.subset_span hc) (Submodule.subset_span hd), hcd⟩

end GeneralHypothesis

@[simp] theorem Hypothesis.toGeneralHypothesis_tau {S : Set (ClassFunction L ℂ)} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis (L := L) (G := G) S A) :
    hyp.toGeneralHypothesis.tau = hyp.tau := rfl

/-- **Peterfalvi (6.6): the common-index p-power degree gap (ℕ).**

This is the same strict gap as `two_mul_lt_sq_of_primePow_gap`, but in the exact
common-index form used in the §8 Sibley X-chain.  If
`d₁ = idx * p^m₁` and `dᵢ = idx * p^mᵢ` with `idx > 0`, `p ≥ 3`, and
`d₁ < dᵢ`, then the p-power residual of `dᵢ` is at least one factor of `p`
larger than the residual of `d₁`; hence `dᵢ ≥ 3 * d₁` and
`2 * dᵢ * d₁ < dᵢ^2`.

This removes the need to name a separate quotient `q = dᵢ / d₁` in the
consumer-facing §8 constructors. -/
theorem two_mul_lt_sq_of_commonIndex_primePower_gap
    {p idx θ₁ θᵢ d₁ dᵢ m₁ mᵢ : ℕ} (hp : 3 ≤ p) (hidx : 0 < idx)
    (hd₁ : d₁ = idx * θ₁) (hdᵢ : dᵢ = idx * θᵢ)
    (hθ₁ : θ₁ = p ^ m₁) (hθᵢ : θᵢ = p ^ mᵢ) (hlt : d₁ < dᵢ) :
    2 * (dᵢ * d₁) < dᵢ * dᵢ := by
  have hθlt : θ₁ < θᵢ := by
    rw [hd₁, hdᵢ] at hlt
    exact (Nat.mul_lt_mul_left hidx).mp hlt
  have hm_lt : m₁ < mᵢ := by
    rw [hθ₁, hθᵢ] at hθlt
    exact (Nat.pow_lt_pow_iff_right (show 1 < p by omega)).mp hθlt
  have hpθ : p * θ₁ ≤ θᵢ := by
    rw [hθ₁, hθᵢ]
    have hm_succ : m₁ + 1 ≤ mᵢ := Nat.succ_le_of_lt hm_lt
    calc
      p * p ^ m₁ = p ^ (m₁ + 1) := by
        rw [pow_succ']
      _ ≤ p ^ mᵢ := Nat.pow_le_pow_right (by omega) hm_succ
  have hgap : 3 * d₁ ≤ dᵢ := by
    rw [hd₁, hdᵢ]
    have h3θ : 3 * θ₁ ≤ θᵢ :=
      (Nat.mul_le_mul_right θ₁ hp).trans hpθ
    calc
      3 * (idx * θ₁) = idx * (3 * θ₁) := by ring
      _ ≤ idx * θᵢ := Nat.mul_le_mul_left idx h3θ
  have hd₁pos : 0 < d₁ := by
    rw [hd₁, hθ₁]
    exact Nat.mul_pos hidx (pow_pos (by omega) m₁)
  nlinarith [hgap, hd₁pos]

/-- **Peterfalvi (6.6): chaining the gap to the partial degree sum (ℕ).**

The gap `2·dᵢ·d₁ < dᵢ²` together with `dᵢ² ∣ D` (the square-divisibility `χᵢ(1)² ∣ ∑_{j<i}χⱼ(1)²`)
and `0 < D` gives `2·dᵢ·d₁ < D`: positivity upgrades the divisibility to `dᵢ² ≤ D`. -/
theorem two_mul_lt_of_sq_dvd_of_gap
    {d₁ dᵢ D : ℕ} (hgap : 2 * (dᵢ * d₁) < dᵢ * dᵢ)
    (hdvd : dᵢ * dᵢ ∣ D) (hDpos : 0 < D) :
    2 * (dᵢ * d₁) < D := by
  have : dᵢ * dᵢ ≤ D := Nat.le_of_dvd hDpos hdvd
  omega

/-- **Peterfalvi (6.6): additive complement of a divisor (ℕ).**

If `a` divides both the `tail` and the `total`, and `head + tail = total`, then `a ∣ head`.
This is the combination step of mmd L78+L80: with `head = ∑_{j<i}χⱼ(1)²`,
`tail = ∑_{j≥i}χⱼ(1)²`, `total = |L| - |L:Z|`, the divisibilities `θᵢ(1)² ∣ tail` and
`θᵢ(1)² ∣ total` give `θᵢ(1)² ∣ head`.  Stated additively to avoid `ℕ` subtraction. -/
theorem dvd_of_add_eq_of_dvd_dvd
    {a head tail total : ℕ} (hsum : head + tail = total)
    (htail : a ∣ tail) (htot : a ∣ total) :
    a ∣ head := by
  have h : a ∣ total - tail := Nat.dvd_sub htot htail
  rwa [show total - tail = head from by omega] at h

/-- **Peterfalvi (6.6): coprimality forcing of the full degree square (ℕ).**

The induced degree factors as `χᵢ(1) = idx·θ` (`idx = |L:K|`, `θ = θᵢ(1)`).  Given that both
`θ²` and `idx²` divide `D` and that `idx` is coprime to `θ` (mmd L80: `(|L:K|, p) = 1` with
`θ` a power of `p`), the full square `χᵢ(1)² = idx²·θ²` divides `D`.

`Coprime idx θ ⟹ Coprime idx² θ²`, and coprime divisors multiply: `idx²·θ² ∣ D`. -/
theorem sq_dvd_of_factored_coprime
    {idx θ chi D : ℕ} (hchi : chi = idx * θ)
    (hθ : θ * θ ∣ D) (hidx : idx * idx ∣ D) (hcop : Nat.Coprime idx θ) :
    chi * chi ∣ D := by
  subst hchi
  have hsq : Nat.Coprime (idx * idx) (θ * θ) := by
    simpa [sq] using Nat.Coprime.pow 2 2 hcop
  have h : (idx * idx) * (θ * θ) ∣ D := hsq.mul_dvd_of_dvd_of_dvd hidx hθ
  calc idx * θ * (idx * θ) = (idx * idx) * (θ * θ) := by ring
    _ ∣ D := h

/-- **Peterfalvi (6.6): full square-divisibility from the additive complement.**

This is the consumer-facing form of mmd L78-80 for the prefix sum `head = ∑_{j<i}χⱼ(1)²`.
If `θ²` divides the complementary tail and the total degree sum, it divides `head`; combined with
`idx² ∣ head`, `χᵢ(1) = idx·θ`, and `Coprime idx θ`, the full square `χᵢ(1)²` divides `head`.

It packages the two arithmetic steps above so the (6.6) coherence step can pass the square
divisibility `hdvd` to `two_mul_degree_lt_sum_ratCast` directly from the character-theoretic
sum identity and coprimality data. -/
theorem sq_dvd_of_factored_coprime_add_complement
    {idx θ chi head tail total : ℕ} (hsum : head + tail = total)
    (hθtail : θ * θ ∣ tail) (hθtotal : θ * θ ∣ total)
    (hidx : idx * idx ∣ head) (hchi : chi = idx * θ)
    (hcop : Nat.Coprime idx θ) :
    chi * chi ∣ head :=
  sq_dvd_of_factored_coprime hchi
    (dvd_of_add_eq_of_dvd_dvd hsum hθtail hθtotal) hidx hcop

/-- **Peterfalvi (6.6): square-divisibility of the complementary tail sum.**

If the anchor p-power degree `θ` divides every tail p-power degree `θdeg j`, then `θ²` divides
the tail sum of the induced degrees `(idx j * θdeg j)²`.  This isolates the `Finset.dvd_sum`
part of mmd L80: once the degree sort gives the divisibility of the p-power factors, every
summand carries a factor `θ²`. -/
theorem sq_dvd_sum_sq_mul_of_dvd
    {ι : Type*} (s : Finset ι) {θ : ℕ} {idx θdeg : ι → ℕ}
    (hθ : ∀ j ∈ s, θ ∣ θdeg j) :
    θ * θ ∣ ∑ j ∈ s, (idx j * θdeg j) * (idx j * θdeg j) := by
  apply Finset.dvd_sum
  intro j hj
  obtain ⟨a, ha⟩ := hθ j hj
  refine ⟨(idx j * a) * (idx j * a), ?_⟩
  rw [ha]
  ring

/-- **Peterfalvi (6.6): divisibility of p-power degrees from monotonicity (ℕ).**

If two p-power degree factors use the same base `p ≥ 2`, then the weak degree order
`θ ≤ θ'` implies `θ ∣ θ'`.  This is the arithmetic core behind the tail assertion
`θᵢ(1) ∣ θⱼ(1)` after the (6.6) degree sort. -/
theorem dvd_primePow_of_le
    {p θ θ' m n : ℕ} (hp : 2 ≤ p)
    (hθ : θ = p ^ m) (hθ' : θ' = p ^ n) (hle : θ ≤ θ') :
    θ ∣ θ' := by
  rw [hθ, hθ'] at hle ⊢
  have hexp : m ≤ n :=
    (Nat.pow_le_pow_iff_right (show 1 < p by omega)).mp hle
  exact Nat.pow_dvd_pow p hexp

/-- **Peterfalvi (6.6): cancelling the common induction index in p-power degrees (ℕ).**

The (6.6) sort compares induced degrees `idx·θ`.  Since `idx = |L:K|` is positive and fixed,
`idx·θ ≤ idx·θ'` reduces to `θ ≤ θ'`, and p-power comparison gives `θ ∣ θ'`. -/
theorem dvd_primePow_of_mul_le_mul
    {p idx θ θ' m n : ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hθ : θ = p ^ m) (hθ' : θ' = p ^ n) (hle : idx * θ ≤ idx * θ') :
    θ ∣ θ' :=
  dvd_primePow_of_le hp hθ hθ' (Nat.le_of_mul_le_mul_left hle hidx)

/-- **Peterfalvi (6.6): tail square-divisibility from sorted p-power degrees (ℕ).**

A consumer-facing form of the tail step: if every tail degree factor `θdeg j` is a p-power
and the sorted induced degrees satisfy `idx·θ ≤ idx·θdeg j`, then `θ²` divides the tail sum
`∑ (idx·θdeg j)²`. -/
theorem sq_dvd_sum_sq_mul_const_of_primePow_mul_le
    {ι : Type*} (s : Finset ι) {p idx θ : ℕ} {θdeg : ι → ℕ}
    {m : ℕ} {n : ι → ℕ} (hp : 2 ≤ p) (hidx : 0 < idx)
    (hθ : θ = p ^ m) (hθdeg : ∀ j ∈ s, θdeg j = p ^ n j)
    (hle : ∀ j ∈ s, idx * θ ≤ idx * θdeg j) :
    θ * θ ∣ ∑ j ∈ s, (idx * θdeg j) * (idx * θdeg j) := by
  exact sq_dvd_sum_sq_mul_of_dvd s (θ := θ) (idx := fun _ ↦ idx) (θdeg := θdeg)
    (fun j hj ↦ dvd_primePow_of_mul_le_mul hp hidx hθ (hθdeg j hj) (hle j hj))

/-- **Peterfalvi (6.6): p-power square divisibility from a square bound (ℕ).**

If `θ` and `q` are powers of the same base `p ≥ 2`, then `θ² ≤ q` forces
`θ² ∣ q`.  In the (6.6) tail/total divisibility chain, this turns the Schur-center
bound `θᵢ(1)² ≤ |K:Z|` into the p-power divisibility input needed for the total sum. -/
theorem sq_dvd_primePow_of_sq_le
    {p θ q m n : ℕ} (hp : 2 ≤ p)
    (hθ : θ = p ^ m) (hq : q = p ^ n) (hle : θ * θ ≤ q) :
    θ * θ ∣ q := by
  rw [hθ, hq] at hle ⊢
  have hpow : p ^ (m + m) ≤ p ^ n := by
    simpa [pow_add] using hle
  have hexp : m + m ≤ n :=
    (Nat.pow_le_pow_iff_right (show 1 < p by omega)).mp hpow
  simpa [pow_add] using Nat.pow_dvd_pow p hexp

/-- **Peterfalvi (6.6): p-power square divisibility through a multiplicative factor (ℕ).**

A factored version of `sq_dvd_primePow_of_sq_le`: once `θ²` divides the p-power factor `q`,
it divides any product `q * c`. -/
theorem sq_dvd_primePow_mul_of_sq_le
    {p θ q c m n : ℕ} (hp : 2 ≤ p)
    (hθ : θ = p ^ m) (hq : q = p ^ n) (hle : θ * θ ≤ q) :
    θ * θ ∣ q * c :=
  dvd_mul_of_dvd_left (sq_dvd_primePow_of_sq_le hp hθ hq hle) c

/-- **Peterfalvi (6.6): head square-divisibility from tail and total p-power data (ℕ).**

This packages the full mmd L78-80 arithmetic chain.  The complementary tail divisibility is derived
from the sorted p-power degrees, the total divisibility from the p-power square bound, and the
additive identity then moves the `θ²` divisor to the head.  Finally the coprime fixed-index factor
upgrades `θ² ∣ head` and `idx² ∣ head` to `(idx·θ)² ∣ head`. -/
theorem sq_dvd_head_of_commonIndex_primePower_sums
    {ι : Type*} (tailSet : Finset ι)
    {p idx θ chi q c head total : ℕ} {θdeg : ι → ℕ}
    {m n : ℕ} {ntail : ι → ℕ} (hp : 2 ≤ p) (hidxpos : 0 < idx)
    (hθ : θ = p ^ m) (hθdeg : ∀ j ∈ tailSet, θdeg j = p ^ ntail j)
    (htail_le : ∀ j ∈ tailSet, idx * θ ≤ idx * θdeg j)
    (hsum : head + (∑ j ∈ tailSet, (idx * θdeg j) * (idx * θdeg j)) = total)
    (hq : q = p ^ n) (hθsq_le_q : θ * θ ≤ q) (htotal : total = q * c)
    (hidx_head : idx * idx ∣ head) (hchi : chi = idx * θ) (hcop : Nat.Coprime idx θ) :
    chi * chi ∣ head := by
  have hθtail : θ * θ ∣ ∑ j ∈ tailSet, (idx * θdeg j) * (idx * θdeg j) :=
    sq_dvd_sum_sq_mul_const_of_primePow_mul_le tailSet hp hidxpos hθ hθdeg htail_le
  have hθtotal : θ * θ ∣ total := by
    rw [htotal]
    exact sq_dvd_primePow_mul_of_sq_le hp hθ hq hθsq_le_q
  exact sq_dvd_of_factored_coprime_add_complement
    hsum hθtail hθtotal hidx_head hchi hcop

end OddOrder.Peterfalvi.S07


