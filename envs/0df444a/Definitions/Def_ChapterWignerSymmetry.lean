-- Prove2me | Definitions.Def_ChapterWignerSymmetry
-- name    : ChapterWignerSymmetry
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:07:18.464144+00:00
-- url     : https://prove2.me/theorems/95dc788b-a381-4ac9-9ec5-923f69491d39
-- title:
--   Chapter WignerSymmetry
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWignerSymmetry.lean`): generated def bundle for ChapterWignerSymmetry. See BookProof/ChapterWignerSymmetry.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWignerSymmetry.lean

import Mathlib


/-!
# Wigner's symmetry theorem (book.tex, §"Unitary representations of the Poincaré group")

`book.tex` uses Wigner's theorem repeatedly, always as an external citation:

> "According to Wigner's theorem, the most general transformations, leaving invariant the
> modulus of the internal product of a Hilbert space, are: unitary or anti-unitary
> operators, defined up to a complex phase, for a complex Hilbert space."

This file **proves** that statement for a complex inner-product space with a finite
orthonormal basis — in particular for every finite-dimensional complex Hilbert space
(`wigner_symmetry`).

## Statement

A **Wigner symmetry** is a map `T : E → E` with `‖⟪T x, T y⟫‖ = ‖⟪x, y⟫‖` for all `x, y`:
no linearity, continuity or surjectivity is assumed, only that all transition
probabilities are preserved.  The theorem produces one linear **or** one conjugate-linear
isometry `U` such that every `T x` equals `U x` up to a phase depending on `x`.

## The proof

*Part I* is the algebraic core, stated for a map `S : (ι → ℂ) → (ι → ℂ)` of coordinate
vectors that preserves the modulus of the standard inner product (`inner_norm`) and of
each coordinate (`coord_norm`), and is normalized so that the two nonzero coordinates of
`S (δ₀ + δᵢ)` agree (`normalized`; this is achieved by rephasing the image basis):

* `modulus_add` — `‖S v o + S v i‖ = ‖v o + v i‖`;
* `exists_zeta` — the vector `δ₀ + i δᵢ` produces a sign `ζᵢ = ±i`;
* `key_index` — hence for each `i`, either `conj (S v o) * S v i = conj (v o) * v i` for
  **all** `v`, or `conj (S v o) * S v i = conj (conj (v o) * v i)` for all `v`;
* `key_consistent` — the alternative is the same for all indices (otherwise the transition
  probability between `δ₀ + δᵢ + δⱼ` and `δ₀ + i δᵢ + i δⱼ` would change from `√5` to `1`);
* `coord_of_key`, `wigner_coord` — therefore `S v = lam • v` for all `v`, or
  `S v = lam • conj v` for all `v`, with `‖lam‖ = 1` depending on `v`.  The case
  `v o = 0` is settled by the equality case of the triangle inequality.

*Part II* transports this to a Hilbert space with an orthonormal basis: the images of the
basis vectors are orthonormal, hence an orthonormal basis; their phases are fixed with the
vectors `b₀ + bᵢ`; and the coordinate map of `T` in these two bases satisfies the
hypotheses of Part I.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace ComplexConjugate
open Finset

namespace BookProof.ChapterWignerSymmetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A **Wigner symmetry**: a map of the Hilbert space preserving all transition
probabilities `|⟪x, y⟫|`. -/
def IsWignerSymmetry (T : E → E) : Prop := ∀ x y : E, ‖⟪T x, T y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖

variable {T : E → E}

/-- A Wigner symmetry preserves norms. -/
theorem norm_map (hT : IsWignerSymmetry T) (x : E) : ‖T x‖ = ‖x‖ := by
  have h := hT x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  simpa using h



/-! ### Two complex-number identities behind the key relation -/







/-! ## Part I — the algebraic core in coordinates -/

section Coord

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate vector `δ_o + δ_i`. -/
def pairCoord (o i : ι) : ι → ℂ := fun k => if k = o then 1 else if k = i then 1 else 0

/-- The coordinate vector `δ_o + i·δ_i`. -/
def pairCoordI (o i : ι) : ι → ℂ := fun k => if k = o then 1 else if k = i then Complex.I else 0

/-- The coordinate vector `δ_o + z·δ_i + z·δ_j`. -/
def tripleCoord (o i j : ι) (z : ℂ) : ι → ℂ :=
  fun k => if k = o then 1 else if k = i then z else if k = j then z else 0







/-- The hypotheses of Wigner's theorem in coordinates. -/
structure WignerCoord (S : (ι → ℂ) → (ι → ℂ)) (o : ι) : Prop where
  /-- The modulus of the standard inner product is preserved. -/
  inner_norm : ∀ v w, ‖∑ k, conj (S v k) * S w k‖ = ‖∑ k, conj (v k) * w k‖
  /-- The modulus of each coordinate is preserved. -/
  coord_norm : ∀ v k, ‖S v k‖ = ‖v k‖
  /-- The image basis has been rephased so that `S (δ_o + δ_i)` has equal coordinates. -/
  normalized : ∀ i, i ≠ o → S (pairCoord o i) o = S (pairCoord o i) i

variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}





















end Coord


/-! ## Part II — transport to a Hilbert space

Part I is stated for coordinate vectors.  We now feed it with the coordinates of `T` in the
orthonormal basis `b` (source) and in the *rephased* image family `imgVec` (target). -/

section Hilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An **antiunitary operator**: additive, conjugate-homogeneous, surjective, and conjugating
the inner product.  (Norms are automatically preserved, by `inner_conj` with `y = x`.) -/
structure IsAntiunitary (U : E → E) : Prop where
  /-- Antiunitary operators are additive. -/
  map_add : ∀ x y, U (x + y) = U x + U y
  /-- Antiunitary operators are conjugate-homogeneous. -/
  map_smul : ∀ (a : ℂ) (x : E), U (a • x) = conj a • U x
  /-- Antiunitary operators conjugate the inner product. -/
  inner_conj : ∀ x y, ⟪U x, U y⟫_ℂ = conj ⟪x, y⟫_ℂ
  /-- Antiunitary operators are onto. -/
  surjective : Function.Surjective U

/-! ### Elementary computations in an orthonormal basis -/







/-! ### Rephasing the image basis -/

/-- The phase by which the image `T (b i)` has to be rotated so that the two nonzero
coordinates of `T (b o + b i)` become equal. -/
noncomputable def alignPhase (b : OrthonormalBasis ι ℂ E) (T : E → E) (o i : ι) : ℂ :=
  if i = o then 1 else ⟪T (b i), T (b o + b i)⟫_ℂ / ⟪T (b o), T (b o + b i)⟫_ℂ

/-- The rephased images of the basis vectors. -/
noncomputable def imgVec (b : OrthonormalBasis ι ℂ E) (T : E → E) (o i : ι) : E :=
  alignPhase b T o i • T (b i)

variable {b : OrthonormalBasis ι ℂ E} {o : ι}

omit [DecidableEq ι] in
theorem inner_pair_left_norm (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) :
    ‖⟪T (b o), T (b o + b i)⟫_ℂ‖ = 1 := by
  classical
  rw [hT (b o) (b o + b i), inner_add_right,
    orthonormal_iff_ite.mp b.orthonormal o o, orthonormal_iff_ite.mp b.orthonormal o i]
  simp [Ne.symm hi]

omit [DecidableEq ι] in
theorem inner_pair_right_norm (hT : IsWignerSymmetry T) {i : ι} (hi : i ≠ o) :
    ‖⟪T (b i), T (b o + b i)⟫_ℂ‖ = 1 := by
  classical
  rw [hT (b i) (b o + b i), inner_add_right,
    orthonormal_iff_ite.mp b.orthonormal i o, orthonormal_iff_ite.mp b.orthonormal i i]
  simp [hi]

theorem alignPhase_norm (hT : IsWignerSymmetry T) (i : ι) : ‖alignPhase b T o i‖ = 1 := by
  rw [alignPhase]
  split_ifs with h
  · simp
  · rw [norm_div, inner_pair_right_norm hT h, inner_pair_left_norm hT h, div_one]



/-- The rephased images of an orthonormal basis are again orthonormal. -/
theorem orthonormal_imgVec (hT : IsWignerSymmetry T) : Orthonormal ℂ (imgVec b T o) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [imgVec, imgVec, inner_smul_left, inner_smul_right]
  by_cases h : i = j
  · subst h
    have hn : ‖T (b i)‖ = 1 := by rw [norm_map hT, b.orthonormal.1 i]
    have h1 : ⟪T (b i), T (b i)⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hn]; norm_num
    have h2 : conj (alignPhase b T o i) * alignPhase b T o i = 1 := by
      rw [mul_comm, Complex.mul_conj]
      have hsq : Complex.normSq (alignPhase b T o i) = ‖alignPhase b T o i‖ ^ 2 := by
        rw [Complex.sq_norm]
      rw [hsq, alignPhase_norm hT]
      norm_num
    rw [h1, mul_one, h2]
    simp
  · have h0 : ⟪T (b i), T (b j)⟫_ℂ = 0 := by
      have := hT (b i) (b j)
      rw [orthonormal_iff_ite.mp b.orthonormal i j, if_neg h] at this
      simpa using this
    rw [h0, if_neg h]
    ring

/-- The rephased images of `b`, as an orthonormal basis. -/
noncomputable def imgBasis (b : OrthonormalBasis ι ℂ E) (T : E → E) (o : ι)
    (hT : IsWignerSymmetry T) : OrthonormalBasis ι ℂ E :=
  haveI : Nonempty ι := ⟨o⟩
  haveI : FiniteDimensional ℂ E := Module.Basis.finiteDimensional_of_finite b.toBasis
  (basisOfLinearIndependentOfCardEqFinrank
      (orthonormal_imgVec (b := b) (o := o) hT).linearIndependent
      (Module.finrank_eq_card_basis b.toBasis).symm).toOrthonormalBasis (by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact orthonormal_imgVec hT)



/-! ### The coordinate map of `T` and Wigner's theorem -/

/-- The matrix of `T` between the basis `b` and the rephased image basis. -/
noncomputable def coordMap (b : OrthonormalBasis ι ℂ E) (T : E → E)
    (G : OrthonormalBasis ι ℂ E) : (ι → ℂ) → (ι → ℂ) :=
  fun v k => ⟪G k, T (∑ j, v j • b j)⟫_ℂ







end Hilbert

end BookProof.ChapterWignerSymmetry


