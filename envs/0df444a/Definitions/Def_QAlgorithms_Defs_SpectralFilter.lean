-- Prove2me | Definitions.Def_QAlgorithms_Defs_SpectralFilter
-- name    : QAlgorithms_Defs_SpectralFilter
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:59:54.238661+00:00
-- url     : https://prove2.me/theorems/eb33e316-2ba1-40e8-a5b4-fc452685c1c4
-- title:
--   Gap-separated eigenvalues, spectral projectors, the Chebyshev filter polynomial, one- and
-- statement:
--   # Gap-separated eigenvalues, spectral projectors, the Chebyshev filter polynomial, one- and
--   two-qubit gates (shared definition layer)
--
--   * L. Lin, Y. Tong, *Optimal polynomial based quantum eigenstate filtering with application to
--     solving quantum linear systems* (arXiv:1910.14596v4), cited "LT p.N" (PDF pages), §3.
--   * L. Lin, Y. Tong, *Near-optimal ground state preparation* (arXiv:2002.12508v3), cited
--     "LT-gs p.N" (PDF pages).
--   -/
--
--   namespace QAlgorithms
--
--   /-- LT §3 p.7, Theorem 3 p.8: `λ` is an eigenvalue of `H` separated from the rest of the spectrum
--   by a gap `Δ`: every eigenvalue (with multiplicity, the frozen `ascEigenvalues`) different from `λ`
--   is at distance `⩾ Δ` from `λ`. Degeneracy of `λ` is allowed (LT p.7: "the `λ`-eigenspace").
--   Used together with `H.IsHermitian` as a separate hypothesis.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SpectralFilter.lean

import Definitions.Def_QAlgorithms_Defs_TannerDecoder
/-!
# Gap-separated eigenvalues, spectral projectors, the Chebyshev filter polynomial, one- and
two-qubit gates (shared definition layer)

* L. Lin, Y. Tong, *Optimal polynomial based quantum eigenstate filtering with application to
  solving quantum linear systems* (arXiv:1910.14596v4), cited "LT p.N" (PDF pages), §3.
* L. Lin, Y. Tong, *Near-optimal ground state preparation* (arXiv:2002.12508v3), cited
  "LT-gs p.N" (PDF pages).
-/

namespace QAlgorithms

/-- LT §3 p.7, Theorem 3 p.8: `λ` is an eigenvalue of `H` separated from the rest of the spectrum
by a gap `Δ`: every eigenvalue (with multiplicity, the frozen `ascEigenvalues`) different from `λ`
is at distance `⩾ Δ` from `λ`. Degeneracy of `λ` is allowed (LT p.7: "the `λ`-eigenspace").
Used together with `H.IsHermitian` as a separate hypothesis. -/
def IsGapSeparatedEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (lam Δ : ℝ) : Prop :=
  (∃ k, ascEigenvalues H k = lam) ∧ ∀ k, ascEigenvalues H k ≠ lam → Δ ≤ |ascEigenvalues H k - lam|

/-- LT p.7: the matrix of the orthogonal projection `P_λ` onto the `λ`-eigenspace of `H` (the
frozen `eigenProjection` with `S = {λ}`; the zero matrix if `λ` is not an eigenvalue). -/
noncomputable def spectralProjector {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (lam : ℝ) : Matrix ι ι ℂ :=
  Matrix.toEuclideanLin.symm
    ((eigenProjection (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) H) {(lam : ℂ)} :
      EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)

/-- LT p.7 (the polynomial of Lemma 2):
`R_ℓ(x; Δ) = T_ℓ(−1 + 2(x² − Δ²)/(1 − Δ²)) / T_ℓ(−1 + 2(−Δ²)/(1 − Δ²))`, `T_ℓ` the Chebyshev
polynomial of the first kind, a polynomial of degree `2ℓ`. Meaningful for `0 < Δ < 1` (the
hypothesis of every statement using it), where both divisions are by non-zero numbers. -/
noncomputable def chebFilterPoly (ℓ : ℕ) (Δ : ℝ) : Polynomial ℝ :=
  Polynomial.C ((Polynomial.Chebyshev.T ℝ ℓ).eval (-1 + 2 * (-Δ ^ 2) / (1 - Δ ^ 2)))⁻¹ *
    (Polynomial.Chebyshev.T ℝ ℓ).comp
      (Polynomial.C (-1 - 2 * Δ ^ 2 / (1 - Δ ^ 2)) + Polynomial.C (2 / (1 - Δ ^ 2)) * Polynomial.X ^ 2)

/-- LT-gs p.7 (Theorem 6, "other one- and two-qubit gates"), LT p.8: the gate set of all one- and
two-qubit unitaries. -/
def oneTwoQubitGateSet : Set Gate :=
  {g | (g.arity = 1 ∨ g.arity = 2) ∧ g.IsUnitary}

/-! ### Sanity tests -/

example (Δ : ℝ) : chebFilterPoly 0 Δ = 1 := by
  simp [chebFilterPoly]

theorem chebFilterPoly_eval_zero (ℓ : ℕ) (Δ : ℝ)
    (h : (Polynomial.Chebyshev.T ℝ ℓ).eval (-1 + 2 * (-Δ ^ 2) / (1 - Δ ^ 2)) ≠ 0) :
    (chebFilterPoly ℓ Δ).eval 0 = 1 := by
  have e : (-1 - 2 * Δ ^ 2 / (1 - Δ ^ 2) : ℝ) = -1 + 2 * (-Δ ^ 2) / (1 - Δ ^ 2) := by ring
  simp only [chebFilterPoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero, add_zero, e]
  exact inv_mul_cancel₀ h

example : (⟨1, 1⟩ : Gate) ∈ oneTwoQubitGateSet :=
  ⟨Or.inl rfl, one_mem _⟩

example : (⟨3, 1⟩ : Gate) ∉ oneTwoQubitGateSet := by
  rintro ⟨h | h, -⟩ <;> simp at h

example {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (k : Fin (Fintype.card ι)) :
    IsGapSeparatedEigenvalue H (ascEigenvalues H k) 0 :=
  ⟨⟨k, rfl⟩, fun _ _ => abs_nonneg _⟩

end QAlgorithms


