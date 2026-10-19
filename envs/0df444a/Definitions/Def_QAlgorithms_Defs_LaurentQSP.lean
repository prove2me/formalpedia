-- Prove2me | Definitions.Def_QAlgorithms_Defs_LaurentQSP
-- name    : QAlgorithms_Defs_LaurentQSP
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:01:37.808757+00:00
-- url     : https://prove2.me/theorems/4ac5f92c-ee30-43e4-a315-6eb89eced800
-- title:
--   Laurent polynomials with `2 × 2` matrix coefficients, the classes `P_n`, `E_n`, primitive
-- statement:
--   # Laurent polynomials with `2 × 2` matrix coefficients, the classes `P_n`, `E_n`, primitive
--   matrices (shared definition layer)
--
--   J. Haah, *Product decomposition of periodic functions in quantum signal processing*
--   (arXiv:1806.10236v4), cited "Haah p.N" (PDF pages), §§2–3.
--
--   A Laurent polynomial `F(t) = Σ_j C_j t^j` with coefficients in `Mat(2; ℂ)` is Mathlib's
--   `LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)`; its coefficient `C_j` is `F.coeff j`. Products
--   `E_{P₁}(t) ⋯ E_{Pₙ}(t)` are written left to right as `(List.ofFn fun i => primitiveMatrix (P i)).prod`.
--   -/
--
--   namespace QAlgorithms
--
--   /-- Haah p.4 (Definition 1; p.3 "on the entire complex plane except the origin"): the evaluation
--   `F(η) = Σ_j C_j η^j` (integer powers), used at `|η| = 1`. Written by hand because Mathlib's
--   `LaurentPolynomial.eval₂` needs a commutative target.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\LaurentQSP.lean

import Definitions.Def_QAlgorithms_Defs_SpectralFilter
/-!
# Laurent polynomials with `2 × 2` matrix coefficients, the classes `P_n`, `E_n`, primitive
matrices (shared definition layer)

J. Haah, *Product decomposition of periodic functions in quantum signal processing*
(arXiv:1806.10236v4), cited "Haah p.N" (PDF pages), §§2–3.

A Laurent polynomial `F(t) = Σ_j C_j t^j` with coefficients in `Mat(2; ℂ)` is Mathlib's
`LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)`; its coefficient `C_j` is `F.coeff j`. Products
`E_{P₁}(t) ⋯ E_{Pₙ}(t)` are written left to right as `(List.ofFn fun i => primitiveMatrix (P i)).prod`.
-/

namespace QAlgorithms

/-- Haah p.4 (Definition 1; p.3 "on the entire complex plane except the origin"): the evaluation
`F(η) = Σ_j C_j η^j` (integer powers), used at `|η| = 1`. Written by hand because Mathlib's
`LaurentPolynomial.eval₂` needs a commutative target. -/
noncomputable def laurentMatEval (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)) (η : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  F.coeff.sum fun j C => (η ^ j) • C

/-- Haah p.4, Definition 1, Eq. (4): the class `P_n` of Laurent polynomials
`F(t) = Σ_{j=−n}^{n} C_j t^j` with `F(η) ∈ SU(2)` for every `η ∈ ℂ` of unit modulus. -/
def IsQSPClassP (n : ℕ) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)) : Prop :=
  (∀ j : ℤ, (n : ℤ) < |j| → F.coeff j = 0) ∧
    ∀ η : ℂ, ‖η‖ = 1 → laurentMatEval F η ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- Haah p.4, Definition 1, Eq. (5): the class `E_n ⊆ P_n`, the exponents of `t` lie in
`{−n, −n + 2, …, n}` (`C_{−n+k} = 0` for odd `k`, i.e. `C_j = 0` when `j + n` is odd). -/
def IsQSPClassE (n : ℕ) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)) : Prop :=
  IsQSPClassP n F ∧ ∀ j : ℤ, Odd (j + n) → F.coeff j = 0

/-- Haah p.4 (Definition 1): `F` has degree `n` if `C_n ≠ 0` or `C_{−n} ≠ 0` (the text extraction
prints `= 0`; the proof on p.5 fixes `≠`). -/
def HasQSPDegree (n : ℕ) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)) : Prop :=
  F.coeff (n : ℤ) ≠ 0 ∨ F.coeff (-(n : ℤ)) ≠ 0

/-- Haah p.3, Eq. (2): `P` is a rank-one orthogonal projector on `ℂ²` (`P = I − Q`; rank `0` or
`2` would make `E_P = t^{∓1} I`, not `SU(2)`-valued). -/
def IsRankOneProjector (P : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  P * P = P ∧ P.IsHermitian ∧ P.rank = 1

/-- Haah p.3, Eq. (2): the primitive matrix `E_P(t) = tP + t⁻¹(I − P)`. -/
noncomputable def primitiveMatrix (P : Matrix (Fin 2) (Fin 2) ℂ) :
    LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ) :=
  LaurentPolynomial.C P * LaurentPolynomial.T 1 + LaurentPolynomial.C (1 - P) * LaurentPolynomial.T (-1)

/-! ### Sanity tests -/

example (η : ℂ) : laurentMatEval 0 η = 0 := by
  simp [laurentMatEval]

example (n : ℕ) : ¬ HasQSPDegree n 0 := by
  simp [HasQSPDegree]

example (n : ℕ) (F : LaurentPolynomial (Matrix (Fin 2) (Fin 2) ℂ)) (h : IsQSPClassE n F) :
    IsQSPClassP n F :=
  h.1

example : ¬ IsQSPClassP 0 0 := by
  rintro ⟨-, h⟩
  have h1 := h 1 (by simp)
  rw [show laurentMatEval 0 1 = 0 by simp [laurentMatEval]] at h1
  have hdet := Matrix.mem_specialUnitaryGroup_iff.1 h1
  simp at hdet

end QAlgorithms


