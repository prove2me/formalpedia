-- Prove2me | Definitions.Def_Disjunctive_SimplexTableau_Tableau
-- name    : Disjunctive_SimplexTableau_Tableau
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T16:50:10.06397+00:00
-- url     : https://prove2.me/theorems/d1eae718-7e01-4fc5-a3ce-332b680e4c99
-- title:
--   Â, the surplus of an arbitrary row, and the general tableau coefficients
-- statement:
--   This definition restates `08-cut-correspondence`'s basis apparatus (`Ahat`, `Bhat`,
--   `Abar0`, `Abar`) and adds this chapter's generalization to an *arbitrary* row of `Ã`, needed
--   because Lemma 9.1/Theorem 9.2 concern the tableau row of every basic variable, not just the
--   disjunction row `k`.
--
--   `SurplusM Atil btil i x := (Ãx)_i - b̃_i` is the slack value at an arbitrary row `i : M` — the
--   general form of `08-cut-correspondence`'s `Surplus`, which only covered rows enumerated by a
--   chosen `ι`. `AbarRow`/`Abar0Row` are `ā_ij := -(Ã_iÂ⁻¹)_j` and `ā_i0 := Ã_iÂ⁻¹b̂-b̃_i` (eq.
--   (9.4)-(9.5)), the tableau coefficients of an arbitrary row `i`, generalizing `Abar`/`Abar0` (which
--   only apply to the disjunction row `k` itself).
--
--   **Formalization Note.** Restated locally per the series convention; the book's own `S`/`N`
--   partition of the augmented row space (surplus vs. structural variables) is not introduced as
--   separate structure, since no theorem in this chunk's own displayed formulas needs it beyond what
--   `SurplusM`'s uniform, row-general treatment already provides (see `MODERATION_NOTES.md`).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 107-109, Section 9-9.1

import Mathlib

namespace Disjunctive.SimplexTableau

/-- `Â`, the `n×n` submatrix of `Ã` whose rows are `ι 0, …, ι (n-1)` (restated locally from
`08-cut-correspondence`): an explicit enumeration `ι : Fin n → M` of the row index set `J`. -/
def Ahat {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (ι : Fin n → M) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Atil (ι i) j

/-- `b̂`, the subvector of `b̃` corresponding to `Â` (restated locally). -/
def Bhat {n : ℕ} {M : Type*} (btil : M → ℝ) (ι : Fin n → M) : Fin n → ℝ :=
  fun i => btil (ι i)

/-- `ā_k0 := e_k Â⁻¹ b̂` (restated locally). -/
noncomputable def Abar0 {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (k : Fin n) : ℝ :=
  (Ahat Atil ι)⁻¹.mulVec (Bhat btil ι) k

/-- `ā_kj := -(Â⁻¹)_{kj}`, indexed by row-position `j` (restated locally). -/
noncomputable def Abar {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (k j : Fin n) : ℝ :=
  -((Ahat Atil ι)⁻¹) k j

/-- The surplus (slack) value `s_i := (Ãx)_i - b̃_i` at an *arbitrary* row `i : M` of `Ã`, a
genuine affine function of `x` for every row, bound or original (Balas §9, p. 107-108, eq.
(9.1)-(9.2), which identify the nonbasic structural variables `x_{N∩J}` with the corresponding
surplus `s_J`). -/
def SurplusM {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (i : M)
    (x : Fin n → ℝ) : ℝ :=
  dotProduct (Atil i) x - btil i

/-- `ā_ij := -(Ã_i Â⁻¹)_j`, the simplex tableau coefficient for nonbasic column `j` (row-position,
via `ι`) in the row of an *arbitrary* basic row/variable `i : M` (Balas §9.1, eq. (9.4), p. 108).
Generalizes `Abar` (which only covers rows enumerated by `ι` itself) to every row of `Ã`. -/
noncomputable def AbarRow {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (ι : Fin n → M) (i : M) (j : Fin n) : ℝ :=
  -(∑ l, Atil i l * ((Ahat Atil ι)⁻¹) l j)

/-- `ā_i0 := Ã_i Â⁻¹ b̂ - b̃_i`, the simplex tableau right-hand side for an arbitrary row `i : M`
(Balas §9.1, eq. (9.5), p. 108). Generalizes `Abar0` to every row of `Ã`. -/
noncomputable def Abar0Row {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (ι : Fin n → M) (i : M) : ℝ :=
  dotProduct (Atil i) ((Ahat Atil ι)⁻¹.mulVec (Bhat btil ι)) - btil i

end Disjunctive.SimplexTableau


