-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBOrth
-- name    : RPLib_S4_AlgGrpBOrth
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:42:25.269729+00:00
-- url     : https://prove2.me/theorems/957591c3-7f2c-42fa-b0d9-3ff8579ec39a
-- title:
--   Larsen's alternative library: `Lie` of a subset of `O(B)` / `Sp(B)`, O5a)
-- statement:
--   For a matrix `B` (symmetric: `O(B)`; alternating: `Sp(B)`), `isoSet B = {g | gᵀ B g = B}`.
--   If `Z ⊆ isoSet B` then every `X ∈ lieS Z` satisfies `Xᵀ B + B X = 0` (`lie_iso`): the polynomials
--   `(xᵀ B x - B)_{ij}` vanish on `Z`, and at the `K[ε]`-point `1 + ε X` they equal `ε (Xᵀ B + B X)_{ij}`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSL

/-!
# S4-AlgGrpB, file Orth: `Lie` of a subset of `O(B)` / `Sp(B)` (spike API (A2), O5a)

For a matrix `B` (symmetric: `O(B)`; alternating: `Sp(B)`), `isoSet B = {g | gᵀ B g = B}`.
If `Z ⊆ isoSet B` then every `X ∈ lieS Z` satisfies `Xᵀ B + B X = 0` (`lie_iso`): the polynomials
`(xᵀ B x - B)_{ij}` vanish on `Z`, and at the `K[ε]`-point `1 + ε X` they equal `ε (Xᵀ B + B X)_{ij}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial
open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- `{g | gᵀ B g = B}`: `O(B)` for symmetric `B`, `Sp(B)` for alternating `B`. -/
def isoSet (B : Matrix n n K) : Set (Matrix.GeneralLinearGroup n K) :=
  {g | (g : Matrix n n K)ᵀ * B * g = B}

theorem mem_isoSet {B : Matrix n n K} {g : Matrix.GeneralLinearGroup n K} :
    g ∈ isoSet B ↔ (g : Matrix n n K)ᵀ * B * g = B := Iff.rfl

/-- The polynomial matrix `xᵀ B x - B` in the coordinates. -/
def isoPoly (B : Matrix n n K) : Matrix n n (MvPolynomial (Var n) K) :=
  (mX (n := n) (K := K))ᵀ * B.map C * mX - B.map C

theorem eval_isoPoly (B : Matrix n n K) (g : Matrix.GeneralLinearGroup n K) (i j : n) :
    eval (crd g) (isoPoly B i j) = ((g : Matrix n n K)ᵀ * B * g - B) i j := by
  simp [isoPoly, mX, Matrix.mul_apply, map_sum]

theorem iso_dual_expand {R : Type*} [CommRing R] (e : R) (hee : e * e = 0) (X' B' : Matrix n n R) :
    (1 + e • X')ᵀ * B' * (1 + e • X') - B' = e • (X'ᵀ * B' + B' * X') := by
  simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, add_mul, mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hee, zero_smul,
    add_zero, smul_add]
  abel

theorem snd_aeval_ptD_isoPoly (B X : Matrix n n K) (i j : n) :
    TrivSqZeroExt.snd (aeval (ptD X) (isoPoly B i j)) = (Xᵀ * B + B * X) i j := by
  have hM : (aeval (ptD X)).mapMatrix (mX (n := n) (K := K)) =
      1 + (DualNumber.eps : DualNumber K) • X.map (TrivSqZeroExt.inl (M := K)) := by
    rw [← ptD_mat]
    refine Matrix.ext fun i j => ?_
    simp [mX]
  have hB : (aeval (ptD X)).mapMatrix (B.map C) = B.map (TrivSqZeroExt.inl (M := K)) := by
    refine Matrix.ext fun k l => ?_
    simp [AlgHom.mapMatrix_apply, TrivSqZeroExt.algebraMap_eq_inl]
  have h : aeval (ptD X) (isoPoly B i j) = ((aeval (ptD X)).mapMatrix (isoPoly B)) i j := rfl
  rw [h, isoPoly, map_sub, map_mul, map_mul, AlgHom.mapMatrix_apply (M := (mX (n := n) (K := K))ᵀ),
    Matrix.transpose_map, ← AlgHom.mapMatrix_apply, hM, hB,
    iso_dual_expand _ DualNumber.eps_mul_eps, Matrix.smul_apply,
    smul_eq_mul, DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, one_mul,
    zero_add]
  simp [Matrix.mul_apply, Matrix.add_apply, TrivSqZeroExt.fst_sum]

/-- `(A2)` for `O(B)` / `Sp(B)`: if `Z ⊆ {g | gᵀ B g = B}` then `Xᵀ B + B X = 0` on `Lie Z`. -/
theorem lie_iso {B : Matrix n n K} {Z : Set (Matrix.GeneralLinearGroup n K)} (hZ : Z ⊆ isoSet B)
    {X : Matrix n n K} (hX : X ∈ lieS Z) : Xᵀ * B + B * X = 0 := by
  ext i j
  have hf : isoPoly B i j ∈ vanI Z :=
    mem_vanI.2 fun g hg => by rw [eval_isoPoly, (mem_isoSet.1 (hZ hg)), sub_self, Matrix.zero_apply]
  have := hX _ hf
  rw [← snd_aeval_ptD, snd_aeval_ptD_isoPoly] at this
  rw [this, Matrix.zero_apply]

end RamanujanPetersson.AlgGrpB

end


