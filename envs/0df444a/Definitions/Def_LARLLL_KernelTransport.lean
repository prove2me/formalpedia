-- Prove2me | Definitions.Def_LARLLL_KernelTransport
-- name    : LARLLL_KernelTransport
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:44:18.07904+00:00
-- url     : https://prove2.me/theorems/26d5778e-9256-477d-acef-9fc3fbe24891
-- title:
--   Checked native matrix transport and determinant refinement data
-- statement:
--   The exact transport between the native row-major matrix and Mathlib matrix representations, with the rational Gram-Schmidt and determinant data needed for the existing LLL refinement proofs.
-- source:
--   Apache-2.0 leanprover/hex source and the already checked native LLL adapters. Exact original module locations and SHA-256 values are recorded in the validation receipt. Whole original declaration commands were retained using the official Lean declaration/sketch and structural syntax oracles, with original notices, checked computational definitions, and csimp proof logic preserved. All retained declaration types and safe non-theorem values were compared to the original environment using kernel-checked reflexivity after expanding safe generated implementation helpers. Source SHA-256: 354242697d65b89d93afad85745c8561299a640fb1569b9d0e3ec2bd7bbe71c5.

import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_LARLLL_NativeLLLData
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Lean

section



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
open InnerProductSpace
open scoped BigOperators
abbrev QVector (dimension : ℕ) := Fin dimension → ℚ
abbrev Space (dimension : ℕ) := EuclideanSpace ℝ (Fin dimension)

def innerQ {dimension : ℕ} (left right : QVector dimension) : ℚ := ∑ index,left index*right index

def realVec {dimension : ℕ} (vector : QVector dimension) : Space dimension :=
  WithLp.toLp 2 (fun index => (vector index : ℝ))













/-- Every projection uses the original current vector and cached earlier
orthogonal vectors; the running algorithm never recomputes its recursion tree. -/
def projection {dimension : ℕ} (orthogonal current : QVector dimension) : QVector dimension :=
  (innerQ orthogonal current/innerQ orthogonal orthogonal) • orthogonal

def orthogonalStep {dimension : ℕ} (previous : List (QVector dimension)) (current : QVector dimension) : QVector dimension :=
  current-(previous.map (fun orthogonal => projection orthogonal current)).sum

/-- Materialized rational Gram--Schmidt cache. A finite input prefix is
processed exactly once; division by zero keeps malformed inputs total. -/
def cache {dimension count : ℕ} (vectors : Fin count → QVector dimension) : ℕ → List (QVector dimension)
  | 0 => []
  | steps+1 =>
      let previous := cache vectors steps
      let current := if h : steps<count then vectors ⟨steps,h⟩ else 0
      previous++[orthogonalStep previous current]



def orthogonal {dimension count : ℕ} (vectors : Fin count → QVector dimension)
    (index : Fin count) : QVector dimension :=
  (cache vectors count).getD index.val 0



noncomputable section























end

def inputVectors {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (column : Fin dimension) : QVector dimension := fun row => (basis row column : ℚ)

noncomputable section







end













noncomputable section





end
end InfoLossLAR.WorstCase.RationalGramSchmidt

end

section




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.RationalGramSchmidt
open InnerProductSpace
open scoped BigOperators

def prefixGram {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (steps : ℕ) (hsteps : steps ≤ dimension) : Matrix (Fin steps) (Fin steps) ℤ :=
  fun first second => ∑ row,basis row (Fin.castLE hsteps first)*basis row (Fin.castLE hsteps second)

noncomputable section







end





noncomputable section














end
end InfoLossLAR.WorstCase.RationalGramSchmidt

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/




namespace Hex.Matrix
end Hex.Matrix





set_option autoImplicit true



section

/-!
Identification lemmas between `Hex.Matrix` and Mathlib's `Matrix`.

This module exposes a concrete equivalence between the dense executable
`Vector`-based matrix representation used by `HexMatrix` and Mathlib's
function-based `Matrix`, together with the first row-operation correspondence
lemmas needed by downstream determinant and rank lemmas.
-/

open Matrix

namespace HexMatrixTheory

universe u

/-- The bijection between a {name}`Hex.Matrix` and the Mathlib
{name}`Matrix` with the same entries. -/
@[expose]
def matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R where
  toFun M := fun i j => M[(i, j)]
  invFun M := Hex.Matrix.ofFn fun i j => M i j
  left_inv M := by
    apply Hex.Matrix.ext_getElem
    intro i j
    exact (Hex.Matrix.getElem_ofFn (fun i j => M[(i, j)]) i j).trans
      (Hex.Matrix.getElem_pair_eq_nested M i j)
  right_inv M := by
    ext i j
    exact (Hex.Matrix.getElem_pair_eq_nested _ i j).trans
      (Hex.Matrix.getElem_ofFn (fun i j => M i j) i j)

/-- `matrixEquiv M` has entry `M[i][j]` at `(i, j)`, so a caller can rewrite
`matrixEquiv M i j` to `M[i][j]` without unfolding the equivalence. -/
@[simp, grind =]
theorem matrixEquiv_apply (M : Hex.Matrix R n m) (i : Fin n) (j : Fin m) :
    matrixEquiv M i j = M[i][j] :=
  Hex.Matrix.getElem_pair_eq_nested M i j





section RowOps

variable [Semiring R]





end RowOps

section RowAdd

variable [CommRing R]



end RowAdd

end HexMatrixTheory

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/





set_option autoImplicit true



section

/-!
The executable-`Vector` ↔ Mathlib-`Fin n → R` equivalence, the fold-to-`Finset.sum`
bridge for dot products, and the matrix-vector-product correspondence.

These are the base facts through which the row-span, rank, and nullspace bridges
(in `HexRowReduceTheory`) and the lattice bridges (in `HexLLLTheory`) move
between the two vector representations.
-/

open Matrix

namespace HexMatrixTheory

universe u

variable {R : Type u} {n m : Nat}

/-- Convert an executable `Vector` into Mathlib's function representation. -/
@[expose]
def vectorEquiv : Vector R n ≃ (Fin n → R) where
  toFun := fun v i => v[i]
  invFun := Vector.ofFn
  left_inv := by
    intro v
    ext i
    simp
  right_inv := by
    intro f
    funext i
    simp















end HexMatrixTheory

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-
Copyright (c) 2026 Slava Naprienko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Slava Naprienko

Inlined into hex-determinant-theory from
https://github.com/leanprover-community/mathlib4/pull/37716
("feat(LinearAlgebra/Matrix/Determinant): Desnanot-Jacobi identity",
authored by Slava Naprienko, commit `bbe9ab491bc1`). The proof was
copied verbatim from that commit and has since been migrated to the
`module`/`public import` system and had two `simp` sets repaired across
toolchain bumps, so it is no longer character-for-character upstream.
When mathlib4 PR #37716 merges, compare the upstream theorem's namespace,
hypotheses, index maps, and factor order before deleting this file; the PR
head currently places it in the `Matrix` namespace. Re-check the direct
consumers `desnanot_jacobi_deleteRowCol_endpoints`,
`desnanot_jacobi_matrixEquiv_reindex`, and
`desnanot_jacobi_borderedMinor_reindex`, then rebuild the downstream
`desnanot_jacobi_borderedMinor` bridge and its Bareiss and integer
Gram–Schmidt consumers before replacing this module's `public import`.
-/





set_option autoImplicit true



section

/-!
# The Desnanot-Jacobi identity

We prove the **Desnanot-Jacobi identity** (also known as the Lewis Carroll identity
or Dodgson condensation identity): for any matrix `M` over a commutative ring,
`det(M) * det(M₁ₖ¹ᵏ) = det(M₁¹) * det(Mₖᵏ) - det(M₁ᵏ) * det(Mₖ¹)`,
where subscripts and superscripts denote row and column deletion.

The proof proceeds by multiplying `M` by an auxiliary matrix built from the adjugate.

## Main results

- `desnanot_jacobi`: the Desnanot-Jacobi identity over any commutative ring.
-/

open Matrix Finset

variable {n : ℕ} {R : Type*} [CommRing R]

 lemma _root_.succ_cast_succ_ne_zero (j : Fin n) :
    (j.succ.castSucc : Fin (n + 2)) ≠ 0 := by simp

 lemma _root_.succ_cast_succ_ne_last (j : Fin n) :
    (j.succ.castSucc : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp

 lemma _root_.cast_succ_succ_ne_last (j : Fin n) :
    (j.castSucc.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by simp

@[simp]
 lemma _root_.last_ne_cast_succ_succ (j : Fin n) :
    Fin.last (n + 1) ≠ (j.castSucc.succ : Fin (n + 2)) :=
  (_root_.cast_succ_succ_ne_last j).symm

 def _root_.M11 (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)

 def _root_.Mkk (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove

 def _root_.M1k (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove

 def _root_.Mk1 (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)

 def _root_.M1k_1k (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :=
  M.submatrix (Fin.succAbove 0 ∘ Fin.succAbove (Fin.last n))
              (Fin.succAbove 0 ∘ Fin.succAbove (Fin.last n))

 def _root_.auxAdjugateM (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j =>
  if j = 0 then adjugate M i 0
  else if j = Fin.last (n + 1) then adjugate M i (Fin.last (n + 1))
  else if i = j then 1
  else 0

 def _root_.auxP (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j =>
  if j = 0 then if i = 0 then M.det else 0
  else if j = Fin.last (n + 1) then if i = Fin.last (n + 1) then M.det else 0
  else M i j

 lemma _root_.aux_adjugate_m_m11_id (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    ((_root_.auxAdjugateM M).submatrix (Fin.succAbove 0) (Fin.succAbove 0)).submatrix
      (Fin.last n).succAbove (Fin.last n).succAbove = 1 := by
  ext i j
  simp [_root_.auxAdjugateM, Fin.succ_inj, Matrix.one_apply]

 lemma _root_.aux_adjugate_m_m1n_id (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    ((_root_.auxAdjugateM M).submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).submatrix
      (Fin.last n).succAbove (Fin.succAbove 0) = 1 := by
  ext i j
  simp only [_root_.auxAdjugateM, submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last, one_apply]
  simp only [_root_.succ_cast_succ_ne_zero, _root_.succ_cast_succ_ne_last, ite_false]
  congr 1
  exact propext ⟨fun h => by simp [Fin.ext_iff] at h ⊢; omega, fun h => by subst h; rfl⟩

 lemma _root_.mul_aux_adjugate_m_eq_aux_p (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M * _root_.auxAdjugateM M = _root_.auxP M := by
  ext i j
  simp only [_root_.auxAdjugateM, _root_.auxP, mul_apply]
  rcases eq_or_ne j 0 with rfl | hj0
  · have h := congr_fun (congr_fun (mul_adjugate M) i) 0
    simpa only [smul_eq_mul, Matrix.smul_apply, one_apply, mul_boole, ite_true, mul_apply] using h
  · rcases eq_or_ne j (Fin.last (n + 1)) with rfl | hjk
    · have h := congr_fun (congr_fun (mul_adjugate M) i) (Fin.last (n + 1))
      have hlast : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := by
        simp [Fin.ext_iff, Fin.val_last]
      simpa only [smul_eq_mul, Matrix.smul_apply, one_apply, mul_boole, mul_apply,
        ite_true, if_neg hlast] using h
    · simp only [hj0, hjk, mul_ite, mul_one, mul_zero]
      rw [sum_eq_single j]
      · exact if_pos rfl
      · exact fun b _ hbj => if_neg hbj
      · exact fun hj => False.elim (hj (mem_univ j))

 lemma _root_.det_aux_p_eq (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    (_root_.auxP M).det = M.det ^ 2 * (_root_.M1k_1k M).det := by
  let Q := (_root_.auxP M).submatrix Fin.succ Fin.succ
  have h_PM :
    (_root_.auxP M).submatrix (Fin.succ ∘ Fin.castSucc) (Fin.succ ∘ Fin.castSucc) = _root_.M1k_1k M := by
    ext i j; simp [_root_.auxP, _root_.M1k_1k, submatrix_apply, Function.comp, Fin.succ_ne_zero]
  have h1 : (_root_.auxP M).det = M.det * Q.det := by
    rw [det_succ_column (_root_.auxP M) 0, sum_eq_single 0]
    · simp [_root_.auxP, Q]
    · intro i _ hi; simp [_root_.auxP, hi]
    · simp
  have h2 : Q.det = M.det * (_root_.M1k_1k M).det := by
    rw [det_succ_column Q (Fin.last n), sum_eq_single (Fin.last n)]
    · simp [Q, h_PM, _root_.auxP]
    · intro b _ hb; simp [Q, _root_.auxP, hb]
    · simp
  rw [h1, h2, pow_two, mul_assoc]

 lemma _root_.det_aux_adjugate_m_eq (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    (_root_.auxAdjugateM M).det = (_root_.M11 M).det * (_root_.Mkk M).det - (_root_.M1k M).det * (_root_.Mk1 M).det := by
  let f0 := (0 : Fin (n + 2)).succAbove
  let fn := (Fin.last (n + 1)).succAbove
  let M'11 := (_root_.auxAdjugateM M).submatrix f0 f0
  let M'1n := (_root_.auxAdjugateM M).submatrix f0 fn
  have h_M'_expand : (_root_.auxAdjugateM M).det =
      _root_.auxAdjugateM M 0 0 * M'11.det + (-1 : R) ^ (n + 1) *
      _root_.auxAdjugateM M 0 (Fin.last (n + 1)) * M'1n.det := by
    rw [Matrix.det_succ_row (_root_.auxAdjugateM M) 0, Fin.sum_univ_succ,
      Finset.sum_eq_single (Fin.last n)]
    · simp [M'11, M'1n, f0, fn]
    · intro b _ hb
      have h1 : (b.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero b
      have h2 : (b.succ : Fin (n + 2)) ≠ Fin.last (n + 1) := by
        intro h; apply hb; exact Fin.succ_inj.mp (by rw [h, ← Fin.succ_last])
      simp [_root_.auxAdjugateM, h1, h1.symm, h2]
    · simp
  rw [h_M'_expand]
  have h_M'00 : _root_.auxAdjugateM M 0 0 = (_root_.M11 M).det := by
    change adjugate M 0 0 = (_root_.M11 M).det; rw [adjugate_fin_succ_eq_det_submatrix]; simp [_root_.M11]
  have h_M'0n : _root_.auxAdjugateM M 0 (Fin.last (n + 1)) = (-1) ^ (n + 1) * (_root_.Mk1 M).det := by
    simp [_root_.auxAdjugateM, adjugate_fin_succ_eq_det_submatrix, _root_.Mk1]
  have h_M'11_det : M'11.det = (_root_.Mkk M).det := by
    rw [det_succ_column M'11 (Fin.last n), sum_eq_single (Fin.last n)]
    · have h_entry : M'11 (Fin.last n) (Fin.last n) = (_root_.Mkk M).det := by
        simp [M'11, _root_.auxAdjugateM, f0, submatrix_apply,
            Fin.succAbove_zero, Fin.succ_last, adjugate_fin_succ_eq_det_submatrix, _root_.Mkk]
      rw [h_entry, _root_.aux_adjugate_m_m11_id, det_one, mul_one]
      simp only [Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    · intro b _ hb
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hb)
      suffices hdet : (M'11.submatrix b.succAbove (Fin.last n).succAbove).det = 0 by rw [hdet]; ring
      exact det_eq_zero_of_row_eq_zero r fun j => by
        simp [submatrix_apply, M'11, _root_.auxAdjugateM, f0, Fin.succAbove_zero, hr]
    · simp
  have h_M'1n : M'1n.det = -(_root_.M1k M).det := by
    rw [det_succ_column M'1n 0, sum_eq_single (Fin.last n)]
    · have h_entry : M'1n (Fin.last n) 0 = adjugate M (Fin.last (n + 1)) 0 := by
        simp [M'1n, _root_.auxAdjugateM, f0, fn, submatrix_apply,
            Fin.succAbove_zero, Fin.succAbove_last, Fin.succ_last]
      rw [h_entry, adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_zero, zero_add, Fin.val_last, _root_.M1k]
      have hp : n + 0 + (n + 1) = 2 * n + 1 := by omega
      rw [_root_.aux_adjugate_m_m1n_id, det_one, mul_one, ← mul_assoc,
      ← pow_add, hp, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
    · intro b _ hb
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq (Ne.symm hb)
      suffices hdet : (M'1n.submatrix b.succAbove (Fin.succAbove 0)).det = 0 by rw [hdet]; ring
      exact det_eq_zero_of_row_eq_zero r fun j => by
        simp [submatrix_apply, M'1n, _root_.auxAdjugateM,
            f0, fn, Fin.succAbove_zero, Fin.succAbove_last, Fin.succ_last, hr]
    · simp
  rw [h_M'00, h_M'11_det, h_M'0n, h_M'1n,
    mul_neg, ← mul_assoc, ← mul_pow, neg_mul_neg, one_mul, one_pow]
  ring

 theorem _root_.det_desnanot_jacobi_mul
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.det * (_root_.M1k_1k M).det) =
    M.det * ((_root_.M11 M).det * (_root_.Mkk M).det - (_root_.M1k M).det * (_root_.Mk1 M).det) := by
  have h_det_prod : M.det * (_root_.auxAdjugateM M).det = (_root_.auxP M).det := by
    rw [← det_mul, _root_.mul_aux_adjugate_m_eq_aux_p M]
  rw [_root_.det_aux_p_eq M, _root_.det_aux_adjugate_m_eq M] at h_det_prod
  rw [pow_two, mul_assoc] at h_det_prod
  exact h_det_prod.symm

 abbrev _root_.UnivRing (n : ℕ) := MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℤ

 noncomputable def _root_.univMatrix (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) (_root_.UnivRing n) :=
  fun i j => MvPolynomial.X (i, j)

 lemma _root_.univMatrix_det_ne_zero {n : ℕ} : (_root_.univMatrix n).det ≠ 0 := by
  intro h
  let f_eval : Fin (n + 2) × Fin (n + 2) → ℤ := fun p => if p.1 = p.2 then 1 else 0
  let eval_hom : _root_.UnivRing n →+* ℤ := MvPolynomial.eval f_eval
  have h1 : eval_hom (_root_.univMatrix n).det = eval_hom 0 := congrArg eval_hom h
  rw [map_zero] at h1
  have h2 : eval_hom (_root_.univMatrix n).det = (eval_hom.mapMatrix (_root_.univMatrix n)).det :=
    RingHom.map_det eval_hom (_root_.univMatrix n)
  rw [h2] at h1
  have h3 : eval_hom.mapMatrix (_root_.univMatrix n) = 1 := by
    ext i j
    change eval_hom (MvPolynomial.X (i, j)) = if i = j then 1 else 0
    simp [eval_hom, f_eval]
  rw [h3, Matrix.det_one] at h1
  exact zero_ne_one h1.symm

 theorem _root_.desnanot_jacobi_domain {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) (hM : M.det ≠ 0) :
    M.det * (_root_.M1k_1k M).det = (_root_.M11 M).det * (_root_.Mkk M).det - (_root_.M1k M).det * (_root_.Mk1 M).det := by
  exact mul_left_cancel₀ hM (_root_.det_desnanot_jacobi_mul M)

 theorem _root_.desnanot_jacobi_univ (n : ℕ) :
    (_root_.univMatrix n).det * (_root_.M1k_1k (_root_.univMatrix n)).det =
    (_root_.M11 (_root_.univMatrix n)).det * (_root_.Mkk (_root_.univMatrix n)).det -
    (_root_.M1k (_root_.univMatrix n)).det * (_root_.Mk1 (_root_.univMatrix n)).det :=
  _root_.desnanot_jacobi_domain (_root_.univMatrix n) _root_.univMatrix_det_ne_zero

 noncomputable def _root_.evalMap {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) : _root_.UnivRing n →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (fun p => M p.1 p.2)

/-- The **Desnanot-Jacobi identity** (Lewis Carroll identity, Dodgson condensation):
for any `(n+2) × (n+2)` matrix `M` over a commutative ring,
`det(M) · det(M_interior) = det(M₁₁) · det(Mₙₙ) - det(M₁ₙ) · det(Mₙ₁)`. -/
theorem desnanot_jacobi {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
      (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det =
    (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
      (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det -
    (M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det *
      (M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det := by
  change M.det * (_root_.M1k_1k M).det = (_root_.M11 M).det * (_root_.Mkk M).det - (_root_.M1k M).det * (_root_.Mk1 M).det
  have hu := _root_.desnanot_jacobi_univ n
  have h_eval := congrArg (_root_.evalMap M) hu
  simp only [map_sub, map_mul] at h_eval
  have h_map {p : ℕ} (f g : Fin p → Fin (n + 2)) :
      _root_.evalMap M ((_root_.univMatrix n).submatrix f g).det = (M.submatrix f g).det := by
    rw [RingHom.map_det]
    congr 1; ext i j; simp [_root_.evalMap, _root_.univMatrix]
  have h_map_M : _root_.evalMap M (_root_.univMatrix n).det = M.det := by
    rw [RingHom.map_det]
    congr 1; ext i j; simp [_root_.evalMap, _root_.univMatrix]
  simp only [_root_.M11, _root_.Mkk, _root_.M1k, _root_.Mk1, _root_.M1k_1k] at h_eval ⊢
  simp only [h_map_M, h_map] at h_eval
  exact h_eval

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/











set_option autoImplicit true



section

/-!
Core determinant correspondence between executable `Hex.Matrix` and Mathlib.

This module proves the central bridge lemma `det_eq`: the executable
Leibniz determinant `Hex.Matrix.det` equals `Matrix.det` of the corresponding
Mathlib matrix `matrixEquiv M`.  It first matches Hex permutation vectors to
Mathlib `Equiv.Perm` (`PermutationVector.toPerm`, `equivs`) and the
inversion-count sign to `Equiv.Perm.sign` (`detSign_eq_permSign`).  Building on
`det_eq`, it translates `matrixEquiv` of leading prefixes, bordered minors,
deleted rows/columns, and row updates, and ports the Desnanot-Jacobi and
adjugate row-replacement identities (`desnanot_jacobi_deleteRowCol_endpoints`,
`det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub`) into the Hex API,
plus the ordered `nMatrix`/`skipIndex2` row-transport helpers used downstream.
-/

namespace HexMatrixTheory
universe u v
variable {R : Type u} {n : Nat}

namespace PermutationVector

theorem get_injective_of_nodup
    {perm : Vector (Fin n) n} (hnodup : perm.toList.Nodup) :
    Function.Injective fun i : Fin n => perm[i] := by
  intro i j hij
  have hi : i.val < perm.toList.length := by
    simp [Vector.length_toList]
  have hj : j.val < perm.toList.length := by
    simp [Vector.length_toList]
  have hget :
      perm.toList[i.val]'hi = perm.toList[j.val]'hj := by
    simpa [Vector.getElem_toList] using hij
  exact Fin.ext ((hnodup.getElem_inj_iff).mp hget)

/-- Convert a Hex permutation vector into the corresponding Mathlib permutation. -/
@[expose]
noncomputable def toPerm (perm : Vector (Fin n) n)
    (hnodup : perm.toList.Nodup) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => perm[i])
    ⟨get_injective_of_nodup hnodup,
      Finite.surjective_of_injective (get_injective_of_nodup hnodup)⟩

@[simp, grind =]
theorem toPerm_apply (perm : Vector (Fin n) n)
    (hnodup : perm.toList.Nodup) (i : Fin n) :
    toPerm perm hnodup i = perm[i] := by
  rfl

theorem toPerm_injective :
    Function.Injective
      (fun p : {perm : Vector (Fin n) n // perm.toList.Nodup} =>
        toPerm p.1 p.2) := by
  intro p q hpq
  apply Subtype.ext
  apply Vector.ext
  intro i hi
  exact congrFun (congrArg Equiv.toFun hpq) ⟨i, hi⟩

 theorem _root_.HexMatrixTheory.PermutationVector.vectorOfPerm_toList (σ : Equiv.Perm (Fin n)) :
    (Vector.ofFn fun i : Fin n => σ i).toList =
      (List.finRange n).map fun i : Fin n => σ i := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro i hi₁ hi₂
    simp [Vector.getElem_toList]

theorem vectorOfPerm_nodup (σ : Equiv.Perm (Fin n)) :
    (Vector.ofFn fun i : Fin n => σ i).toList.Nodup := by
  rw [_root_.HexMatrixTheory.PermutationVector.vectorOfPerm_toList]
  exact List.Nodup.map σ.injective (List.nodup_finRange n)

theorem toPerm_vectorOfPerm (σ : Equiv.Perm (Fin n)) :
    toPerm (Vector.ofFn fun i : Fin n => σ i) (vectorOfPerm_nodup σ) = σ := by
  ext i
  simp [toPerm]

/-- Hex permutation vectors converted to Mathlib permutations, with proofs attached. -/
@[expose]
noncomputable def equivs (n : Nat) : List (Equiv.Perm (Fin n)) :=
  (Hex.Matrix.permutationVectors n).attach.map fun perm =>
    toPerm perm.1 (Hex.Matrix.permutationVectors_nodup perm.2)

theorem equivs_complete (σ : Equiv.Perm (Fin n)) :
    σ ∈ equivs n := by
  let perm : Vector (Fin n) n := Vector.ofFn fun i : Fin n => σ i
  have hnodup : perm.toList.Nodup := vectorOfPerm_nodup σ
  have hmem : perm ∈ Hex.Matrix.permutationVectors n :=
    Hex.Matrix.permutationVectors_complete hnodup
  rw [equivs, List.mem_map]
  refine ⟨⟨perm, hmem⟩, List.mem_attach _ _, ?_⟩
  exact toPerm_vectorOfPerm σ

theorem equivs_nodup (n : Nat) :
    (equivs n).Nodup := by
  unfold equivs
  refine List.Nodup.map ?_ (List.Nodup.attach Hex.Matrix.permutationVectors_nodup_list)
  intro p q hpq
  apply Subtype.ext
  have hpq' :
      (⟨p.1, Hex.Matrix.permutationVectors_nodup p.2⟩ :
        {perm : Vector (Fin n) n // perm.toList.Nodup}) =
        ⟨q.1, Hex.Matrix.permutationVectors_nodup q.2⟩ := by
    exact toPerm_injective hpq
  exact congrArg (fun x : {perm : Vector (Fin n) n // perm.toList.Nodup} => x.1) hpq'

 theorem _root_.HexMatrixTheory.PermutationVector.vectorOfPerm_swap_mul (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (Vector.ofFn fun r : Fin n => (Equiv.swap i j * σ) r) =
      Hex.Matrix.swapPermutationValues (Vector.ofFn fun r : Fin n => σ r) i j := by
  apply Vector.ext
  intro r hr
  show (Vector.ofFn fun r : Fin n => (Equiv.swap i j * σ) r)[(⟨r, hr⟩ : Fin n)] =
    (Hex.Matrix.swapPermutationValues (Vector.ofFn fun r : Fin n => σ r) i j)[(⟨r, hr⟩ : Fin n)]
  rw [Hex.Matrix.swapPermutationValues_get_if]
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_def]

/-- Hex's inversion-count determinant sign agrees with Mathlib's permutation sign. -/
theorem detSign_vectorOfPerm_eq_permSign [CommRing R] (σ : Equiv.Perm (Fin n)) :
    Hex.Matrix.detSign (R := R) (Vector.ofFn fun i : Fin n => σ i) =
      ((Equiv.Perm.sign σ : Int) : R) := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
      simp [Hex.Matrix.detSign_identity]
  | swap_mul σ i j hne ih =>
      rw [_root_.HexMatrixTheory.PermutationVector.vectorOfPerm_swap_mul σ i j]
      have hflip := Hex.Matrix.detSign_swapPermutationValues (R := R)
        (perm := (Vector.ofFn fun r : Fin n => σ r)) (i := i) (j := j)
        (hnodup := vectorOfPerm_nodup σ) hne
      have hswapped :
          Hex.Matrix.detSign (R := R)
              (Hex.Matrix.swapPermutationValues (Vector.ofFn fun r : Fin n => σ r) i j) =
            -Hex.Matrix.detSign (R := R) (Vector.ofFn fun r : Fin n => σ r) := by
        rw [hflip]
        simp
      rw [hswapped, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, ih]
      norm_num

/-- Hex's inversion-count determinant sign agrees with Mathlib's permutation sign. -/
theorem detSign_eq_permSign [CommRing R]
    (perm : Vector (Fin n) n) (hnodup : perm.toList.Nodup) :
    Hex.Matrix.detSign (R := R) perm =
      ((Equiv.Perm.sign (toPerm perm hnodup) : Int) : R) := by
  have hperm :
      (Vector.ofFn fun i : Fin n => toPerm perm hnodup i) = perm := by
    apply Vector.ext
    intro i hi
    simp [toPerm]
  calc
    Hex.Matrix.detSign (R := R) perm =
        Hex.Matrix.detSign (R := R) (Vector.ofFn fun i : Fin n => toPerm perm hnodup i) := by
          rw [hperm]
    _ = ((Equiv.Perm.sign (toPerm perm hnodup) : Int) : R) := by
          exact detSign_vectorOfPerm_eq_permSign (R := R) (toPerm perm hnodup)

end PermutationVector



@[simp, grind =]
theorem detTerm_eq_matrixEquiv
    [Lean.Grind.Ring R] (M : Hex.Matrix R n n) (perm : Vector (Fin n) n) :
    Hex.Matrix.detTerm M perm =
      Hex.Matrix.detSign perm *
        (List.finRange n).foldl (fun acc i => acc * matrixEquiv M i (perm[i])) 1 := by
  rw [Hex.Matrix.detTerm, Hex.Matrix.detProduct, Fin.foldl_eq_finRange_foldl]
  rfl

 theorem _root_.HexMatrixTheory.foldl_sum_map_start {α : Type u} {S : Type v} [AddCommMonoid S]
    (xs : List α) (f : α → S) (z : S) :
    xs.foldl (fun acc x => acc + f x) z = z + (xs.map f).sum := by
  induction xs generalizing z with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (z + f x)]
      simp [add_assoc]

 theorem _root_.HexMatrixTheory.foldl_sum_map {α : Type u} {S : Type v} [AddCommMonoid S]
    (xs : List α) (f : α → S) :
    xs.foldl (fun acc x => acc + f x) 0 = (xs.map f).sum := by
  simpa using _root_.HexMatrixTheory.foldl_sum_map_start xs f (0 : S)

 theorem _root_.HexMatrixTheory.foldl_prod_map_start {α : Type u} {S : Type v} [CommMonoid S]
    (xs : List α) (f : α → S) (z : S) :
    xs.foldl (fun acc x => acc * f x) z = z * (xs.map f).prod := by
  induction xs generalizing z with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (z * f x)]
      simp [mul_assoc]

 theorem _root_.HexMatrixTheory.foldl_prod_finRange {S : Type u} [CommMonoid S] {n : Nat}
    (f : Fin n → S) :
    (List.finRange n).foldl (fun acc i => acc * f i) 1 = ∏ i, f i := by
  rw [_root_.HexMatrixTheory.foldl_prod_map_start]
  simp only [one_mul]
  rw [← List.prod_toFinset f (List.nodup_finRange n), List.toFinset_finRange]

 theorem _root_.HexMatrixTheory.prod_perm_inv [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (σ : Equiv.Perm (Fin n)) :
    (∏ i, A (σ i) i) = ∏ i, A i (σ⁻¹ i) := by
  refine Finset.prod_bij (fun i _ => σ i) ?_ ?_ ?_ ?_
  · intro i hi
    simp
  · intro i hi j hj hij
    exact σ.injective hij
  · intro j hj
    refine ⟨σ⁻¹ j, by simp, ?_⟩
    simp
  · intro i hi
    simp

 theorem _root_.HexMatrixTheory.det_apply_row [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
    A.det = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : Int) : R) * ∏ i, A i (σ i) := by
  rw [Matrix.det_apply']
  refine Finset.sum_bij (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp
  · intro σ hσ τ hτ h
    exact inv_injective h
  · intro τ hτ
    refine ⟨τ⁻¹, by simp, ?_⟩
    simp
  · intro σ hσ
    rw [Equiv.Perm.sign_inv]
    simp [_root_.HexMatrixTheory.prod_perm_inv]

 theorem _root_.HexMatrixTheory.equivs_toFinset (n : Nat) :
    (PermutationVector.equivs n).toFinset =
      (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
  ext σ
  simp [PermutationVector.equivs_complete]

/-- The executable Leibniz determinant {name}`Hex.Matrix.det` agrees with
Mathlib's {name}`Matrix.det` of the corresponding matrix
under {name}`HexMatrixTheory.matrixEquiv`. This bridge lets a fact about
{name}`Matrix.det` be discharged by running the executable
determinant, or lets the executable determinant be analyzed with Mathlib's
determinant theory. -/
theorem det_eq [CommRing R] (M : Hex.Matrix R n n) :
    Hex.Matrix.det M = Matrix.det (matrixEquiv M) := by
  let term : Equiv.Perm (Fin n) → R := fun σ =>
    ((Equiv.Perm.sign σ : Int) : R) * ∏ i, matrixEquiv M i (σ i)
  have hhex : Hex.Matrix.det M = (PermutationVector.equivs n).toFinset.sum term := by
    unfold Hex.Matrix.det
    rw [_root_.HexMatrixTheory.foldl_sum_map]
    calc
      ((Hex.Matrix.permutationVectors n).map (Hex.Matrix.detTerm M)).sum =
          ((Hex.Matrix.permutationVectors n).attach.map fun p =>
            Hex.Matrix.detTerm M p.1).sum := by
            rw [List.attach_map_val]
      _ = ((Hex.Matrix.permutationVectors n).attach.map fun p =>
            term (PermutationVector.toPerm p.1
              (Hex.Matrix.permutationVectors_nodup p.2))).sum := by
            congr 1
            apply List.map_congr_left
            intro p hp
            dsimp [term]
            rw [detTerm_eq_matrixEquiv]
            rw [PermutationVector.detSign_eq_permSign
              (hnodup := Hex.Matrix.permutationVectors_nodup p.2)]
            rw [_root_.HexMatrixTheory.foldl_prod_finRange]
            simp [PermutationVector.toPerm_apply]
      _ = ((PermutationVector.equivs n).map term).sum := by
            rw [PermutationVector.equivs, List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro p hp
            rfl
      _ = (PermutationVector.equivs n).toFinset.sum term := by
            exact (List.sum_toFinset term (PermutationVector.equivs_nodup n)).symm
  rw [hhex, _root_.HexMatrixTheory.det_apply_row, _root_.HexMatrixTheory.equivs_toFinset]









































/-! # Ordered `nMatrix` row transport helpers -/































/-! # Cyclic shift permutation for ordered four-row `B[p1]` transports

These helpers package the row permutation that moves `B[p1]` from position
`p1.val` past the intermediate rows up to position `p_t.val - 1`. Together
with `Matrix.det_permute`, they give signed `nDet` transports for the
`cofactorRowPairing M r? B[p1]` pairings used by the ordered four-row
Plucker assembly.
-/

namespace OrderedFourShift

variable {n : Nat}





























end OrderedFourShift

















end HexMatrixTheory

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end

section
/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/






set_option autoImplicit true



section

/-!
Mathlib-side Grassmann-Plucker identity for the executable `Hex.Matrix` minors.

This module assembles the three-term Plucker relation among the ordered
`nDet` minors of a tall matrix `B`.  Starting from the two-row replacement
adjugate identity, it transports the double `setRow` matrix to the signed
`nDet B p2 p3` minor via the disjoint-cycle permutation
`cycleAhead * cycleBehind`, proving `det_double_setRow_eq_pow_mul_nDet` and the
signed `ordered_four_signed_Plucker_p1_side`.  These combine into the raw
kernel `det_plucker_three_term_nDet_of_ordered_four` and, after a case split on
the position of a basis-vector row `q`, the arbitrary-row form
`det_plucker_three_term_basisVec_of_ne` (with its diagonal `q = p_t` cases).
-/

namespace HexMatrixTheory
universe u v
variable {R : Type u} {n : Nat}






/-! # Double-row replacement transport to `nDet B p2 p3`

The double `setRow` matrix `setRow (setRow M r2 B[p1]) r3 B[q]` (with
`M = nMatrix B p1 q`, `r2 = ⟨p2.val - 1, _⟩`, `r3 = ⟨p3.val - 1, _⟩`)
shares the same row content as `nMatrix B p2 p3`, just permuted: `B[p1]` is
moved up from position `p1.val` to position `p2.val - 1`, and `B[q]` is
moved down from position `q.val - 2` to position `p3.val - 1`. The
resulting permutation is the product of two disjoint cycles
`cycleAhead p1.val (p2.val - p1.val - 1)` and
`cycleBehind (p3.val - 1) (q.val - p3.val - 1)`, with combined sign
`(-1) ^ (p2.val - p1.val - 1 + (q.val - p3.val - 1))`.
-/







































/-- Reindex the `(k+2) × (k+2)` bordered minor so Desnanot-Jacobi deletes the
Bareiss pivot row/column first and the trailing row/column last.

The order is `[k, 0, 1, ..., k-1, k+1]` in the original bordered-minor
coordinates. Applying the same permutation to rows and columns preserves the
determinant and makes the Desnanot interior the previous leading pivot. -/
@[expose]
def bareissDesnanotIndex (k : Nat) : Fin (k + 2) ≃ Fin (k + 2) where
  toFun r :=
    if hzero : r.val = 0 then
      ⟨k, by omega⟩
    else if hlast : r.val = k + 1 then
      Fin.last (k + 1)
    else
      ⟨r.val - 1, by omega⟩
  invFun r :=
    if hk : r.val = k then
      0
    else if hlt : r.val < k then
      ⟨r.val + 1, by omega⟩
    else
      Fin.last (k + 1)
  left_inv r := by
    ext
    dsimp
    by_cases hzero : r.val = 0
    · simp [hzero]
    · by_cases hlast : r.val = k + 1
      · simp [hlast]
      · have hlt : r.val - 1 < k := by omega
        have hne : r.val - 1 ≠ k := by omega
        simp [hzero, hlast, hlt, hne]
        omega
  right_inv r := by
    ext
    dsimp
    by_cases hk : r.val = k
    · simp [hk]
    · by_cases hlt : r.val < k
      · have hsucc_ne_last : r.val + 1 ≠ k + 1 := by omega
        simp [hk, hlt]
      · have hlast : r.val = k + 1 := by omega
        simp [hlast]





/-- Reindexing a bordered minor by `bareissDesnanotIndex` on both axes does not
change its determinant. -/
theorem det_borderedMinor_bareissDesnanotIndex [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n)
    (i j : Fin n) :
    ((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).det =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) := by
  rw [Matrix.det_submatrix_equiv_self, ← det_eq]

/-- Desnanot-Jacobi specialized to a Bareiss bordered minor after the row/column
reindexing used by `bareissDesnanotIndex`.

This is the Mathlib determinant identity that later proofs rewrite through
`matrixEquiv_borderedMinor`/`det_borderedMinor_eq_submatrix_det` to obtain the
`hdesnanot` hypothesis for `bareissExactDiv_borderedMinor_of_mul_eq`. -/
theorem desnanot_jacobi_borderedMinor_reindex [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n)
    (i j : Fin n) :
    let M : Matrix (Fin (k + 2)) (Fin (k + 2)) R :=
      (matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)
    M.det *
        (M.submatrix (Fin.succAbove 0 ∘ (Fin.last k).succAbove)
          (Fin.succAbove 0 ∘ (Fin.last k).succAbove)).det =
      (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
        (M.submatrix (Fin.last (k + 1)).succAbove
          (Fin.last (k + 1)).succAbove).det -
      (M.submatrix (Fin.succAbove 0) (Fin.last (k + 1)).succAbove).det *
        (M.submatrix (Fin.last (k + 1)).succAbove (Fin.succAbove 0)).det := by
  intro M
  exact desnanot_jacobi M





/-- Cyclic shift on `Fin (k + 1)` mapping `0 ↦ k`, `r ↦ r - 1` for `r ≥ 1`.

This is the row/column rearrangement induced by `bareissDesnanotIndex k` on the
sub-positions selected by `(Fin.last (k + 1)).succAbove`: it carries the Bareiss
pivot row (originally position `k`) from sub-position `0` back to the trailing
sub-position `k`. The same shift compares `bareissDesnanotIndex k` columns with
the natural bordered-minor column order. Defined as the inverse of Mathlib's
`finRotate (k + 1)` so the sign is available immediately. -/
 def _root_.HexMatrixTheory.bareissCyclicShift (k : Nat) : Fin (k + 1) ≃ Fin (k + 1) :=
  (finRotate (k + 1)).symm

@[simp]
 theorem _root_.HexMatrixTheory.bareissCyclicShift_apply_zero (k : Nat) :
    _root_.HexMatrixTheory.bareissCyclicShift k 0 = (Fin.last k : Fin (k + 1)) := by
  show (finRotate (k + 1)).symm 0 = Fin.last k
  rw [Equiv.symm_apply_eq]
  exact finRotate_last.symm

 theorem _root_.HexMatrixTheory.bareissCyclicShift_apply_of_pos (k : Nat) (r : Fin (k + 1))
    (h : 0 < r.val) :
    _root_.HexMatrixTheory.bareissCyclicShift k r = (⟨r.val - 1, by omega⟩ : Fin (k + 1)) := by
  have hne : r ≠ 0 := by
    intro h_eq
    rw [h_eq] at h
    exact absurd h (Nat.lt_irrefl _)
  have : NeZero (k + 1) := ⟨Nat.succ_ne_zero _⟩
  ext
  show ((finRotate (k + 1)).symm r : ℕ) = r.val - 1
  exact coe_finRotate_symm_of_ne_zero hne



/-- The entry formula for a Bareiss-reindexed bordered minor: the position
returned by `bareissDesnanotIndex k s.succ` is either an interior source row
(when `s.val < k`) or the trailing row `i` (when `s.val = k`). -/
 theorem _root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt (k : Nat) (s : Fin (k + 1))
    (hs : s.val < k) :
    bareissDesnanotIndex k s.succ = (⟨s.val, by omega⟩ : Fin (k + 2)) := by
  show (if hzero : s.succ.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.succ.val = k + 1 then Fin.last (k + 1)
        else ⟨s.succ.val - 1, by omega⟩) = _
  have hzero : s.succ.val ≠ 0 := Nat.succ_ne_zero _
  have hne_last : s.succ.val ≠ k + 1 := by
    show s.val + 1 ≠ k + 1; omega
  rw [dif_neg hzero, dif_neg hne_last]
  ext
  show s.succ.val - 1 = s.val
  simp

 theorem _root_.HexMatrixTheory.bareissDesnanotIndex_succ_top (k : Nat) (s : Fin (k + 1))
    (hs : s.val = k) :
    bareissDesnanotIndex k s.succ = Fin.last (k + 1) := by
  show (if hzero : s.succ.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.succ.val = k + 1 then Fin.last (k + 1)
        else ⟨s.succ.val - 1, by omega⟩) = _
  have hzero : s.succ.val ≠ 0 := Nat.succ_ne_zero _
  have hlast : s.succ.val = k + 1 := by
    show s.val + 1 = k + 1; omega
  rw [dif_neg hzero, dif_pos hlast]

 theorem _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero (k : Nat) (s : Fin (k + 1))
    (hs : s.val = 0) :
    bareissDesnanotIndex k s.castSucc = (⟨k, by omega⟩ : Fin (k + 2)) := by
  show (if hzero : s.castSucc.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.castSucc.val = k + 1 then Fin.last (k + 1)
        else ⟨s.castSucc.val - 1, by omega⟩) = _
  have hzero' : s.castSucc.val = 0 := hs
  rw [dif_pos hzero']

 theorem _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos (k : Nat) (s : Fin (k + 1))
    (hs : 0 < s.val) :
    bareissDesnanotIndex k s.castSucc = (⟨s.val - 1, by omega⟩ : Fin (k + 2)) := by
  have hcv : s.castSucc.val = s.val := rfl
  show (if hzero : s.castSucc.val = 0 then (⟨k, by omega⟩ : Fin (k + 2))
        else if hlast : s.castSucc.val = k + 1 then Fin.last (k + 1)
        else ⟨s.castSucc.val - 1, by omega⟩) = _
  have hne_zero : s.castSucc.val ≠ 0 := by rw [hcv]; exact Nat.ne_of_gt hs
  have hne_last : s.castSucc.val ≠ k + 1 := by
    rw [hcv]; exact Nat.ne_of_lt (by have := s.isLt; omega)
  rw [dif_neg hne_zero, dif_neg hne_last]
  ext
  show s.castSucc.val - 1 = s.val - 1
  rw [hcv]

/-- Source-row index returned by `bareissDesnanotIndex k r.succ` from `r : Fin (k+1)`:
`r.val` for interior `r.val < k`, `i` when `r.val = k`. -/
 theorem _root_.HexMatrixTheory.source_row_of_succ
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r : Fin (k + 1)) :
    ∀ (c : Fin (k + 1)),
      matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.succ) (bareissDesnanotIndex k c.succ) =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  intro c
  have hkn : k < n := Nat.lt_of_succ_lt hnext
  by_cases hr : r.val < k <;> by_cases hc : c.val < k
  · rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k r hr, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k c hc]
    have hri : (⟨r.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show r.val < k + 1; omega
    have hci : (⟨c.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show c.val < k + 1; omega
    rw [matrixEquiv_apply]
    rw [Hex.Matrix.borderedMinor_entry_lt_lt source (k + 1) hnext i j _ _ hri hci]
    simp [hr, hc]
  · have hc_eq : c.val = k := by have := c.isLt; omega
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k r hr, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k c hc_eq]
    have hri : (⟨r.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show r.val < k + 1; omega
    rw [matrixEquiv_apply]
    rw [Hex.Matrix.borderedMinor_entry_lt_last source (k + 1) hnext i j _ hri]
    simp [hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k r hr_eq, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k c hc]
    have hci : (⟨c.val, by omega⟩ : Fin (k + 2)).val < k + 1 := by show c.val < k + 1; omega
    rw [matrixEquiv_apply]
    rw [Hex.Matrix.borderedMinor_entry_last_lt source (k + 1) hnext i j _ hci]
    simp [hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    have hc_eq : c.val = k := by have := c.isLt; omega
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k r hr_eq, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k c hc_eq]
    rw [matrixEquiv_apply]
    rw [Hex.Matrix.borderedMinor_entry_last_last]
    simp [hr, hc]

 theorem _root_.HexMatrixTheory.source_row_of_borderedMinor
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) r c =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  rw [matrixEquiv_apply]
  show (Hex.Matrix.borderedMinor source k hk i j)[r][c] = _
  simp only [Hex.Matrix.borderedMinor]
  rw [Hex.Matrix.getElem_ofFn]
  simp

/-- For row positions `r.castSucc` (i.e. column `(Fin.last (k + 1)).succAbove r`),
the entry at `bareissDesnanotIndex k r.castSucc` lands in the interior of the
`(k+2)` bordered minor: source row `k` for `r = 0`, source row `r.val - 1` for
`r.val ≥ 1`. Same for columns. -/
 theorem _root_.HexMatrixTheory.source_row_of_castSucc
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.castSucc) (bareissDesnanotIndex k c.castSucc) =
      (let rr : Fin n := if r.val = 0 then ⟨k, by omega⟩ else ⟨r.val - 1, by omega⟩
       let cc : Fin n := if c.val = 0 then ⟨k, by omega⟩ else ⟨c.val - 1, by omega⟩
       source[rr][cc]) := by
  by_cases hr : r.val = 0 <;> by_cases hc : c.val = 0
  · rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k r hr,
        _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k c hc]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]
  · have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k r hr,
        _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k c hcpos]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k r hrpos,
        _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k c hc]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k r hrpos,
        _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k c hcpos]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]

/-- Mixed `succ`/`castSucc` source-row helper used for `M_1k`. -/
 theorem _root_.HexMatrixTheory.source_row_of_succ_castSucc
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.succ) (bareissDesnanotIndex k c.castSucc) =
      (let rr : Fin n := if hr : r.val < k then ⟨r.val, by omega⟩ else i
       let cc : Fin n := if c.val = 0 then ⟨k, by omega⟩ else ⟨c.val - 1, by omega⟩
       source[rr][cc]) := by
  by_cases hr : r.val < k <;> by_cases hc : c.val = 0
  · rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k r hr, _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k c hc]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨k, by omega⟩ : Fin (k + 2))] = _
    have hrle : r.val ≤ k := hr.le
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc, hrle]
  · have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k r hr, _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k c hcpos]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val, by omega⟩ : Fin (k + 2))][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    have hrle : r.val ≤ k := hr.le
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc, hrle]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k r hr_eq, _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k c hc]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        Fin.last (k + 1)][(⟨k, by omega⟩ : Fin (k + 2))] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]
  · have hr_eq : r.val = k := by have := r.isLt; omega
    have hcpos : 0 < c.val := Nat.pos_of_ne_zero hc
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k r hr_eq, _root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k c hcpos]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        Fin.last (k + 1)][(⟨c.val - 1, by omega⟩ : Fin (k + 2))] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]

/-- Mixed `castSucc`/`succ` source-row helper used for `M_k1`. -/
 theorem _root_.HexMatrixTheory.source_row_of_castSucc_succ
    (source : Hex.Matrix R n n) (k : Nat) (hnext : k + 1 < n) (i j : Fin n)
    (r c : Fin (k + 1)) :
    matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k r.castSucc) (bareissDesnanotIndex k c.succ) =
      (let rr : Fin n := if r.val = 0 then ⟨k, by omega⟩ else ⟨r.val - 1, by omega⟩
       let cc : Fin n := if hc : c.val < k then ⟨c.val, by omega⟩ else j
       source[rr][cc]) := by
  by_cases hr : r.val = 0 <;> by_cases hc : c.val < k
  · rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k r hr, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k c hc]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] = _
    have hcle : c.val ≤ k := hc.le
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc, hcle]
  · have hc_eq : c.val = k := by have := c.isLt; omega
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_zero k r hr, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k c hc_eq]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨k, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k r hrpos, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k c hc]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][(⟨c.val, by omega⟩ : Fin (k + 2))] = _
    have hcle : c.val ≤ k := hc.le
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc, hcle]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hc_eq : c.val = k := by have := c.isLt; omega
    rw [_root_.HexMatrixTheory.bareissDesnanotIndex_castSucc_pos k r hrpos, _root_.HexMatrixTheory.bareissDesnanotIndex_succ_top k c hc_eq]
    rw [matrixEquiv_apply]
    show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
        (⟨r.val - 1, by omega⟩ : Fin (k + 2))][Fin.last (k + 1)] = _
    simp only [Hex.Matrix.borderedMinor]
    rw [Hex.Matrix.getElem_ofFn]
    simp [hr, hc]

/-- The Fin-valued cyclic shift on `Fin (k+1)` agrees with the
position-indexing-by-cases used in `source_row_of_castSucc`. -/
 theorem _root_.HexMatrixTheory.fin_n_cyclicShift_eq_castSucc_index (k : Nat) (hk : k < n)
    (r : Fin (k + 1)) :
    (if r.val = 0 then (⟨k, hk⟩ : Fin n) else ⟨r.val - 1, by omega⟩) =
    (if h : (_root_.HexMatrixTheory.bareissCyclicShift k r).val < k then (⟨(_root_.HexMatrixTheory.bareissCyclicShift k r).val, by omega⟩ : Fin n)
     else ⟨k, hk⟩) := by
  by_cases hr : r.val = 0
  · have hr0 : r = 0 := Fin.ext hr
    have hbs : _root_.HexMatrixTheory.bareissCyclicShift k r = (Fin.last k : Fin (k + 1)) := by
      rw [hr0]; exact _root_.HexMatrixTheory.bareissCyclicShift_apply_zero k
    have hge : ¬ (_root_.HexMatrixTheory.bareissCyclicShift k r).val < k := by
      rw [hbs]; show ¬ k < k; exact Nat.lt_irrefl _
    rw [if_pos hr, dif_neg hge]
  · have hpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hbs : _root_.HexMatrixTheory.bareissCyclicShift k r = (⟨r.val - 1, by omega⟩ : Fin (k + 1)) :=
      _root_.HexMatrixTheory.bareissCyclicShift_apply_of_pos k r hpos
    have hbs_val : (_root_.HexMatrixTheory.bareissCyclicShift k r).val = r.val - 1 := by rw [hbs]
    have hlt : (_root_.HexMatrixTheory.bareissCyclicShift k r).val < k := by
      rw [hbs_val]; have := r.isLt; omega
    rw [if_neg hr, dif_pos hlt]
    apply Fin.ext
    show r.val - 1 = (_root_.HexMatrixTheory.bareissCyclicShift k r).val
    rw [hbs_val]

/-- After reindexing by `bareissDesnanotIndex k`, deleting the last row and
column yields the natural `(k+1)` bordered minor of `source` with the original
pivot row/column position `⟨k, _⟩` (i.e. the leading prefix of `source` of size
`k+1`), reindexed by the cyclic shift `bareissCyclicShift k`. -/
 theorem _root_.HexMatrixTheory.M_kk_eq_matrixEquiv_borderedMinor_submatrix
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (Fin.last (k + 1))) (Fin.succAbove (Fin.last (k + 1)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk
        (⟨k, hk⟩ : Fin n) (⟨k, hk⟩ : Fin n))).submatrix
        (_root_.HexMatrixTheory.bareissCyclicShift k) (_root_.HexMatrixTheory.bareissCyclicShift k) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) r))
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk ⟨k, hk⟩ ⟨k, hk⟩)
        (_root_.HexMatrixTheory.bareissCyclicShift k r) (_root_.HexMatrixTheory.bareissCyclicShift k c)
  simp only [Fin.succAbove_last]
  rw [_root_.HexMatrixTheory.source_row_of_castSucc source k hnext i j r c,
      _root_.HexMatrixTheory.source_row_of_borderedMinor source k hk ⟨k, hk⟩ ⟨k, hk⟩
        (_root_.HexMatrixTheory.bareissCyclicShift k r) (_root_.HexMatrixTheory.bareissCyclicShift k c)]
  dsimp only
  simp only [_root_.HexMatrixTheory.fin_n_cyclicShift_eq_castSucc_index k hk r,
             _root_.HexMatrixTheory.fin_n_cyclicShift_eq_castSucc_index k hk c]

/-- After reindexing by `bareissDesnanotIndex k`, deleting row 0 and the last
column yields the natural `(k+1)` bordered minor with trailing row `i` and
trailing column position `⟨k, _⟩`, with columns reindexed by
`bareissCyclicShift k`. -/
 theorem _root_.HexMatrixTheory.M_1k_eq_matrixEquiv_borderedMinor_submatrix
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2))) (Fin.succAbove (Fin.last (k + 1)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk i (⟨k, hk⟩ : Fin n))).submatrix
        id (_root_.HexMatrixTheory.bareissCyclicShift k) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) r))
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i ⟨k, hk⟩)
        r (_root_.HexMatrixTheory.bareissCyclicShift k c)
  rw [show Fin.succAbove (0 : Fin (k + 2)) r = r.succ from rfl]
  simp only [Fin.succAbove_last]
  rw [_root_.HexMatrixTheory.source_row_of_succ_castSucc source k hnext i j r c,
      _root_.HexMatrixTheory.source_row_of_borderedMinor source k hk i ⟨k, hk⟩ r (_root_.HexMatrixTheory.bareissCyclicShift k c)]
  dsimp only
  simp only [_root_.HexMatrixTheory.fin_n_cyclicShift_eq_castSucc_index k hk c]

/-- After reindexing by `bareissDesnanotIndex k`, deleting the last row and
column 0 yields the natural `(k+1)` bordered minor with trailing row position
`⟨k, _⟩` and trailing column `j`, with rows reindexed by
`bareissCyclicShift k`. -/
 theorem _root_.HexMatrixTheory.M_k1_eq_matrixEquiv_borderedMinor_submatrix
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (Fin.last (k + 1))) (Fin.succAbove (0 : Fin (k + 2)))) =
      (matrixEquiv (Hex.Matrix.borderedMinor source k hk (⟨k, hk⟩ : Fin n) j)).submatrix
        (_root_.HexMatrixTheory.bareissCyclicShift k) id := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (Fin.last (k + 1)) r))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk ⟨k, hk⟩ j)
        (_root_.HexMatrixTheory.bareissCyclicShift k r) c
  rw [show Fin.succAbove (0 : Fin (k + 2)) c = c.succ from rfl]
  simp only [Fin.succAbove_last]
  rw [_root_.HexMatrixTheory.source_row_of_castSucc_succ source k hnext i j r c,
      _root_.HexMatrixTheory.source_row_of_borderedMinor source k hk ⟨k, hk⟩ j (_root_.HexMatrixTheory.bareissCyclicShift k r) c]
  dsimp only
  simp only [_root_.HexMatrixTheory.fin_n_cyclicShift_eq_castSucc_index k hk r]

/-- The interior `(k × k)` submatrix of the reindexed Bareiss bordered minor:
deleting both row 0 and the last row (and similarly columns) leaves exactly
`matrixEquiv (principalSubmatrix source k _)`. -/
 theorem _root_.HexMatrixTheory.M_interior_eq_matrixEquiv_principalSubmatrix
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2)) ∘ (Fin.last k).succAbove)
        (Fin.succAbove (0 : Fin (k + 2)) ∘ (Fin.last k).succAbove)) =
      matrixEquiv (Hex.Matrix.principalSubmatrix source k (Nat.le_of_lt hk)) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2))
          ((Fin.last k).succAbove r)))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2))
          ((Fin.last k).succAbove c))) =
      matrixEquiv (Hex.Matrix.principalSubmatrix source k (Nat.le_of_lt hk)) r c
  -- (last k).succAbove r = r.castSucc, then succAbove 0 of r.castSucc = r.castSucc.succ
  simp only [Fin.succAbove_last, Fin.succAbove_zero]
  -- Now use bareissDesnanotIndex_succ_lt with r.castSucc, since (r.castSucc).val = r.val < k
  have hrlt : (r.castSucc : Fin (k + 1)).val < k := r.isLt
  have hclt : (c.castSucc : Fin (k + 1)).val < k := c.isLt
  rw [_root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k r.castSucc hrlt,
      _root_.HexMatrixTheory.bareissDesnanotIndex_succ_lt k c.castSucc hclt]
  rw [matrixEquiv_apply, matrixEquiv_apply]
  show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
      (⟨(r.castSucc : Fin (k + 1)).val, by omega⟩ : Fin (k + 2))][
      (⟨(c.castSucc : Fin (k + 1)).val, by omega⟩ : Fin (k + 2))] = _
  -- Both indices are < k+1, so use borderedMinor_entry_lt_lt
  show (Hex.Matrix.borderedMinor source (k + 1) hnext i j)[
      (⟨r.val, by omega⟩ : Fin (k + 2))][
      (⟨c.val, by omega⟩ : Fin (k + 2))] = _
  simp only [Hex.Matrix.borderedMinor]
  rw [Hex.Matrix.getElem_ofFn, Hex.Matrix.getElem_principalSubmatrix]
  simp [show r.val ≤ k from r.isLt.le, show c.val ≤ k from c.isLt.le]

/-- After reindexing the `(k+2)` bordered minor by `bareissDesnanotIndex k`,
deleting row 0 and column 0 yields exactly `matrixEquiv` of the natural
`(k+1)` bordered minor with the same trailing row `i` and column `j`. -/
 theorem _root_.HexMatrixTheory.M11_eq_matrixEquiv_borderedMinor
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) :
    (((matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)).submatrix
        (bareissDesnanotIndex k) (bareissDesnanotIndex k)).submatrix
        (Fin.succAbove (0 : Fin (k + 2))) (Fin.succAbove (0 : Fin (k + 2)))) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) := by
  ext r c
  show matrixEquiv (Hex.Matrix.borderedMinor source (k + 1) hnext i j)
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) r))
        (bareissDesnanotIndex k (Fin.succAbove (0 : Fin (k + 2)) c)) =
      matrixEquiv (Hex.Matrix.borderedMinor source k hk i j) r c
  rw [show Fin.succAbove (0 : Fin (k + 2)) r = r.succ from rfl,
      show Fin.succAbove (0 : Fin (k + 2)) c = c.succ from rfl,
      _root_.HexMatrixTheory.source_row_of_succ source k hnext i j r c,
      _root_.HexMatrixTheory.source_row_of_borderedMinor source k hk i j r c]

/-- Desnanot-Jacobi specialised to a Bareiss bordered minor: the Mathlib
determinant identity from `desnanot_jacobi_borderedMinor_reindex` translated
back into Hex `borderedMinor`/`principalSubmatrix` determinants. This produces the
`hdesnanot` premise expected by `bareissExactDiv_borderedMinor_of_mul_eq` with
`prevPivot` instantiated as `det (principalSubmatrix source k _)`. -/
theorem desnanot_jacobi_borderedMinor [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) :
    Hex.Matrix.det (Hex.Matrix.borderedMinor source (k + 1) hnext i j) *
        Hex.Matrix.det (Hex.Matrix.principalSubmatrix source k (Nat.le_of_lt hk)) =
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i j) -
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
        Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j) := by
  -- Mathlib Desnanot-Jacobi on the reindexed bordered minor.
  have hdj := desnanot_jacobi_borderedMinor_reindex source k hnext i j
  -- Unfold the local `let M := ...` binding in hdj so subsequent rewrites match.
  dsimp only at hdj
  -- Identify each Mathlib determinant with a Hex determinant.
  rw [det_borderedMinor_bareissDesnanotIndex source k hnext i j] at hdj
  rw [_root_.HexMatrixTheory.M_interior_eq_matrixEquiv_principalSubmatrix source k hk hnext i j,
      ← det_eq] at hdj
  rw [_root_.HexMatrixTheory.M11_eq_matrixEquiv_borderedMinor source k hk hnext i j, ← det_eq] at hdj
  rw [_root_.HexMatrixTheory.M_kk_eq_matrixEquiv_borderedMinor_submatrix source k hk hnext i j,
      Matrix.det_submatrix_equiv_self, ← det_eq] at hdj
  rw [_root_.HexMatrixTheory.M_1k_eq_matrixEquiv_borderedMinor_submatrix source k hk hnext i j,
      Matrix.det_permute', ← det_eq] at hdj
  rw [_root_.HexMatrixTheory.M_k1_eq_matrixEquiv_borderedMinor_submatrix source k hk hnext i j,
      Matrix.det_permute, ← det_eq] at hdj
  -- hdj has the form M.det * Mint.det = M11.det * Mkk.det - (sign σ * X) * (sign σ * Y).
  -- Sign² = 1, so the sign factors cancel.
  have hsign_sq : ((Equiv.Perm.sign (_root_.HexMatrixTheory.bareissCyclicShift k) : ℤ) : R) *
      ((Equiv.Perm.sign (_root_.HexMatrixTheory.bareissCyclicShift k) : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
        Int.cast_one]
  -- Rearrange hdj using commutativity (M11 * Mkk = Mkk * M11) and the sign²=1
  -- cancellation (M1k * sign * Mk1 * sign = M1k * Mk1).
  linear_combination hdj -
    (Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk i
        (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
      Hex.Matrix.det (Hex.Matrix.borderedMinor source k hk
        (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j)) * hsign_sq

end HexMatrixTheory

/- Modified compatibility port (2026-11-15): imports namespaced under
Solutions.RegevBridgeNativeLLLVendor; pure Lean portability changes and removal
of native runtime hooks are recorded in MODIFICATIONS.json and the provenance
receipt. Original copyright/author notices and Apache-2.0 license are retained. -/

end

end


