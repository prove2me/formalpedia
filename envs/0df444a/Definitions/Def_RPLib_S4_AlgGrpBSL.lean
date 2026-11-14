-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSL
-- name    : RPLib_S4_AlgGrpBSL
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:41:16.519899+00:00
-- url     : https://prove2.me/theorems/c57de174-e487-42f0-bb57-6facc38d7574
-- title:
--   Larsen's alternative library: `Lie H ⊇ sl_n` forces `H ⊇ SL_n` for `SL`)
-- statement:
--   Char 0. If `H ⊆ GL_n(K)` is a Zariski-closed subgroup and every elementary matrix `E_ij`
--   (`i ≠ j`) lies in `Lie H`, then `H` contains every transvection (`unip_mem`), hence every
--   `diag2n` (a product of six transvections, `diag2n_eq_prod`), hence all of `SL_n(K)`
--   (`Matrix.SpecialLinearGroup.diagonal_transvection_induction'`): `toGL_mem_of_single_mem_lieS`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBExp

/-!
# S4-AlgGrpB, file SL: `Lie H ⊇ sl_n` forces `H ⊇ SL_n` (spike API (A4) for `SL`)

Char 0. If `H ⊆ GL_n(K)` is a Zariski-closed subgroup and every elementary matrix `E_ij`
(`i ≠ j`) lies in `Lie H`, then `H` contains every transvection (`unip_mem`), hence every
`diag2n` (a product of six transvections, `diag2n_eq_prod`), hence all of `SL_n(K)`
(`Matrix.SpecialLinearGroup.diagonal_transvection_induction'`): `toGL_mem_of_single_mem_lieS`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- `diag(…, c, …, c⁻¹, …)` as a product of six transvections (as in `diag2_decompose`). -/
theorem diag2n_eq_prod {i j : n} (hij : i ≠ j) (c : K) (hc : c ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij c hc =
      Matrix.SpecialLinearGroup.transvection hij c *
        Matrix.SpecialLinearGroup.transvection hij.symm (-c⁻¹) *
        Matrix.SpecialLinearGroup.transvection hij c *
        Matrix.SpecialLinearGroup.transvection hij (-1) *
        Matrix.SpecialLinearGroup.transvection hij.symm 1 *
        Matrix.SpecialLinearGroup.transvection hij (-1) := by
  have ht : ∀ {a b : n} (h : a ≠ b) (x : K),
      ((Matrix.SpecialLinearGroup.transvection h x : Matrix.SpecialLinearGroup n K) :
        Matrix n n K) = Matrix.transvection a b x := fun _ _ => rfl
  ext k l
  simp only [Matrix.SpecialLinearGroup.coe_mul, ht, Matrix.SpecialLinearGroup.diag2n_coe,
    mul_assoc]
  have hc' : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  have hc'' : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  by_cases hki : k = i
  · subst hki
    simp only [Matrix.transvection_mul_apply_same, Matrix.transvection_mul_apply_of_ne, hij,
      Ne.symm hij, ne_eq, not_false_eq_true]
    by_cases hlk : l = k
    · subst hlk
      simp [Matrix.transvection, Matrix.single_apply, Matrix.diagonal_apply, hc, hij, Ne.symm hij]
      try linear_combination hc'
    · by_cases hlj : l = j
      · subst hlj
        simp [Matrix.transvection, Matrix.single_apply, Matrix.diagonal_apply, hc, hij, Ne.symm hij]
        try linear_combination (-1 : K) * hc'
      · simp [Matrix.transvection, Matrix.single_apply, Matrix.diagonal_apply, hc, hij, Ne.symm hlk, Ne.symm hlj]
  by_cases hkj : k = j
  · subst hkj
    simp only [Matrix.transvection_mul_apply_same, Matrix.transvection_mul_apply_of_ne, hij,
      Ne.symm hij, ne_eq, not_false_eq_true]
    by_cases hlk : l = k
    · subst hlk
      simp [Matrix.transvection, Matrix.single_apply, Matrix.diagonal_apply, hc, hij, Ne.symm hij]
      try linear_combination (-1 : K) * hc''
    · by_cases hli : l = i
      · subst hli
        simp [Matrix.transvection, Matrix.single_apply, Matrix.diagonal_apply, hc, hij, Ne.symm hij]
        try linear_combination 2 * hc'
      · simp [Matrix.transvection, Matrix.single_apply, Matrix.diagonal_apply, hc, Ne.symm hlk, Ne.symm hli]
  · simp only [Matrix.transvection_mul_apply_of_ne, hki, hkj, ne_eq, not_false_eq_true]
    simp [Matrix.transvection, Matrix.single_apply, Matrix.diagonal_apply, hc, hki, hkj, Ne.symm hki, Ne.symm hkj,
      Matrix.one_apply]

variable [CharZero K]

attribute [local instance] zarTop

theorem toGL_transvection_mem {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
    {i j : n} (hij : i ≠ j)
    (hE : Matrix.single i j (1 : K) ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) (a : K) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) ∈ H := by
  have hNN : Matrix.single i j (1 : K) * Matrix.single i j 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne]
    exact Ne.symm hij
  convert unip_mem hH hNN hE a using 1
  refine Units.ext ?_
  change Matrix.transvection i j a = 1 + a • Matrix.single i j (1 : K)
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rfl

/-- `(A4)` for `SL` (char 0): a Zariski-closed `H` whose Lie algebra contains every `E_ij`
(`i ≠ j`) contains `SL_n(K)`. -/
theorem toGL_mem_of_single_mem_lieS {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
    (hE : ∀ i j : n, i ≠ j →
      Matrix.single i j (1 : K) ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    (M : Matrix.SpecialLinearGroup n K) : Matrix.SpecialLinearGroup.toGL M ∈ H := by
  by_cases hn : Nontrivial n
  · refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => Matrix.SpecialLinearGroup.toGL A ∈ H) M ?_ ?_ ?_
    · intro i j hij c hc
      change Matrix.SpecialLinearGroup.toGL _ ∈ H
      rw [diag2n_eq_prod hij c hc]
      simp only [map_mul]
      refine H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
        first
        | exact toGL_transvection_mem hH hij (hE _ _ hij) _
        | exact toGL_transvection_mem hH hij.symm (hE _ _ hij.symm) _
    · intro i j hij a
      exact toGL_transvection_mem hH hij (hE i j hij) a
    · intro A B hA hB
      change Matrix.SpecialLinearGroup.toGL (A * B) ∈ H
      rw [map_mul]
      exact H.mul_mem hA hB
  · rw [not_nontrivial_iff_subsingleton] at hn
    have h1 : M = 1 := by
      ext i j
      obtain rfl : i = j := Subsingleton.elim i j
      let _ : Unique n := uniqueOfSubsingleton i
      have hd : Matrix.det (M : Matrix n n K) = (M : Matrix n n K) i i := by
        rw [Matrix.det_unique, Subsingleton.elim (default : n) i]
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, ← hd, M.2]
    rw [h1, map_one]
    exact H.one_mem

end RamanujanPetersson.AlgGrpB


