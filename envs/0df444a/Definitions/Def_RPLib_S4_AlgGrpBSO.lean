-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSO
-- name    : RPLib_S4_AlgGrpBSO
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:52:58.87859+00:00
-- url     : https://prove2.me/theorems/61fba920-3b18-4944-9159-1ca341bdb72d
-- title:
--   Larsen's alternative library: Eichler transformations and reflections
-- statement:
--   `B` symmetric (`Bᵀ = B`). For `y` isotropic and `w ⊥ y`, the Eichler matrix
--   `NE B y w` (`x ↦ B(y, x) w - B(w, x) y`) lies in `so(B)` and has cube `0`, so (char 0)
--   `eich = exp3 (NE B y w) c` lies in every closed `H` with `so(B) ⊆ Lie H`, preserves `B`, has
--   determinant `1` and fixes `{y, w}^⊥` (`eich_good`). `eich_move` moves `x` to `x'` when
--   `B(y, x) = B(y, x') = 1` and `B(x, x) = B(x', x')`. `reflM B x c = 1 + c x (xᵀ B)` has
--   determinant `1 + c B(x, x)` (`det_reflM`). Nondegeneracy on `orthS B S` (`exists_bf_ne_sym`),
--   anisotropic vectors (`exists_aniso`), and `eq_of_agree` (matrices agreeing on `S` with
--   `orthS B S = 0` are equal).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBExp3

/-!
# S4-AlgGrpB, file SO: Eichler transformations and reflections (O5b-SO part 1)

`B` symmetric (`Bᵀ = B`). For `y` isotropic and `w ⊥ y`, the Eichler matrix
`NE B y w` (`x ↦ B(y, x) w - B(w, x) y`) lies in `so(B)` and has cube `0`, so (char 0)
`eich = exp3 (NE B y w) c` lies in every closed `H` with `so(B) ⊆ Lie H`, preserves `B`, has
determinant `1` and fixes `{y, w}^⊥` (`eich_good`). `eich_move` moves `x` to `x'` when
`B(y, x) = B(y, x') = 1` and `B(x, x) = B(x', x')`. `reflM B x c = 1 + c x (xᵀ B)` has
determinant `1 + c B(x, x)` (`det_reflM`). Nondegeneracy on `orthS B S` (`exists_bf_ne_sym`),
anisotropic vectors (`exists_aniso`), and `eq_of_agree` (matrices agreeing on `S` with
`orthS B S = 0` are equal).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Sym

variable {B : Matrix n n K}

theorem bf_swap_sym (hB : Bᵀ = B) (x y : n → K) : bf B y x = bf B x y := by
  rw [bf_swap_transpose, hB]

/-- `vecMulVec u (v ᵥ* B)` acts by `x ↦ B(v, x) u`. -/
theorem vmv_mulVec (u v x : n → K) : Matrix.vecMulVec u (v ᵥ* B) *ᵥ x = bf B v x • u := by
  rw [Matrix.vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, op_smul_eq_smul]
  rfl

/-- The Eichler matrix: `NE B y w x = B(y, x) w - B(w, x) y`. -/
def NE (B : Matrix n n K) (y w : n → K) : Matrix n n K :=
  Matrix.vecMulVec w (y ᵥ* B) - Matrix.vecMulVec y (w ᵥ* B)

theorem NE_mulVec (y w x : n → K) : NE B y w *ᵥ x = bf B y x • w - bf B w x • y := by
  rw [NE, Matrix.sub_mulVec, vmv_mulVec, vmv_mulVec]

theorem NE_so (hB : Bᵀ = B) (y w : n → K) : (NE B y w)ᵀ * B + B * NE B y w = 0 := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  have hv : ∀ v : n → K, v ᵥ* B = B *ᵥ v := fun v => by
    rw [← Matrix.mulVec_transpose, hB]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, NE_mulVec, NE,
    Matrix.transpose_sub, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec, Matrix.sub_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.zero_mulVec, hv, hv]
  simp only [bf]
  abel

theorem NE_sq_mulVec (hB : Bᵀ = B) {y w : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0)
    (x : n → K) : (NE B y w * NE B y w) *ᵥ x = -(bf B w w * bf B y x) • y := by
  have hwy : bf B w y = 0 := by rw [bf_swap_sym hB, hyw]
  rw [← Matrix.mulVec_mulVec, NE_mulVec, NE_mulVec]
  simp only [bf_sub_right, bf_smul_right, hyy, hyw, hwy]
  module

theorem NE_cube (hB : Bᵀ = B) {y w : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0) :
    NE B y w * NE B y w * NE B y w = 0 := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  rw [← Matrix.mulVec_mulVec, NE_sq_mulVec hB hyy hyw, NE_mulVec]
  simp only [bf_sub_right, bf_smul_right, hyy, hyw, mul_zero, sub_zero, neg_zero, zero_smul,
    Matrix.zero_mulVec]

/-- `1 + c · x (xᵀ B)`: `v ↦ v + c B(x, v) x` (a reflection when `c B(x, x) = -2`). -/
def reflM (B : Matrix n n K) (x : n → K) (c : K) : Matrix n n K :=
  1 + Matrix.vecMulVec (c • x) (x ᵥ* B)

theorem reflM_mulVec (x : n → K) (c : K) (v : n → K) :
    reflM B x c *ᵥ v = v + (c * bf B x v) • x := by
  rw [reflM, Matrix.add_mulVec, Matrix.one_mulVec, vmv_mulVec, smul_smul, mul_comm (bf B x v) c]

theorem det_reflM (x : n → K) (c : K) : (reflM B x c).det = 1 + c * bf B x x := by
  rw [reflM, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, ← Matrix.dotProduct_mulVec, smul_eq_mul]
  rfl

theorem exists_bf_ne_sym (hB : Bᵀ = B) (hnd : B.Nondegenerate) {S : Set (n → K)} (hD : DecS B S)
    {x : n → K} (hx : x ∈ orthS B S) (hx0 : x ≠ 0) : ∃ z ∈ orthS B S, bf B x z ≠ 0 := by
  obtain ⟨z0, hz0⟩ := hnd.exists_not_ortho_of_ne_zero hx0
  obtain ⟨s, hs, hzs⟩ := hD z0
  refine ⟨z0 - s, hzs, ?_⟩
  have h0 : bf B x s = 0 := by rw [bf_swap_sym hB s x, bf_span_left hx hs]
  rw [bf_sub_right, h0, sub_zero]
  exact hz0

theorem exists_aniso [CharZero K] (hB : Bᵀ = B) (hnd : B.Nondegenerate) {S : Set (n → K)}
    (hD : DecS B S) (h0 : orthS B S ≠ ⊥) : ∃ z ∈ orthS B S, bf B z z ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  by_cases hxx : bf B x x = 0
  · obtain ⟨z, hz, hxz⟩ := exists_bf_ne_sym hB hnd hD hx hx0
    by_cases hzz : bf B z z = 0
    · refine ⟨x + z, Submodule.add_mem _ hx hz, fun h => hxz ?_⟩
      rw [bf_add_left, bf_add_right, bf_add_right, hxx, hzz, bf_swap_sym hB x z] at h
      have h2 : (2 : K) * bf B x z = 0 := by linear_combination h
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    · exact ⟨z, hz, hzz⟩
  · exact ⟨x, hx, hxx⟩

end Sym

theorem agree_span {S : Set (n → K)} {A A' : Matrix n n K} (h : ∀ s ∈ S, A *ᵥ s = A' *ᵥ s)
    {s : n → K} (hs : s ∈ Submodule.span K S) : A *ᵥ s = A' *ᵥ s := by
  induction hs using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, Matrix.mulVec_add, hy, hz]
  | smul a y _ hy => rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hy]

/-- Matrices agreeing on `S` are equal when `DecS B S` and `orthS B S = 0`. -/
theorem eq_of_agree {B : Matrix n n K} {S : Set (n → K)} (hD : DecS B S) (h0 : orthS B S = ⊥)
    {A A' : Matrix n n K} (h : ∀ s ∈ S, A *ᵥ s = A' *ᵥ s) : A = A' := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  obtain ⟨s, hs, hxs⟩ := hD x
  rw [h0, Submodule.mem_bot, sub_eq_zero] at hxs
  rw [hxs]
  exact agree_span h hs

/-- `GoodS` plus determinant one. -/
def GoodSO (H : Subgroup (Matrix.GeneralLinearGroup n K)) (B : Matrix n n K) (S : Set (n → K))
    (u : Matrix.GeneralLinearGroup n K) : Prop :=
  GoodS H B S u ∧ (u : Matrix n n K).det = 1

theorem GoodSO.mul {H : Subgroup (Matrix.GeneralLinearGroup n K)} {B : Matrix n n K}
    {S : Set (n → K)} {u w : Matrix.GeneralLinearGroup n K} (hu : GoodSO H B S u)
    (hw : GoodSO H B S w) : GoodSO H B S (u * w) :=
  ⟨hu.1.mul hw.1, by rw [Units.val_mul, Matrix.det_mul, hu.2, hw.2, one_mul]⟩

section Eich

variable [CharZero K] {B : Matrix n n K}

/-- The Eichler transformation `exp(c N)`, `N x = B(y, x) w - B(w, x) y`. -/
def eich (hB : Bᵀ = B) {y w : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0) (c : K) :
    Matrix.GeneralLinearGroup n K :=
  exp3 (NE B y w) (NE_cube hB hyy hyw) c

theorem eich_mulVec (hB : Bᵀ = B) {y w : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0)
    (c : K) (x : n → K) :
    ((eich hB hyy hyw c : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x =
      x + c • (bf B y x • w - bf B w x • y) -
        (c ^ 2 * (2 : K)⁻¹ * (bf B w w * bf B y x)) • y := by
  rw [eich, val_exp3, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, NE_mulVec, NE_sq_mulVec hB hyy hyw]
  module

theorem eich_fix (hB : Bᵀ = B) {y w : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0)
    (c : K) {x : n → K} (h1 : bf B y x = 0) (h2 : bf B w x = 0) :
    ((eich hB hyy hyw c : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x = x := by
  rw [eich_mulVec, h1, h2]
  simp

/-- `eich y (x' - x) 1` maps `x` to `x'` (`B(y, x) = B(y, x') = 1`, `B(x, x) = B(x', x')`). -/
theorem eich_move (hB : Bᵀ = B) {y x x' : n → K} (hyy : bf B y y = 0) (hyx : bf B y x = 1)
    (hxx : bf B x' x' = bf B x x) (hyw : bf B y (x' - x) = 0) :
    ((eich hB hyy hyw 1 : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x = x' := by
  have hc : bf B (x' - x) x + 2⁻¹ * bf B (x' - x) (x' - x) = 0 := by
    rw [bf_sub_left, bf_sub_left, bf_sub_right, bf_sub_right, bf_swap_sym hB x x', hxx]
    ring
  rw [eich_mulVec, hyx]
  calc _ = x' - (bf B (x' - x) x + 2⁻¹ * bf B (x' - x) (x' - x)) • y := by module
    _ = x' := by rw [hc, zero_smul, sub_zero]

section Good

attribute [local instance] zarTop

theorem eich_good (hB : Bᵀ = B) {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
    (hso : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 →
      X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {S : Set (n → K)} {y w : n → K} (hy : y ∈ orthS B S) (hw : w ∈ orthS B S)
    (hyy : bf B y y = 0) (hyw : bf B y w = 0) (c : K) : GoodSO H B S (eich hB hyy hyw c) :=
  ⟨⟨exp3_mem hH _ (hso _ (NE_so hB y w)) c, exp3_mem_isoSub _ (NE_so hB y w) c,
      fun s hs => eich_fix hB hyy hyw c (by rw [bf_swap_sym hB, hy s hs])
        (by rw [bf_swap_sym hB, hw s hs])⟩,
    det_exp3 _ _ c⟩

end Good

end Eich

end RamanujanPetersson.AlgGrpB

end


