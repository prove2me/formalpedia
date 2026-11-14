-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBForm
-- name    : RPLib_S4_AlgGrpBForm
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:44:26.944189+00:00
-- url     : https://prove2.me/theorems/017391b1-f30f-43c9-ab81-42f38c7a9b5b
-- title:
--   Larsen's alternative library: bilinear-form toolkit for the generation of `Sp(B)` / `SO(B)`
-- statement:
--   `bf B x y = xᵀ B y`; `isoSub B` is the subgroup `{g | gᵀ B g = B}` of `GL_n(K)`; it preserves `bf B`
--   (`bf_iso`). `orthS B S` is the subspace of vectors `B`-orthogonal to a set `S` (`B(s, x) = 0`), and
--   `DecS B S` says that every vector is `s + w` with `s ∈ span S` and `w ∈ orthS B S`. A unipotent
--   `1 + c N` with `N² = 0` and `Nᵀ B + B N = 0` lies in `isoSet B` (`unip_mem_isoSet`). If `orthS B S = 0`,
--   `DecS B S` holds and `g` fixes `S` pointwise, then `g = 1` (`eq_one_of_fix`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBOrth

/-!
# S4-AlgGrpB, file Form: bilinear-form toolkit for the generation of `Sp(B)` / `SO(B)` (O5b)

`bf B x y = xᵀ B y`; `isoSub B` is the subgroup `{g | gᵀ B g = B}` of `GL_n(K)`; it preserves `bf B`
(`bf_iso`). `orthS B S` is the subspace of vectors `B`-orthogonal to a set `S` (`B(s, x) = 0`), and
`DecS B S` says that every vector is `s + w` with `s ∈ span S` and `w ∈ orthS B S`. A unipotent
`1 + c N` with `N² = 0` and `Nᵀ B + B N = 0` lies in `isoSet B` (`unip_mem_isoSet`). If `orthS B S = 0`,
`DecS B S` holds and `g` fixes `S` pointwise, then `g = 1` (`eq_one_of_fix`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- The bilinear form `B(x, y) = xᵀ B y`. -/
def bf (B : Matrix n n K) (x y : n → K) : K := x ⬝ᵥ B *ᵥ y

section Bf

variable (B : Matrix n n K)

theorem bf_add_left (x x' y : n → K) : bf B (x + x') y = bf B x y + bf B x' y := by
  simp [bf, add_dotProduct]

theorem bf_add_right (x y y' : n → K) : bf B x (y + y') = bf B x y + bf B x y' := by
  simp [bf, Matrix.mulVec_add, dotProduct_add]

theorem bf_sub_left (x x' y : n → K) : bf B (x - x') y = bf B x y - bf B x' y := by
  simp [bf, sub_dotProduct]

theorem bf_sub_right (x y y' : n → K) : bf B x (y - y') = bf B x y - bf B x y' := by
  simp [bf, Matrix.mulVec_sub, dotProduct_sub]

theorem bf_smul_left (a : K) (x y : n → K) : bf B (a • x) y = a * bf B x y := by
  simp [bf, smul_dotProduct]

theorem bf_smul_right (a : K) (x y : n → K) : bf B x (a • y) = a * bf B x y := by
  simp [bf, Matrix.mulVec_smul, dotProduct_smul]

theorem bf_zero_left (y : n → K) : bf B 0 y = 0 := by simp [bf]

theorem bf_zero_right (x : n → K) : bf B x 0 = 0 := by simp [bf]

/-- `B(y, x) = B(x, Bᵀ-side)`: the swap rule through the transpose. -/
theorem bf_swap_transpose (x y : n → K) : bf B y x = bf Bᵀ x y := by
  unfold bf
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

/-- `B(x, A y)` for a matrix `A`. -/
theorem bf_mulVec (A : Matrix n n K) (x y : n → K) :
    bf B (A *ᵥ x) (A *ᵥ y) = bf (Aᵀ * B * A) x y := by
  unfold bf
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mul_assoc]

end Bf

/-- `{g | gᵀ B g = B}` as a subgroup of `GL_n(K)`. -/
def isoSub (B : Matrix n n K) : Subgroup (Matrix.GeneralLinearGroup n K) where
  carrier := isoSet B
  one_mem' := by simp [isoSet]
  mul_mem' := by
    intro a b ha hb
    change ((a * b : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B * _ = B
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (b : Matrix n n K)ᵀ * (a : Matrix n n K)ᵀ * B * ((a : Matrix n n K) * b)
        = (b : Matrix n n K)ᵀ * ((a : Matrix n n K)ᵀ * B * a) * b := by simp only [Matrix.mul_assoc]
      _ = B := by rw [mem_isoSet.1 ha, mem_isoSet.1 hb]
  inv_mem' := by
    intro a ha
    change ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ * B * _ = B
    have h1 : ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * a = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (a : Matrix n n K) * ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    conv_lhs => rw [← mem_isoSet.1 ha]
    calc ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)ᵀ *
          ((a : Matrix n n K)ᵀ * B * a) * ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)
        = (((a : Matrix n n K) * ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K))ᵀ * B) *
            ((a : Matrix n n K) * ((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = B := by rw [h2, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_isoSub {B : Matrix n n K} {g : Matrix.GeneralLinearGroup n K} :
    g ∈ isoSub B ↔ (g : Matrix n n K)ᵀ * B * g = B := Iff.rfl

theorem bf_iso {B : Matrix n n K} {g : Matrix.GeneralLinearGroup n K} (hg : g ∈ isoSub B)
    (x y : n → K) : bf B ((g : Matrix n n K) *ᵥ x) ((g : Matrix n n K) *ᵥ y) = bf B x y := by
  rw [bf_mulVec, mem_isoSub.1 hg]

theorem mulVec_mul_GL (g h : Matrix.GeneralLinearGroup n K) (x : n → K) :
    ((g * h : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x =
      (g : Matrix n n K) *ᵥ ((h : Matrix n n K) *ᵥ x) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem inv_mulVec_GL (g : Matrix.GeneralLinearGroup n K) (x : n → K) :
    ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ ((g : Matrix n n K) *ᵥ x) = x := by
  rw [← mulVec_mul_GL, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/-- A unipotent `1 + c N` with `N² = 0` and `N ∈ Lie(isoSet B)` preserves `B`. -/
theorem unip_mem_isoSub {B N : Matrix n n K} (hNN : N * N = 0) (hN : Nᵀ * B + B * N = 0) (c : K) :
    unip N hNN c ∈ isoSub B := by
  rw [mem_isoSub, val_unip]
  have h1 : Nᵀ * B = -(B * N) := eq_neg_of_add_eq_zero_left hN
  have h2 : Nᵀ * B * N = 0 := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc, hNN, Matrix.mul_zero,
    neg_zero]
  have key : (1 + c • N)ᵀ * B * (1 + c • N) =
      B + c • (Nᵀ * B + B * N) + (c * c) • (Nᵀ * B * N) := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, add_mul, mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
    abel
  rw [key, hN, h2, smul_zero, smul_zero, add_zero, add_zero]

/-- Vectors `B`-orthogonal to every element of `S` (`B(s, x) = 0`). -/
def orthS (B : Matrix n n K) (S : Set (n → K)) : Submodule K (n → K) where
  carrier := {x | ∀ s ∈ S, bf B s x = 0}
  add_mem' := by
    intro x y hx hy s hs
    rw [bf_add_right, hx s hs, hy s hs, add_zero]
  zero_mem' := by
    intro s _
    exact bf_zero_right B s
  smul_mem' := by
    intro a x hx s hs
    rw [bf_smul_right, hx s hs, mul_zero]

theorem mem_orthS {B : Matrix n n K} {S : Set (n → K)} {x : n → K} :
    x ∈ orthS B S ↔ ∀ s ∈ S, bf B s x = 0 := Iff.rfl

theorem orthS_anti {B : Matrix n n K} {S S' : Set (n → K)} (h : S ⊆ S') : orthS B S' ≤ orthS B S :=
  fun _ hx s hs => hx s (h hs)

/-- `x ⊥ S` implies `x ⊥ span S` (on the left of `B`). -/
theorem bf_span_left {B : Matrix n n K} {S : Set (n → K)} {x : n → K} (hx : x ∈ orthS B S)
    {s : n → K} (hs : s ∈ Submodule.span K S) : bf B s x = 0 := by
  induction hs using Submodule.span_induction with
  | mem y hy => exact hx y hy
  | zero => exact bf_zero_left B x
  | add y z _ _ hy hz => rw [bf_add_left, hy, hz, add_zero]
  | smul a y _ hy => rw [bf_smul_left, hy, mul_zero]

/-- Every vector is `s + w` with `s ∈ span S` and `w ⊥ S`. -/
def DecS (B : Matrix n n K) (S : Set (n → K)) : Prop :=
  ∀ x : n → K, ∃ s ∈ Submodule.span K S, x - s ∈ orthS B S

theorem decS_empty (B : Matrix n n K) : DecS B ∅ :=
  fun _ => ⟨0, Submodule.zero_mem _, fun s hs => absurd hs (Set.notMem_empty s)⟩

/-- A matrix fixing `S` pointwise fixes `span S`. -/
theorem fix_span {A : Matrix n n K} {S : Set (n → K)} (hA : ∀ s ∈ S, A *ᵥ s = s)
    {s : n → K} (hs : s ∈ Submodule.span K S) : A *ᵥ s = s := by
  induction hs using Submodule.span_induction with
  | mem y hy => exact hA y hy
  | zero => exact Matrix.mulVec_zero A
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | smul a y _ hy => rw [Matrix.mulVec_smul, hy]

theorem eq_one_of_fix {B : Matrix n n K} {S : Set (n → K)} (hD : DecS B S) (h0 : orthS B S = ⊥)
    {g : Matrix.GeneralLinearGroup n K} (hg : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) : g = 1 := by
  refine Units.ext (Matrix.ext_iff_mulVec.2 fun x => ?_)
  obtain ⟨s, hs, hxs⟩ := hD x
  rw [h0, Submodule.mem_bot, sub_eq_zero] at hxs
  rw [hxs, fix_span hg hs, Units.val_one, Matrix.one_mulVec]

/-- A form-preserving `g` fixing `S` pointwise maps `orthS B S` into itself. -/
theorem iso_orthS {B : Matrix n n K} {S : Set (n → K)} {g : Matrix.GeneralLinearGroup n K}
    (hg : g ∈ isoSub B) (hfix : ∀ s ∈ S, (g : Matrix n n K) *ᵥ s = s) {x : n → K}
    (hx : x ∈ orthS B S) : (g : Matrix n n K) *ᵥ x ∈ orthS B S := by
  intro s hs
  rw [← hfix s hs, bf_iso hg]
  exact hx s hs

end RamanujanPetersson.AlgGrpB

end


