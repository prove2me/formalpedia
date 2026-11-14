-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSp
-- name    : RPLib_S4_AlgGrpBSp
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:47:09.273875+00:00
-- url     : https://prove2.me/theorems/2f320fbb-870c-4b01-a2ff-27001ea09357
-- title:
--   Larsen's alternative library: symplectic transvections and their transitivity
-- statement:
--   `B` alternating (`Bᵀ = -B`), char 0. `Nv B v = v (vᵀ B)` (so `Nv B v x = B(v, x) v`) has square `0` and
--   lies in `sp(B)`; `tv hB v c = 1 + c Nv B v` is the symplectic transvection `x ↦ x + c B(v, x) v`.
--   If `H` is a closed subgroup with `sp(B) ⊆ Lie H`, every `tv` is in `H`.
--   `GoodS H B S u`: `u ∈ H`, `u` preserves `B` and fixes `S` pointwise. For `B` nondegenerate and
--   `DecS B S`, the `GoodS` elements act transitively on nonzero vectors of `orthS B S` (`vec_trans`)
--   and on hyperbolic pairs `(e, f)` (`B(e, f) = 1`) in `orthS B S` (`pair_trans`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBForm

/-!
# S4-AlgGrpB, file Sp: symplectic transvections and their transitivity (O5b, `Sp` part 1)

`B` alternating (`Bᵀ = -B`), char 0. `Nv B v = v (vᵀ B)` (so `Nv B v x = B(v, x) v`) has square `0` and
lies in `sp(B)`; `tv hB v c = 1 + c Nv B v` is the symplectic transvection `x ↦ x + c B(v, x) v`.
If `H` is a closed subgroup with `sp(B) ⊆ Lie H`, every `tv` is in `H`.
`GoodS H B S u`: `u ∈ H`, `u` preserves `B` and fixes `S` pointwise. For `B` nondegenerate and
`DecS B S`, the `GoodS` elements act transitively on nonzero vectors of `orthS B S` (`vec_trans`)
and on hyperbolic pairs `(e, f)` (`B(e, f) = 1`) in `orthS B S` (`pair_trans`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Alt

variable {B : Matrix n n K}

theorem bf_swap_alt (hB : Bᵀ = -B) (x y : n → K) : bf B y x = -bf B x y := by
  rw [bf_swap_transpose, hB]
  simp only [bf, Matrix.neg_mulVec, dotProduct_neg]

theorem bf_self_alt [CharZero K] (hB : Bᵀ = -B) (x : n → K) : bf B x x = 0 := by
  have h := bf_swap_alt hB x x
  have h2 : (2 : K) * bf B x x = 0 := by linear_combination h
  exact (mul_eq_zero.1 h2).resolve_left two_ne_zero

/-- `N_v = v (vᵀ B)`, so `N_v x = B(v, x) v`. -/
def Nv (B : Matrix n n K) (v : n → K) : Matrix n n K := Matrix.vecMulVec v (v ᵥ* B)

theorem Nv_mulVec (v x : n → K) : Nv B v *ᵥ x = bf B v x • v := by
  rw [Nv, Matrix.vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, op_smul_eq_smul]
  rfl

theorem Nv_sq [CharZero K] (hB : Bᵀ = -B) (v : n → K) : Nv B v * Nv B v = 0 := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  rw [← Matrix.mulVec_mulVec, Nv_mulVec, Nv_mulVec, bf_smul_right, bf_self_alt hB, mul_zero,
    zero_smul, Matrix.zero_mulVec]

theorem Nv_sp (hB : Bᵀ = -B) (v : n → K) : (Nv B v)ᵀ * B + B * Nv B v = 0 := by
  refine Matrix.ext_iff_mulVec.2 fun x => ?_
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Nv_mulVec, Nv,
    Matrix.transpose_vecMulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, ← Matrix.mulVec_transpose,
    hB, Matrix.neg_mulVec, Matrix.mulVec_smul, Matrix.zero_mulVec]
  simp only [bf, smul_neg, neg_add_cancel]

variable [CharZero K]

/-- The symplectic transvection `x ↦ x + c B(v, x) v`. -/
def tv (hB : Bᵀ = -B) (v : n → K) (c : K) : Matrix.GeneralLinearGroup n K := unip (Nv B v) (Nv_sq hB v) c

theorem tv_mulVec (hB : Bᵀ = -B) (v : n → K) (c : K) (x : n → K) :
    ((tv hB v c : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x = x + (c * bf B v x) • v := by
  rw [tv, val_unip, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Nv_mulVec, smul_smul]

theorem tv_mem_iso (hB : Bᵀ = -B) (v : n → K) (c : K) : tv hB v c ∈ isoSub B :=
  unip_mem_isoSub (Nv_sq hB v) (Nv_sp hB v) c

theorem tv_fix (hB : Bᵀ = -B) {v w : n → K} (c : K) (h : bf B v w = 0) :
    ((tv hB v c : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ w = w := by
  rw [tv_mulVec, h, mul_zero, zero_smul, add_zero]

theorem tv_move (hB : Bᵀ = -B) {x y : n → K} (h : bf B y x ≠ 0) :
    ((tv hB (y - x) (bf B y x)⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x = y := by
  rw [tv_mulVec, bf_sub_left, bf_self_alt hB, sub_zero, inv_mul_cancel₀ h, one_smul]
  abel

end Alt

/-- `u ∈ H`, `u` preserves `B` and fixes `S` pointwise. -/
def GoodS (H : Subgroup (Matrix.GeneralLinearGroup n K)) (B : Matrix n n K) (S : Set (n → K))
    (u : Matrix.GeneralLinearGroup n K) : Prop :=
  u ∈ H ∧ u ∈ isoSub B ∧ ∀ s ∈ S, (u : Matrix n n K) *ᵥ s = s

theorem GoodS.mul {H : Subgroup (Matrix.GeneralLinearGroup n K)} {B : Matrix n n K}
    {S : Set (n → K)} {u w : Matrix.GeneralLinearGroup n K} (hu : GoodS H B S u)
    (hw : GoodS H B S w) : GoodS H B S (u * w) :=
  ⟨H.mul_mem hu.1 hw.1, (isoSub B).mul_mem hu.2.1 hw.2.1,
    fun s hs => by rw [mulVec_mul_GL, hw.2.2 s hs, hu.2.2 s hs]⟩

section Trans

attribute [local instance] zarTop

variable [CharZero K] {B : Matrix n n K} (hB : Bᵀ = -B)
  {H : Subgroup (Matrix.GeneralLinearGroup n K)}
  (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
  (hsp : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 → X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
  {S : Set (n → K)}

include hB hH hsp in
theorem tv_good {v : n → K} (hv : v ∈ orthS B S) (c : K) : GoodS H B S (tv hB v c) :=
  ⟨unip_mem hH (Nv_sq hB v) (hsp _ (Nv_sp hB v)) c, tv_mem_iso hB v c,
    fun s hs => tv_fix hB c (by rw [bf_swap_alt hB s v, hv s hs, neg_zero])⟩

include hB hH hsp in
theorem step1 {x y : n → K} (hx : x ∈ orthS B S) (hy : y ∈ orthS B S) (h : bf B y x ≠ 0) :
    ∃ u, GoodS H B S u ∧ (u : Matrix n n K) *ᵥ x = y :=
  ⟨_, tv_good hB hH hsp (Submodule.sub_mem _ hy hx) _, tv_move hB h⟩

include hB in
theorem exists_bf_ne (hnd : B.Nondegenerate) (hD : DecS B S) {x : n → K} (hx : x ∈ orthS B S)
    (hx0 : x ≠ 0) : ∃ z ∈ orthS B S, bf B x z ≠ 0 := by
  obtain ⟨z0, hz0⟩ := hnd.exists_not_ortho_of_ne_zero hx0
  obtain ⟨s, hs, hzs⟩ := hD z0
  refine ⟨z0 - s, hzs, ?_⟩
  have h0 : bf B x s = 0 := by rw [bf_swap_alt hB s x, bf_span_left hx hs, neg_zero]
  rw [bf_sub_right, h0, sub_zero]
  exact hz0

include hB in
theorem exists_bf_ne₂ (hnd : B.Nondegenerate) (hD : DecS B S) {x y : n → K}
    (hx : x ∈ orthS B S) (hy : y ∈ orthS B S) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ z ∈ orthS B S, bf B x z ≠ 0 ∧ bf B y z ≠ 0 := by
  obtain ⟨z1, hz1, h1⟩ := exists_bf_ne hB hnd hD hx hx0
  obtain ⟨z2, hz2, h2⟩ := exists_bf_ne hB hnd hD hy hy0
  by_cases a : bf B y z1 = 0
  · by_cases b : bf B x z2 = 0
    · refine ⟨z1 + z2, Submodule.add_mem _ hz1 hz2, ?_, ?_⟩
      · rw [bf_add_right, b, add_zero]; exact h1
      · rw [bf_add_right, a, zero_add]; exact h2
    · exact ⟨z2, hz2, b, h2⟩
  · exact ⟨z1, hz1, h1, a⟩

include hB hH hsp in
theorem vec_trans (hnd : B.Nondegenerate) (hD : DecS B S) {x y : n → K} (hx : x ∈ orthS B S)
    (hy : y ∈ orthS B S) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ u, GoodS H B S u ∧ (u : Matrix n n K) *ᵥ x = y := by
  obtain ⟨z, hz, hxz, hyz⟩ := exists_bf_ne₂ hB hnd hD hx hy hx0 hy0
  obtain ⟨u1, hu1, h1⟩ := step1 hB hH hsp hx hz (by rw [bf_swap_alt hB x z]; exact neg_ne_zero.2 hxz)
  obtain ⟨u2, hu2, h2⟩ := step1 hB hH hsp hz hy hyz
  exact ⟨u2 * u1, hu2.mul hu1, by rw [mulVec_mul_GL, h1, h2]⟩

include hB hH hsp in
theorem fix_move_A {e f₁ f' : n → K} (_he : e ∈ orthS B S) (hf₁ : f₁ ∈ orthS B S)
    (hf' : f' ∈ orthS B S) (h1 : bf B e f₁ = 1) (h2 : bf B e f' = 1) (h3 : bf B f' f₁ ≠ 0) :
    ∃ u, GoodS H B S u ∧ (u : Matrix n n K) *ᵥ e = e ∧ (u : Matrix n n K) *ᵥ f₁ = f' := by
  refine ⟨_, tv_good hB hH hsp (Submodule.sub_mem _ hf' hf₁) _, tv_fix hB _ ?_, tv_move hB h3⟩
  rw [bf_sub_left, bf_swap_alt hB e f', bf_swap_alt hB e f₁, h1, h2, sub_self]

include hB hH hsp in
theorem fix_move {e f₁ f' : n → K} (he : e ∈ orthS B S) (hf₁ : f₁ ∈ orthS B S)
    (hf' : f' ∈ orthS B S) (h1 : bf B e f₁ = 1) (h2 : bf B e f' = 1) :
    ∃ u, GoodS H B S u ∧ (u : Matrix n n K) *ᵥ e = e ∧ (u : Matrix n n K) *ᵥ f₁ = f' := by
  by_cases h3 : bf B f' f₁ = 0
  · set f₂ := f₁ + e
    have hf₂ : f₂ ∈ orthS B S := Submodule.add_mem _ hf₁ he
    have hu1 := tv_good hB hH hsp he (1 : K) (S := S)
    have m1 : ((tv hB e 1 : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ e = e :=
      tv_fix hB 1 (bf_self_alt hB e)
    have m2 : ((tv hB e 1 : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ f₁ = f₂ := by
      rw [tv_mulVec, h1, one_mul, one_smul]
    have h1' : bf B e f₂ = 1 := by rw [bf_add_right, h1, bf_self_alt hB, add_zero]
    have h3' : bf B f' f₂ ≠ 0 := by
      rw [bf_add_right, h3, zero_add, bf_swap_alt hB e f', h2]
      exact neg_ne_zero.2 one_ne_zero
    obtain ⟨u2, hu2, k1, k2⟩ := fix_move_A hB hH hsp he hf₂ hf' h1' h2 h3'
    exact ⟨u2 * tv hB e 1, hu2.mul hu1, by rw [mulVec_mul_GL, m1, k1],
      by rw [mulVec_mul_GL, m2, k2]⟩
  · exact fix_move_A hB hH hsp he hf₁ hf' h1 h2 h3

include hB hH hsp in
/-- Transitivity on hyperbolic pairs of `orthS B S`, by elements fixing `S`. -/
theorem pair_trans (hnd : B.Nondegenerate) (hD : DecS B S) {e f e' f' : n → K}
    (he : e ∈ orthS B S) (hf : f ∈ orthS B S) (he' : e' ∈ orthS B S) (hf' : f' ∈ orthS B S)
    (hef : bf B e f = 1) (hef' : bf B e' f' = 1) :
    ∃ u, GoodS H B S u ∧ (u : Matrix n n K) *ᵥ e = e' ∧ (u : Matrix n n K) *ᵥ f = f' := by
  have he0 : e ≠ 0 := by rintro rfl; rw [bf_zero_left] at hef; exact zero_ne_one hef
  have he0' : e' ≠ 0 := by rintro rfl; rw [bf_zero_left] at hef'; exact zero_ne_one hef'
  obtain ⟨u1, hu1, k1⟩ := vec_trans hB hH hsp hnd hD he he' he0 he0'
  have hf₁ := iso_orthS hu1.2.1 hu1.2.2 hf
  have h1 : bf B e' ((u1 : Matrix n n K) *ᵥ f) = 1 := by rw [← k1, bf_iso hu1.2.1, hef]
  obtain ⟨u2, hu2, k2, k3⟩ := fix_move hB hH hsp he' hf₁ hf' h1 hef'
  exact ⟨u2 * u1, hu2.mul hu1, by rw [mulVec_mul_GL, k1, k2], by rw [mulVec_mul_GL, k3]⟩

end Trans

end RamanujanPetersson.AlgGrpB

end


