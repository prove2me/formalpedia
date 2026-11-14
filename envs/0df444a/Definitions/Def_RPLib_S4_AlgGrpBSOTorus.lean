-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpBSOTorus
-- name    : RPLib_S4_AlgGrpBSOTorus
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:56:12.077514+00:00
-- url     : https://prove2.me/theorems/714f512d-60c2-40ec-94c1-d73be7409515
-- title:
--   Larsen's alternative library: the split torus of a hyperbolic plane from Eichler elements
-- statement:
--   `B` symmetric, char 0. Let `(e, f)` be a hyperbolic pair (`B(e, e) = B(f, f) = 0`, `B(e, f) = 1`)
--   and `z ⊥ e, f` with `B(z, z) = -2`. With `X c = eich e z c`, `Y c = eich f z c` and `a b = 1`,
--   `Wl a b = X(a) Y(-b) X(a)` maps `e ↦ b² f`, `f ↦ a² e`, `z ↦ -z` and fixes `{e, f, z}^⊥`;
--   `tor a b = Wl a b * Wl 1 1` maps `e ↦ a² e`, `f ↦ b² f` and fixes every `x ⊥ e, f` (`tor_fix`).
--   It lies in every closed `H` with `so(B) ⊆ Lie H`, preserves `B` and has determinant one
--   (`tor_good`).
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpBSO

/-!
# S4-AlgGrpB, file SOTorus: the split torus of a hyperbolic plane from Eichler elements (O5b-SO part 3)

`B` symmetric, char 0. Let `(e, f)` be a hyperbolic pair (`B(e, e) = B(f, f) = 0`, `B(e, f) = 1`)
and `z ⊥ e, f` with `B(z, z) = -2`. With `X c = eich e z c`, `Y c = eich f z c` and `a b = 1`,
`Wl a b = X(a) Y(-b) X(a)` maps `e ↦ b² f`, `f ↦ a² e`, `z ↦ -z` and fixes `{e, f, z}^⊥`;
`tor a b = Wl a b * Wl 1 1` maps `e ↦ a² e`, `f ↦ b² f` and fixes every `x ⊥ e, f` (`tor_fix`).
It lies in every closed `H` with `so(B) ⊆ Lie H`, preserves `B` and has determinant one
(`tor_good`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpB

open RamanujanPetersson.AlgGrpA

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

section Torus

variable [CharZero K] {B : Matrix n n K}

theorem eichA_y (hB : Bᵀ = B) {y w : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0) (c : K) :
    ((eich hB hyy hyw c : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ y = y :=
  eich_fix hB hyy hyw c hyy (by rw [bf_swap_sym hB y w, hyw])

theorem eichA_p (hB : Bᵀ = B) {y w p : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0)
    (hyp : bf B y p = 1) (hwp : bf B w p = 0) (hww : bf B w w = -2) (c : K) :
    ((eich hB hyy hyw c : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ p =
      p + c • w + c ^ 2 • y := by
  have hc : c ^ 2 * (2 : K)⁻¹ * (-2 * 1) = -(c ^ 2) := by
    have h2 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
    linear_combination (-(c ^ 2)) * h2
  rw [eich_mulVec, hyp, hwp, hww, hc]
  module

theorem eichA_w (hB : Bᵀ = B) {y w : n → K} (hyy : bf B y y = 0) (hyw : bf B y w = 0)
    (hww : bf B w w = -2) (c : K) :
    ((eich hB hyy hyw c : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ w =
      w + (2 * c) • y := by
  rw [eich_mulVec, hyw, hww]
  module

/-- `Wl a b = X(a) Y(-b) X(a)` with `X = eich e z`, `Y = eich f z`. -/
def Wl (hB : Bᵀ = B) {e f z : n → K} (hee : bf B e e = 0) (hff : bf B f f = 0)
    (hez : bf B e z = 0) (hfz : bf B f z = 0) (a b : K) : Matrix.GeneralLinearGroup n K :=
  eich hB hee hez a * eich hB hff hfz (-b) * eich hB hee hez a

/-- The torus element `tor a b = Wl a b * Wl 1 1`: `e ↦ a² e`, `f ↦ b² f`. -/
def tor (hB : Bᵀ = B) {e f z : n → K} (hee : bf B e e = 0) (hff : bf B f f = 0)
    (hez : bf B e z = 0) (hfz : bf B f z = 0) (a b : K) : Matrix.GeneralLinearGroup n K :=
  Wl hB hee hff hez hfz a b * Wl hB hee hff hez hfz 1 1

section Act

variable (hB : Bᵀ = B) {e f z : n → K} (hee : bf B e e = 0) (hff : bf B f f = 0)
  (hez : bf B e z = 0) (hfz : bf B f z = 0) (hef : bf B e f = 1) (hzz : bf B z z = -2)

include hef hzz in
theorem wl_e {a b : K} (hab : a * b = 1) :
    ((Wl hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ e =
      b ^ 2 • f := by
  have hfe : bf B f e = 1 := by rw [bf_swap_sym hB e f, hef]
  have hze : bf B z e = 0 := by rw [bf_swap_sym hB e z, hez]
  have hzf : bf B z f = 0 := by rw [bf_swap_sym hB f z, hfz]
  rw [Wl, mulVec_mul_GL, mulVec_mul_GL, eichA_y hB hee hez a,
    eichA_p hB hff hfz hfe hze hzz (-b), Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, eichA_y hB hee hez a, eichA_w hB hee hez hzz a,
    eichA_p hB hee hez hef hzf hzz a]
  calc _ = ((a * b - 1) ^ 2) • e + (b * (a * b - 1)) • z + b ^ 2 • f := by module
    _ = b ^ 2 • f := by rw [hab]; simp

include hef hzz in
theorem wl_f {a b : K} (hab : a * b = 1) :
    ((Wl hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ f =
      a ^ 2 • e := by
  have hfe : bf B f e = 1 := by rw [bf_swap_sym hB e f, hef]
  have hze : bf B z e = 0 := by rw [bf_swap_sym hB e z, hez]
  have hzf : bf B z f = 0 := by rw [bf_swap_sym hB f z, hfz]
  have h1 : ((eich hB hff hfz (-b) : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ
      (f + a • z + a ^ 2 • e) = a ^ 2 • e := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      eichA_y hB hff hfz (-b), eichA_w hB hff hfz hzz (-b), eichA_p hB hff hfz hfe hze hzz (-b)]
    calc _ = ((a * b - 1) ^ 2) • f + (-(a * (a * b - 1))) • z + a ^ 2 • e := by module
      _ = a ^ 2 • e := by rw [hab]; simp
  rw [Wl, mulVec_mul_GL, mulVec_mul_GL, eichA_p hB hee hez hef hzf hzz a, h1, Matrix.mulVec_smul,
    eichA_y hB hee hez a]

include hef hzz in
theorem wl_z {a b : K} (hab : a * b = 1) :
    ((Wl hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ z = -z := by
  have hfe : bf B f e = 1 := by rw [bf_swap_sym hB e f, hef]
  have hze : bf B z e = 0 := by rw [bf_swap_sym hB e z, hez]
  have h1 : ((eich hB hff hfz (-b) : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ
      (z + (2 * a) • e) = (2 * a) • e - z := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, eichA_w hB hff hfz hzz (-b),
      eichA_p hB hff hfz hfe hze hzz (-b)]
    calc _ = (2 * a) • e - z + (2 * (1 - a * b)) • z + (2 * b * (a * b - 1)) • f := by module
      _ = (2 * a) • e - z := by rw [hab]; simp
  rw [Wl, mulVec_mul_GL, mulVec_mul_GL, eichA_w hB hee hez hzz a, h1, Matrix.mulVec_sub,
    Matrix.mulVec_smul, eichA_y hB hee hez a, eichA_w hB hee hez hzz a]
  module

theorem wl_perp (a b : K) {x : n → K} (hx1 : bf B e x = 0) (hx2 : bf B f x = 0)
    (hx3 : bf B z x = 0) :
    ((Wl hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x = x := by
  rw [Wl, mulVec_mul_GL, mulVec_mul_GL, eich_fix hB hee hez a hx1 hx3,
    eich_fix hB hff hfz (-b) hx2 hx3, eich_fix hB hee hez a hx1 hx3]

include hef hzz in
theorem tor_e {a b : K} (hab : a * b = 1) :
    ((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ e =
      a ^ 2 • e := by
  rw [tor, mulVec_mul_GL, wl_e hB hee hff hez hfz hef hzz (one_mul 1), Matrix.mulVec_smul,
    wl_f hB hee hff hez hfz hef hzz hab, one_pow, one_smul]

include hef hzz in
theorem tor_f {a b : K} (hab : a * b = 1) :
    ((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ f =
      b ^ 2 • f := by
  rw [tor, mulVec_mul_GL, wl_f hB hee hff hez hfz hef hzz (one_mul 1), Matrix.mulVec_smul,
    wl_e hB hee hff hez hfz hef hzz hab, one_pow, one_smul]

include hef hzz in
theorem tor_z {a b : K} (hab : a * b = 1) :
    ((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ z = z := by
  rw [tor, mulVec_mul_GL, wl_z hB hee hff hez hfz hef hzz (one_mul 1), Matrix.mulVec_neg,
    wl_z hB hee hff hez hfz hef hzz hab, neg_neg]

include hef hzz in
/-- `tor a b` fixes every `x ⊥ e, f`. -/
theorem tor_fix {a b : K} (hab : a * b = 1) {x : n → K} (hx1 : bf B e x = 0)
    (hx2 : bf B f x = 0) :
    ((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x = x := by
  set κ := (2 : K)⁻¹ * bf B z x
  have h3 : bf B z (x + κ • z) = 0 := by
    have h2 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
    rw [bf_add_right, bf_smul_right, hzz]
    linear_combination (-bf B z x) * h2
  have h1 : bf B e (x + κ • z) = 0 := by rw [bf_add_right, bf_smul_right, hx1, hez]; ring
  have h2 : bf B f (x + κ • z) = 0 := by rw [bf_add_right, bf_smul_right, hx2, hfz]; ring
  have hp : ((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ
      (x + κ • z) = x + κ • z := by
    rw [tor, mulVec_mul_GL, wl_perp hB hee hff hez hfz 1 1 h1 h2 h3,
      wl_perp hB hee hff hez hfz a b h1 h2 h3]
  calc ((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ x
      = ((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ
          (x + κ • z) - κ • (((tor hB hee hff hez hfz a b : Matrix.GeneralLinearGroup n K) :
            Matrix n n K) *ᵥ z) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]; abel
    _ = x := by rw [hp, tor_z hB hee hff hez hfz hef hzz hab]; abel

end Act

section Good

attribute [local instance] zarTop

theorem tor_good (hB : Bᵀ = B) {H : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hH : IsClosed (H : Set (Matrix.GeneralLinearGroup n K)))
    (hso : ∀ X : Matrix n n K, Xᵀ * B + B * X = 0 →
      X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)))
    {e f z : n → K} (hee : bf B e e = 0) (hff : bf B f f = 0) (hez : bf B e z = 0)
    (hfz : bf B f z = 0) (a b : K) : GoodSO H B ∅ (tor hB hee hff hez hfz a b) := by
  have h0 : ∀ x : n → K, x ∈ orthS B ∅ := fun _ s hs => absurd hs (Set.notMem_empty s)
  have hX : ∀ c : K, GoodSO H B ∅ (eich hB hee hez c) :=
    fun c => eich_good hB hH hso (h0 e) (h0 z) hee hez c
  have hY : ∀ c : K, GoodSO H B ∅ (eich hB hff hfz c) :=
    fun c => eich_good hB hH hso (h0 f) (h0 z) hff hfz c
  exact (((hX a).mul (hY (-b))).mul (hX a)).mul (((hX 1).mul (hY (-1))).mul (hX 1))

end Good

end Torus

end RamanujanPetersson.AlgGrpB

end


