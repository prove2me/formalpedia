-- Prove2me | Definitions.Def_DetDLP_S8B_MomentCompare
-- name    : DetDLP_S8B_MomentCompare
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T03:59:19.44899+00:00
-- url     : https://prove2.me/theorems/872640c8-583b-4b18-ac07-dc485dd69929
-- title:
--   Stage I exact natural-number comparison of child moment averages
-- statement:
--   Given the numerator and denominator of the common expected size and both child moment tables, the Boolean comparison selects the right child exactly when the left has zero mass or the right has positive mass and strictly lower signed cross-product. The implementation uses polynomial-time natural-number arithmetic without truncated subtraction. A nonempty tie goes left.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Theorems.Thm_Groundwork_PolyT_mul
import Definitions.Def_ToTuring_Lib_Nat1
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_Groundwork_PolyT_const

set_option autoImplicit false
namespace DetDLP.S8B
open Groundwork Groundwork.PolyT

/-- `d = p^m` and `u = (n*T)^m` are the common denominator and numerator of μ.
The two summands below encode opposite signs, without using truncated subtraction. -/
def posPart (d g B J : ℕ) := d * d * (g * J + 64 * B)
def negPart (d u A : ℕ) := 128 * d * u * A

def momentRight (d u g h0 a0 b0 j0 h1 a1 b1 j1 : ℕ) : Bool :=
  if h0 = 0 then true else if h1 = 0 then false else
    decide (posPart d g b1 j1 * h0 + negPart d u a0 * h1 <
            posPart d g b0 j0 * h1 + negPart d u a1 * h0)

attribute [local fun_prop] Groundwork.PolyT.mul Groundwork.PolyT.const P2M_Groundwork_PolyT_ite__226169acf219

theorem momentRight_poly {α : Type} [Enc α] {d u g h0 a0 b0 j0 h1 a1 b1 j1 : α → ℕ}
    (hd : PolyT d) (hu : PolyT u) (hg : PolyT g) (hh0 : PolyT h0) (ha0 : PolyT a0)
    (hb0 : PolyT b0) (hj0 : PolyT j0) (hh1 : PolyT h1) (ha1 : PolyT a1)
    (hb1 : PolyT b1) (hj1 : PolyT j1) : PolyT (fun x => momentRight (d x) (u x) (g x)
      (h0 x) (a0 x) (b0 x) (j0 x) (h1 x) (a1 x) (b1 x) (j1 x)) := by
  unfold momentRight posPart negPart
  fun_prop

/-- Equivalent signed cross-product test, including the exact priority of zero counts. -/
theorem momentRight_spec (d u g h0 a0 b0 j0 h1 a1 b1 j1 : ℕ) :
    momentRight d u g h0 a0 b0 j0 h1 a1 b1 j1 = true ↔
      h0 = 0 ∨ (h1 ≠ 0 ∧
        ((posPart d g b1 j1 : ℤ) - negPart d u a1) * (h0 : ℤ) <
        ((posPart d g b0 j0 : ℤ) - negPart d u a0) * (h1 : ℤ)) := by
  by_cases hl : h0 = 0 <;> by_cases hr : h1 = 0 <;> simp [momentRight, hl, hr]
  rw [sub_mul, sub_mul, ← Nat.cast_lt (α := ℤ)]
  push_cast
  omega

end DetDLP.S8B


