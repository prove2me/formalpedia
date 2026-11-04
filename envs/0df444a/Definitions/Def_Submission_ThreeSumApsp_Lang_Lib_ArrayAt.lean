-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
-- name    : Submission_ThreeSumApsp_Lang_Lib_ArrayAt
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:24.101596+00:00
-- url     : https://prove2.me/theorems/91821164-119a-49ae-a940-21d938a2304c
-- title:
--   Array At
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
@[expose] public section
namespace Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
structure ListAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  below : a + N ≤ top := by
    first
    | omega
    | ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
structure ArrayAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N : ℕ) (U : ℤ) (top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  bound : AbsLe l U
  below : a + N ≤ top := by
    first
    | omega
    | ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
namespace ListAt
end ListAt
namespace ArrayAt
end ArrayAt
structure IndexAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) (N p top : ℕ) : Prop where
  len : l.length = N
  seg : SegN μ a l
  lt : ∀ x ∈ l, x < p
  below : a + N ≤ top := by
    first
    | omega
    | ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
namespace IndexAt
variable {l : List ℕ} {p : ℕ}
end IndexAt
end Light


