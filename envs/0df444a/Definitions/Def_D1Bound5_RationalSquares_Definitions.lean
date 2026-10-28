-- Prove2me | Definitions.Def_D1Bound5_RationalSquares_Definitions
-- name    : D1Bound5_RationalSquares_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:07:59.893014+00:00
-- url     : https://prove2.me/theorems/1524489d-ee34-47ce-a598-b2d5aa4f6826
-- title:
--   Rational Squares
-- statement:
--   A square which is a rational integer is either the square of a rational integer or comes from a trace-zero, purely imaginary root. No assumptions on the quadratic coordinate ring are needed. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/RationalSquares.lean, lines 7-36, SHA-256 4cd56ab129029a6551801f8c22878c2598ef5298b732a909ebb1ad48e70f5e58; D1Bound5/RationalSquares.lean, lines 38-56, SHA-256 4cd56ab129029a6551801f8c22878c2598ef5298b732a909ebb1ad48e70f5e58; D1Bound5/RationalSquares.lean, lines 58-67, SHA-256 4cd56ab129029a6551801f8c22878c2598ef5298b732a909ebb1ad48e70f5e58; D1Bound5/RationalSquares.lean, lines 69-84, SHA-256 4cd56ab129029a6551801f8c22878c2598ef5298b732a909ebb1ad48e70f5e58. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5

open QuadInt

/-- A square which is a rational integer is either the square of a
rational integer or comes from a trace-zero, purely imaginary root.
No assumptions on the quadratic coordinate ring are needed. -/
theorem rational_integer_square_cases {tau nu m : ℤ}
    (r : QuadInt tau nu) (hr : r*r = (m : QuadInt tau nu)) :
    (r.im = 0 ∧ r.re*r.re = m) ∨
    (2*r.re+tau*r.im = 0 ∧ 4*m = -discriminant tau nu*r.im^2) := by
  have hre : r.re*r.re-nu*r.im*r.im = m := by
    have h := congrArg QuadraticAlgebra.re hr
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast] at h
    calc
      r.re*r.re-nu*r.im*r.im = r.re*r.re+(-nu)*r.im*r.im := by ring
      _ = m := h
  have him : (2*r.re+tau*r.im)*r.im = 0 := by
    have h := congrArg QuadraticAlgebra.im hr
    simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast] at h
    nlinarith only [h]
  rcases mul_eq_zero.mp him with he | hi
  · right
    refine ⟨he, ?_⟩
    have ht : 4*r.re*r.re-tau^2*r.im^2=0 := by
      calc
        _ = (2*r.re+tau*r.im)*(2*r.re-tau*r.im) := by ring
        _ = 0 := by rw [he]; ring
    dsimp [discriminant]
    nlinarith only [hre, ht]
  · left
    refine ⟨hi, ?_⟩
    rw [hi] at hre
    simpa using hre

/-- A negative rational integer square has a purely imaginary root.
Its imaginary coordinate obeys the discriminant identity and parity. -/
theorem negative_integer_square_constraint {tau nu m : ℤ} (hm : m < 0)
    (hr : ∃ r : QuadInt tau nu, r*r = (m : QuadInt tau nu)) :
    ∃ y : ℤ, y ≠ 0 ∧ (tau*y)%2 = 0 ∧
      4*(-m) = discriminant tau nu*y^2 := by
  obtain ⟨r,hr⟩ := hr
  rcases rational_integer_square_cases r hr with h | h
  · have hnonneg := sq_nonneg r.re
    rcases h with ⟨_,hrm⟩
    nlinarith only [hm, hnonneg, hrm]
  · rcases h with ⟨he,heq⟩
    refine ⟨r.im, ?_, ?_, ?_⟩
    · intro hz
      rw [hz] at heq
      norm_num at heq
      omega
    · omega
    · nlinarith only [heq]

/-- The trace-zero model requires negative rational squares to be
minus the defining parameter times an integer square. -/
theorem negative_integer_square_trace_zero {nu m : ℤ} (hm : m < 0)
    (hr : ∃ r : QuadInt 0 nu, r*r = (m : QuadInt 0 nu)) :
    ∃ y : ℤ, m = -nu*y^2 := by
  obtain ⟨y,_,_,h⟩ := negative_integer_square_constraint hm hr
  refine ⟨y, ?_⟩
  dsimp [discriminant] at h
  norm_num at h
  nlinarith only [h]

/-- In the half-integral basis with trace one, a negative rational square
is minus the discriminant times an integer square. -/
theorem negative_integer_square_trace_one {nu m : ℤ} (hm : m < 0)
    (hr : ∃ r : QuadInt 1 nu, r*r = (m : QuadInt 1 nu)) :
    ∃ y : ℤ, m = -(4*nu-1)*y^2 := by
  obtain ⟨r,hr⟩ := hr
  rcases rational_integer_square_cases r hr with ⟨_,hrm⟩ | ⟨he,heq⟩
  · have hsq := sq_nonneg r.re
    nlinarith only [hm, hsq, hrm]
  · have hp : r.im % 2 = 0 := by omega
    let y := r.im/2
    have hy : r.im = 2*y := by dsimp [y]; omega
    refine ⟨y, ?_⟩
    rw [hy] at heq
    dsimp [discriminant] at heq
    nlinarith only [heq]



end D1Bound5
end


