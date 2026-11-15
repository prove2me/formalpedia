-- Prove2me | Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
-- name    : Kyprianou_Ch03_IsSubmultiplicative
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T13:26:55.580103+00:00
-- url     : https://prove2.me/theorems/d6bdcbf7-87e6-4a4d-bf5c-263527694bb7
-- title:
--   Submultiplicative nonnegative functions (Definition 3.7)
-- statement:
--   A real function g taking nonnegative values is submultiplicative if some strictly positive constant c bounds g(x+y) above by c*g(x)*g(y) for every two real inputs. The nonnegative codomain is encoded as a universal nonnegativity condition.
-- source:
--   Kyprianou (2006), Chapter 3, Definition 3.7, printed p. 77.

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- A nonnegative real-valued submultiplicative function: its value on a sum
is bounded by a fixed positive constant times the product of its values. -/
def IsSubmultiplicative (g : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, 0 ≤ g x) ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ x y : ℝ, g (x + y) ≤ c * g x * g y

end Kyprianou.Ch03


