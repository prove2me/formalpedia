-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_ProjectiveLine
-- name    : IntegerMatrixMortality_FixedImage_ProjectiveLine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:29:03.056204+00:00
-- url     : https://prove2.me/theorems/faf026b0-fdf7-431a-a86b-51b7c10e208d
-- title:
--   Rational projective points and actual matrix actions
-- statement:
--   Represent the rational projective line by ℚ together with an extra point ∞. A finite coordinate z denotes the line spanned by (z,1), and ∞ denotes the line spanned by (1,0). For A=(a b;c d), define its projective action, on nonsingular matrices, by
--
--   $$A(z)=\frac{az+b}{cz+d},\qquad A(\infty)=a/c,$$
--
--   interpreting a zero denominator as ∞. In particular poles never become the default rational value zero. Projective reachability in G means that some finite unrestricted matrix word, including the empty word, sends its source to its target.
--
--   The chart and the actual subspace model are both available, allowing arbitrary source and target lines, including ∞.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), §3, PDF p. 5 / printed p. 3

import Mathlib
import Definitions.Def_IntegerMatrixMortality_FixedImage_MatrixMortality

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage
/-- The full rational projective chart; none denotes infinity. -/
abbrev ProjectivePoint := Option ℚ

def projectiveAction (A : QMat) : ProjectivePoint → ProjectivePoint
  | none => if A 1 0 = 0 then none else some (A 0 0 / A 1 0)
  | some z => if A 1 0 * z + A 1 1 = 0 then none
      else some ((A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1))

def chartVector : ProjectivePoint → QVec
  | none => ![1,0]
  | some z => ![z,1]

def chartLine (z : ProjectivePoint) : Submodule ℚ QVec := Submodule.span ℚ {chartVector z}

def lineReach {K : Type} [Semiring K] (cast : K →+* ℚ)
    (G : Set (Matrix (Fin 2) (Fin 2) K)) (s t : ProjectivePoint) : Prop :=
  ∃ w : List (Matrix (Fin 2) (Fin 2) K), (∀ A ∈ w, A ∈ G) ∧
    projectiveAction ((wordMatrix w).map cast) s = t

end IntegerMatrixMortality.FixedImage


