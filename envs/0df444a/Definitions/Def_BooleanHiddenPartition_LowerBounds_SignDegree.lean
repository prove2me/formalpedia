-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_SignDegree
-- name    : BooleanHiddenPartition_LowerBounds_SignDegree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:20:53.234577+00:00
-- url     : https://prove2.me/theorems/29116b3c-7049-4ca4-bd2d-58afb438aa24
-- title:
--   Real-polynomial sign representation and sign degree
-- statement:
--   For a Boolean function f on the k-cube, SignRepresents f p requires a genuine real multivariate polynomial p to have strictly the same sign as f at every cube point. Sign degree is the least total degree among these polynomials.
--
--   $$p(x)f(x)>0\quad\hbox{for every }x,\qquad \deg_\pm(f)=\min_{p\text{ sign-represents }f}\deg(p).$$
--
--   The infimum is taken in WithTop Nat, whose empty infimum is infinity. Every Boolean function has a polynomial interpolation, so the source instances have a finite attained minimum. This definition does not use the dual witness or the desired communication bound. Zero arity is also meaningful: the cube is a singleton and the degree is zero.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), pp. 3, 14, definitions and conventions.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Scalar

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

def SignRepresents {k : ℕ} (f : Cube k → Bool) (p : MvPolynomial (Fin k) ℝ) : Prop :=
  ∀ x, 0 < MvPolynomial.eval (fun j => sign (x j)) p * sign (f x)

/-- The least actual polynomial total degree. Empty sets have value infinity,
not a fabricated zero; Boolean interpolation makes this set nonempty. -/
def signDegree {k : ℕ} (f : Cube k → Bool) : WithTop ℕ :=
  sInf {d | ∃ p : MvPolynomial (Fin k) ℝ, SignRepresents f p ∧
    (p.totalDegree : WithTop ℕ) = d}

end

end BooleanHiddenPartition.LowerBounds


