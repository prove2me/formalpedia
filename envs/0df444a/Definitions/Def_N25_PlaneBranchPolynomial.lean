-- Prove2me | Definitions.Def_N25_PlaneBranchPolynomial
-- name    : N25_PlaneBranchPolynomial
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:10.811764+00:00
-- url     : https://prove2.me/theorems/f44f06fa-cf42-4048-a7dd-8340ae738737
-- title:
--   The degree-eleven branch polynomial
-- statement:
--   Defines the degree-$11$ polynomial $B(t)$ occurring as the nontrivial branch factor in the discriminant of the quartic plane model, its homogeneous form $B(n,d)$, and its integral coefficient polynomial. These forms are used in branch-locus and numerator–denominator arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
/-! The nontrivial branch polynomial for projection of the plane curve to its first coordinate. -/
namespace N25

/-- The degree-eleven branch factor of the plane quartic discriminant. -/
def planeBranchValue {k : Type*} [CommRing k] (t : k) : k :=
  27*t^11-14*t^10+221*t^9+64*t^8+275*t^7+4*t^6+
    25*t^5+26*t^4+19*t^3-8*t+4

/-- Its homogeneous form, for numerator-denominator arguments. -/
def planeBranchForm {k : Type*} [CommRing k] (n d : k) : k :=
  27*n^11-14*n^10*d+221*n^9*d^2+64*n^8*d^3+275*n^7*d^4+
    4*n^6*d^5+25*n^5*d^6+26*n^4*d^7+19*n^3*d^8-8*n*d^10+4*d^11

/-- The coefficient polynomial over the integers. -/
noncomputable def planeBranchIntPolynomial : Polynomial ℤ := planeBranchValue Polynomial.X

end N25


