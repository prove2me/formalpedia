-- Prove2me | Definitions.Def_KeystoneResultantCerts
-- name    : KeystoneResultantCerts
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:06:21.091648+00:00
-- url     : https://prove2.me/theorems/b0b58348-16f9-4714-aecd-5a01edff3ecd
-- title:
--   Bézout cofactors for low division-polynomial resultants
-- statement:
--   This certificate-only file defines the large explicit cofactor polynomials associated with the indices $3$ and $4$ and packages the resultant identities needed to separate the low division-polynomial strata. The resulting certificates rule out the simultaneous vanishing patterns that would contradict nonsingularity of the Weierstrass curve. They are isolated here so the expensive algebraic certificates can be compiled once and reused by the coprimality capstone.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_DivisionBezoutFourTermsA
import Definitions.Def_DivisionBezoutFourTermsB
import Definitions.Def_DivisionBezoutThreeTermsA
import Definitions.Def_DivisionBezoutThreeTermsB
import Definitions.Def_DivisionBezoutThreeTermsC
import Definitions.Def_WardSomos
/-! # Keystone resultant/Bezout nonsingularity certificates (avenue c)

Isolated from KeystoneCoprimality for olean caching: the P3P4 bezout `ring1` is large
(~250-term cofactor); this file builds once. Exports the three public nonsingularity
lemmas used by the coprimality capstone. -/

open Polynomial
open scoped Polynomial
open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

def divisionBezoutThree (W : WeierstrassCurve k) : k[X] :=
  divisionBezoutThreeTerm0 W + divisionBezoutThreeTerm1 W + divisionBezoutThreeTerm2 W + divisionBezoutThreeTerm3 W + divisionBezoutThreeTerm4 W + divisionBezoutThreeTerm5 W + divisionBezoutThreeTerm6 W + divisionBezoutThreeTerm7 W + divisionBezoutThreeTerm8 W

def divisionBezoutFour (W : WeierstrassCurve k) : k[X] :=
  divisionBezoutFourTerm0 W + divisionBezoutFourTerm1 W + divisionBezoutFourTerm2 W + divisionBezoutFourTerm3 W + divisionBezoutFourTerm4 W + divisionBezoutFourTerm5 W

end

end WeierstrassCurve


