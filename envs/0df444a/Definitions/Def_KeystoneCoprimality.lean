-- Prove2me | Definitions.Def_KeystoneCoprimality
-- name    : KeystoneCoprimality
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:50.380184+00:00
-- url     : https://prove2.me/theorems/eaabf509-1917-4dd8-b1c5-c9259c539a3e
-- title:
--   Coprimality certificates for x-coordinate division polynomials
-- statement:
--   This certificate module names the evaluated division-polynomial factors $p_n(x)$, $Ψ_2(x)^2$, and $Ψ_3(x)$, and packages the odd- and even-index non-common-zero statements for the projective pair $[Φ_n(x):Ψ_n(x)^2]$. In particular, the numerator and denominator cannot vanish simultaneously on an elliptic curve under the stated characteristic assumptions. These certificates guarantee that the x-only ladder representatives are genuine points of $P^1$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardSomos
/-! # Keystone avenue (c): coprimality capstone (propagation + rank-3 + 2-torsion).
Resultant/Bezout certs are in scratch.KeystoneResultantCerts (imported above). -/

open Polynomial
open scoped Polynomial
open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

@[expose] public abbrev pe (W : WeierstrassCurve k) (x : k) (i : ℤ) : k := (W.preΨ i).eval x
@[expose] public abbrev sx (W : WeierstrassCurve k) (x : k) : k := W.Ψ₂Sq.eval x
@[expose] public abbrev c3x (W : WeierstrassCurve k) (x : k) : k := W.Ψ₃.eval x

end

end WeierstrassCurve


