-- Prove2me | Definitions.Def_KeystoneDoubling
-- name    : KeystoneDoubling
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:03.44001+00:00
-- url     : https://prove2.me/theorems/3c846a55-7899-41c4-bf76-715768cce6c0
-- title:
--   Homogeneous x-coordinate doubling formulas
-- statement:
--   For a Weierstrass curve with invariants $b_2,b_4,b_6,b_8$, the file defines the homogeneous doubling pair $$N=X^4-b_4X^2Z^2-2b_6XZ^3-b_8Z^4,$$ $$D=4X^3Z+b_2X^2Z^2+2b_4XZ^3+b_6Z^4.$$ This pair represents the projective x-coordinate of $2P$ and is matched to the even division-polynomial formulas.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
/-!
# Keystone doubling — the division-polynomial duplication identities

`PsiSq_two_mul : W.ΨSq (2*m) = dupDenH (W.Φ m) (W.ΨSq m)` and the numerator analogue. These are the
x-coordinate duplication formulas; via a Ψ₃-saturated `linear_combination` over `prePsi_adjacent_somos`
(Adj) + `preΨ_invariant` (Inv, = Ward `InvarRel` on ψ) + `b_relation` (bRel), then cancel `Ψ₃≠0`.
All four parity×num/den cofactor certificates were CAS-verified (see `KEYSTONE_DOUBLING_CERT.md`).
-/

namespace WeierstrassCurve

open Polynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Homogeneous x-doubling numerator on `R[X]` representatives. -/
@[expose] public noncomputable def dupNumP (Xc Zc : R[X]) : R[X] :=
  Xc ^ 4 - C W.b₄ * Xc ^ 2 * Zc ^ 2 - C (2 * W.b₆) * Xc * Zc ^ 3 - C W.b₈ * Zc ^ 4

/-- Homogeneous x-doubling denominator on `R[X]` representatives. -/
@[expose] public noncomputable def dupDenP (Xc Zc : R[X]) : R[X] :=
  C 4 * Xc ^ 3 * Zc + C W.b₂ * Xc ^ 2 * Zc ^ 2 + C (2 * W.b₄) * Xc * Zc ^ 3 + C W.b₆ * Zc ^ 4

end WeierstrassCurve


