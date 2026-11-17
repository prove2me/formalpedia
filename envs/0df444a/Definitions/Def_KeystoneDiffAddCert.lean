-- Prove2me | Definitions.Def_KeystoneDiffAddCert
-- name    : KeystoneDiffAddCert
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:57.061414+00:00
-- url     : https://prove2.me/theorems/3dd6e382-c5e9-433c-a5ad-33ff5d5147ff
-- title:
--   Homogeneous differential-addition formulas for x-coordinates
-- statement:
--   For polynomial representatives $(X_0,Z_0)$ and $(X_1,Z_1)$, the file defines $$δ=X_0Z_1-X_1Z_0,$$ the homogeneous numerator $S$ for the sum of the two complementary x-coordinates, and the differential-addition pair $$N=S-δ^2X,   D=δ^2.$$ These polynomials are the certificate-level formulas that recover $x(A+B)$ from $x(A)$, $x(B)$, and $x(A-B)$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardSomos
/-!
# Keystone differential addition — the x-only diff-add duplication identity (odd index).

`ΨSq (2m+1) = deltaP²` (definitional, `ΨSq_odd`) and the numerator analogue
`Φ (2m+1) = sumNumP − deltaP²·X` via a Ψ₃-saturated `linear_combination` over
`prePsi_adjacent_somos` (Adj) + `preΨ_invariant` (Inv) at m and m+1 + `b_relation` (bRel),
then cancel `Ψ₃≠0`.  Design: ChatGPT dm1 git-drop a3191d16; cofactors CAS-extracted here.
-/

open Polynomial
open scoped Polynomial
open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `deltaP = X0·Z1 − X1·Z0` on `R[X]` representatives. -/
@[expose] public noncomputable def deltaP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  X0 * Z1 - X1 * Z0

/-- Homogeneous numerator for `x₊ + x₋` on `R[X]` representatives. -/
@[expose] public noncomputable def sumNumP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  C (2 : R) * X0 * X1 * (X0 * Z1 + X1 * Z0)
    + C W.b₂ * X0 * X1 * Z0 * Z1
    + C W.b₄ * Z0 * Z1 * (X0 * Z1 + X1 * Z0)
    + C W.b₆ * Z0 ^ 2 * Z1 ^ 2

/-- x-only differential-addition numerator on representatives. -/
@[expose] public noncomputable def diffAddNumP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  sumNumP W X0 Z0 X1 Z1 - (deltaP W X0 Z0 X1 Z1) ^ 2 * X

/-- x-only differential-addition denominator on representatives. -/
@[expose] public noncomputable def diffAddDenP (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) : R[X] :=
  (deltaP W X0 Z0 X1 Z1) ^ 2

end

end WeierstrassCurve


