-- Prove2me | Definitions.Def_PsiInvariant
-- name    : PsiInvariant
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:59.61629+00:00
-- url     : https://prove2.me/theorems/83cfae42-2472-4663-999e-e8e1a8c3b849
-- title:
--   Ward’s invariant numerator and denominator for division polynomials
-- statement:
--   For a Weierstrass curve $W$ and an integer $m$, the file defines a parity-adjusted numerator $$N_m^{ψ}=ψ_{m+2}ψ_{m-1}^2+ψ_{m+1}^2ψ_{m-2}+ε_mψ_m^3$$ and denominator $$D_m^{ψ}=ψ_{m+1}ψ_mψ_{m-1},$$ where $ε_m$ is the appropriate square-division-polynomial factor for even $m$ and $1$ for odd $m$. These carriers translate the Ward–Somos conserved quantity into the division-polynomial setting.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_WardSomos
open Polynomial
open scoped Polynomial
open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

@[expose] public def preΨInvN (W : WeierstrassCurve R) (m : ℤ) : R[X] :=
  W.preΨ (m + 2) * W.preΨ (m - 1) ^ 2
    + W.preΨ (m + 1) ^ 2 * W.preΨ (m - 2)
    + (if Even m then W.Ψ₂Sq ^ 2 else 1) * W.preΨ m ^ 3

@[expose] public def preΨInvD (W : WeierstrassCurve R) (m : ℤ) : R[X] :=
  W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)

end

end WeierstrassCurve


