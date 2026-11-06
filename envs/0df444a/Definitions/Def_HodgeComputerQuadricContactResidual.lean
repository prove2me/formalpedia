-- Prove2me | Definitions.Def_HodgeComputerQuadricContactResidual
-- name    : HodgeComputerQuadricContactResidual
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:02:50.229354+00:00
-- url     : https://prove2.me/theorems/248375b8-74b3-4be2-977a-aef72b24d29f
-- title:
--   Quadric contact · residual sector — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Quadric contact · residual sector”](https://hodge.computer/#case/quadric-contact-residual), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=F_*+t\cdot X_0\cdot X_1\cdot Y_0\cdot Y_1\cdot(X_2^2+2\cdot Y_2^2).
--   $$
--
--   $$
--   q=1,\qquad A=X_{0}^{3} Y_{0}^{3}.
--   $$
--
--   where
--
--   $$
--   \begin{aligned}
--   F_0&=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6 \\
--   t&=\frac{5}{7} \\
--   F_*&=F_0+5\cdot\bigl(X_0^4\cdot Y_0^2+X_0^2\cdot Y_0^4+(X_0^2+Y_0^2)\cdot Q\bigr) \\
--   Q&=X_1^2\cdot Y_1^2+X_1\cdot X_2\cdot Y_1\cdot Y_2+X_2^2\cdot Y_2^2
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/quadric-contact-residual/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.QuadricContactResidual
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := (((((((((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + (((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (4 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ)))) + ((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (2 : ℕ)))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6)))) + ((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ)))) + (((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (4 : ℕ)))) + (((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + (((((((10 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + ((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (2 : ℕ)))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6)))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + ((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ)))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ)))
def q : ℕ := 1
end HodgeComputer.QuadricContactResidual


