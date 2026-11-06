-- Prove2me | Definitions.Def_HodgeComputerKleinCoupledCharacter
-- name    : HodgeComputerKleinCoupledCharacter
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T21:43:05.46321+00:00
-- url     : https://prove2.me/theorems/e48f7576-2aa1-4b5c-b346-d7220b9e4dfb
-- title:
--   Coupled Klein · nontrivial character — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Coupled Klein · nontrivial character”](https://hodge.computer/#case/klein-coupled-character), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=K+Y_0^6+Y_1^6+Y_2^6+t\cdot P.
--   $$
--
--   $$
--   q=1,\qquad A=X_{0}^{3} \cdot Y_{0}^{3}.
--   $$
--
--   where
--
--   $$
--   \begin{aligned}
--   t&=\frac57 \\
--   K&=X_0^5\cdot X_1+X_1^5\cdot X_2+X_2^5\cdot X_0 \\
--   P&=2 \cdot X_{0}^{3} \cdot X_{2} \cdot Y_{1} \cdot Y_{2} + X_{0} \cdot X_{1}^{3} \cdot Y_{0} \cdot Y_{1} + 3 \cdot X_{1} \cdot X_{2}^{3} \cdot Y_{0} \cdot Y_{2}
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/klein-coupled-character/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.KleinCoupledCharacter
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := (((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (5 : ℕ)) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) + ((((((10 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (5 : ℕ)))) + (((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (5 : ℕ)) * (MvPolynomial.X (R := ℂ) (2 : Fin 6)))) + ((((((15 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ)))
def q : ℕ := 1
end HodgeComputer.KleinCoupledCharacter


