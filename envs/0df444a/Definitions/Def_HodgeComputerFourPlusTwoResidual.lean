-- Prove2me | Definitions.Def_HodgeComputerFourPlusTwoResidual
-- name    : HodgeComputerFourPlusTwoResidual
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:02:34.017089+00:00
-- url     : https://prove2.me/theorems/c341e3ae-c576-40ec-b4a9-1e27c1910aa3
-- title:
--   Four plus two · suspension remainder — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Four plus two · suspension remainder”](https://hodge.computer/#case/four-plus-two-residual), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=H+B.
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
--   H&=X_{0}^{6} + \frac{5}{7}\cdot X_{0}^{5}\cdot X_{1} + \frac{5}{7}\cdot X_{0}^{3}\cdot X_{1}\cdot Y_{0}\cdot Y_{1} + \frac{10}{7}\cdot X_{0}\cdot X_{1}^{5} + \frac{10}{7}\cdot X_{0}\cdot X_{1}\cdot Y_{0}^{3}\cdot Y_{1} + X_{1}^{6} + Y_{0}^{6} + \frac{5}{7}\cdot Y_{0}^{5}\cdot Y_{1} + \frac{15}{7}\cdot Y_{0}\cdot Y_{1}^{5} + Y_{1}^{6} \\
--   B&=X_{2}^{6} + \frac{15}{7}\cdot X_{2}^{4}\cdot Y_{2}^{2} + \frac{10}{7}\cdot X_{2}^{2}\cdot Y_{2}^{4} + Y_{2}^{6}
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/four-plus-two-residual/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.FourPlusTwoResidual
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := (((((((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + ((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (5 : ℕ))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((10 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (5 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((10 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + ((((15 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (4 : ℕ))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((10 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (4 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (5 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((15 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (5 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ)))
def q : ℕ := 1
end HodgeComputer.FourPlusTwoResidual


