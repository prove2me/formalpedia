-- Prove2me | Definitions.Def_HodgeComputerCyclicTripleResidual
-- name    : HodgeComputerCyclicTripleResidual
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:05:12.873973+00:00
-- url     : https://prove2.me/theorems/4c2b8f63-f38b-43ee-9e8d-42ffa69fa7fa
-- title:
--   Cyclic triple cover · complementary character — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Cyclic triple cover · complementary character”](https://hodge.computer/#case/cyclic-triple-residual), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=X_2^6+t\cdot X_2^3\cdot C+H.
--   $$
--
--   $$
--   q=1,\qquad A=X_0^3\cdot Y_0^3.
--   $$
--
--   where
--
--   $$
--   \begin{aligned}
--   t&=\frac57 \\
--   C&=X_{0}^{3} + X_{0} \cdot Y_{1} \cdot Y_{2} + X_{1} \cdot Y_{0} \cdot Y_{1} \\
--   H&=X_{0}^{6} + \frac{5}{7}\cdot X_{0}^{3}\cdot X_{1}\cdot Y_{0}\cdot Y_{1} + \frac{5}{7}\cdot X_{0}^{2}\cdot Y_{0}\cdot Y_{1}\cdot Y_{2}^{2} + \frac{5}{7}\cdot X_{0}\cdot X_{1}\cdot Y_{1}^{3}\cdot Y_{2} + X_{1}^{6} + Y_{0}^{6} + Y_{1}^{6} + Y_{2}^{6}
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/cyclic-triple-residual/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.CyclicTripleResidual
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := (((((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ)))
def q : ℕ := 1
end HodgeComputer.CyclicTripleResidual


