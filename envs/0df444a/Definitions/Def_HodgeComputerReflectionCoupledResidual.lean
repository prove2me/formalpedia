-- Prove2me | Definitions.Def_HodgeComputerReflectionCoupledResidual
-- name    : HodgeComputerReflectionCoupledResidual
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:03:07.339194+00:00
-- url     : https://prove2.me/theorems/3e894792-1352-4e2f-bddb-8e1007629e53
-- title:
--   Reflection · complementary character — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Reflection · complementary character”](https://hodge.computer/#case/reflection-coupled-residual), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=F_0+t\cdot P.
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
--   F_0&=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6 \\
--   t&=\frac{5}{7} \\
--   P&=X_{0}^{3} \cdot X_{1} \cdot Y_{0} \cdot Y_{1} + X_{0} \cdot X_{1} \cdot Y_{0}^{3} \cdot Y_{1} + X_{0} \cdot X_{1} \cdot Y_{0}^{2} \cdot Y_{2}^{2} + 2 \cdot X_{0} \cdot X_{1} \cdot Y_{1}^{2} \cdot Y_{2}^{2} + 3 \cdot X_{0} \cdot X_{2}^{3} \cdot Y_{0} \cdot Y_{1} + 2 \cdot X_{1}^{3} \cdot X_{2} \cdot Y_{0} \cdot Y_{1} + X_{1} \cdot X_{2} \cdot Y_{0} \cdot Y_{1}^{3}
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/reflection-coupled-residual/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.ReflectionCoupledResidual
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := ((((((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((10 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((15 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + ((((((10 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (3 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ)))
def q : ℕ := 1
end HodgeComputer.ReflectionCoupledResidual


