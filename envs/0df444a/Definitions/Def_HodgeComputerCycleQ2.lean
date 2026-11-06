-- Prove2me | Definitions.Def_HodgeComputerCycleQ2
-- name    : HodgeComputerCycleQ2
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T21:37:17.965206+00:00
-- url     : https://prove2.me/theorems/ae654700-647d-4a97-a08a-d1243174ea5f
-- title:
--   Cyclic coupling · pole order two — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Cyclic coupling · pole order two”](https://hodge.computer/#case/cycle-q2), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=F_0 + \frac{X_{0}^{3} X_{1} Y_{0} Y_{1}}{2} + \frac{X_{0} X_{2}^{3} Y_{0} Y_{2}}{2} + \frac{X_{1}^{3} X_{2} Y_{1} Y_{2}}{2}.
--   $$
--
--   $$
--   q=2,\qquad A=X_{0}^{2} X_{1}^{2} X_{2}^{3} Y_{0}^{2} Y_{1}^{2} Y_{2}.
--   $$
--
--   where
--
--   $$
--   \begin{aligned}
--   F_0&=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/cycle-q2/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.CycleQ2
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := ((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + ((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 2 : ℂ))) + (((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 2 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + ((((((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ)) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 2 : ℂ))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ)) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6)))
def q : ℕ := 2
end HodgeComputer.CycleQ2


