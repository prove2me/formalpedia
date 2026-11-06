-- Prove2me | Definitions.Def_HodgeComputerOffPaired
-- name    : HodgeComputerOffPaired
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:01:50.481953+00:00
-- url     : https://prove2.me/theorems/d588ed3d-13bd-4b95-9038-7154b8db7406
-- title:
--   Broken paired signs — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Broken paired signs”](https://hodge.computer/#case/off-paired), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=F_0 + \frac{X_{0}^{3} X_{1} Y_{0} Y_{1}}{2} + \frac{X_{0}^{2} X_{1} X_{2} Y_{0} Y_{2}}{3} + \frac{X_{1}^{3} X_{2} Y_{1} Y_{2}}{2}.
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
--   F_0&=X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/off-paired/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.OffPaired
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := ((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + ((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 2 : ℂ))) + (((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ)) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 3 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + ((((((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ)) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 2 : ℂ))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ)))
def q : ℕ := 1
end HodgeComputer.OffPaired


