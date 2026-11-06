-- Prove2me | Definitions.Def_HodgeComputerOneReflectionSkew
-- name    : HodgeComputerOneReflectionSkew
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:02:52.098786+00:00
-- url     : https://prove2.me/theorems/9b14fd6c-bf8f-4eac-ace4-3c9592be926b
-- title:
--   One reflection · skew coupling — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“One reflection · skew coupling”](https://hodge.computer/#case/one-reflection-skew), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=F_0 + X_0^3 X_1 Y_0 Y_1 + X_1^3 X_2 Y_0 Y_1 + \frac17 X_0 X_1 Y_0 Y_1 (Y_0^2-Y_1^2).
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
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/one-reflection-skew/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.OneReflectionSkew
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := (((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + (((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6)))) + (((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) - (((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (3 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + (((((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ)) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6)))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := (((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ)))
def q : ℕ := 1
end HodgeComputer.OneReflectionSkew


