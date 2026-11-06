-- Prove2me | Definitions.Def_HodgeComputerDiagonalPermutation
-- name    : HodgeComputerDiagonalPermutation
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:03:24.49819+00:00
-- url     : https://prove2.me/theorems/8b6203ea-9c81-4085-9069-2caaf82e8550
-- title:
--   Simultaneous permutations · standard sector — instance data
-- statement:
--   The exact fixed polynomials and pole parameter for [“Simultaneous permutations · standard sector”](https://hodge.computer/#case/diagonal-permutation), over $\mathbb C$ with coordinates $X_0,X_1,X_2,Y_0,Y_1,Y_2$:
--
--   $$
--   F=F_0+\frac57\cdot O_1+\frac5{11}\cdot O_2+\frac5{13}\cdot O_3.
--   $$
--
--   $$
--   q=1,\qquad A=X_{0}^{3} \cdot Y_{0}^{3} - X_{1}^{3} \cdot Y_{1}^{3}.
--   $$
--
--   where
--
--   $$
--   \begin{aligned}
--   F_0&=\sum_{i=0}^{2}(X_i^6+Y_i^6) \\
--   \mathcal P&=\{(i,j,k):\{i,j,k\}=\{0,1,2\}\} \\
--   O_1&=\sum_{(i,j,k)\in\mathcal P}X_i^3\cdot X_j\cdot Y_i\cdot Y_j \\
--   O_2&=\sum_{(i,j,k)\in\mathcal P}X_i^3\cdot X_j\cdot Y_k^2 \\
--   O_3&=\sum_{(i,j,k)\in\mathcal P}Y_i^3\cdot Y_j\cdot X_k^2
--   \end{aligned}
--   $$
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/diagonal-permutation/instance.rec

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.DiagonalPermutation
def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := (((((((((((((((((((((((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (6 : ℕ)) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 11 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 11 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 13 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (3 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 13 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 11 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (0 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 11 : ℂ))) + ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (6 : ℕ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 11 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (2 : Fin 6))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 13 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (3 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 13 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (2 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 11 : ℂ))) + ((((((5 : MvPolynomial (Fin 6) ℂ) * (MvPolynomial.X (R := ℂ) (1 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * (MvPolynomial.X (R := ℂ) (5 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ))) + ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (6 : ℕ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (2 : ℕ))) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ))) * (MvPolynomial.X (R := ℂ) (4 : Fin 6))) * MvPolynomial.C (σ := Fin 6) (1 / 13 : ℂ))) + (((((5 : MvPolynomial (Fin 6) ℂ) * ((MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (2 : ℕ))) * (MvPolynomial.X (R := ℂ) (3 : Fin 6))) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (3 : ℕ))) * MvPolynomial.C (σ := Fin 6) (1 / 13 : ℂ))) + ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (6 : ℕ))) + ((MvPolynomial.X (R := ℂ) (5 : Fin 6)) ^ (6 : ℕ)))
def A : HodgeComputer.AmbientPoly n := ((((MvPolynomial.X (R := ℂ) (0 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (3 : Fin 6)) ^ (3 : ℕ))) - (((MvPolynomial.X (R := ℂ) (1 : Fin 6)) ^ (3 : ℕ)) * ((MvPolynomial.X (R := ℂ) (4 : Fin 6)) ^ (3 : ℕ))))
def q : ℕ := 1
end HodgeComputer.DiagonalPermutation


