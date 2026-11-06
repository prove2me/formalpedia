-- Prove2me | Definitions.Def_HodgeComputerFermat
-- name    : HodgeComputerFermat
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-05T22:23:09.593951+00:00
-- url     : https://prove2.me/theorems/b9686eaa-7dd8-4480-aa99-c67c75253d3e
-- title:
--   The Fermat sextic and odd sources
-- statement:
--   Set $n=5$, $d=6$, and $F=\sum_{i=0}^{5}z_i^6$, with $z=(X_0,X_1,X_2,Y_0,Y_1,Y_2)$. A polynomial $A$ is odd when $A(X,-Y)=-A(X,Y)$, equivalently every monomial with nonzero coefficient has odd total $Y$-degree.
-- source:
--   Benjamin E. Diamond, Hodge Structures in Sextic Fourfolds Equipped with an Involution, https://arxiv.org/abs/2603.29157, Section 3; subset Euler construction specialized to the sign-flip involution.

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.Fermat
open MvPolynomial
open scoped BigOperators

def n : ℕ := 5
def d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := ∑ i : Fin 6, X i ^ 6

def OddSource (A : HodgeComputer.AmbientPoly n) : Prop :=
  ∀ ⦃m : Fin 6 →₀ ℕ⦄, coeff m A ≠ 0 → Odd (m 3 + m 4 + m 5)

end HodgeComputer.Fermat


