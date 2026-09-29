-- Prove2me | Definitions.Def_eulerScalarEquation
-- name    : eulerScalarEquation
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T19:39:53.3893+00:00
-- url     : https://prove2.me/theorems/7c290b92-0ff9-4a23-b542-660100705fa5
-- title:
--   Explicit scalar differential operator for the Euler E-system
-- source:
--   Direct elimination in the classical Euler E-system X f prime = [[0,0,0],[0,X,0],[-1,1,X]] f; specialization of the cyclic construction in Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorem 3.2.

import Definitions.Def_beukersLiftingData
import Definitions.Def_eulerMascheroni_formalESystem

noncomputable section
namespace EulerMascheroni.Mixed

/-- A constant linear combination of the three Euler E-functions. -/
def formalCombination (a b c : ℂ) : PowerSeries ℂ :=
  PowerSeries.C a + PowerSeries.C b * PowerSeries.exp ℂ + PowerSeries.C c * formalExpEin

/-- A scalar differential operator for the nondegenerate Euler combination. -/
def scalarOperator (a c : ℂ) (n : ℕ) : Polynomial ℂ :=
  if n = 0 then Polynomial.C c else
  if n = 1 then Polynomial.C a * Polynomial.X^2 - 2*Polynomial.C a*Polynomial.X +
    2*Polynomial.C a + Polynomial.C c*Polynomial.X - 3*Polynomial.C c else
  if n = 2 then -2*Polynomial.C a*Polynomial.X^2 + 3*Polynomial.C a*Polynomial.X -
    2*Polynomial.C a - 2*Polynomial.C c*Polynomial.X + 2*Polynomial.C c else
  Polynomial.X*(Polynomial.C a*Polynomial.X - Polynomial.C a + Polynomial.C c)

end EulerMascheroni.Mixed


