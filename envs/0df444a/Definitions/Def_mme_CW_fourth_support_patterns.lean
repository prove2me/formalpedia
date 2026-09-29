-- Prove2me | Definitions.Def_mme_CW_fourth_support_patterns
-- name    : mme_CW_fourth_support_patterns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T19:26:57.069883+00:00
-- url     : https://prove2.me/theorems/63253723-860b-4c10-b38c-4465a6c74e04
-- title:
--   Six one-factor support patterns for the fourth Coppersmith--Winograd power
-- statement:
--   The support of one Coppersmith--Winograd tensor consists of six grade patterns of total degree two: $(0,1,1)$, $(1,0,1)$, $(1,1,0)$, $(0,0,2)$, $(0,2,0)$, and $(2,0,0)$. The definition also records the coordinatewise sum of four chosen patterns. It is independent of the parameter $q$ once $q>0$, and supplies the finite combinatorial interface between four literal CW monomials and the 45 fourth-power shapes.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proc. Royal Soc. Edinburgh 143A (2013), Section 5, printed p. 363, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib

open scoped BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-- The six total-grade-two patterns of one Coppersmith--Winograd monomial: the three ordinary edges and the three doubled loops. -/
def cwSingleSupportPattern : Fin 6 → Fin 3 → ℕ :=
  ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0],
    ![0, 0, 2], ![0, 2, 0], ![2, 0, 0]]

/-- Coordinatewise sum of four single-CW support patterns. -/
def cwFourSupportNatAddress (r : Fin 4 → Fin 6) (s : Fin 3) : ℕ :=
  ∑ l, cwSingleSupportPattern (r l) s

end MME.StothersFourth


