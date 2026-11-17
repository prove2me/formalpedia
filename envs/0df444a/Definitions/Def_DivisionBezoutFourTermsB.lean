-- Prove2me | Definitions.Def_DivisionBezoutFourTermsB
-- name    : DivisionBezoutFourTermsB
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:05.567195+00:00
-- url     : https://prove2.me/theorems/3d9fb626-2e01-4238-92e7-e166163db9a8
-- title:
--   Second block of the fourth-division Bézout cofactor
-- statement:
--   Stores the remaining explicit polynomials $B_3,B_4,B_5∈k[X]$ in $b_2,b_4,b_6,b_8$. These technical terms complete the cofactor of $Ψ̃_4$ in the Bézout certificate used for division-polynomial nonsingularity and coprimality.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_WardSomos
/-! Coefficient data of the Bezout certificates for the division polynomials. -/
open Polynomial
open scoped Polynomial
open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

def divisionBezoutFourTerm3 (W : WeierstrassCurve k) : k[X] :=
  (540 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          - (6360 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (1593 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (2079 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 4
          - (2944 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈) ^ 3
          - (1116 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (162 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆)
          + (22329 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          + (7695 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (101736 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (35640 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (5832 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 5
          + (27024 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          - (6561 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₈)
          - (18225 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          + (35964 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (277992 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (18954 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (33264 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (488592 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (11664 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 4 * (C W.b₈)
          - (47040 : k[X]) * X * (C W.b₂) * (C W.b₈) ^ 4
          + (6561 : k[X]) * X * (C W.b₄) ^ 7 * (C W.b₆)
          + (29160 : k[X]) * X * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          + (59049 : k[X]) * X * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (371952 : k[X]) * X * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (1183896 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (393660 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 5
          + (677376 : k[X]) * X * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          + (58320 : k[X]) * X * (C W.b₆) ^ 3 * (C W.b₈) ^ 2

def divisionBezoutFourTerm4 (W : WeierstrassCurve k) : k[X] :=
  - (3 : k[X]) * (C W.b₂) ^ 7 * (C W.b₆) * (C W.b₈) ^ 2
          + (2 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (5 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (C W.b₂) ^ 6 * (C W.b₆) ^ 4
          - (9 : k[X]) * (C W.b₂) ^ 6 * (C W.b₈) ^ 3
          - (3 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (356 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (67 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) ^ 3 * (C W.b₈)
          - (216 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (900 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (162 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 4
          + (800 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₈) ^ 3
          - (2238 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (756 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (54 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (11934 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (3519 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (2187 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 5
          - (824 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) * (C W.b₈) ^ 3
          - (162 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₈)
          + (7065 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (27513 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (4374 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (22104 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (132516 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (15066 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          + (5264 : k[X]) * (C W.b₂) ^ 2 * (C W.b₈) ^ 4
          - (26973 : k[X]) * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          + (2187 : k[X]) * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          + (84888 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2

def divisionBezoutFourTerm5 (W : WeierstrassCurve k) : k[X] :=
  - (404838 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (118098 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 5
          - (3024 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (441288 : k[X]) * (C W.b₂) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (6561 : k[X]) * (C W.b₄) ^ 7 * (C W.b₈)
          - (61236 : k[X]) * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          + (181521 : k[X]) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          - (39366 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          + (190512 : k[X]) * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          - (818424 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (1522152 : k[X]) * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          - (197568 : k[X]) * (C W.b₄) * (C W.b₈) ^ 4
          - (531441 : k[X]) * (C W.b₆) ^ 6
          + (789264 : k[X]) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3

end

end WeierstrassCurve


