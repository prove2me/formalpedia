-- Prove2me | Definitions.Def_DivisionBezoutThreeTermsC
-- name    : DivisionBezoutThreeTermsC
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:13.8032+00:00
-- url     : https://prove2.me/theorems/9aeb90d2-efd2-4f78-b09c-1839b8f4467b
-- title:
--   Final block of the $Ψ_3$ Bézout cofactor
-- statement:
--   Stores the final three explicit polynomials $A_6,A_7,A_8∈k[X]$ in $b_2,b_4,b_6,b_8$. Together with the preceding blocks, these technical certificate terms assemble the cofactor of $Ψ_3$ in the division-polynomial Bézout identity.
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

def divisionBezoutThreeTerm6 (W : WeierstrassCurve k) : k[X] :=
  - (2112 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (846 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (25048 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (4872 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (6114 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₆) ^ 4 * (C W.b₈)
          - (5264 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₈) ^ 4
          + (720 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          - (270 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (88896 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (702 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (5994 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 5
          - (285184 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (71352 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (25272 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          + (71523 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          - (28188 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          - (157248 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          + (959256 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (170424 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          + (244608 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈) ^ 4
          - (45927 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 6
          + (1082928 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (29160 : k[X]) * X * (C W.b₄) ^ 6 * (C W.b₆) * (C W.b₈)
          + (10935 : k[X]) * X * (C W.b₄) ^ 5 * (C W.b₆) ^ 3
          - (9072 : k[X]) * X * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          - (375192 : k[X]) * X * (C W.b₄) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          + (148716 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆) ^ 5
          + (903168 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          - (3251664 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (1259712 : k[X]) * X * (C W.b₆) ^ 5 * (C W.b₈)

def divisionBezoutThreeTerm7 (W : WeierstrassCurve k) : k[X] :=
  - (1843968 : k[X]) * X * (C W.b₆) * (C W.b₈) ^ 4
          + (C W.b₂) ^ 8 * (C W.b₈) ^ 3
          - (3 : k[X]) * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (3 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (111 : k[X]) * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 3
          - (27 : k[X]) * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (424 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (25 : k[X]) * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (7 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) ^ 5
          + (864 : k[X]) * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 3
          - (78 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (456 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (18 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (3760 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (2290 : k[X]) * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (693 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆) ^ 4 * (C W.b₈)
          - (1632 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈) ^ 4
          + (126 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          + (162 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (14034 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (2511 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (1422 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 5
          - (43432 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (7432 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          - (54 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆) ^ 2
          + (3663 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          + (13410 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          + (1107 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          - (39944 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 3

def divisionBezoutThreeTerm8 (W : WeierstrassCurve k) : k[X] :=
  (200916 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (26406 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          + (88816 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 4
          + (1944 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 6
          + (179888 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (5103 : k[X]) * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆) * (C W.b₈)
          - (5346 : k[X]) * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 3
          + (48600 : k[X]) * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          - (211410 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          + (45684 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 5
          + (103824 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          - (756648 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          + (188568 : k[X]) * (C W.b₂) * (C W.b₆) ^ 5 * (C W.b₈)
          - (639744 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 4
          + (2187 : k[X]) * (C W.b₄) ^ 7 * (C W.b₆) ^ 2
          - (20412 : k[X]) * (C W.b₄) ^ 6 * (C W.b₈) ^ 2
          + (46899 : k[X]) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          + (6561 : k[X]) * (C W.b₄) ^ 4 * (C W.b₆) ^ 4
          + (190512 : k[X]) * (C W.b₄) ^ 4 * (C W.b₈) ^ 3
          - (666360 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (983664 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          - (592704 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈) ^ 4
          - (308367 : k[X]) * (C W.b₄) * (C W.b₆) ^ 6
          + (1553328 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          - (400464 : k[X]) * (C W.b₆) ^ 4 * (C W.b₈) ^ 2
          + (614656 : k[X]) * (C W.b₈) ^ 5

end

end WeierstrassCurve


