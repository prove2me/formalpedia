-- Prove2me | Definitions.Def_DivisionBezoutThreeTermsA
-- name    : DivisionBezoutThreeTermsA
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:28.072469+00:00
-- url     : https://prove2.me/theorems/936eef05-9168-4857-bb4b-e1bfc1734d39
-- title:
--   First block of the $Ψ_3$ Bézout cofactor
-- statement:
--   Stores the first three explicit polynomials $A_0,A_1,A_2∈k[X]$, with coefficients expressed through the Weierstrass invariants $b_2,b_4,b_6,b_8$. They are machine-generated certificate data for the cofactor $A_W$ multiplying $Ψ_3$ in the identity $A_WΨ_3+B_WΨ̃_4=Δ^4$, used to certify coprimality of adjacent division polynomials.
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

def divisionBezoutThreeTerm0 (W : WeierstrassCurve k) : k[X] :=
  (2 : k[X]) * X ^ 5 * (C W.b₂) ^ 7 * (C W.b₈) ^ 2
          - (4 : k[X]) * X ^ 5 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          + (2 : k[X]) * X ^ 5 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          - (200 : k[X]) * X ^ 5 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₈) ^ 2
          - (72 : k[X]) * X ^ 5 * (C W.b₂) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          + (596 : k[X]) * X ^ 5 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          + (36 : k[X]) * X ^ 5 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 3
          + (1440 : k[X]) * X ^ 5 * (C W.b₂) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          - (144 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₈)
          - (324 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          + (5792 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (648 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + (1134 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₆) ^ 4
          - (1152 : k[X]) * X ^ 5 * (C W.b₂) ^ 3 * (C W.b₈) ^ 3
          + (108 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆)
          - (18144 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          - (1674 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (74304 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (17496 : k[X]) * X ^ 5 * (C W.b₂) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (5832 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₈)
          + (10692 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          - (36288 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (227232 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (40824 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 4
          + (56448 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄) * (C W.b₈) ^ 3
          + (295488 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (4374 : k[X]) * X ^ 5 * (C W.b₄) ^ 6 * (C W.b₆)
          - (25272 : k[X]) * X ^ 5 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (34992 : k[X]) * X ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (284256 : k[X]) * X ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2

def divisionBezoutThreeTerm1 (W : WeierstrassCurve k) : k[X] :=
  - (886464 : k[X]) * X ^ 5 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (314928 : k[X]) * X ^ 5 * (C W.b₆) ^ 5
          - (508032 : k[X]) * X ^ 5 * (C W.b₆) * (C W.b₈) ^ 3
          + X ^ 4 * (C W.b₂) ^ 8 * (C W.b₈) ^ 2
          - (2 : k[X]) * X ^ 4 * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          + X ^ 4 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          - (102 : k[X]) * X ^ 4 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 2
          - (34 : k[X]) * X ^ 4 * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈)
          + (300 : k[X]) * X ^ 4 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          + (16 : k[X]) * X ^ 4 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3
          + (734 : k[X]) * X ^ 4 * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 2
          - (72 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈)
          - (162 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          + (3062 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (468 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + (519 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₆) ^ 4
          - (808 : k[X]) * X ^ 4 * (C W.b₂) ^ 4 * (C W.b₈) ^ 3
          + (54 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆)
          - (9384 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          - (513 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (37632 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (8502 : k[X]) * X ^ 4 * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          + (3024 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈)
          + (5238 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          - (22656 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (117450 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (18792 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4
          + (41216 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 3
          + (149832 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (2187 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆)

def divisionBezoutThreeTerm2 (W : WeierstrassCurve k) : k[X] :=
  - (2430 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (28188 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (133920 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (444528 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (144342 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₆) ^ 5
          - (327264 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 3
          - (4374 : k[X]) * X ^ 4 * (C W.b₄) ^ 6 * (C W.b₈)
          + (4374 : k[X]) * X ^ 4 * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          + (40824 : k[X]) * X ^ 4 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (89424 : k[X]) * X ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (56862 : k[X]) * X ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          - (127008 : k[X]) * X ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (235872 : k[X]) * X ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (52488 : k[X]) * X ^ 4 * (C W.b₆) ^ 4 * (C W.b₈)
          + (131712 : k[X]) * X ^ 4 * (C W.b₈) ^ 4
          + (4 : k[X]) * X ^ 3 * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₈) ^ 2
          + X ^ 3 * (C W.b₂) ^ 7 * (C W.b₆) ^ 2 * (C W.b₈)
          - (9 : k[X]) * X ^ 3 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          - X ^ 3 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 3
          + (7 : k[X]) * X ^ 3 * (C W.b₂) ^ 6 * (C W.b₆) * (C W.b₈) ^ 2
          + (5 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          - (415 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (256 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (22 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₆) ^ 4
          - (92 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₈) ^ 3
          + (1334 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (252 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          + (3176 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (223 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₆) ^ 3 * (C W.b₈)
          - (306 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₈)

end

end WeierstrassCurve


