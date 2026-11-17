-- Prove2me | Definitions.Def_DivisionBezoutFourTermsA
-- name    : DivisionBezoutFourTermsA
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:26.480786+00:00
-- url     : https://prove2.me/theorems/809678e3-0a6f-46c3-b030-c3c366d41bd8
-- title:
--   First block of the fourth-division Bézout cofactor
-- statement:
--   Stores the first three explicit polynomials $B_0,B_1,B_2∈k[X]$ in the Weierstrass invariants. They are machine-generated certificate data for the cofactor multiplying the normalized fourth division polynomial $Ψ̃_4$ in $A_WΨ_3+B_WΨ̃_4=Δ^4$.
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

def divisionBezoutFourTerm0 (W : WeierstrassCurve k) : k[X] :=
  -(3 : k[X]) * X ^ 3 * (C W.b₂) ^ 7 * (C W.b₈) ^ 2
          + (6 : k[X]) * X ^ 3 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (3 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          + (300 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₈) ^ 2
          + (108 : k[X]) * X ^ 3 * (C W.b₂) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈)
          - (894 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          - (54 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 3
          - (2160 : k[X]) * X ^ 3 * (C W.b₂) ^ 4 * (C W.b₆) * (C W.b₈) ^ 2
          + (216 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₈)
          + (486 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          - (8688 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (972 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (1701 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆) ^ 4
          + (1728 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₈) ^ 3
          - (162 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆)
          + (27216 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (2511 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          + (111456 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (26244 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (8748 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₈)
          - (16038 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          + (54432 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (340848 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (61236 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 4
          - (84672 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₈) ^ 3
          - (443232 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (6561 : k[X]) * X ^ 3 * (C W.b₄) ^ 6 * (C W.b₆)
          + (37908 : k[X]) * X ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          + (52488 : k[X]) * X ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (426384 : k[X]) * X ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2

def divisionBezoutFourTerm1 (W : WeierstrassCurve k) : k[X] :=
  (1329696 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (472392 : k[X]) * X ^ 3 * (C W.b₆) ^ 5
          + (762048 : k[X]) * X ^ 3 * (C W.b₆) * (C W.b₈) ^ 3
          - X ^ 2 * (C W.b₂) ^ 8 * (C W.b₈) ^ 2
          + (2 : k[X]) * X ^ 2 * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2
          + (103 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₈) ^ 2
          + (33 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₆) ^ 2 * (C W.b₈)
          - (301 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          - (15 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 3
          - (741 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₆) * (C W.b₈) ^ 2
          + (72 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 4 * (C W.b₈)
          + (162 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          - (3145 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (540 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          - (495 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆) ^ 4
          + (924 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₈) ^ 3
          - (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₆)
          + (9540 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (351 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          + (37872 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (8379 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆) ^ 3 * (C W.b₈)
          - (3078 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₈)
          - (5184 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          + (24912 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          - (119367 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (17982 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 4
          - (47712 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈) ^ 3
          - (150876 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (2187 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₆)

def divisionBezoutFourTerm2 (W : WeierstrassCurve k) : k[X] :=
  - (2673 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          + (33534 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (129816 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          + (445176 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (137781 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 5
          + (363888 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) * (C W.b₈) ^ 3
          + (6561 : k[X]) * X ^ 2 * (C W.b₄) ^ 6 * (C W.b₈)
          - (6561 : k[X]) * X ^ 2 * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          - (61236 : k[X]) * X ^ 2 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (134136 : k[X]) * X ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (85293 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (190512 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (353808 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (78732 : k[X]) * X ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          - (197568 : k[X]) * X ^ 2 * (C W.b₈) ^ 4
          - (2 : k[X]) * X * (C W.b₂) ^ 7 * (C W.b₄) * (C W.b₈) ^ 2
          - X * (C W.b₂) ^ 7 * (C W.b₆) ^ 2 * (C W.b₈)
          + (5 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈)
          + X * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 3
          - (7 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₆) * (C W.b₈) ^ 2
          - (3 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2
          + (214 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          + (186 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + (21 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₆) ^ 4
          + (80 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₈) ^ 3
          - (738 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          - (216 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (1644 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (273 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆) ^ 3 * (C W.b₈)
          + (162 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 5 * (C W.b₈)

end

end WeierstrassCurve


