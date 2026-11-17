-- Prove2me | Definitions.Def_DivisionBezoutThreeTermsB
-- name    : DivisionBezoutThreeTermsB
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:03.749211+00:00
-- url     : https://prove2.me/theorems/8209a237-fd18-453e-a386-96430a23f27a
-- title:
--   Middle block of the $Ψ_3$ Bézout cofactor
-- statement:
--   Stores the next three explicit polynomials $A_3,A_4,A_5∈k[X]$ in the Weierstrass invariants $b_2,b_4,b_6,b_8$. This is the middle certificate-data block of the cofactor multiplying $Ψ_3$ in $A_WΨ_3+B_WΨ̃_4=Δ^4$.
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

def divisionBezoutThreeTerm3 (W : WeierstrassCurve k) : k[X] :=
  - (864 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2
          + (12176 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (729 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          + (3357 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 4
          + (2400 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈) ^ 3
          + (1092 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (270 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₆)
          - (40401 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (9423 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          - (180648 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (50220 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (6075 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₆) ^ 5
          - (30224 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈) ^ 3
          + (12393 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 6 * (C W.b₈)
          + (28917 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          - (71604 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          + (511272 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          - (64395 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (85680 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          + (808272 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (972 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₆) ^ 4 * (C W.b₈)
          + (53312 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₈) ^ 4
          - (10935 : k[X]) * X ^ 3 * (C W.b₄) ^ 7 * (C W.b₆)
          - (57348 : k[X]) * X ^ 3 * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)
          - (91854 : k[X]) * X ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          + (674352 : k[X]) * X ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          - (2118960 : k[X]) * X ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          + (734832 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₆) ^ 5
          - (1213632 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          - (38880 : k[X]) * X ^ 3 * (C W.b₆) ^ 3 * (C W.b₈) ^ 2

def divisionBezoutThreeTerm4 (W : WeierstrassCurve k) : k[X] :=
  (10 : k[X]) * X ^ 2 * (C W.b₂) ^ 7 * (C W.b₆) * (C W.b₈) ^ 2
          - (4 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) ^ 2 * (C W.b₈) ^ 2
          - (17 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈)
          + X ^ 2 * (C W.b₂) ^ 6 * (C W.b₆) ^ 4
          + (10 : k[X]) * X ^ 2 * (C W.b₂) ^ 6 * (C W.b₈) ^ 3
          + (5 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈)
          + (5 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 3
          - (1047 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          - (316 : k[X]) * X ^ 2 * (C W.b₂) ^ 5 * (C W.b₆) ^ 3 * (C W.b₈)
          + (385 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (2840 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (84 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 4
          - (1084 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₈) ^ 3
          + (7260 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (1572 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₆) * (C W.b₈)
          - (756 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 3 * (C W.b₆) ^ 3
          + (31940 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (5541 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          + (6075 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆) ^ 5
          - (2992 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆) * (C W.b₈) ^ 3
          + (270 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 6 * (C W.b₈)
          + (270 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 5 * (C W.b₆) ^ 2
          - (11694 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2
          - (87183 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 2 * (C W.b₈)
          + (189 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 4
          + (35568 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₈) ^ 3
          - (390492 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (75816 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₆) ^ 4 * (C W.b₈)
          - (5600 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈) ^ 4
          + (57591 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 5 * (C W.b₆) * (C W.b₈)

def divisionBezoutThreeTerm5 (W : WeierstrassCurve k) : k[X] :=
  (24543 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 4 * (C W.b₆) ^ 3
          - (220104 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3 * (C W.b₆) * (C W.b₈) ^ 2
          + (1193076 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆) ^ 3 * (C W.b₈)
          - (270459 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 5
          + (127344 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 3
          + (1469664 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 3 * (C W.b₈) ^ 2
          - (10935 : k[X]) * X ^ 2 * (C W.b₄) ^ 7 * (C W.b₈)
          - (10935 : k[X]) * X ^ 2 * (C W.b₄) ^ 6 * (C W.b₆) ^ 2
          + (102060 : k[X]) * X ^ 2 * (C W.b₄) ^ 5 * (C W.b₈) ^ 2
          - (356238 : k[X]) * X ^ 2 * (C W.b₄) ^ 4 * (C W.b₆) ^ 2 * (C W.b₈)
          - (28431 : k[X]) * X ^ 2 * (C W.b₄) ^ 3 * (C W.b₆) ^ 4
          - (317520 : k[X]) * X ^ 2 * (C W.b₄) ^ 3 * (C W.b₈) ^ 3
          + (2036448 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          - (4639356 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₆) ^ 4 * (C W.b₈)
          + (329280 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈) ^ 4
          + (1614006 : k[X]) * X ^ 2 * (C W.b₆) ^ 6
          - (2558304 : k[X]) * X ^ 2 * (C W.b₆) ^ 2 * (C W.b₈) ^ 3
          + (9 : k[X]) * X * (C W.b₂) ^ 7 * (C W.b₈) ^ 3
          - (25 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₄) * (C W.b₆) * (C W.b₈) ^ 2
          + (7 : k[X]) * X * (C W.b₂) ^ 6 * (C W.b₆) ^ 3 * (C W.b₈)
          + (2 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 3 * (C W.b₈) ^ 2
          + (12 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) ^ 2 * (C W.b₆) ^ 2 * (C W.b₈)
          - (5 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₆) ^ 4
          - (880 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₄) * (C W.b₈) ^ 3
          - (274 : k[X]) * X * (C W.b₂) ^ 5 * (C W.b₆) ^ 2 * (C W.b₈) ^ 2
          + (3098 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) ^ 2 * (C W.b₆) * (C W.b₈) ^ 2
          - (258 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₄) * (C W.b₆) ^ 3 * (C W.b₈)
          - (165 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆) ^ 5
          + (5720 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆) * (C W.b₈) ^ 3
          - (705 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 4 * (C W.b₈) ^ 2

end

end WeierstrassCurve


