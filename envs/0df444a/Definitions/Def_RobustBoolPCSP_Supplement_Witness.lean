-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_Witness
-- name    : RobustBoolPCSP_Supplement_Witness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:22:17.846562+00:00
-- url     : https://prove2.me/theorems/ce23772e-20d5-4d6f-a483-ee83c6f787e9
-- title:
--   The witness template $T^*$
-- statement:
--   The Boolean same-domain template $T^*$ has the four-ary pair
--
--   $$P=\{x\in\{0,1\}^4: x_1+x_2+x_3=1+x_0\},\qquad Q=\{0,1\}^4\setminus\{1000,0111\},$$
--
--   together with the two unary pins $(\{0\},\{0\})$ and $(\{1\},\{1\})$.
--
--   It is the fixed hard template inside $\mathfrak P$ (Theorems 2.7, 6.5, 6.10 and 7.16).
--
--   **Formalization Note** Coordinates are numbered $0,1,2,3$; the index `none` is the four-ary pair and `some c` the pin at $c$.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §2.2, p.9, eq. (1) and the pins

import Mathlib
import Definitions.Def_RobustBoolPCSP_Template

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- The strong relation of the witness: `P = {x ∈ {0,1}⁴ : x₁ + x₂ + x₃ = 1 + x₀}` (eq. (1), p.9),
with coordinates numbered `0, 1, 2, 3`. -/
def PStar : Set (Fin 4 → Bool) :=
  {x | (x 1).toNat + (x 2).toNat + (x 3).toNat = 1 + (x 0).toNat}

/-- The weak relation of the witness: `Q = {0,1}⁴ \ {1000, 0111}` (eq. (1), p.9). -/
def QStar : Set (Fin 4 → Bool) :=
  {x | x ≠ ![true, false, false, false] ∧ x ≠ ![false, true, true, true]}

/-- The **witness template `T∗`** (eq. (1), p.9).
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §2.2, p.9: "Let T∗ consist of P = {x ∈ {0, 1}⁴ : x1 + x2 + x3 = 1 + x0},
Q = {0, 1}⁴ \ {1000, 0111}, (1) together with the pins {0} → {0} and {1} → {1}."

**Formalization Note.** Boolean (`false` = 0, `true` = 1), same domain. The index type is
`Option Bool`: `none` is the four-ary pair `(P, Q)`; `some c` is the unary pin `({c}, {c})`. -/
def TStar : Template (Option Bool) Bool Bool where
  r := fun o => match o with
    | none => 4
    | some _ => 1
  P := fun o => match o with
    | none => PStar
    | some c => {x : Fin 1 → Bool | x 0 = c}
  Q := fun o => match o with
    | none => QStar
    | some c => {x : Fin 1 → Bool | x 0 = c}

end RobustBoolPCSP.Supplement


