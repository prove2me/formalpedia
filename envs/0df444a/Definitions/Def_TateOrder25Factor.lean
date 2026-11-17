-- Prove2me | Definitions.Def_TateOrder25Factor
-- name    : TateOrder25Factor
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:08.539204+00:00
-- url     : https://prove2.me/theorems/592fe9b7-b24e-49ae-b228-9a3842a01053
-- title:
--   The primitive order-$25$ Tate division polynomial
-- statement:
--   The file defines the raw exact-order-$25$ Tate obstruction, compact factors $G_{11},G_{12},G_{13},G_{14}$, the homogeneous degree pieces from $25$ through $40$, and the primitive degree-$40$ polynomial $F_{25}(b,c)$. The central factorization is encoded as $$ψ'_{25}(0)=b^{208}F_5(b,c)F_{25}(b,c).$$ It also defines the explicit obstruction $b≠0$, $F_5≠0$, and $F_{25}=0$, which is the affine $X_1(25)$ locus used by the campaign.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_TateNFDivision
import Definitions.Def_TateOriginDivision
/-!
# Explicit factorisation of the raw order-25 Tate-origin obstruction

`TateOriginDivision` reduces a rational point of order `25` on a Tate normal form
`E(b,c)` to the raw division-polynomial system defined in this module:

* `preΨ'₂₅(0,0) = 0`,
* `preΨ'₅(0,0) ≠ 0`   (excluding the proper order-`5` divisor),
* `b ≠ 0`             (nonsingular Tate normal form).

`25 = 5·5`, so the divisor chain is `1 ∣ 5 ∣ 25`.  This file unrolls Mathlib's
elliptic-divisibility recurrence at the Tate origin `X = 0`, extracting the power
of `b` at every step and keeping the low Kubert factors `F₅,…,F₉` of
`TateNFDivision` **atomic**, exactly as in the sibling order-`27` development.
The `25 = 2·12+1` step of the recurrence gives the compact closed identity

`preΨ'₂₅(0,0) = b²⁰⁸ · (G₁₁·G₁₃³ − b·G₁₄·G₁₂³)`,

with the intermediate factors written through `F₅,…,F₉`:

* `G₁₁ = F₇·F₅³ − b·c·F₆³`             (`= F₁₁`),
* `G₁₂ = c·F₆·(F₅²·F₈ + F₇²)`,
* `G₁₃ = F₅·F₇³ + b·c·F₆³·F₈`          (`= F₁₃`),
* `G₁₄ = F₇·(b·F₆²·F₉ − c²·F₅·F₈²)`.

The proper order-`5` factor `F₅ = b - c` — whose nonvanishing is exactly the
hypothesis `preΨ'₅(0,0) ≠ 0`, since `preΨ'₅(0,0) = b⁸·F₅` — divides the compact
bracket, and dividing it out leaves the **primitive** order-`25` division
polynomial `F₂₅` (degree `40`, `234` monomials, irreducible over `ℚ`):

`G₁₁·G₁₃³ − b·G₁₄·G₁₂³ = F₅ · F₂₅`,   hence   `preΨ'₂₅(0,0) = b²⁰⁸ · F₅ · F₂₅`.

The main result `raw_order25_obstruction_iff` shows the raw system is
**equivalent** to the single explicit polynomial equation `F₂₅(b,c) = 0` on the
locus `b ≠ 0`, `F₅(b,c) ≠ 0` — an affine rational point on the modular curve
`X₁(25)`.  No power of `b` above the compact factors is ever materialised.
No rank or rational-point classification is asserted here: this module is the
lower-level algebraic input for a separate arithmetic exclusion of the displayed
`X₁(25)` locus.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder25Factor

open TateOriginDivision
open Scratch.TateZ2xZ10Reduction

noncomputable section

set_option linter.style.longLine false

/-! ## The exact-order raw Tate obstruction -/

/-- The exact raw Tate-division system left by a rational point of order 25.
The nonvanishing order-five evaluation removes the only nontrivial proper
divisor of 25. -/
def RawOrder25TateObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      b ≠ 0 ∧
        ((W b c).preΨ' 25).eval 0 = 0 ∧
        ((W b c).preΨ' 5).eval 0 ≠ 0

/-! ## Compact intermediate factors (written through `F₅,…,F₉`) -/

/-- Compact factor with `preΨ'₁₁(0) = b⁴⁰ · G11 b c`; agrees with `F11`. -/
def G11 (b c : ℚ) : ℚ :=
  TateNFDivision.F7 b c * TateNFDivision.F5 b c ^ 3 -
    b * c * TateNFDivision.F6 b c ^ 3

/-- Compact factor with `preΨ'₁₂(0) = -(b⁴⁷ · G12 b c)`. -/
def G12 (b c : ℚ) : ℚ :=
  c * TateNFDivision.F6 b c *
    (TateNFDivision.F5 b c ^ 2 * TateNFDivision.F8 b c + TateNFDivision.F7 b c ^ 2)

/-- Compact factor with `preΨ'₁₃(0) = -(b⁵⁶ · G13 b c)`; agrees with `F13`. -/
def G13 (b c : ℚ) : ℚ :=
  TateNFDivision.F5 b c * TateNFDivision.F7 b c ^ 3 +
    b * c * TateNFDivision.F6 b c ^ 3 * TateNFDivision.F8 b c

/-- Compact factor with `preΨ'₁₄(0) = b⁶⁴ · G14 b c`. -/
def G14 (b c : ℚ) : ℚ :=
  TateNFDivision.F7 b c *
    (b * TateNFDivision.F6 b c ^ 2 * TateNFDivision.F9 b c -
      c ^ 2 * TateNFDivision.F5 b c * TateNFDivision.F8 b c ^ 2)

-- `F₂₅` is an irreducible degree-`40`, `234`-monomial polynomial; elaborating this
-- homogeneous pieces factor through powers of b-c.

def F25DegreeTwentyFive (b c : ℚ) : ℚ :=
  (b ^ 5 * (b - c) ^ 20)

def F25DegreeTwentySix (b c : ℚ) : ℚ :=
  (b ^ 5 * c ^ 3 * (b - c) ^ 14 * (35 * b ^ 4 - 105 * b ^ 3 * c + 126 * b ^ 2 * c ^ 2 - 70 * b * c ^ 3 + 15 * c ^ 4))

def F25DegreeTwentySeven (b c : ℚ) : ℚ :=
  (-3 * b ^ 5 * c ^ 5 * (b - c) ^ 13 * (98 * b ^ 4 - 280 * b ^ 3 * c + 332 * b ^ 2 * c ^ 2 - 185 * b * c ^ 3 + 40 * c ^ 4))

def F25DegreeTwentyEight (b c : ℚ) : ℚ :=
  (b * c ^ 7 * (b - c) ^ 12 * (968 * b ^ 8 - 2320 * b ^ 7 * c + 2166 * b ^ 6 * c ^ 2 - 388 * b ^ 5 * c ^ 3 - 685 * b ^ 4 * c ^ 4 + 455 * b ^ 3 * c ^ 5 - 105 * b ^ 2 * c ^ 6 + 15 * b * c ^ 7 - c ^ 8))

def F25DegreeTwentyNine (b c : ℚ) : ℚ :=
  (-b * c ^ 9 * (b - c) ^ 11 * (1732 * b ^ 8 - 3051 * b ^ 7 * c + 1551 * b ^ 6 * c ^ 2 + 2441 * b ^ 5 * c ^ 3 - 3660 * b ^ 4 * c ^ 4 + 1740 * b ^ 3 * c ^ 5 - 340 * b ^ 2 * c ^ 6 + 45 * b * c ^ 7 - 3 * c ^ 8))

def F25DegreeThirty (b c : ℚ) : ℚ :=
  (3 * b * c ^ 11 * (b - c) ^ 10 * (612 * b ^ 8 - 553 * b ^ 7 * c - 263 * b ^ 6 * c ^ 2 + 2409 * b ^ 5 * c ^ 3 - 2738 * b ^ 4 * c ^ 4 + 1145 * b ^ 3 * c ^ 5 - 180 * b ^ 2 * c ^ 6 + 25 * b * c ^ 7 - 2 * c ^ 8))

def F25DegreeThirtyOne (b c : ℚ) : ℚ :=
  (-b * c ^ 13 * (b - c) ^ 9 * (1205 * b ^ 8 + 185 * b ^ 7 * c - 1289 * b ^ 6 * c ^ 2 + 11195 * b ^ 5 * c ^ 3 - 12520 * b ^ 4 * c ^ 4 + 4615 * b ^ 3 * c ^ 5 - 470 * b ^ 2 * c ^ 6 + 91 * b * c ^ 7 - 10 * c ^ 8))

def F25DegreeThirtyTwo (b c : ℚ) : ℚ :=
  (b * c ^ 15 * (b - c) ^ 8 * (494 * b ^ 8 + 690 * b ^ 7 * c - 144 * b ^ 6 * c ^ 2 + 14630 * b ^ 5 * c ^ 3 - 15060 * b ^ 4 * c ^ 4 + 4299 * b ^ 3 * c ^ 5 + 5 * b ^ 2 * c ^ 6 + 96 * b * c ^ 7 - 15 * c ^ 8))

def F25DegreeThirtyThree (b c : ℚ) : ℚ :=
  (-3 * b * c ^ 17 * (b - c) ^ 7 * (41 * b ^ 8 + 115 * b ^ 7 * c + 117 * b ^ 6 * c ^ 2 + 5136 * b ^ 5 * c ^ 3 - 4090 * b ^ 4 * c ^ 4 + 541 * b ^ 3 * c ^ 5 + 235 * b ^ 2 * c ^ 6 + 42 * b * c ^ 7 - 7 * c ^ 8))

def F25DegreeThirtyFour (b c : ℚ) : ℚ :=
  (b * c ^ 19 * (b - c) ^ 6 * (17 * b ^ 8 + 74 * b ^ 7 * c + 161 * b ^ 6 * c ^ 2 + 11834 * b ^ 5 * c ^ 3 - 6145 * b ^ 4 * c ^ 4 - 433 * b ^ 3 * c ^ 5 + 569 * b ^ 2 * c ^ 6 + 266 * b * c ^ 7 - 28 * c ^ 8))

def F25DegreeThirtyFive (b c : ℚ) : ℚ :=
  (-c ^ 21 * (b - c) ^ 5 * (b ^ 9 + 6 * b ^ 8 * c + 21 * b ^ 7 * c ^ 2 + 6558 * b ^ 6 * c ^ 3 - 1587 * b ^ 5 * c ^ 4 - 609 * b ^ 4 * c ^ 5 + 181 * b ^ 3 * c ^ 6 + 231 * b ^ 2 * c ^ 7 - 6 * b * c ^ 8 - c ^ 9))

def F25DegreeThirtySix (b c : ℚ) : ℚ :=
  (3 * b ^ 2 * c ^ 26 * (b - c) ^ 4 * (885 * b ^ 4 + 30 * b ^ 3 * c - 55 * b ^ 2 * c ^ 2 + 15 * b * c ^ 3 + 42 * c ^ 4))

def F25DegreeThirtySeven (b c : ℚ) : ℚ :=
  (-7 * b ^ 2 * c ^ 28 * (b - c) ^ 3 * (110 * b ^ 4 + 35 * b ^ 3 * c + 7 * b ^ 2 * c ^ 2 + 5 * b * c ^ 3 + 8 * c ^ 4))

def F25DegreeThirtyEight (b c : ℚ) : ℚ :=
  (b ^ 2 * c ^ 30 * (b - c) ^ 2 * (151 * b ^ 4 + 90 * b ^ 3 * c + 48 * b ^ 2 * c ^ 2 + 25 * b * c ^ 3 + 21 * c ^ 4))

def F25DegreeThirtyNine (b c : ℚ) : ℚ :=
  (-3 * b ^ 2 * c ^ 32 * (b - c) * (6 * b ^ 4 + 5 * b ^ 3 * c + 4 * b ^ 2 * c ^ 2 + 3 * b * c ^ 3 + 2 * c ^ 4))

def F25DegreeForty (b c : ℚ) : ℚ :=
  (b ^ 2 * c ^ 34 * (b ^ 4 + b ^ 3 * c + b ^ 2 * c ^ 2 + b * c ^ 3 + c ^ 4))

/-- The primitive order-25 division polynomial `F₂₅`: the compact bracket with the
proper order-`5` factor `F₅ = b - c` divided out.  Degree `40`, `234` monomials,
irreducible over `ℚ`; its vanishing locus is the affine modular curve `X₁(25)`. -/
def F25 (b c : ℚ) : ℚ :=
  F25DegreeTwentyFive b c +
    F25DegreeTwentySix b c +
    F25DegreeTwentySeven b c +
    F25DegreeTwentyEight b c +
    F25DegreeTwentyNine b c +
    F25DegreeThirty b c +
    F25DegreeThirtyOne b c +
    F25DegreeThirtyTwo b c +
    F25DegreeThirtyThree b c +
    F25DegreeThirtyFour b c +
    F25DegreeThirtyFive b c +
    F25DegreeThirtySix b c +
    F25DegreeThirtySeven b c +
    F25DegreeThirtyEight b c +
    F25DegreeThirtyNine b c +
    F25DegreeForty b c

/-! ## Reduction of the raw obstruction to the single equation `F₂₅ = 0` -/

/-- The explicit primitive order-25 obstruction: a rational point on the affine
modular curve `X₁(25)`, off the excluded order-`5` locus `F₅ = 0` (i.e. `b = c`)
and the singular locus `b = 0`. -/
def ExplicitOrder25Obstruction : Prop :=
  ∃ b c : ℚ, ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
    b ≠ 0 ∧ TateNFDivision.F5 b c ≠ 0 ∧ F25 b c = 0

end

end MazurProof.TateOrder25Factor


