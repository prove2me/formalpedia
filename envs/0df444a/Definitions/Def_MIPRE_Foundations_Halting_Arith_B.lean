-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Arith_B
-- name    : MIPRE_Foundations_Halting_Arith_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:17.761384+00:00
-- url     : https://prove2.me/theorems/5dbf757d-1d47-4464-a0a7-633d02ec8042
-- title:
--   Definitions of Arith (addendum): Arithmetic in the ambient model: increment, unary conversion, multiplication, polynomials The arithmetic the wrapper…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Halting.Arith` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Arithmetic in the ambient model: increment, unary conversion, multiplication, polynomials. The arithmetic the wrapper decider (`Halting/Wrapper.lean`) and the compressor's decider (`Halting/Compressor.lean`) need, each with its cost: * `Prog.incProg`: the successor of a canonical binary numeral (`Data.inc`, with `Data.inc_bits : inc n.bits = (n + 1).bits`), used to enumerate the bit queries; * `Prog.toUnaryProg`: a binary numeral to unary (`encode n ↦ ofNat n`), by the fold `k ↦ 2k + b` over the bits from the most significant one, doubling the unary accumulator with `revOntoProg`; *…
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_Halting_Arith` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (3): `MIPRE.Cost.Prog.mulBody` (Body of the multiplication loop, on the state `cons bRest acc`, with the first factor `a` one variable further out: at the end stop with…); `MIPRE.Cost.Prog.mulProg` (`mulProg` on `cons (ofNat a) (ofNat b)` computes `ofNat (a * b)`.); `MIPRE.Cost.Prog.polyProg` (Horner evaluation of the coefficient list `cs` on a unary input `m`: `polyProg (c :: cs)` computes `c + m · polyProg cs`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Halting.Arith` (`MIPRE/Foundations/Halting/Arith.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Arith.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Arith.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Halting_Arith does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith

/-!
# Arithmetic in the ambient model: increment, unary conversion, multiplication, polynomials

The arithmetic the wrapper decider (`Halting/Wrapper.lean`) and the compressor's decider
(`Halting/Compressor.lean`) need, each with its cost:

* `Prog.incProg`: the successor of a canonical binary numeral (`Data.inc`, with
  `Data.inc_bits : inc n.bits = (n + 1).bits`), used to enumerate the bit queries;
* `Prog.toUnaryProg`: a binary numeral to unary (`encode n ↦ ofNat n`), by the fold
  `k ↦ 2k + b` over the bits from the most significant one, doubling the unary accumulator with
  `revOntoProg`;
* `Prog.mulProg`: multiplication of unary numerals, by repeated `addProg`;
* `Prog.polyProg cs`: the Horner evaluation `c₀ + m (c₁ + m (…))` of a polynomial given by its
  coefficient list, on a unary input; `hornerCoeffs` and `Data.polyEval_hornerCoeffs` connect it
  to `Polynomial.eval`, so that the wrapper can compute the paper's `poly(n, λ)` bounds.

Costs are polynomial in the *values* (the unary numerals are as long as the values); the
polynomial evaluation is bounded by an explicit `Polynomial ℕ` in the argument
(`Prog.polyProg_runs`), which is what the time accounting downstream composes.
-/

namespace MIPRE.Cost

open Polynomial

namespace Data

/-! ## The successor of a binary numeral -/

/-! ## Binary to unary -/

/-! ## Polynomials by their coefficients -/

end Data

namespace Prog

open Data

/-! ## The increment program -/

/-! ## Binary to unary -/

/-! ## Multiplication of unary numerals -/

/-- Body of the multiplication loop, on the state `cons bRest acc`, with the first factor `a`
one variable further out: at the end stop with `acc`, otherwise add `a` to `acc`. -/
def mulBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.let_ (.let_ (.cons (.var 5) (.var 3)) addProg)
        (.cons (.cons .nil .nil) (.cons (.var 2) (.var 0)))))

/-- `mulProg` on `cons (ofNat a) (ofNat b)` computes `ofNat (a * b)`. -/
def mulProg : Prog := .elim 0 .nil (.let_ (.cons (.var 1) .nil) (.loop mulBody))

/-! ## Polynomials, by Horner's rule -/

/-- Horner evaluation of the coefficient list `cs` on a unary input `m`:
`polyProg (c :: cs)` computes `c + m · polyProg cs`. -/
def polyProg : List ℕ → Prog
  | [] => .nil
  | c :: cs =>
    .let_ (polyProg cs)
      (.let_ (.let_ (.cons (.var 1) (.var 0)) mulProg)
        (.let_ (.cons (.const (ofNat c)) (.var 0)) addProg))

end Prog

/-! ## Evaluating a fixed polynomial, primitively recursively

The answer-length budget of the tabulation is `bound.eval (n + λ)` for the fixed polynomial
`bound` of `MIPRE.GapCompression`, so `MIPRE.Halting.tab_computable` needs a polynomial's
evaluation to be primitive recursive in its argument. It goes through this file's own
`Data.polyEval` and `hornerCoeffs` rather than Mathlib's `Polynomial` API: the coefficient
list is fixed data, and Horner's rule on a fixed list is a fixed composition of `+` and `*`.
-/

end MIPRE.Cost


