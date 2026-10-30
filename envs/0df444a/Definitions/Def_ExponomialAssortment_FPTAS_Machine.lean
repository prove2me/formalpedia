-- Prove2me | Definitions.Def_ExponomialAssortment_FPTAS_Machine
-- name    : ExponomialAssortment_FPTAS_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:12:11.325472+00:00
-- url     : https://prove2.me/theorems/2573b76b-78be-495e-881d-a25cc5911353
-- title:
--   Binary machine execution and numerical encodings
-- statement:
--   A finite-state Post-Turing machine over blank and two binary symbols, a step-indexed halting execution relation, self-delimiting binary integers and rational numbers, and finite exact expressions. There is no real-arithmetic oracle or assumed comparison procedure.
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, §2.4 and §5.3, printed 9, 19, PDF 10, 20

import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Rat.Defs

namespace ExponomialAssortment.FPTAS
open Turing

/-- A fixed finite alphabet and finite control; no numerical oracle instructions. -/
structure BinaryMachine where
  states : ℕ
  code : TM0.Machine (Option Bool) (Fin (states + 1))

def MachineRuns (M : BinaryMachine) (input output : List Bool) (time : ℕ) : Prop :=
  ∃ c : ℕ → TM0.Cfg (Option Bool) (Fin (M.states + 1)),
    c 0 = TM0.init (input.map some) ∧
    (∀ t, t < time → TM0.step M.code (c t) = some (c (t + 1))) ∧
    TM0.step M.code (c time) = none ∧
    (c time).Tape = Tape.mk₁ (output.map some)

/-- Self-delimiting binary natural: unary bit-length, separator, little-endian bits. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeInt (z : ℤ) : List Bool := (decide (z < 0)) :: encodeNat z.natAbs

def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

inductive ExactExpr where
  | rational : ℚ → ExactExpr
  | add : ExactExpr → ExactExpr → ExactExpr
  | mul : ExactExpr → ExactExpr → ExactExpr
  | exp : ExactExpr → ExactExpr

def encodeExpr : ExactExpr → List Bool
  | .rational q => [false, false] ++ encodeRat q
  | .add a b => [false, true] ++ encodeExpr a ++ encodeExpr b
  | .mul a b => [true, false] ++ encodeExpr a ++ encodeExpr b
  | .exp a => [true, true] ++ encodeExpr a

end ExponomialAssortment.FPTAS


