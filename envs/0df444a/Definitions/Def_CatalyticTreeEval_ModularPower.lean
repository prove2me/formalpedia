-- Prove2me | Definitions.Def_CatalyticTreeEval_ModularPower
-- name    : CatalyticTreeEval_ModularPower
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:15:50.722271+00:00
-- url     : https://prove2.me/theorems/79d907da-ff97-419b-9aa8-f27e0287a6b2
-- title:
--   Bounded-register binary modular exponentiation
-- statement:
--   Define an iterative square-and-multiply algorithm with a retained base, exponent and accumulator. Each round halves the exponent and reduces products modulo the modulus. The reference algorithm takes one more than the binary logarithm of the exponent in rounds. Correctness, bounds and native finite-machine implementation are separate obligations.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 3.4, Lemma 3.19, efficient CRT reconstruction infrastructure.

import Definitions.Def_CatalyticTreeEval_Main_Encoding

set_option autoImplicit false

namespace CatalyticTreeEval.BinaryArithmetic

/-- Three nonnegative registers for square-and-multiply. -/
structure PowerState where
  base : ℕ
  exponent : ℕ
  accumulator : ℕ
  deriving DecidableEq

/-- One binary-exponentiation round. Products are reduced before the next
round, so all retained arithmetic registers are smaller than the modulus. -/
def powerStep (m : ℕ) (s : PowerState) : PowerState where
  base := s.base * s.base % m
  exponent := s.exponent / 2
  accumulator := if s.exponent % 2 = 1 then s.accumulator * s.base % m
    else s.accumulator

def powerRun (m : ℕ) (s : PowerState) : ℕ → PowerState
  | 0 => s
  | rounds + 1 => powerStep m (powerRun m s rounds)

/-- A fixed number of rounds determined by the exponent's binary width. The
native implementation uses a counter and these three registers, not a stack. -/
def modularPower (m a exponent : ℕ) : ℕ :=
  (powerRun m ⟨a % m, exponent, 1 % m⟩ (Nat.log 2 exponent + 1)).accumulator

end CatalyticTreeEval.BinaryArithmetic


