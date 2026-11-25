-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_PackingRAM
-- name    : PandoraKnapsack_Skipping_PackingRAM
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:43:16.776693+00:00
-- url     : https://prove2.me/theorems/91bc25d5-0eeb-5655-9c08-da9542d42cf0
-- title:
--   Costed implementation of the bounded projected-row packing algorithm
-- statement:
--   The program checks a finite grid of profit guesses and iterates clipped separating-row steps for a dimension-dependent budget. It explicitly computes every dot product and retains the best feasible rescaled vector.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, explicit implementation of Algorithm 1 and the polynomial-time clause of Theorem 5.1 under the machine model in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef. Derived implementation for the dyadic approximate solver.

import Definitions.Def_PandoraKnapsack_Skipping_ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
namespace Packing
noncomputable section

abbrev dReg : N := .var 3
abbrev rReg : N := .var 4
abbrev colReg : N := .var 25
abbrev rowReg : N := .var 26
abbrev guessReg : N := .var 27

def atCol (t : Fin 16) : R := .get t colReg

def matrixCoeff : R := .get 2 (rowReg * dReg + colReg)

def columnsLoop (body : C) : C := .forN 25 dReg body

def fill (t : Fin 16) (e : R) : C := columnsLoop (.put t colReg e)

/-- The accumulator in real register 28 is reset for every dot product. -/
def scalarProduct (a b : R) : C := .seq (.letR 28 0)
  (columnsLoop (.letR 28 (.var 28 + a*b)))

def projectedUpdate (a : R) : C := columnsLoop <|
  .seq (.letR 29 (atCol 5 - .var 25 * a)) <|
    .itePos (.var 29 - 1) (.put 5 colReg 1)
      (.itePos (.var 29) (.put 5 colReg (.var 29)) (.put 5 colReg 0))

/-- A violated row performs the projection immediately, then marks the scan as done. -/
def checkRow (a limit : R) : C := .seq (scalarProduct a (atCol 5)) <|
  .itePos (.var 28 - limit - (1/8 : R)) (.seq (projectedUpdate a) (.letR 27 1)) .skip

/-- The profit constraint comes first, followed by the original rows in matrix order. -/
def oneScan : C := .seq (.letR 27 0) <|
  .seq (checkRow (0 - atCol 3) (0 - .nat guessReg / 8)) <|
  .seq (.forN 26 rReg (.itePos (.var 27) .skip (checkRow matrixCoeff 1))) <|
  .itePos (.var 27) .skip (.letR 26 1)

def fuelExpr : N := 64 * (dReg+1) * (dReg+1) + 1

def tryGuess : C := .seq (fill 5 0) <|
  .seq (.letR 26 0) <|
  .seq (.forN 28 fuelExpr (.itePos (.var 26) .skip oneScan)) <|
  .seq (.itePos (.var 26) (fill 5 ((8/9 : R) * atCol 5)) (fill 5 0)) <|
  .seq (scalarProduct (atCol 3) (atCol 4)) <|
  .seq (.letR 30 (.var 28)) <|
  .seq (scalarProduct (atCol 3) (atCol 5)) <|
  .itePos (.var 28 - .var 30) (fill 4 (atCol 5)) .skip

end
end Packing

/-- Input: dimensions in N3,N4, matrix in table 2 at row*d+col and profits in table 3.
Output: table 4. Scratch consists of table 5, N25..28 and R25..30. -/
noncomputable def packingCode : C := .seq (Packing.fill 4 0) <|
  .seq (.letR 25 (1 / (8 * .nat (Packing.dReg + 1)))) <|
  .forN 27 (8 * Packing.dReg + 1) Packing.tryGuess

end PandoraKnapsack.Skipping.ArrayRAM


