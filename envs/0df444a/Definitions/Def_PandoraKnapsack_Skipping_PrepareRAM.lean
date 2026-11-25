-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_PrepareRAM
-- name    : PandoraKnapsack_Skipping_PrepareRAM
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:43:51.795387+00:00
-- url     : https://prove2.me/theorems/a2c918f4-e39e-4719-8615-dbda3263f3f4
-- title:
--   Dyadic LP coefficient assembly on the costed machine
-- statement:
--   A sequence of doubling steps generates time labels. Nested loops compute effective weights and each normalized packing coefficient via the coefficient oracles. The maximum initial profit normalizes nonnegative objective coefficients.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, explicit implementation of Algorithm 1 and the polynomial-time clause of Theorem 5.1 under the machine model in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef. Derived implementation for the dyadic approximate solver.

import Definitions.Def_PandoraKnapsack_Skipping_ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM.Prepare
noncomputable section

private abbrev v := N.var
private abbrev x := R.var

/-- Labels are stored as real coefficients. Only their ordinal indices are used as
addresses, including when capacity is exponentially larger than its bit length. -/
def labels : C :=
  .seq (.letN 2 1) <| .seq (.put 0 0 (.lit 0)) <| .seq (.letR 1 (.lit 1)) <|
    .whilePos ((x 0 + R.lit 1) - x 1)
      (.seq (.put 0 (v 2) (x 1)) <| .seq (.letN 2 (v 2 + 1)) (.letR 1 (x 1 + x 1)))

/-- Register 3 is the number of columns, register 4 the number of packing rows. -/
def dimensions : C :=
  .seq (.letN 3 (v 0 * (v 1 * v 2))) (.letN 4 (v 0 + v 2))

/-- Flatten item, choice, and time-label ordinals in lexicographic order. -/
def colAddr : N := (v 5 * v 1 + v 6) * v 2 + v 7

/-- Raw rewards for one column, evaluated at its dyadic start. -/
def weightBody : C :=
  .seq (.value 3 (v 5)) <| .seq (.cost 4 (v 5) (v 6)) <|
  .seq (.cdf 5 (v 5) (v 6) (x 0 - .get 0 (v 7))) <|
    .put 1 colAddr (x 3 * x 5 - x 4)

def weights : C := .forN 5 (v 0) (.forN 6 (v 1) (.forN 7 (v 2) weightBody))

/-- Keep the largest initial profit in real register 2. -/
def maxBody : C :=
  let val := R.get 1 ((v 5 * v 1 + v 6) * v 2)
  .itePos (val - x 2) (.letR 2 val) .skip

def maximum : C := .seq (.letR 2 0) (.forN 5 (v 0) (.forN 6 (v 1) maxBody))

/-- Profit vector, with negative profits discarded and total real division at zero. -/
def profits : C :=
  .forN 9 (v 3) <|
    .itePos (.get 1 (v 9)) (.put 3 (v 9) (.get 1 (v 9) / x 2)) (.put 3 (v 9) 0)

/-- Fill the item-incidence entry for one row and column. The row index in register 8
is a natural number, so its difference from register 5 has integer magnitude. -/
def itemEntry : C :=
  let addr := v 8 * v 3 + colAddr
  let diff := R.nat (v 8) - R.nat (v 5)
  .itePos (1 - diff * diff) (.put 2 addr 1) (.put 2 addr 0)

/-- Fill a checkpoint entry. At zero the numerator is zero and total division gives zero. -/
def timeEntry : C :=
  let addr := (v 0 + v 8) * v 3 + colAddr
  let t := R.get 0 (v 7)
  let r := R.get 0 (v 8)
  .itePos (t-r) (.put 2 addr 0)
    (.seq (.truncMean 6 (v 5) (v 6) r) (.put 2 addr (x 6 / (2*r))))

def itemMatrix : C := .forN 5 (v 0) (.forN 6 (v 1) (.forN 7 (v 2) (.forN 8 (v 0) itemEntry)))

def timeMatrix : C := .forN 5 (v 0) (.forN 6 (v 1) (.forN 7 (v 2) (.forN 8 (v 2) timeEntry)))

def matrix : C := .seq itemMatrix timeMatrix

def code : C := .seq labels (.seq dimensions (.seq weights (.seq maximum (.seq profits matrix))))

end
end PandoraKnapsack.Skipping.ArrayRAM.Prepare


