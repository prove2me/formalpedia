-- Prove2me | Definitions.Def_PNormRegLib_AddressBound
-- name    : PNormRegLib_AddressBound
-- status  : Definition
-- author  : @milia
-- created : 2026-11-15T08:10:03.11907+00:00
-- url     : https://prove2.me/theorems/1e059b9e-abe5-42e0-b91b-b5aeef668d92
-- title:
--   Bounded pointers and literal bounds for the real RAM
-- statement:
--   Consider the real RAM of the definition `PNormReg_Machine`, with integer pointer registers $p_0,p_1,\dots$ and integer memory $I:\mathbb Z\to\mathbb Z$.
--
--   1. For $X\in\mathbb Z$, a state $s$ is **$X$-bounded** if
--   $$|p_q|\le X\ \text{ for every pointer register } q\qquad\text{and}\qquad |I(z)|\le X\ \text{ for every } z\in\mathbb Z.$$
--   2. A program $P$ has **literal bound $L$** if every integer constant $c$ of an instruction $p_q:=c$ of $P$ satisfies $|c|\le L$.
--
--   The machine has no pointer multiplication and no conversion from reals to integers. Its integers are therefore built from literals, inputs and earlier integers by addition and subtraction only, and these two quantities control every integer value, and hence every memory address, a run can produce.
--
--   **Formalization Note.** `PBounded X s` and `LitBound P L`.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; the doubling argument is the standard one for machines whose only integer arithmetic is addition and subtraction.

import Mathlib
import Definitions.Def_PNormReg_Machine

namespace PNormRegLib

open PNormReg

/-- Every pointer register and every integer-memory cell of `s` has absolute value at most `X`. -/
def PBounded (X : ℤ) (s : State) : Prop :=
  (∀ q, |s.core.ptrs q| ≤ X) ∧ ∀ z, |s.integerMemory z| ≤ X

/-- Every integer literal of `P` (the constant `c` of an instruction `pset q c`) has absolute value
at most `L`. -/
def LitBound (P : Program) (L : ℤ) : Prop :=
  ∀ q c, Instr.core (.pset q c) ∈ P → |c| ≤ L

end PNormRegLib


