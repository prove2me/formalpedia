-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
-- name    : APSPSource_ThreeSumApsp_Machine_Solving
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:47:07.01112+00:00
-- url     : https://prove2.me/theorems/8466e5a9-8b79-4743-bebe-014ad0b28e99
-- title:
--   Bounded problem instances and the word-RAM problem interface
-- statement:
--   Let $Q$ be a computational problem with instances $x$ of natural size $n$, integer input list $I_Q(x)$, decision predicate $Y_Q(x)$, and output predicate $O_Q(x,o)$. A bounded instance packages $(n,U,x)$ with a natural bound $U$ satisfying
--
--   $$\forall z\in I_Q(x),\ |z|\le U.$$
--
--   The accompanying structural lemma states this bound as an integer inequality. The adapter to the general word-RAM problem interface uses $[n]$ as its size-parameter list, prepends $n$ to the input, and specifies the answer by
--
--   $$I(n,U,x)=[n]\mathbin{+\!+}I_Q(x),\qquad
--   A((n,U,x),v,o)\iff(v=\mathrm{true}\iff Y_Q(x))\land O_Q(x,o).$$
--
--   Here $+\!+$ is list concatenation, $v$ is the Boolean verdict, and $o$ is the integer output sequence. The magnitude bound is carried as certified instance data; it is not itself appended to the input.
--
--   This definition connects the end-statement problem specifications to the more general interfaces used in the machine correctness proofs.
--
--   References:
--
--   1. [Source formalization, lines 40–65](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Solving.lean#L40-L65).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Solving.lean#L40-L65

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The notions of solving are monotone

That the program `P` with slope `b` solves the problem on the instances in `dom` within time `T`, at
every admissible word size, stays true for a larger slope, a smaller set of instances and a larger
time bound (`Solves.mono`).  The same holds for a two-stage data structure (`IsDataStructure.mono`).

* The item statements on the problems of the end statement use `SolvesWithin`.  It is `Solves` for
  the problem `ofEnd Q`, whose instances carry their size and a bound on their numbers
  (`solvesWithin_iff`, `solvedInTimeAt_iff`).

* A statement "there are a program and a constant `C` such that the time is at most `C f(x)`" stays
  true for every bound `g` with `f = O(g)`: `exists_solves_of_dominated`, and
  `exists_isDataStructure_of_dominated` for a data structure.
* For the bounds `O(n^a (log n)^e)` in one size: a larger exponent (`SolvedInTime.mono_exponent`),
  and a larger exponent that absorbs the logarithms (`SolvedInPolylogTime.solvedInTime`).
-/

public section

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)
open Filter

/-! ## The problems of the end statement as problems in the sense of `Problem` -/

/-- An instance of a problem of the end statement, with its size `n` and a bound `U` on its
numbers. -/
structure Bounded (Q : EndStatement.Problem) where
  /-- The size. -/
  n : ℕ
  /-- The bound on the absolute values of the numbers of the input. -/
  U : ℕ
  /-- The instance. -/
  x : Q.Instance n
  /-- The numbers are bounded. -/
  bounded : ∀ a ∈ Q.input x, a.natAbs ≤ U

/-- The numbers of the input of a bounded instance are within the bound. -/
theorem Bounded.abs_le {Q : EndStatement.Problem} {x : Bounded Q} {a : ℤ} (ha : a ∈ Q.input x.x) :
    |a| ≤ (x.U : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast x.bounded a ha

/-- A problem of the end statement as a `Problem`, read as `EndStatement.Problem.SolvedBy` reads it:
the size is the one parameter of the word size, it stands in cell 0 in front of the input, the
verdict has to be `accept` exactly if the answer is yes, and the output has to be right. -/
abbrev ofEnd (Q : EndStatement.Problem) : Problem where
  Inst := Bounded Q
  params x := [x.n]
  input x := (x.n : ℤ) :: Q.input x.x
  IsAnswer x verdict out := (verdict = true ↔ Q.yes x.x) ∧ Q.output x.x out





























/-! ## Monotonicity -/




























/-! ## Bounds up to a constant -/

































/-! ## Bounds in one size -/


































end ThreeSumApsp.WordRam


