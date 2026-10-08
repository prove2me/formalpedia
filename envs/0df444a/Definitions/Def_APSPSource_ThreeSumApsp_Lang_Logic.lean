-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
-- name    : APSPSource_ThreeSumApsp_Lang_Logic
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:21:54.483128+00:00
-- url     : https://prove2.me/theorems/0f0fb5b6-9dcf-4a34-8f0f-c60b941eec9d
-- title:
--   Bounded termination assertions for the structured language
-- statement:
--   Fix execution limits $\lambda$, a program $P$, a call depth $d$, a statement $s$, an initial state $\sigma$, a natural step bound $T$, and a postcondition $Q$. Define
--
--   $$\operatorname{Ends}(\lambda,P,d,s,\sigma,T,Q)\iff\exists\sigma',t,\ \operatorname{Exec}(\lambda,P,d,s,\sigma,\sigma',t)\land t\le T\land Q(\sigma').$$
--
--   The bundle also provides expression notation for local variables, natural constants, and memory loads. An integer comparison $a\le b$ is represented by $a<b+1$; branching on inequality swaps the branches of an equality test.
--
--   The standard-limits predicate packages the assumptions
--
--   $$\mathrm{space}\le\mathrm{word},\qquad100\le\mathrm{word},$$
--
--   so addresses and the routine constants fit the stated word-magnitude bound. These definitions supply the assertions and notation used to state the later program-verification rules.
--
--   References:
--
--   1. [Source formalization, lines 77–80](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L77-L80).
--   2. [Source formalization, lines 214–219](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L214-L219).
--   3. [Source formalization, lines 230–231](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L230-L231).
--   4. [Source formalization, lines 234–235](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L234-L235).
--   5. [Source formalization, lines 262–266](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L262-L266).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L77-L80; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L214-L219; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L230-L231; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L234-L235; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Logic.lean#L262-L266

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Runs -/



































/-! ## The rules -/

/-- The statement s, started in σ, ends within T steps in a state that satisfies Q. -/
def Ends (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (T : ℕ) (Q : State → Prop) :
    Prop :=
  ∃ σ' c, Exec lim P d s σ σ' c ∧ c ≤ T ∧ Q σ'

































































































































/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/

/-- Local variable number x. -/
abbrev v (x : ℕ) : Expr := .var x
/-- The constant n. -/
abbrev k (n : ℕ) : Expr := .const n
/-- The memory cell at address a. -/
abbrev M (a : Expr) : Expr := .load a
/-- The sum of two expressions. -/
infixl:65 " +' " => Expr.op Op.add
/-- The difference of two expressions. -/
infixl:65 " -' " => Expr.op Op.sub
/-- The product of two expressions. -/
infixl:70 " *' " => Expr.op Op.mul
 infix:50 " <' " => Cond.lt
 infix:50 " =' " => Cond.eq
 infixr:30 " ;; " => Stmt.seq

/-- The test a ≤ b, written as a < b + 1. -/
abbrev Cond.le (a b : Expr) : Cond := (Light.Cond.lt a ((Light.Expr.op Light.Op.add) b (k 1)))
@[inherit_doc] infix:50 " ≤' " => Cond.le

/-- Branching on a ≠ b: the branches of the test a = b, swapped. -/
abbrev Stmt.iteNe (a b : Expr) (s₁ s₂ : Stmt) : Stmt := .ite ((Light.Cond.eq a b)) s₂ s₁





/-! ## Simplification -/

attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
















/-! ## The limits -/

/-- The standing assumptions about the limits: an address fits in a word, and so do the constants
of the programs. -/
structure Std (lim : Limits) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  const_le : (100 : ℤ) ≤ lim.word


















end Light


