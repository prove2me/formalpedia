-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
-- name    : APSPSource_ThreeSumApsp_Machine_Realized
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:08:52.481953+00:00
-- url     : https://prove2.me/theorems/f9b8eb87-30d8-4f9d-8182-5a1d53dc3b73
-- title:
--   Uniform realization of an integer-input problem with a time function
-- statement:
--   Let $Q$ be an integer-input problem and let $T:\mathbb N\times\mathbb R\to\mathbb R$ be a proposed time function in size and magnitude bound. The realization predicate requires
--
--   $$\forall\kappa\in\mathbb N,\ \exists P\ \exists b\in\mathbb N\ \exists c\in\mathbb R_{\ge0},\quad P\text{ solves every bounded instance with }U=n^\kappa\text{ within }c\max\{T(n,U),0\}+c\text{ steps}.$$
--
--   Here $P$ is a finite word-RAM program, $b$ is a natural word-size slope, and the displayed nonnegativity requirement applies to the real constant $c$; the underlying solve predicate quantifies over every admissible word size. The program, slope, and constant may depend on $\kappa$, but not on the instance or its size. Size zero is included.
--
--   The nonnegative truncation and additive constant keep the time allowance meaningful for all inputs. This is the predicate used to connect concrete machine implementations to later asymptotic claims; defining it does not supply a realizing program.
--
--   References:
--
--   1. [Source formalization, lines 35–41](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Realized.lean#L35-L41).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Machine/Realized.lean#L35-L41

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
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
namespace EndStatement
end EndStatement


/-!
# A running time that is realized on the word RAM

The deductions between running-time claims are made for an arbitrary reading `M : DetTimeModel` of
"is solved by a deterministic algorithm in time T".  `RealizedWithin` is the link to programs: the
problem is solved on the word RAM, in its input layout, within `c T + c` steps.
-/

@[expose] public section

open EndStatement (Instr)

namespace ThreeSumApsp.WordRam












/-- `RealizedWithin` for a problem of the form of `EndStatement.lean`, on the instances of all
sizes, 0 included: for every exponent `κ` some program solves all instances whose numbers are
bounded by `U = n^κ`, within `c max(T, 0) + c` steps. (A running time `T n U` says nothing at
`n = 0`.) -/
def Realized (Q : EndStatement.Problem) (T : ℕ → ℝ → ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List Instr) (b : ℕ) (c : ℝ), 0 ≤ c ∧
    Solves (ofEnd Q) P b (fun x => x.U = x.n ^ κ) (fun x => c * max (T x.n x.U) 0 + c)

end ThreeSumApsp.WordRam


