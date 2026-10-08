-- Prove2me | Definitions.Def_ThreeSumSource_CH20Contracts
-- name    : ThreeSumSource_CH20Contracts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-06T17:18:42.324543+00:00
-- url     : https://prove2.me/theorems/6909f5c8-2a67-4152-8d8d-3b78f4d21080
-- title:
--   Program contracts and supporting definitions for the Chan–He 3SUM reduction
-- statement:
--   The source program bodies, memory contracts, time and resource bounds, and arithmetic parameters used by the verified front-end routines of the deterministic Chan–He reduction from 3SUM to Convolution-3SUM. These definitions reuse the existing APSP programming language and machine definitions. They are taken from Anthropic’s formalization; correctness and running-time claims are proved separately.
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/ChanHe/Program.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Realized
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem19_Choice
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Statements_Exponents
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Corollary15_16
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem21_22
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_UpperBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Ceil
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_ThreeSumSource_ReductionClaims
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Init
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Iterate
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Light_Sec3_claim_VW13_Theorem_3_3
import Theorems.Thm_Light_Sec3_claim_VW18_Theorem_4_2
import Theorems.Thm_Light_Sec3_claim_apspFromMinPlus
import Theorems.Thm_Light_Sec3_et17_spec
import Theorems.Thm_Light_Sec3_obeysBound17_hostTime
import Theorems.Thm_Light_Sec4_allInstances26_solves
import Theorems.Thm_Light_Sec4_allInstancesTime26_le
import Theorems.Thm_Light_Sec4_pre31_program31
import Theorems.Thm_Light_Sec4_queryAt_spec
import Theorems.Thm_Light_Sec4_specs40
import Theorems.Thm_Light_Wrap_realized
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually
import Theorems.Thm_ThreeSumApsp_FromClaims_solvedAt_of_realized
import Theorems.Thm_ThreeSumApsp_Theorem19_Choice_ceil_le_sqrt
import Theorems.Thm_ThreeSumApsp_WordRam_bigO_of_le_rpow
import Theorems.Thm_ThreeSumApsp_goodTime_uniformTime
import Theorems.Thm_TrulySubcubicAPSP_sourceSpecificationTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ThreeSumApsp.Spec.ChanHeArray
end ThreeSumApsp.Spec.ChanHeArray


-- Original source module: PaperStatements
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Further statements of the paper

Statements of the paper «Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse
Lopsided Graphs» (Josh Alman, Virginia Vassilevska Williams) beyond the five claims of
`EndStatement.lean`, each as a proposition, with the definitions that they use; and statements that
the notions which this file and `EndStatement.lean` both define agree. The file imports
`EndStatement.lean` and Mathlib. It proves none of the statements: the proofs are in the library,
the folder `ThreeSumApsp/`. The five claims do not depend on this file: it is for a reader who wants
to believe a further lemma, equation, table or theorem of the paper.

`Challenge/PaperStatements.lean` states that the propositions hold: `PaperStatements.lemma_6` says
that `PaperStatements.Lemma_6` holds, and `ThreeSumApsp.wordRam_theorem_5` that the running-time
sentence `ThreeSumApsp.WordRam.Items.Theorem_5` holds.

The parts, in this order:

* Section 2: definitions
* Section 2: statements
* Section 3: definitions
* The reduction of Chan and He: definitions
* Section 3: statements
* Section 4: definitions
* Section 4: statements
* Section 5: definitions
* Section 5: statements
* The word RAM: problems
* Agreement with the definitions of EndStatement.lean
* The word RAM: running times

In a comment, "this part" means the part in which the comment stands.
-/

@[expose] public section

/-!
## Section 2: definitions

Definitions used by the statements of Section 2, "Quickly computing certain entries of a thin matrix
product".  They follow the paper's order and names.  Only what the statements need, directly or
through another definition, is defined here; the other notions of the section, among them the tiling
of Section 2.3.4, are defined with the proofs.

Conventions used throughout.

* The paper numbers indices from 1; Lean's `Fin n` starts at 0.  So the paper's `x₁, x₂, x₃` are
  `LeftVar.x 0, LeftVar.x 1, LeftVar.x 2`, the paper's `p₂₁` is `LeftVar.p 1 0`, and so on.
* A string of length `L` over an alphabet `α` is a function `Fin L → α`.  The paper's level
  `ℓ ∈ {1, …, L}` is the element `ℓ - 1` of `Fin L`; the order of the levels is the order of
  `Fin L`.
* The string `s u'` (the variable `s` followed by the string `u'`) is `Fin.cons s u'`; the first
  variable of `u` is `u 0` and the rest of it is `Fin.tail u`.  The empty string is `Fin.elim0`.
* A linear form is given by the vector of its coefficients: a linear form in the left variables is a
  function `LeftVar → ℤ`.  `Pi.single s 1` is the form consisting of the single variable `s`.
-/

section Sec2Definitions

open Finset

namespace ThreeSumApsp

/-! ### 2.2 Schönhage's identity for an inner product and an outer product -/






















































/-! ### 2.3.1 The recursion -/



















/-! ### 2.3.2 Unraveling the recursion computation -/













/-! ### 2.3.3 Batch computation of multiple matrix products -/









































/-! ### 2.3.4 Tiling the N × D × N product by products of shape N₀ × D × N₀: the number `M` -/



/-! ### 2.4.1 Sharing the encoding -/





/-! ### 2.4.2 Skipping the calls that are not needed -/























/-! ### 2.4.3 Few leaves contribute to a sparse set of entries -/













end ThreeSumApsp

end Sec2Definitions

/-!
## Section 2: statements

The numbered lemmas and equations of Section 2 of the paper, and the figures that
assert something of their own.

* Equation (1) is `Eq_1`. Equations (2) and (3) are the definitions `Mult` and `gamma`. Equation (4)
  is the display of `Lemma_9`. Equation (5) is stated in three pieces: `Eq_5_ratio`, `Eq_5_bound`,
  `Eq_5`. Equation (6) is `Eq_6`.
* Lemmas 6 to 11 are `Lemma_6` to `Lemma_11`, each as one statement.
* Of Figure 3 the two worked examples of the caption are stated: `Figure_3`. Of Figure 4 the worked
  example is stated: `Figure_4`. Figure 6 is `Figure_6`; the two counts
  `Sec2_card_contributing_of_order` and `Sec2_card_outStr_of_leaf` say what its numbers count.
* Theorem 5 is a sentence about a machine. It is `Items.Theorem_5`. So of the tiling (Section 2.3.4)
  and of the proof of Theorem 5 (Section 2.4.4) nothing is stated here but the number `M` and
  equation (6): the statements of this part are about a single run of the recursion.
* Remark 12 makes no mathematical claim. Figure 2 recalls Strassen's recursion for intuition; only
  identity (1) is stated. Figure 5 makes no claim of its own. Figure 7 draws the count of Lemma 11;
  two remarks of its caption, that "the bound |U|α_d grows with d up to d ≈ 0.9m" and that the proof
  splits at a point "which is not necessarily where the two bounds cross", are not stated.

`docs/INDEX.md` says for each item of the paper what is stated and what is not.

A hypothesis that is not in the printed text is marked NOTE in the docstring. A hypothesis of the
printed text that is not needed (such as m ≥ 1, Section 2.3.3) is left out without a mark.
-/

section Sec2Statements

open Finset

namespace PaperStatements

open ThreeSumApsp

/-! ### 2.1 Strassen's recursive algorithm -/



/-! ### 2.2 Schönhage's identity for an inner product and an outer product -/



/-! ### 2.3.1 The recursion -/



/-! ### 2.3.2 Unraveling the recursion computation -/





/-! ### 2.3.3 Batch computation of multiple matrix products -/





/-! ### 2.4.2 Skipping the calls that are not needed -/



/-! ### 2.4.3 Few leaves contribute to a sparse set of entries -/















/-! ### 2.4.4 Proof of Theorem 5 -/



end PaperStatements

end Sec2Statements

/-!
## Section 3: definitions

Definitions used by the statements of Section 3, "Exact Triangle reduces to computing certain
entries of a thin matrix product".  They follow the paper's order and names.  Only what the
statements need, directly or through another definition, is defined here; some of the definitions
are used by the statements about programs and not by those of Section 3.

Conventions used throughout.

* A part of `n` vertices is the type `Fin n`.  A pair `(a, b) ∈ A × B` is an element of
  `Fin n × Fin n`, a triple `(a, b, c) ∈ A × B × C` an element of `Fin n × Fin n × Fin n`.
* The paper numbers the pieces from 1; here pieces and chunks are numbered from 0.
* `√D` is the real square root `Real.sqrt D`, `⌊·⌋` and `⌈·⌉` are `Nat.floor` and `Nat.ceil` of real
  numbers, and `log` is the natural logarithm `Real.log` unless a base is written.
* `x ≡ y (mod p)` is `Int.ModEq`, written `x ≡ y [ZMOD p]`.  A residue or label in `ℤ_p` is an
  element of `Fin p`.
* No definition of this part mentions time.  For the sentences of the paper about running time see
  `docs/REMARKS.md`, "Section 3: running times". -/

section Sec3Definitions

namespace ThreeSumApsp

/-! ### 3.1 The Lopsided All-Edges Sparse Triangle problem -/



attribute [instance] LopInstance.fintypeM













/-! #### Cutting a set of pairs into sets of bounded size

Corollary 15 ("splitting W into sets of at most n²/√D query pairs") and the proof of Theorem 17
("cut it into chunks of at most n²/√D query pairs") cut a set of pairs into smaller sets.  The paper
does not say how; we cut along the row-major order of the pairs. -/











/-! ### 3.2 A deterministic reduction from Exact Triangle to Lop-AE-SparseTri -/



namespace TriangleInstance













end TriangleInstance



/-! #### Hashing modulo a prime (proof of Theorem 17) -/



namespace TriangleInstance





end TriangleInstance

/-! #### The instances (proof of Theorem 17) -/











namespace TriangleInstance









/-! #### Witnesses (proof of Theorem 17) -/









end TriangleInstance

/-! ### 3.4 3SUM and APSP reduce to Exact Triangle: the problems -/











/-! A directed graph on the vertices `Fin n` with edge weights in `R` is a function
`w : Fin n → Fin n → WithTop R`: `w i j` is the weight of the edge from `i` to `j`, and `⊤` (that
is, `+∞`) if there is no such edge.  A walk that starts at `i` is given by the list of the vertices
it visits after `i`. -/















/-! #### The shape of the two reductions of [VW13] that Theorem 21 cites -/









/-! #### Asymptotic notation of Section 3 -/







end ThreeSumApsp

end Sec3Definitions

/-!
## The reduction of Chan and He: definitions

[CH20] is Timothy M. Chan and Qizheng He, *Reducing 3SUM to Convolution-3SUM*, Proc. 3rd SIAM
Symposium on Simplicity in Algorithms (SOSA 2020).  Theorem 21(a) of the paper cites [CH20].  What
is used is the reduction in the proof of its Theorem 5.1, a deterministic reduction from 3SUM to
polylogarithmically many instances of Convolution-3SUM.  The theorem itself is a statement about
running times, for 3SUM on three sets and Convolution-3SUM on three arrays.

This part defines such a reduction, as a function from inputs to lists of instances.  What is proved
about it is stated by `Theorem_21a_threeSum_to_convolution` and `Theorem_21a_threeSum_to_exact`.
The construction follows the proof of Theorem 5.1.  Where it differs from [CH20], and what it adds,
is listed in `docs/REMARKS.md`, "Section 3: cited results".

### Why all these definitions are trusted

The list of instances depends on the input.  A statement of the form "there is a list of instances
such that the input has a solution iff one of them has" would be true for trivial reasons.  So the
statements are about the explicitly defined function `instances`, which is built from `reduction`,
and their worth rests on the definitions of this part.

* `reduction` takes three sets of at most n integers.  It returns the nodes of a recursion tree, and
  each node stands for one instance of Convolution-3SUM on three arrays.  3SUM on three sets (are
  there a, b, c, one from each set, with a + b + c = 0?) and Convolution-3SUM on three arrays (are
  there i, j with X i + Y j = Z (i + j)?) are the problems of Definitions 2.1 and 2.2 of [CH20], for
  which Theorem 5.1 is stated.
* `instances` takes n numbers, for the problem whether three of them, at three different positions,
  sum to 0.  It returns instances of Convolution-3SUM on one array.  These are the problems of the
  paper, 3SUM in the reading fixed at `ThreeSum`.

Evaluated literally, `coll` and `heavy` compare all pairs of elements, and each search tests all its
candidates, so the definitions are a specification and not the algorithm.  Nothing in this part is
about a machine.

Every choice that the two functions make depends only on which elements collide and how many pairs
do, on which sets are empty, on binary digits of the numbers and on how often a number occurs.  None
depends on whether a solution exists, with one exception: the solution 0, 0, 0 exists exactly when 0
occurs at three positions.  So it is detected by counting, and it is reported through the three-set
input (`zeroSet x`, {0}, {0}), which has a solution exactly in that case.

In this part `ν` is a node of the recursion tree.  It is not the exponent ν of Theorem 21, which
the statements call `κ`.
-/

section ChanHeDefinitions

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ### Collisions and heavy elements -/



/-- The elements of `S` that share their residue modulo `M` with another element of `S`.  They play
the role of the bad elements of [CH20].  The other elements of `S`, those that are alone in their
residue class modulo `M`, are called light below; they play the role of the good elements of [CH20].
-/
def heavy (S : Finset ℤ) (M : ℕ) : Finset ℤ := {x ∈ S | ∃ y ∈ S, y ≠ x ∧ (M : ℤ) ∣ x - y}

/-! ### The arrays of one node -/

/-- The elements of `S` with remainder `r` modulo `M`. -/
def bucket (S : Finset ℤ) (M : ℕ) (r : ℤ) : Finset ℤ := {x ∈ S | x % (M : ℤ) = r}

/-- The array of the light elements of `S`.  Cell `i` holds the element of the bucket of `i` if that
bucket has exactly one element, and the padding value `pad` otherwise. -/
def arr (S : Finset ℤ) (M : ℕ) (pad : ℤ) (i : ℕ) : ℤ :=
  if #(bucket S M i) = 1 then ∑ x ∈ bucket S M i, x else pad

/-- The padding value `2U + 1`.  It is too large to take part in a solution among numbers of
absolute value at most `U`. -/
def pad (U : ℕ) : ℤ := 2 * U + 1

/-- The array made from the first or the second set of a node. -/
def arrXY (S : Finset ℤ) (M U : ℕ) : ℕ → ℤ := arr S M (pad U)

/-- The third array of a node.  A light element `c` of `S` is written as `-c` into the two cells `r`
and `r + M`, where `r` is the remainder of `-c`.  All other cells, and all cells from `2M` on, hold
`-pad U`. -/
def arrZ (S : Finset ℤ) (M U : ℕ) (k : ℕ) : ℤ :=
  if k < 2 * M then arr (S.image fun c => -c) M (-pad U) (k % M) else -pad U

/-! ### The choice of the modulus -/

/-- The least element of a finite set of natural numbers, and 1 if the set is empty. -/
def pick (T : Finset ℕ) : ℕ := if h : T.Nonempty then T.min' h else 1

/-- The first prime: the least `p` in `Q` modulo which each of the three sets has at most
`3Λ|S|²/|Q|` colliding pairs.  Here and below, `Q` is the set of candidate primes, and `Λ` bounds
how many of them divide a nonzero difference of two elements.  `reduction` takes the primes up to
`mPar n U` for `Q`, and `Lam U` for `Λ`. -/
def firstP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  pick {p ∈ Q | coll S₁ p * #Q ≤ 3 * Λ * #S₁ ^ 2 ∧ coll S₂ p * #Q ≤ 3 * Λ * #S₂ ^ 2 ∧
    coll S₃ p * #Q ≤ 3 * Λ * #S₃ ^ 2}

/-- The second prime, given the first: the least `q` in `Q` such that, in each of the three sets, at
most the fraction `3Λ/|Q|` of the pairs that collide modulo `p` still collide modulo `pq`. -/
def secondP (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) (p : ℕ) : ℕ :=
  pick {q ∈ Q | coll S₁ (p * q) * #Q ≤ 3 * Λ * coll S₁ p ∧
    coll S₂ (p * q) * #Q ≤ 3 * Λ * coll S₂ p ∧ coll S₃ (p * q) * #Q ≤ 3 * Λ * coll S₃ p}

/-- The modulus of a node: the product of the two primes. -/
def modulus (Q : Finset ℕ) (Λ : ℕ) (S₁ S₂ S₃ : Finset ℤ) : ℕ :=
  firstP Q Λ S₁ S₂ S₃ * secondP Q Λ S₁ S₂ S₃ (firstP Q Λ S₁ S₂ S₃)

/-! ### The recursion tree -/

/-- A node of the recursion tree: three sets and the modulus chosen for them. -/
structure Node where
  /-- The first set. -/
  S₁ : Finset ℤ
  /-- The second set. -/
  S₂ : Finset ℤ
  /-- The third set. -/
  S₃ : Finset ℤ
  /-- The modulus. -/
  M : ℕ



/-! ### The parameters -/

/-- `⌊log₂(2U)⌋ + 1`.  A nonzero difference of two numbers in `[-U, U]` has fewer prime divisors
than this, and this many binary digits are enough for every number in `[0, 2U]`. -/
def Lam (U : ℕ) : ℕ := Nat.log 2 (2 * U) + 1

/-- `⌈log₂(⌊log₂ n⌋ + 2)⌉`.  In the recursion tree of `reduction n U`, for three sets of at most
`n ≥ 1` elements each, all of absolute value at most `U` (the hypotheses of the library's lemma
`ChanHe.reduction_correct`), a set is empty after this many replacements by its heavy elements. -/
def height (n : ℕ) : ℕ := Nat.clog 2 (Nat.log 2 n + 2)

/-- The number of levels of the recursion tree that are built.  Under the hypotheses named at
`height`, each of the three sets of a node has been replaced at most `height n - 1` times, because
it is not empty.  So a node has at most `3 (height n - 1)` nodes above it. -/
def fuel (n : ℕ) : ℕ := 3 * height n - 2

/-- The number of primes that we want to choose from. -/
def wPar (n U : ℕ) : ℕ := 5 * Lam U * (Nat.sqrt n + 1)

/-- The bound `m` on the primes.  There are at least `wPar n U` primes up to `m` (the library's
lemma `ChanHe.wPar_le_card_primesLE`). -/
def mPar (n U : ℕ) : ℕ := (wPar n U + 1) * (2 * Nat.log 2 (wPar n U + 1) + 4)

/-! ### The reduction for three sets -/



/-! ### From n numbers to three sets -/

/-- The label of an element of `[-U, U]`: its value shifted into `[0, 2U]`. -/
def lab (U : ℕ) (x : ℤ) : ℕ := (x + U).toNat





/-- The numbers `2a`, for the values `a ≠ 0` that occur at two positions or more. -/
def twiceSet {n : ℕ} (x : Fin n → ℤ) : Finset ℤ :=
  ({a ∈ univ.image x | a ≠ 0 ∧ 2 ≤ #{i : Fin n | x i = a}}).image fun a => 2 * a



/-! ### Three arrays in one -/

/-- **Three arrays in one.**  With `G = 3W + 1`, where `W` bounds the entries of the three arrays,
cell `4i + 1` holds `X i + G`, cell `4i + 2` holds `Y i + 3G`, cell `4i + 3` holds `Z i + 4G`, and
cell `4i` holds `10G`.  In an equation `y_u + y_v = y_{u+v}` the multiples of `G` have to cancel,
and they do so only when `u` and `v` have the remainders 1 and 2 modulo 4. -/
def oneArray (W : ℕ) (X Y Z : ℕ → ℤ) (u : ℕ) : ℤ :=
  let G : ℤ := 3 * W + 1
  if u % 4 = 1 then X (u / 4) + G else if u % 4 = 2 then Y (u / 4) + 3 * G
  else if u % 4 = 3 then Z (u / 4) + 4 * G else 10 * G

/-- The one-array instance of a node. -/
def Node.oneArray (ν : Node) (U : ℕ) : ℕ → ℤ :=
  ChanHe.oneArray (2 * U + 1) (arrXY ν.S₁ ν.M U) (arrXY ν.S₂ ν.M U) (arrZ ν.S₃ ν.M U)

/-! ### The whole reduction -/







/-! ### Sizes for inputs of absolute value at most n ^ κ -/







end ChanHe

end ThreeSumApsp

end ChanHeDefinitions

/-!
## Section 3: statements

The claims of Section 3 of the paper, proved or cited there, that are
mathematics and not sentences about a machine.

* Theorem 17, everything but the running time: `Theorem_17`, with `Theorem_17_scanOrder_exists` (its
  hypothesis on the order of the scans can be met) and two pieces of arithmetic behind two terms of
  the additional time, `Theorem_17_hashing_sum_sq_le` and `Theorem_17_write_cost`.
* Remark 18 compares the instances of Theorem 17 with graphs of [VX20]. Stated is what the
  comparison says about the paper's own instance, namely which residues its edges and query pairs
  have: `Remark_18_block`.
* Remark 20: `Remark_20_balance`, `Remark_20_brute_force`.
* Theorem 21, which the paper cites from the literature without a proof: the correctness, the
  numbers and the sizes of the instances of the reductions, and the arithmetic behind the printed
  forms (stated for arbitrary functions, and not applied to the bounds of the reductions). Part (b):
  `Theorem_21b_repeated_squaring`, `Theorem_21b_entries_bounded`, `Theorem_21b_negative_to_exact`,
  `Theorem_21b_log_factors`. Part (a): `Theorem_21a_convolution_to_exact`, `Theorem_21a_compose`,
  and, for the reduction that the paper cites from Chan and He,
  `Theorem_21a_threeSum_to_convolution` and `Theorem_21a_threeSum_to_exact`.
* Definitions 13 and 14 are rendered by definitions. Corollaries 15 and 16 and Theorems 19 and 22
  are sentences about running time; they are stated about programs (`Items.Corollary_15` to
  `Items.Theorem_22_threeSum`).

Not stated here:

* The running time of the reduction of Theorem 17, the time bound of Theorem 21(a), and Theorem
  21(b) in its printed form ("If a deterministic algorithm solves Exact Triangle [...] in time T(s)
  [...], then [...]") have no statement.
* [VW18, Theorem 4.2] has no mathematical statement.
* Remark 23, where the paper indicates the method in one sentence and gives no proof, and
  footnote 9.
* The other sentences inside proofs, and unnumbered claims, are lemmas of the library or are not
  formalized.

`docs/INDEX.md` says for each item of the paper what is stated and what is not. `docs/REMARKS.md`,
"Section 3: running times" and "Section 3: cited results", has the details.

Hypotheses that are added or changed are marked NOTE and listed in `docs/REMARKS.md`, "Section 3:
differences".  Lower bounds that only exclude empty or degenerate cases (`1 ≤ N`, `1 ≤ U`, `0 ≤ U`,
`2 ≤ n`, `0 ≤ κ`, `0 ≤ τ` in the statements for Theorem 21) carry no NOTE.
-/

section Sec3Statements

namespace PaperStatements

open ThreeSumApsp

/-! ### 3.2 A deterministic reduction from Exact Triangle to Lop-AE-SparseTri -/

/-! #### Theorem 17, first step: hashing modulo a prime -/



/-! #### Theorem 17, second step: the instances -/



/-! #### Theorem 17, third step: witnesses -/







/-! ### 3.3 Exact Triangle in truly subcubic time

Theorem 19 is a statement about running time: `Items.Theorem_19`.
Stated here: Remark 20. -/





/-! ### 3.4 3SUM and APSP reduce to Exact Triangle

Theorem 22 is a statement about running time (`Items.Theorem_22_first`, `Items.Theorem_22_second`,
`Items.Theorem_22_threeSum`).  Theorem 21 is cited from the literature, part (a) from [CH20, VW13]
and part (b) from [VW10, VW18, VW13], and the paper gives no proof.  The route taken here:

* for (a), from 3SUM to Convolution-3SUM [CH20, Theorem 5.1], and from there to Exact Triangle
  [VW13, Theorem 4.3];
* for (b), from Negative Triangle to Exact Triangle [VW13, Theorem 3.3], from the (min,+)-product to
  Negative Triangle [VW18, Theorem 4.2], and from APSP to the (min,+)-product by repeated squaring.

Stated here: the parts of this route that are mathematics, among them the combinatorial content of
the two reductions of [VW13]. -/













/-! #### Theorem 21(a): the reduction from 3SUM to Convolution-3SUM, after Chan and He

The first step towards Theorem 21(a), after [CH20, Theorem 5.1]: from n integers bounded by a power
of n, a deterministic reduction computes polylogarithmically many arrays of length Õ(n), whose
entries are again bounded by a power of n, in Õ(n^{3/2}) time; three of the integers sum to 0
exactly if one of the arrays is a yes-instance of Convolution-3SUM.

The namespace `ChanHe` defines a reduction of this kind, as a function from inputs to lists of
instances, in two versions: `ChanHe.reduction` for three sets and three arrays, and
`ChanHe.instances` for n numbers and one array.  Nothing is stated here about `ChanHe.reduction`.

Nothing here is about a machine. That the functions can be evaluated deterministically in n^(3/2)
polylog n time on a word RAM is not stated. Theorem 5.1 of [CH20] as printed is a statement about
running times, so it is not stated here. The easy converse reduction, from Convolution-3SUM to
3SUM, is not treated. -/

section ChanHe

open Finset





end ChanHe

end PaperStatements

end Sec3Statements

/-!
## Section 4: definitions

Definitions used by the statements of Section 4, "The matrix theorem in general: a data structure".
They follow the paper's order and names, with three exceptions: `Cube.starsToP0`, from the proof of
Lemma 29, stands with the cubes of Section 4.2; `epsStar`, from Section 4.1, stands with `Rc`; and
the definitions for Table 2, which is printed in Section 4.1, come last. Every notion of Section 2
(terms, leaves, output strings, inner sets, private leaf, order, `α_d`, `β_d`, `Φ_τ`, `Ψ_τ`) is the
one defined for Section 2 and is not redefined.

Conventions, in addition to those of the definitions of Section 2.

* Table 1: `m` and `L` are natural-number variables, and `D = 4^m`, `N₀ = 3^{L-m}`,
  `K = binom(L, m)`, `M = K N₀²`, `α_d`, `β_d` are `D m`, `N0 L m`, `K L m`, `M L m`, `alpha m d`,
  `beta L m d` of Section 2. The remaining rows of Table 1: `ρ` is `rho L m`, and `γ`, `q`, `R_c(γ)`
  are `gammaOf c θ`, `qOf θ`, `Rc c γ`, all defined below; the switching order is a natural number
  `t`, and the ratio `c`, `ε` and `κ` are real numbers.
* "we say that level ℓ is lower than level ℓ' if ℓ < ℓ'" (Section 4): levels are compared in the
  order of `Fin L`.
* An output string is `η` in the Lean text; the paper writes w.
* The paper fixes `0 ≤ t ≤ m` (Section 4.2) and `L ≥ 10m` (Section 4). The definitions below make
  sense for all natural numbers; the statements carry `t ≤ m` and `10 * m ≤ L` as explicit
  hypotheses where they are needed. `m - t` is subtraction of natural numbers, which is the ordinary
  difference because `t ≤ m`.
-/

section Sec4Definitions

open Finset

namespace ThreeSumApsp

/-! ### Notions from Section 2 -/



/-! ### 4.2 Boxes -/





































/-! ### 4.3 The data structure, in terms of the parameters -/

















/-! ### 4.4 Choosing the parameters -/





















/-! #### Table 2 -/













end ThreeSumApsp

end Sec4Definitions

/-!
## Section 4: statements

The claims of Section 4 of the paper, "The matrix theorem in general: a data structure", that are
mathematics and not sentences about a machine. `docs/INDEX.md` says for each item of the paper what
is stated and what is not. The places where the Lean text differs from the wording of the paper are
collected in `docs/REMARKS.md`, "Section 4: differences".

The order is the paper's, with these exceptions. Figure 10 and `Lemma_28_boxes` come after Lemma 28.
`Eq_10`, from the proof of Corollary 31, stands with equation (10). `Sec4_epsStar_numeric` (Section
4.1) and `Sec4_Rc_lt_epsStar` (Table 1) stand with the clauses of Corollary 31 on ε*. The statements
on Table 2, `Table_1_section_2_column` and `Corollary_26_W` come at the end.

* Sentences about running time and space are sentences about a machine. Those of Theorems 24, 25 and
  30 and of Corollaries 26, 31 and 32 are stated about programs: `Items.Theorem_24` to
  `Items.Corollary_32`. The bound of the second sentence of Lemma 29 ("in O(L) time and space per
  box") has no statement; Theorem 30 about programs has its consequence, the first term of (8).
* Expressions (8) and (9) are the definitions `cost8` and `cost9`. Equation (11) is the definition
  `Rc`.
* Figure 9 draws the cube and the boxes of one output string in a small example (L = 3, t = 1).
  Nothing is stated for it.
* No statement says that q increases with θ on (0, 0.9), or that there is only one θ with
  γ = κ - q. So "the θ that gives the q of the column" and "the θ at which γ = κ - q" (Section 4.4)
  are rendered by "some θ with ..." in `Table2Query`, `Table2Density` and the field `eps` of
  `Table2Row`.
* The standing assumptions of the section, `0 ≤ t ≤ m` (Section 4.2) and `L ≥ 10m` (Section 4),
  appear as the explicit hypotheses `t ≤ m` and `10 * m ≤ L` in the statements that need them. "As
  in Section 2.4.3, all output strings in this section have inner sets of exactly m elements"
  (Section 4) is the hypothesis `(innerSetO η).card = m`.
* An output string is `η` in the Lean text; the paper writes w.
* `D m = 4 ^ m` is the paper's `D` after "from now on D = 4^m" (the proof of Corollary 26). The
  inner dimension of the given matrices, before it is padded to a power of four, is written `D₀`.
* Where a statement renders an `O(·)`, it has an explicit constant and an explicit order of
  quantifiers, and the docstring says how the sentence was read.
-/

section Sec4Statements

open Finset

namespace PaperStatements

open ThreeSumApsp

/-! ### 4.2 Boxes -/



















/-! ### 4.3 The data structure, in terms of the parameters -/







/-! #### The decay rate ρ and equation (7) -/







/-! ### 4.4 Choosing the parameters -/







/-! #### Corollary 31: the clauses that are not about time -/











/-! #### Corollary 32 -/



/-! #### Table 2, and the column of Table 1 on Section 2 -/







/-! ##### The six rows of Table 2

Each statement has the numbers of a row in the order in which the paper prints them: the first line
has `c`, `ε` and the left half, the second line the right half. It says that every entry is computed
as Section 4.4 prescribes and is rounded down to four decimals, and that the `ε` of the row is below
`R_c(γ)` at every entry and is rounded down to three decimals. By `Table_2_query_valid`,
`Table_2_ninth_valid` and `Table_2_density_valid`, Corollary 31 or 32 then gives what the caption
claims for the entry. -/

















/-! #### Corollary 26 -/



end PaperStatements

end Sec4Statements

/-!
## Section 5: definitions

Definitions used by the statements about Section 5, in the paper's order. Only what the statements
need is defined: blocks of matrices (5.1, 5.2, 5.4), comparison counts, the two counting
problems, and the construction of Lemma 37 (5.2), and the three hinted matrix-vector problems with
the conjectures about them (5.4). The definitions of 5.4 are used by the statements about programs.
The weighted `k`-Clique problems of 5.3 are `EndStatement.ZeroWeightKClique`,
`WordRam.MinKClique` and `WordRam.MaxKClique`.

Conventions.

* The paper numbers indices from 1; Lean's `Fin n` starts at 0.
* The paper treats n^μ, n/d, n/t₂ as integers.  Here a matrix that is cut into `b` blocks of `m`
  consecutive rows has `b * m` rows, and row `i` of block `p` is row `p * m + i`, which is
  `finProdFinEquiv (p, i)`.  The arithmetic of Theorem 35 has `d = ⌊n^{1/40}⌋` and the real quotient
  `n/d`; nothing is stated about cutting into blocks of `d` when `d` does not divide `n`.
* Definitions shared with Section 3 (`TriangleInstance`, `IsMinPlusProduct`, ...) and Section 4
  (`epsStar`, `padInnerCols`, `padInnerRows`) stand with the definitions of these sections.
-/

section Sec5Definitions

open Finset

namespace ThreeSumApsp

/-! ### Blocks of consecutive rows and columns (used in 5.1, 5.2 and 5.4) -/





/-! ### 5.2 Comparison counts -/

namespace ComparisonCounts





























/-! #### The objects in the proof of Lemma 36 -/

















/-! #### The construction of Lemma 37 -/



























/-! #### The parameters of Corollary 38 and of the proof of Theorem 35 -/







end ComparisonCounts

/-! ### 5.4 Three conjectures of van den Brand, Nanongkai, and Saranurak -/

namespace HintedMv

















end HintedMv

end ThreeSumApsp

end Sec5Definitions

/-!
## Section 5: statements

The pieces of Sections 5.1 and 5.2 that the paper itself argues and that are mathematics:
correctness of the constructions, counts, and the arithmetic of the exponents, with the paper's
constants. `docs/INDEX.md` says for each item of the paper what is stated and what is not. Where a
statement differs from the printed sentence, `docs/REMARKS.md`, "Section 5 and the introduction:
differences", says why.

* The sentences of the form "can be solved in O(...) time" are not stated here. Those of Corollaries
  39 and 40 are stated about programs of the word RAM (`Items.Corollary_39_zero` to
  `Items.Corollary_40_fail`), and nothing else of Sections 5.3 and 5.4 is stated. Those of Theorem
  35 and of Corollary 38 are about randomized algorithms or real numbers, and the machine has
  neither random bits nor real numbers. That of Theorem 34 rests on Theorem 33, which the paper
  proves and which is not proved here, and on μ, which is defined through ω(1, μ, 1). Three lemmas
  of the library (the files that hold the proofs), `conditional_theorem_34`,
  `conditional_corollary_38` and `conditional_theorem_35`, say how each follows from the results
  that its proof uses, which are taken as hypotheses. The running time of Lemma 37 and Lemma 36 as a
  whole occur only as hypotheses of these lemmas. The list is in `docs/REMARKS.md`, "Section 5 and
  the introduction: running times".
* The theorems of other papers that Section 5 uses as black boxes are not stated (`docs/REMARKS.md`,
  "Section 5: cited results"). In particular the randomized reductions behind Lemma 36 are cited.
  Nothing of Theorem 33 and of its proof is stated.
* Of Lemma 36, the size O(n²/d) of the pair set of part (b) is not stated;
  `Theorem_35_three_sum_count` puts n²/d in its place. The last sentence of the lemma, on the
  operations applied to real numbers, is not stated.
* The other sentences inside proofs are lemmas of the library or are not formalized.
* The statements on blocks have n = b * d; the paper's proof treats n/d as an integer.
* "Õ(f)" is read as "O(f · (log n)^c) for some constant c".
-/

section Sec5Statements

open Finset Asymptotics Filter

namespace PaperStatements

open ThreeSumApsp

/-! ### 5.1 Directed APSP with small integer weights -/









/-! ### 5.2 3SUM, APSP, and Exact Triangle with real inputs -/

section ComparisonCounts

open ComparisonCounts

/-! #### Lemma 36(a): the parts argued in the paper -/









/-! Proof of Lemma 36(a): "APSP with real weights and no negative cycles can be computed by
successive squaring of the weight matrix, performing ⌈log₂ n⌉ such products." This is
`Theorem_21b_repeated_squaring` (Theorem 21(b)), which is stated for weights in any linearly ordered
commutative group, in particular for real weights. -/











/-! #### Lemma 36(b): the parts argued in the paper -/







/-! #### Lemma 37

The lemma says "we can build matrices X [...] and Y [...] and compute integers γ₂(r,c), (r,c) ∈ P,
with" γ(r,c) = (XY)[r,c] + γ₂(r,c). Read as a bare existence statement this would be trivial (take
X = Y = 0), so the statements below are about the matrices and the integers that the proof
constructs: `matX`, `matY`, `sameBlockCount`, for an arbitrary outcome `o` of the sort and an
arbitrary indexing `idx` of the pairs (color, block). The running time of the lemma is a hypothesis
of the library's lemma `conditional_corollary_38`. -/









/-! #### Corollary 38: correctness and parameter arithmetic -/





/-! #### Proof of Theorem 35: the arithmetic, with d := ⌊n^{1/40}⌋ -/



















end ComparisonCounts

end PaperStatements

end Sec5Statements

/-!
## The word RAM: problems

First comes what it means that a program of the machine of `EndStatement.lean` solves a problem
within a time bound.  Then come the problems: which number lies in which cell at the start, and
what a right answer is.  No sentence of the paper is stated here; the sentences are the item
statements `Items.Theorem_5`, …, in the terms that are defined here.  `docs/MACHINE.md`, Part 1,
goes through the definitions at length and compares the machine with the standard word RAM point by
point.

**What a reader of the statements about programs can skip.**  Of the definitions of Sections 2 to 5
the statements `wordRam_theorem_5`, … use only these 28:
* Section 2: `N0`, `K`, `alpha`;
* Section 3: `LopInstance`, `LopInstance.commonNeighbors`, `LopInstance.InTriangle`,
  `LopInstance.numTriangles`, `LopInstance.ofMatrices`, `GraphHasZeroTriangle`;
* Section 4: `rho`, `cost8`, `costQuery`, `cost9`, `entropy`, `rhoC`, `gammaOf`, `qOf`, `lnΛ`, `Rc`,
  `epsStar`;
* Section 5, namespace `HintedMv`: `boolMul`, `toInt`, `vHintedOutput`, `MvHintedOutput`,
  `uMvHintedOutput`, `Conjecture52`, `Conjecture57`, `Conjecture512`.

NOTE.  Eight notions are defined twice: in `EndStatement.lean`, and with Mathlib for the statements
on the reductions and about programs.  For each of them a statement, named in brackets, says that
the two definitions agree (a further form of `O(n^a)`, the bound `Within` on the steps of a phase,
is not compared):
* "a program solves a problem": there `Problem`, `Problem.SolvedBy` and the word sizes of
  `Problem.SolvedInTime`, for one size `n`; here `Problem`, `Admissible`, `output` and `Solves`, for
  several sizes (`Agreement_solves`);
* `O(n^r)`: there `BigO`, for a rational exponent and from `n = 2` on; in Section 3 `IsBigOPow`, for
  a real exponent and all large `n` (`Agreement_bigO`, for `r ≥ 0`);
* "solved in time": there `Problem.SolvedInTime` and `BigO`, with a rational exponent and a bound
  `T(n)` that is `O(n^r)` from `n = 2` on; here `SolvesWithin`, `SolvedInTimeAt` and `SolvedInTime`,
  with a real exponent and the bound `C (n^a (log n)^e + 1)` at every size
  (`Agreement_solvedInTime`, for a rational exponent `r ≥ 0` and `e = 0`); both are stated through
  `Problem.SolvedBy`;
* Exact Triangle: `EndStatement.ExactTriangle` and `TriangleInstance.HasZeroTriangle`
  (`Agreement_exactTriangle`);
* the (min,+)-product: `EndStatement.MinPlusProduct` and `IsMinPlusProduct`
  (`Agreement_minPlusProduct`);
* APSP: `EndStatement.Path` and `EndStatement.APSP`, where a missing edge is `none`, and
  `walkWeight`, `NoNegativeCycle` and `IsDistanceMatrix`, where it is `⊤`
  (`Agreement_apsp_noNegativeCycle`, `Agreement_apsp_output`);
* a matrix written row by row: `EndStatement.rowByRow` and `rowMajor` (`Agreement_rowByRow`);
* the weight of a `k`-clique: the sum in `EndStatement.ZeroWeightKClique` and `cliqueWeight`
  (`Agreement_cliqueWeight`).

**The machine** is defined in `EndStatement.lean` and nowhere else: `Instr`, `exec` and
`loadWords`.  The paper works "in the standard word RAM model with O(log N)-bit words", and so
counts "operations on O(log N)-bit integers" (Section 2).  There is no division, no shift, no
bitwise operation and no constant but 1: in its instructions the machine is weaker than the standard
word RAM.

NOTE.  On four points the machine is generous; none of them changes an exponent:
* Every cell outside the input, with a positive or a negative name, holds 0 at the start, and
  `Solves`, `SolvesWithin` and `RunsPhases` charge no space, so a table that is addressed directly
  by a number costs nothing to set up (on a machine without this, lazy initialisation costs a
  constant factor).
* The finitely many cells that a program names in its text need not be addressable by a word.
* The slope `b` of the word size is chosen after the exponent `κ` of the magnitude of the numbers.
* The inputs of phases and the queries arrive at no cost. -/

section WordRamProblems

namespace ThreeSumApsp.WordRam

open EndStatement (Instr exec loadWords)

/-! ### What it means to solve a problem

**The order of the choices.**  In every statement the order is: the constants of the problem (the
exponent `κ` of the magnitude of the numbers, the `k` of `k`-Clique); then the program, the slope
`b` of the word size and the constant `C` of the time bound; then the instance; then the word size,
any number of bits that is admissible for the slope.  So the program cannot depend on the instance
or on its size, and it cannot rely on long words. -/

/-! #### The word size and the output cells -/





/-! #### Problems, and solving a problem within a time bound -/





/-! #### Time bounds in one size `n`, for the problems of `EndStatement.lean` -/











/-! #### A query program that serves one query after the other -/





/-! #### Programs that receive their input in phases

A problem in phases has one program for each phase.  The inputs of the phases are laid
out one after the other in the cells 0, 1, 2, …, but the input of a phase is written into its cells
only when the phase starts.  Each program starts at its first instruction on the memory that the
previous phase has left; the first one starts on a memory of zeros.  So a phase cannot see the input
of a later phase, and nothing is reset between phases.  The output is read from the cells after the
last input.  Receiving an input takes no steps, and the inputs of earlier phases stay in memory
unless a program overwrites them.  What an earlier phase has left in the cells of a later input is
lost; the earlier phase knows which cells these are, since all sizes are given in Phase 1.  (In the
running times of Corollary 40 the bound of a phase is at least the length of its input, if the
exponent `γ` of `Items.Corollary_40_general_times` is at most 1; so they do not depend on inputs
being free.) -/







/-! ### The problems of the paper, their inputs and their answers

**Layout.**  Matrices are written row by row, one number per cell, as signed words.  Booleans are
written as 0 and 1, and indices and vertices count from 0.  The first cells hold the sizes.  The
bound on the absolute values of the numbers is not written into memory.  For the matrix problems it
is a number `U` that is part of the instance as a mathematical object (`ThinPair`); for the problems
in the form of `EndStatement.Problem` it is a hypothesis of `SolvesWithin`.  In the statements it is
a fixed power of the size, with an exponent that is fixed before the program (and 1 for the 0/1
matrices of the lopsided triangle problems).  A program for a problem with an output has to accept,
and to leave the output in the cells right after the input. -/

/-! #### How matrices and Booleans are written -/





/-! #### The wanted entries of a thin matrix product (Theorems 1, 5, 25 and 30, Corollaries 26 and
32) -/









/-! #### The two-stage data structure for a thin matrix product (Section 4) -/





/-! #### The lopsided triangle problems (Definitions 13 and 14) -/









/-! #### Exact Triangle, 3SUM, the (min,+)-product and APSP

These four are the problems `ExactTriangle`, `ThreeSum`, `MinPlusProduct` and `APSP` of
`EndStatement.lean`. -/

/-! #### Exact Triangle on `n`-vertex graphs -/





/-! #### Zero-Weight, Min-Weight and Max-Weight `k`-Clique (Corollary 39)

Zero-Weight `k`-Clique is the problem `ZeroWeightKClique k` of `EndStatement.lean`.  The other two
have its input: for each ordered pair of parts `(p, q)`, in row-major order, an `n × n` block of
numbers, where `w p q u v` is the weight between vertex `u` of part `p` and vertex `v` of part `q`.

NOTE.  All `k²` blocks are input, but only the blocks with `p < q` count; the others may hold
anything within the bound on the numbers of the input.  The paper does not fix a layout. -/







/-! #### The three hinted matrix-vector problems of [vdBNS19] (Corollary 40) -/









end ThreeSumApsp.WordRam

end WordRamProblems

/-!
## Agreement with the definitions of EndStatement.lean

Eight notions have two definitions each.  `EndStatement.lean` defines them for the five claims, with
Lean's core library only, for integers and square matrices.  The statements on the reductions and
the statements about programs use definitions with Mathlib: the paper needs Exact Triangle and the
(min,+)-product also over the real numbers, matrices that are not square, problems with several
sizes, and time bounds with real exponents and logarithmic factors.  The statements below say that
the two definitions of each notion agree.  APSP has two statements, one for the promise and one for
the output.
-/

section AgreementStatements

open ThreeSumApsp.WordRam

namespace PaperStatements

open ThreeSumApsp



















end PaperStatements

end AgreementStatements

/-!
## The word RAM: running times

An item statement is a running-time sentence of the paper, written as a proposition about programs
of the machine of `EndStatement.lean` and named after its item, such as `Items.Theorem_5` or
`Items.Corollary_26`.  Its docstring quotes the sentence.  The notions of solving are `Solves`,
`IsDataStructure`, `SolvesWithin` and `RunsPhases`, and the forms derived from them (`SolvedInTime`,
`AchievesVHinted`, …); the layouts of the inputs and the order of the choices are explained with
them.  The definitions only say what the sentences mean.  That they hold is stated by the theorems
`wordRam_theorem_5`, `wordRam_corollary_26`, ….  The five claims of `EndStatement.lean` are five of
the bounds of `Theorem_19`, `Theorem_22_second` and `Corollary_39_zero`.

* **Order.**  Sections 2 to 5 in the paper's order, then the introduction.  Its Theorems 1 to 4
  restate and combine the later items (here Theorem 3 is stated through Corollary 26, and Theorem 4
  through Corollary 40), so they stand last.
* **Items and propositions.**  Some items have several propositions, for instance `Corollary_26` for
  the data structure and `Corollary_26_wanted` for the entries at a given set of positions; and some
  propositions hold several bounds of their item, joined by "and", for instance `Theorem_19`.
* **Definitions that are not items.**  `thinDom`, `HasDataStructure` and `theorem30Dom` abbreviate
  hypotheses or sentences that occur in more than one proposition.  `DataStructureBelow` and
  `WantedBelow` state the last sentences of Theorems 3 and 1 ("More generally, …") with a bound `ε₀`
  in the place of 0.1204.
* **Departures.**  Where a proposition departs from the printed sentence, for instance by a lower
  bound `D ≥ 1` that the paper leaves out, its docstring, or that of the definition through which it
  is stated, says so, mostly in a paragraph that begins with NOTE.
* **Real parameters.**  Corollaries 31 and 32 have real parameters `c` and `θ`.  The statements do
  not mention the numbers `⌈cm⌉` and `⌈θm⌉` of the proof; they only say that programs with certain
  time bounds exist.  So they make sense, and are stated, for all real `c` and `θ`, although a
  program is a finite text: a proof may use rational parameters close to `c` and `θ`, which the
  strict inequality `ε < R_c(γ)` leaves room for.
* **Not stated about programs.**  The other sentences of the paper about running time are not stated
  about programs.  The machine has neither random bits nor real numbers: Theorem 35 (with the half
  of Theorem 2 on real inputs) needs both, and Corollary 38 needs real numbers.  Theorem 34 rests on
  Theorem 33, which the paper proves and which is not proved here, and on μ, which is defined
  through ω(1, μ, 1). For these three items see the library's lemmas `conditional_theorem_34`,
  `conditional_corollary_38` and `conditional_theorem_35`, where Theorem 33 and Lemmas 36 and 37 are
  hypotheses.  Theorems 17 and 21 speak of an arbitrary solver, while each item statement is about
  one fixed program.  The time bound of Lemma 29 enters the bound (8) of Theorem 30. -/

section WordRamItems

namespace ThreeSumApsp.WordRam

open EndStatement (Instr)

namespace Items

/-! ### Section 2: Theorem 5 -/



/-! ### Section 3: Corollaries 15 and 16, Theorems 19 and 22 -/













/-! ### Section 4: Theorems 24 and 25, Corollary 26, Theorem 30, Corollaries 31 and 32 -/



























/-! ### Section 5: Corollaries 39 and 40 -/











/-! ### Section 1, the introduction: Theorems 1 to 4 -/











end Items

end ThreeSumApsp.WordRam

end WordRamItems

end
end


-- Original source module: ThreeSumApsp.Lang.Lib.Emod
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}
namespace Emod

/-- The local variables of emod: the arguments x, M and fr (the result replaces x), what is left
of |x|, the number of entries of the table, and the next multiple of M. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Modulus : ℕ := 1
@[inherit_doc Arg] abbrev Free : ℕ := 2
@[inherit_doc Arg] abbrev Rest : ℕ := 3
@[inherit_doc Arg] abbrev Count : ℕ := 4
@[inherit_doc Arg] abbrev Mult : ℕ := 5

end Emod

open Emod in
/-- One entry of the table: the multiple is written to the table and doubled. -/
def emodTableRound : Stmt :=
  .store (v Free +' v Count) (v Mult) ;;
  .set Count (v Count +' k 1) ;;
  .set Mult (v Mult +' v Mult)

open Emod in
/-- The table: M, 2M, 4M, … are written to the free pointer as long as they are at most |x|. -/
def emodTable : Stmt := .while (v Mult ≤' v Rest) emodTableRound

open Emod in
/-- The last entry of the table that has not been tried is subtracted if possible. -/
def emodReduceRound : Stmt :=
  .set Count (v Count -' k 1) ;;
  .ite (M (v Free +' v Count) ≤' v Rest) (.set Rest (v Rest -' M (v Free +' v Count))) .skip

open Emod in
/-- The entries of the table are subtracted, from the largest down, where possible. -/
def emodReduce : Stmt := .while (k 0 <' v Count) emodReduceRound

open Emod in
/-- The sign: the remainder r of |x| gives the remainder of x. -/
def emodSign : Stmt :=
  .ite (v Arg <' k 0)
    (.ite (v Rest =' k 0) (.set Arg (k 0)) (.set Arg (v Modulus -' v Rest)))
    (.set Arg (v Rest))

open Emod in
/-- emod(x, M, fr). -/
def emodBody : Stmt :=
  .ite (v Arg <' k 0) (.set Rest (k 0 -' v Arg)) (.set Rest (v Arg)) ;;
  .set Count (k 0) ;;
  .set Mult (v Modulus) ;;
  emodTable ;;
  emodReduce ;;
  emodSign










namespace Emod





variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}









end Emod

end Light

end
end


-- Original source module: ThreeSumApsp.Lang.Lib.Logs
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs



@[inherit_doc Arg] abbrev Power : ℕ := 2

end Logs

open Logs

/-! ## The logarithm, rounded down -/

/-- log2(x): the candidate is L, and the power is 2^(L + 1). -/
def log2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 2) ;;
  .while (v Power ≤' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)





/-! ## The logarithm, rounded up -/

/-- clog2(x): the candidate is L, and the power is 2^L. -/
def clog2Body : Stmt :=
  .set Cand (k 0) ;;
  .set Power (k 1) ;;
  .while (v Power <' v Arg) (
    .set Power (v Power +' v Power) ;;
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)





/-! ## The cube root, rounded up -/

























/-! ## Halves, rounded up -/

/-- half(h): the candidate is r. -/
def halfBody : Stmt :=
  .set Cand (k 0) ;;
  .while (v Cand +' v Cand <' v Arg) (
    .set Cand (v Cand +' k 1)) ;;
  .set Arg (v Cand)





end Light

end
end


-- Original source module: ThreeSumApsp.Lang.Lib.Merge
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Merging two segments

merge(a, na, b, nb, dst) writes the merge of the na cells from a and the nb cells from b to the na +
nb cells from dst, within `mergeTime (na + nb)` steps (`merge_meets`).  The model is `List.merge`:
the next output is the head of the first list unless the head of the second list is smaller.
Nothing is assumed about the order of the two lists.  Numbers are only compared and copied, so their
size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Merge

/-! ## The pure side: one step of List.merge on the rests of two lists -/

variable {l r : List ℤ} {i j : ℕ}









end Merge

/-! ## The program -/

namespace Merge

/-- The local variables of merge: the arguments a, na, b, nb, dst, and the numbers i and j of cells
already taken from the first and the second list. -/
abbrev ListA : ℕ := 0
@[inherit_doc ListA] abbrev LenA : ℕ := 1
@[inherit_doc ListA] abbrev ListB : ℕ := 2
@[inherit_doc ListA] abbrev LenB : ℕ := 3
@[inherit_doc ListA] abbrev Dest : ℕ := 4
@[inherit_doc ListA] abbrev DoneA : ℕ := 5
@[inherit_doc ListA] abbrev DoneB : ℕ := 6

end Merge

open Merge in
/-- The next output is the head of the first list: dst[i + j] := a[i]; i := i + 1. -/
def mergeTakeLeft : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListA +' v DoneA)) ;;
  .set DoneA (v DoneA +' k 1)

open Merge in
/-- The next output is the head of the second list: dst[i + j] := b[j]; j := j + 1. -/
def mergeTakeRight : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListB +' v DoneB)) ;;
  .set DoneB (v DoneB +' k 1)

open Merge in
/-- merge(a, na, b, nb, dst). -/
def mergeBody : Stmt :=
  .set DoneA (k 0) ;;
  .set DoneB (k 0) ;;
  .while (v DoneA +' v DoneB <' v LenA +' v LenB) (
    .ite (v DoneA <' v LenA)
      (.ite (v DoneB <' v LenB)
        (.ite (M (v ListB +' v DoneB) <' M (v ListA +' v DoneA)) mergeTakeRight mergeTakeLeft)
        mergeTakeLeft)
      mergeTakeRight)

namespace Merge







variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}









end Merge

end Light

end
end


-- Original source module: ThreeSumApsp.Lang.Lib.MergeSort
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Merge sort

sort(n, a, fr) sorts the n cells from a in place, in ascending order (`sort_meets`).  It is the
recursive merge sort: sort the first ⌈n/2⌉ cells, sort the rest, merge the two halves into the n
cells from the free pointer fr, and copy them back.  It calls half, merge and copy.

The proof is an induction on n.  `body_ends` treats the body of the procedure, given that the
procedure sorts the lists of half the length, and `join_ends` its last two calls; `sorted_merge`
says that what the four calls leave is a sorted permutation of the list.  The number of steps,
`sortTime n`, is of the order n log n (`clog_split`, `time_split`), and the calls are nested
⌈log₂ n⌉ + 1 deep.  Numbers are only compared and copied, so their size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program}

namespace MergeSort

/-- The local variables of sort: the arguments n, a and fr; h = ⌈n/2⌉; and a local that takes the
results of the calls, which are not used. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Start : ℕ := 1
@[inherit_doc Len] abbrev Free : ℕ := 2
@[inherit_doc Len] abbrev Half : ℕ := 3
@[inherit_doc Len] abbrev Unused : ℕ := 4

end MergeSort

open MergeSort in
/-- The two sorted halves are merged into the cells from fr and copied back. -/
def sortJoin (pMerge pCopy : ℕ) : Stmt :=
  .call pMerge [v Start, v Half, v Start +' v Half, v Len -' v Half, v Free] Unused ;;
  .call pCopy [v Free, v Start, v Len] Unused

open MergeSort in
/-- sort(n, a, fr).  The parameters are the procedure numbers of sort itself, half, merge and
copy. -/
def sortBody (pSort pHalf pMerge pCopy : ℕ) : Stmt :=
  .ite (k 1 <' v Len) (
    .call pHalf [v Len] Half ;;
    .call pSort [v Half, v Start, v Free] Unused ;;
    .call pSort [v Len -' v Half, v Start +' v Half, v Free] Unused ;;
    sortJoin pMerge pCopy) .skip



namespace MergeSort



/-- The program holds the four procedures. -/
structure Procs (P : Program) (pSort pHalf pMerge pCopy : ℕ) : Prop where
  sort : P[pSort]? = some (sortBody pSort pHalf pMerge pCopy)
  half : P[pHalf]? = some halfBody
  merge : P[pMerge]? = some mergeBody
  copy : P[pCopy]? = some copyBody









variable {pSort pHalf pMerge pCopy : ℕ}







end MergeSort

end Light

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Bits
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: binary digits of the labels, and selection by digits

Theorem 21(a), after [CH20, Theorem 5.1].  The reduction for n numbers
splits the set of the values by one or two binary digits of the labels x + V (`ChanHe.splitA`,
`ChanHe.splitB`).  Two routines do this.

* pick copies the elements whose digits at one or two given positions have given values
  (`pick_spec`, with `pickRound_runs` for one round).  What it has written after the first i
  elements is `pickPart`, and `Pick.Ctx.step` says how one more element changes it, in terms of the
  cells that the program reads.
* bits writes the table of the binary digits of the labels, Λ cells for each element (`bits_spec`,
  with `bitsElem_ends` for one element).  It first computes 2^Λ by doubling (`bitsPow_ends`).  The
  digits of one label are found from the top down: the rest of the label is doubled, and the digit
  is 1 if the result reaches 2^Λ (`bitsRow_ends`).

Where the body of a loop is a block, the goal of a round is `s.Runs lim σ R`.  This is a pair, which
says that the block s, started in σ, stays within the limits, and that R holds of the state after
it.  A procedure returns what its local 0 holds at the end.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.Spec ThreeSumApsp.ChanHe

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## pick -/







namespace Pick















end Pick

















/-! ## bits -/







namespace Bits

/-- The locals of bits.  The arguments: len, s, V, Λ, bt and the free pointer, which is not used.
Then the counter, the power 2^Λ, the address of the digits of the current element, the address of
the current digit, the rest of the label, and the counter of the loop that computes the power. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Bound : ℕ := 2
@[inherit_doc Len] abbrev Width : ℕ := 3
@[inherit_doc Len] abbrev Table : ℕ := 4

@[inherit_doc Len] abbrev Idx : ℕ := 6
@[inherit_doc Len] abbrev Pow : ℕ := 7
@[inherit_doc Len] abbrev Row : ℕ := 8
@[inherit_doc Len] abbrev Cur : ℕ := 9
@[inherit_doc Len] abbrev Rest : ℕ := 10
@[inherit_doc Len] abbrev Cnt : ℕ := 11

end Bits

open Bits in
/-- The power 2^Λ, by doubling. -/
def bitsPow : Stmt :=
  .set Pow (k 1) ;;
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Width) (
    .set Pow (k 2 *' v Pow) ;;
    .set Cnt (v Cnt +' k 1))

open Bits in
/-- The digits of one label, from the top down: the rest of the label is kept at the top of Λ bits;
it is doubled, and the digit is 1 if the result reaches 2^Λ. -/
def bitsRow : Stmt :=
  .while (v Row <' v Cur) (
    .set Cur (v Cur -' k 1) ;;
    .set Rest (k 2 *' v Rest) ;;
    .ite (v Rest <' v Pow) (.store (v Cur) (k 0))
      (.store (v Cur) (k 1) ;; .set Rest (v Rest -' v Pow)))

open Bits in
/-- The digits of the label of the current element. -/
def bitsElem : Stmt :=
  .set Rest (M (v Src +' v Idx) +' v Bound) ;;
  .set Cur (v Row +' v Width) ;;
  bitsRow ;;
  .set Row (v Row +' v Width)

open Bits in
/-- bits(len, s, V, Λ, bt, fr): len numbers of absolute value at most V stand at s.  Writes the Λ
lowest binary digits of each label x + V to the table at bt. -/
def bitsBody : Stmt :=
  bitsPow ;;
  .set Row (v Table) ;;
  .for Idx (v Len) bitsElem















end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Sec3.Theorem21a.ChanHe.Definitions
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 21(a), the reduction of Chan and He: the problems on three sets and on arrays

The problems between which the reduction of [CH20] passes on its way from 3SUM to Convolution-3SUM:
3SUM on three sets (`HasSol`), Convolution-3SUM on three arrays (`ConvSol`, and `Node.Conv` for the
arrays of a node of the recursion tree) and on one array (`ConvOne`).  An array is a function on
`ℕ`, of which only the cells below a given length are read.  `Bdd U S` says that the elements of `S`
have absolute value at most `U`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace ChanHe

open Finset









/-- All elements of `S` have absolute value at most `U`. -/
def Bdd (U : ℕ) (S : Finset ℤ) : Prop := ∀ x ∈ S, |x| ≤ (U : ℤ)

end ChanHe

end ThreeSumApsp

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The reduction from 3SUM to Convolution-3SUM after Chan and He, as a program.  Specifications

Theorem 21(a), after [CH20, Theorem 5.1].  This file contains no program
and no proof.  It states the specifications of the routines of the reduction: the general library,
the routines below the recursion tree, the tree, and the routines that prepare the splittings.  The
proof of a routine uses only the specifications of the routines that it calls.

* The pure models are the definitions of the reduction themselves (`ChanHe.coll`, `heavy`,
  `modulus`, `Node.oneArray`, `nodes`, …), applied to finite sets.  A set lies in the memory as a
  list without repetitions, in any order, with its length passed beside its address (`SetAt`).
* The specification of a routine is a proposition `XSpec lim P p …`: "procedure number `p` of the
  program `P`, run on these arguments in a memory that satisfies this, ends within `tX` steps with
  this result in a memory that satisfies that" (`Meets`).  It is proved for every program that holds
  the body of X at the number `p` and meets the specifications of the routines that X calls.
* The last argument of most routines is the free pointer `fr`; such a routine writes only its output
  segments, the count table (which it leaves as it found it), and cells from `fr` on.
* The count table: `cap` cells from `cnt`, below every free pointer, all zeros between calls
  (`ZeroAt`).  A routine that uses it clears what it wrote.
* Time functions are definitions.  The time function of a caller is written in terms of those of its
  callees.
* Limits: one hypothesis `(xNeed …).Ok lim fr d`, or a field of the structure that collects the
  hypotheses of the routine.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

/-! ## Vocabulary -/

/-- The `len` cells from `a` hold the elements of the set `S`, each once, in some order. -/
def SetAt (μ : ℕ → ℤ) (a len : ℕ) (S : Finset ℤ) : Prop :=
  ∃ L : List ℤ, L.length = len ∧ Seg μ a L ∧ L.Nodup ∧ L.toFinset = S

/-- The `cap` cells from `cnt` hold zeros. -/
def ZeroAt (μ : ℕ → ℤ) (cnt cap : ℕ) : Prop := ∀ r < cap, μ (cnt + r) = 0

/-! ## Time functions and needs -/

/-- The time of a remainder of a number of absolute value at most `V`. -/
def tEmod (V : ℕ) : ℕ := 60 * (Nat.log 2 (V + 1) + 1) + 40
/-- What a remainder needs: words for doubled multiples of the modulus, and a cell for each of
them. -/
def emodNeed (V M : ℕ) : Need := ⟨4 * V + 4 * M + 16, Nat.log 2 (V + 1) + 2, 0⟩

/-- The remainders of `len` numbers. -/
def tResid (len V : ℕ) : ℕ := len * (tEmod V + 30) + 20
/-- One pass over `len` remainders that changes their counts. -/
def tTally (len : ℕ) : ℕ := 30 * len + 20
/-- The colliding pairs of a set of `len` numbers: remainders, counting, a pass that adds up, and
removing the counts. -/
def tColl (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 30 * len + 60
/-- The heavy elements of a set of `len` numbers: remainders, counting, a pass that copies, and
removing the counts. -/
def tHeavy (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 40 * len + 60
/-- One search: every candidate prime costs three collision counts. -/
def tSearch (np l₁ l₂ l₃ V : ℕ) : ℕ := np * (tColl l₁ V + tColl l₂ V + tColl l₃ V + 120) + 40
/-- The modulus of a node: two searches, and the collision counts modulo the first prime. -/
def tModulus (np l₁ l₂ l₃ V : ℕ) : ℕ := 2 * tSearch np l₁ l₂ l₃ V + tColl l₁ V + tColl l₂ V +
  tColl l₃ V + 160
/-- The array of a node: the padding pattern, and for each of the three sets remainders, counting, a
pass that writes, and removing the counts. -/
def tNodeArray (m l₁ l₂ l₃ V : ℕ) : ℕ :=
  80 * (2 * m ^ 2) + (tResid l₁ V + tResid l₂ V + tResid l₃ V) +
    2 * (tTally l₁ + tTally l₂ + tTally l₃) + 60 * (l₁ + l₂ + l₃) + 200

/-- The words that the routines below the tree need, for sets of at most `n` numbers of absolute
value at most `V` and moduli up to `M`: products of a collision count and a number of primes,
thresholds of the searches, entries and indices of the arrays. -/
def wordNeed (n V M : ℕ) : ℕ := 64 * (n + 1) ^ 2 * (M + 1) * (V + 1)

/-- The needs.  A caller's need covers its callees': the remainders of a set take `len` cells, a
long division `log₂ (V + 1) + 2`; the depth is the number of levels of calls below the routine. -/
def residNeed (len V M : ℕ) : Need := ⟨wordNeed len V M, Nat.log 2 (V + 1) + 2, 1⟩
/-- The need of coll and of heavy. -/
def collNeed (len V M : ℕ) : Need := ⟨wordNeed len V M, len + Nat.log 2 (V + 1) + 2, 2⟩
/-- The need of modulus; the moduli are at most `m²`. -/
def modulusNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 4⟩
/-- The need of nodeArray. -/
def nodeArrayNeed (n V m : ℕ) : Need := ⟨wordNeed n V (m * m), n + Nat.log 2 (V + 1) + 2, 2⟩

/-! ## The generic library

The logarithms, the remainder, the sieve and sorting of the general library meet these
specifications (`EmodSpec` is below). -/

/-- The time of log2. -/
def tLog2 (x : ℕ) : ℕ := 30 * (Nat.log 2 x + 1) + 20

/-- log2(x) returns `⌊log₂ x⌋` (0 for `x = 0`); it touches no cell. -/
def Log2Spec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d x : ℕ) (μ : ℕ → ℤ), (4 * x + 4 : ℤ) ≤ lim.word →
    Meets lim P p d [x] μ (tLog2 x) fun r μ' => r = (Nat.log 2 x : ℤ) ∧ μ' = μ

/-- clog2(x) returns `⌈log₂ x⌉` (0 for `x ≤ 1`); it touches no cell. -/
def Clog2Spec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d x : ℕ) (μ : ℕ → ℤ), (4 * x + 4 : ℤ) ≤ lim.word →
    Meets lim P p d [x] μ (tLog2 x + 30) fun r μ' => r = (Nat.clog 2 x : ℤ) ∧ μ' = μ

/-- The time of the sieve. -/
def tPrimes (m : ℕ) : ℕ := 60 * m * (Nat.log 2 m + 2) + 60
/-- The need of the sieve: a table of `m + 1` cells. -/
def primesNeed (m : ℕ) : Need := ⟨4 * m + 16, m + 1, 0⟩

/-- primes(m, out, fr) writes the primes up to `m` in ascending order to `out` (room for `m` cells)
and returns their number. -/
def PrimesSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr m out : ℕ) (μ : ℕ → ℤ), out + m ≤ fr → (primesNeed m).Ok lim fr d →
    Meets lim P p d [m, out, fr] μ (tPrimes m) fun r μ' =>
      r = (#(Nat.primesLE m) : ℤ) ∧
        Seg μ' out (((Nat.primesLE m).sort (· ≤ ·)).map fun q : ℕ => (q : ℤ)) ∧
        KeptBut μ μ' fr out m

/-- The time of sorting. -/
def tSort (n : ℕ) : ℕ := 80 * n * (Nat.log 2 n + 2) + 60
/-- The need of sorting: `n` cells, and a level of calls for each halving. -/
def sortNeed (n V : ℕ) : Need := ⟨2 * V + 4 * n + 16, n, Nat.log 2 n + 2⟩

/-- sort(n, a, fr) sorts the `n` cells from `a` in place, in ascending order. -/
def SortSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr a V : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Seg μ a L → AbsLe L V → a + L.length ≤ fr →
    (sortNeed L.length V).Ok lim fr d →
    Meets lim P p d [L.length, a, fr] μ (tSort L.length) fun _ μ' =>
      (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧ KeptBut μ μ' fr a L.length

/-! ## Remainders, counts, collisions, heavy elements -/

/-- emod(x, M, fr) returns `x % M`, for `M ≥ 1`. -/
def EmodSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M : ℕ) (x : ℤ) (μ : ℕ → ℤ), 1 ≤ M → |x| ≤ (V : ℤ) → (emodNeed V M).Ok lim fr d →
    Meets lim P p d [x, M, fr] μ (tEmod V) fun r μ' => r = x % (M : ℤ) ∧ Kept μ μ' fr

/-- resid(len, s, sg, M, key, fr) writes the remainders of `sg · x` modulo `M`, for the `len`
numbers `x` from `s`, to `key`.  `sg` is 1 or -1. -/
def ResidSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s key : ℕ) (sg : ℤ) (L : List ℤ) (μ : ℕ → ℤ), 1 ≤ M → (sg = 1 ∨ sg = -1) → AbsLe L V →
    Seg μ s L →
    s + L.length ≤ fr → key + L.length ≤ fr → Apart s L.length key L.length →
    (residNeed L.length V M).Ok lim fr d →
    Meets lim P p d [L.length, s, sg, M, key, fr] μ (tResid L.length V) fun _ μ' =>
      Seg μ' key (L.map fun x => (sg * x) % (M : ℤ)) ∧ KeptBut μ μ' fr key L.length

/-- tally(len, key, cnt, δ) adds `δ` to the cell `cnt + k` for each of the `len` numbers `k` from
`key`. -/
def TallySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d key cnt cap : ℕ) (δ : ℤ) (K : List ℕ) (μ : ℕ → ℤ), (∀ k ∈ K, k < cap) → (δ = 1 ∨ δ = -1) →
    Seg μ key (K.map fun k : ℕ => (k : ℤ)) → Apart key K.length cnt cap →
    (∀ r < cap, |μ (cnt + r)| ≤ (K.length : ℤ)) →
    key + K.length ≤ lim.space → cnt + cap ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    (2 * K.length + 2 : ℤ) ≤ lim.word →
    Meets lim P p d [K.length, key, cnt, δ] μ (tTally K.length) fun _ μ' =>
      (∀ r < cap, μ' (cnt + r) = μ (cnt + r) + δ * (K.count r : ℤ)) ∧ SameOutside μ μ' cnt cap

/-- A set of `len` numbers of absolute value at most `V` at `s`, and a table of zeros at `cnt` with
a cell for each remainder modulo `M`; both below the free pointer, and apart. -/
structure BucketMem (μ : ℕ → ℤ) (fr V M s len cnt cap : ℕ) (S : Finset ℤ) : Prop where
  modulus_pos : 1 ≤ M
  modulus_le : M ≤ cap
  bdd : Bdd V S
  set : SetAt μ s len S
  zero : ZeroAt μ cnt cap
  belowSet : s + len ≤ fr
  belowTable : cnt + cap ≤ fr
  apart : Apart s len cnt cap

/-- coll(len, s, M, cnt, fr) returns the number of colliding ordered pairs of the set at `s` modulo
`M`. -/
def CollSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s len cnt cap : ℕ) (S : Finset ℤ) (μ : ℕ → ℤ), BucketMem μ fr V M s len cnt cap S →
    (collNeed len V M).Ok lim fr d →
    Meets lim P p d [len, s, M, cnt, fr] μ (tColl len V) fun r μ' =>
      r = (coll S M : ℤ) ∧ Kept μ μ' fr

/-- Where the output of heavy stands: below the free pointer, apart from the set and the table. -/
structure HeavyOut (fr s cnt cap out len : ℕ) : Prop where
  below : out + len ≤ fr
  apartSet : Apart s len out len
  apartTable : Apart out len cnt cap

/-- heavy(len, s, M, out, cnt, fr) writes the heavy elements of the set at `s` modulo `M` to `out`
(room for `len` cells) and returns their number. -/
def HeavySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr V M s len out cnt cap : ℕ) (S : Finset ℤ) (μ : ℕ → ℤ),
    BucketMem μ fr V M s len cnt cap S → HeavyOut fr s cnt cap out len →
    (collNeed len V M).Ok lim fr d →
    Meets lim P p d [len, s, M, out, cnt, fr] μ (tHeavy len V) fun r μ' =>
      r = (#(heavy S M) : ℤ) ∧ SetAt μ' out #(heavy S M) (heavy S M) ∧ KeptBut μ μ' fr out len

/-! ## The modulus of a node -/

/-- The primes up to `m`, in ascending order, lie in the `np` cells from `pr`. -/
def PrimesAt (μ : ℕ → ℤ) (pr np m : ℕ) : Prop :=
  np = #(Nat.primesLE m) ∧ Seg μ pr (((Nat.primesLE m).sort (· ≤ ·)).map fun q : ℕ => (q : ℤ))





/-- The primes up to `m` and the count table are in the memory, below the free pointer and apart. -/
structure Env.Ok (μ : ℕ → ℤ) (e : Env) : Prop where
  primes : PrimesAt μ e.pr e.np e.m
  zero : ZeroAt μ e.cnt (e.m * e.m)
  belowPr : e.pr + e.np ≤ e.fr
  belowCnt : e.cnt + e.m * e.m ≤ e.fr
  apartPr : Apart e.pr e.np e.cnt (e.m * e.m)

/-- A set of at most `n` numbers of absolute value at most `V` is in the memory, below the free
pointer and apart from the count table. -/
structure Slot.Ok (μ : ℕ → ℤ) (e : Env) (X : Slot) : Prop where
  set : SetAt μ X.addr X.len X.set
  le : X.len ≤ e.n
  bdd : Bdd e.V X.set
  below : X.addr + X.len ≤ e.fr
  apart : Apart X.addr X.len e.cnt (e.m * e.m)



/-- The addresses and lengths of the three sets, as the routines are given them. -/
@[simp] abbrev NodeArgs.sets (a : NodeArgs) : List ℤ :=
  [a.X₁.addr, a.X₁.len, a.X₂.addr, a.X₂.len, a.X₃.addr, a.X₃.len]

/-- The three sets of a node, the primes and the count table are in the memory. -/
structure NodeMem (μ : ℕ → ℤ) (a : NodeArgs) : Prop where
  envOk : a.toEnv.Ok μ
  set₁ : a.X₁.Ok μ a.toEnv
  set₂ : a.X₂.Ok μ a.toEnv
  set₃ : a.X₃.Ok μ a.toEnv













/-- The values of the arguments of modulus. -/
@[simp] abbrev NodeArgs.modulusVals (a : NodeArgs) (Λ : ℕ) : List ℤ :=
  a.sets ++ [(Λ : ℤ), a.np, a.pr, a.cnt, a.fr]

/-- modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr) returns the modulus of the node. -/
def ModulusSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (a : NodeArgs) (Λ : ℕ) (μ : ℕ → ℤ), NodeMem μ a → Λ ≤ a.V + 2 →
    ∀ d, (modulusNeed a.n a.V a.m).Ok lim a.fr d →
    Meets lim P p d (a.modulusVals Λ) μ
      (tModulus a.np a.X₁.len a.X₂.len a.X₃.len a.V) fun r μ' =>
      r = (modulus (Nat.primesLE a.m) Λ a.X₁.set a.X₂.set a.X₃.set : ℤ) ∧ Kept μ μ' a.fr

/-! ## The array of a node -/

/-- Where the array of a node is written: `8 m²` cells from `y`, below the free pointer and apart
from the three sets and the count table. -/
structure NodeArrayOut (a : NodeArgs) (y : ℕ) : Prop where
  below : y + 8 * a.m ^ 2 ≤ a.fr
  apart₁ : Apart y (8 * a.m ^ 2) a.X₁.addr a.X₁.len
  apart₂ : Apart y (8 * a.m ^ 2) a.X₂.addr a.X₂.len
  apart₃ : Apart y (8 * a.m ^ 2) a.X₃.addr a.X₃.len
  apartCnt : Apart y (8 * a.m ^ 2) a.cnt (a.m * a.m)

/-- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr) writes the first `8 m²` cells of the
one-array instance of the node to `y`. -/
def NodeArraySpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (a : NodeArgs) (M y : ℕ) (μ : ℕ → ℤ), NodeMem μ a → 1 ≤ M → M ≤ a.m * a.m →
    NodeArrayOut a y →
    ∀ d, (nodeArrayNeed a.n a.V a.m).Ok lim a.fr d →
    Meets lim P p d ((M : ℤ) :: a.sets ++ [(a.V : ℤ), a.m, y, a.cnt, a.fr]) μ
      (tNodeArray a.m a.X₁.len a.X₂.len a.X₃.len a.V) fun _ μ' =>
      (∀ u < 8 * a.m ^ 2,
        μ' (y + u) = Node.oneArray ⟨a.X₁.set, a.X₂.set, a.X₃.set, M⟩ a.V u) ∧
        KeptBut μ μ' a.fr y (8 * a.m ^ 2)

/-! ## The recursion tree -/







/-- What the recursive procedure needs with `f` levels to go: a set of heavy elements for each
level, one array, and what the solver needs. -/
def nodesNeed (r : ℕ → ℕ → Need) (n V m f : ℕ) : Need :=
  ⟨max (modulusNeed n V m).word (r (8 * m ^ 2) (60 * V + 40)).word,
    f * n + 8 * m ^ 2 + max (modulusNeed n V m).cells (r (8 * m ^ 2) (60 * V + 40)).cells,
    f + 1 + max (modulusNeed n V m).depth (r (8 * m ^ 2) (60 * V + 40)).depth⟩

/-- The block of parameters that the recursive procedure gets by its address `cx`: `V`, `m`, `Λ`,
`np`, `pr`, `cnt`. -/
def CtxAt (μ : ℕ → ℤ) (cx V m Λ np pr cnt : ℕ) : Prop := Seg μ cx [(V : ℤ), m, Λ, np, pr, cnt]

/-- What the recursive procedure assumes with `f` levels to go: the memory of a node, the block of
parameters at `cx`, below the free pointer and apart from the count table, and the limits. -/
structure NodesPre (lim : Limits) (r : ℕ → ℕ → Need) (μ : ℕ → ℤ) (a : NodeArgs) (Λ cx f d : ℕ) :
    Prop where
  mem : NodeMem μ a
  ctx : CtxAt μ cx a.V a.m Λ a.np a.pr a.cnt
  belowCtx : cx + 6 ≤ a.fr
  apartCtx : Apart cx 6 a.cnt (a.m * a.m)
  V_pos : 1 ≤ a.V
  m_pos : 1 ≤ a.m
  lam : Λ = Lam a.V
  primes : (Nat.primesLE a.m).Nonempty
  ok : (nodesNeed r a.n a.V a.m f).Ok lim a.fr d











/-! ## The front: distinct values, multiplicities, binary digits, the splittings -/

/-- The time of distinct. -/
def tDistinct (n : ℕ) : ℕ := 60 * n + 40


/-- The time of bits. -/
def tBits (len Λ : ℕ) : ℕ := len * (60 * Λ + 40) + 40 * Λ + 60


/-- What distinct assumes: the sorted list stands at `a`; the three regions lie in the memory and do
not meet; addresses and counts fit in a word. -/
structure Distinct.Ctx (lim : Limits) (μ : ℕ → ℤ) (a val mul : ℕ) (L : List ℤ) : Prop where
  sorted : L.Pairwise (· ≤ ·)
  seg : Seg μ a L
  apartVal : Apart a L.length val L.length
  apartMul : Apart a L.length mul L.length
  apart : Apart val L.length mul L.length
  spaceSrc : a + L.length ≤ lim.space
  spaceVal : val + L.length ≤ lim.space
  spaceMul : mul + L.length ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (2 * L.length + 8 : ℤ) ≤ lim.word

/-- distinct(n, a, val, mul): the `n` cells from `a` hold a sorted list.  Writes its distinct values
to `val` and how often each occurs to `mul` (room for `n` cells each), and returns the number of
distinct values. -/
def DistinctSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d a val mul : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Distinct.Ctx lim μ a val mul L →
    Meets lim P p d [L.length, a, val, mul] μ (tDistinct L.length) fun r μ' =>
      (∃ D : List ℤ, r = (D.length : ℤ) ∧ D.Nodup ∧ D.toFinset = L.toFinset ∧ Seg μ' val D ∧
        Seg μ' mul (D.map fun x => (L.count x : ℤ))) ∧
      SameOutside2 μ μ' val L.length mul L.length









/-- The table of the binary digits of the labels: digit `β` of the label of the `i`-th element in
cell `i Λ + β`. -/
def bitTable (V Λ : ℕ) (L : List ℤ) : List ℤ :=
  L.flatMap fun x => (List.range Λ).map fun β => if (lab V x).testBit β then 1 else 0

/-- What bits assumes: the list of numbers of absolute value at most `V` stands at `s`; the labels
have `Λ` binary digits, and `2^Λ` is not much larger than they are; the list and the table lie in
the memory and do not meet; addresses and doubled labels fit in a word. -/
structure Bits.Ctx (lim : Limits) (μ : ℕ → ℤ) (s V Λ bt : ℕ) (L : List ℤ) : Prop where
  bounded : AbsLe L V
  lt_pow : 2 * V < 2 ^ Λ
  pow_le : 2 ^ Λ ≤ 4 * V + 4
  seg : Seg μ s L
  apart : Apart s L.length bt (L.length * Λ)
  spaceSrc : s + L.length ≤ lim.space
  spaceTable : bt + L.length * Λ ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (8 * V + 16 : ℤ) ≤ lim.word

/-- bits(len, s, V, Λ, bt, fr) writes the table of the binary digits of the labels `x + V` of the
`len` numbers from `s` to `bt` (`len Λ` cells).  It does not use the free pointer. -/
def BitsSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d fr s bt V Λ : ℕ) (L : List ℤ) (μ : ℕ → ℤ), Bits.Ctx lim μ s V Λ bt L →
    Meets lim P p d [L.length, s, V, Λ, bt, fr] μ (tBits L.length Λ) fun _ μ' =>
      Seg μ' bt (bitTable V Λ L) ∧ SameOutside μ μ' bt (L.length * Λ)







end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Buckets
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: remainders, counts, collisions, heavy elements

Four routines of the reduction of [CH20, Theorem 5.1] (for Theorem 21(a)).
They hash a set of integers modulo M.

* resid writes the remainders of the elements of a set (`resid_spec`).
* tally adds the remainders to a table of counts, or removes them from it (`tally_spec`).
* coll returns the number of colliding ordered pairs (`coll_spec`): by `coll_eq_list` it is the sum,
  over the elements, of the size of the element's bucket minus 1.
* heavy extracts the elements that are not alone in their bucket (`heavy_spec`,
  `heavyList_toFinset`).

In the statements the modulus is Mo, since in a program text M (…) reads a cell of the memory.
`keys M L` is the list of the remainders x % M of the numbers of L, as natural numbers, and `SegN`
is `Seg` for a list of natural numbers.

coll and heavy begin and end in the same way: resid writes the remainders to the free pointer, tally
counts them (`Counted`), a loop reads the counts, and tally removes them, so that the table holds
zeros again.  The three calls are `BucketPre.resid_meets`, `count_meets` and `uncount_meets`.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray Finset

variable {lim : Limits} {P : Program}

/-! ## resid -/

namespace Resid

/-- The local variables of resid: the arguments len, s, sg, M, key, fr, the counter i, and the
remainder. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Sign : ℕ := 2
@[inherit_doc Len] abbrev Modulus : ℕ := 3
@[inherit_doc Len] abbrev Key : ℕ := 4
@[inherit_doc Len] abbrev Free : ℕ := 5
@[inherit_doc Len] abbrev Idx : ℕ := 6
@[inherit_doc Len] abbrev Rem : ℕ := 7

end Resid

open Resid in
/-- resid(len, s, sg, M, key, fr): for i < len, mem[key + i] := emod(sg * mem[s + i], M, fr). -/
def residBody (pEmod : ℕ) : Stmt :=
  .for Idx (v Len) (
    .call pEmod [v Sign *' M (v Src +' v Idx), v Modulus, v Free] Rem ;;
    .store (v Key +' v Idx) (v Rem))









/-! ## tally -/

namespace Tally

/-- The local variables of tally: the arguments len, key, cnt, δ, and the counter i. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Key : ℕ := 1
@[inherit_doc Len] abbrev Count : ℕ := 2
@[inherit_doc Len] abbrev Delta : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4

end Tally

open Tally in
/-- tally(len, key, cnt, δ): for i < len, mem[cnt + mem[key + i]] += δ. -/
def tallyBody : Stmt :=
  .for Idx (v Len) (
    .store (v Count +' M (v Key +' v Idx)) (M (v Count +' M (v Key +' v Idx)) +' v Delta))







/-! ## The pure side: buckets, collisions and heavy elements from the list of the remainders -/









/-! ## What coll and heavy share: the remainders are counted, used, and removed from the table -/

/-- What coll and heavy assume: the list L at s, a count table of zeros with a cell for each
remainder, both below the free pointer and apart, and the limits. -/
structure BucketPre (lim : Limits) (μ : ℕ → ℤ) (d fr V Mo s cnt cap : ℕ) (L : List ℤ) : Prop where
  modulus_pos : 1 ≤ Mo
  modulus_le : Mo ≤ cap
  bounded : AbsLe L V
  list : Seg μ s L
  zero : ZeroAt μ cnt cap
  belowList : s + L.length ≤ fr
  belowTable : cnt + cap ≤ fr
  apart : Apart s L.length cnt cap
  ok : (collNeed L.length V Mo).Ok lim fr d











namespace BucketPre

variable {μ μ₁ : ℕ → ℤ} {d fr V Mo s cnt cap pResid pTally : ℕ} {L : List ℤ} {K : List ℕ}











end BucketPre

/-! ## coll -/

namespace Coll

/-- The local variables of coll: the arguments len, s, M, cnt, fr, the results of the calls, which
are not used, the counter i, and the sum.  Local 0 also takes the result. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Result : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Modulus : ℕ := 2
@[inherit_doc Len] abbrev Count : ℕ := 3
@[inherit_doc Len] abbrev Free : ℕ := 4
@[inherit_doc Len] abbrev Res : ℕ := 5
@[inherit_doc Len] abbrev Idx : ℕ := 6
@[inherit_doc Len] abbrev Total : ℕ := 7

end Coll

open Coll in
/-- The part of coll that adds up: sum := 0; for i < len, sum += mem[cnt + mem[fr + i]] - 1. -/
def collSum : Stmt :=
  .set Total (k 0) ;;
  .for Idx (v Len) (.set Total (v Total +' M (v Count +' M (v Free +' v Idx)) -' k 1))

open Coll in
/-- coll(len, s, M, cnt, fr) writes the remainders to fr, counts them, adds up, removes them from
the table, and returns the sum. -/
def collBody (pResid pTally : ℕ) : Stmt :=
  .call pResid [v Len, v Src, k 1, v Modulus, v Free, v Free +' v Len] Res ;;
  .call pTally [v Len, v Free, v Count, k 1] Res ;;
  collSum ;;
  .call pTally [v Len, v Free, v Count, k 0 -' k 1] Res ;;
  .set Result (v Total)











/-! ## heavy -/

namespace Heavy

/-- The local variables of heavy: the arguments len, s, M, out, cnt, fr, the results of the calls,
which are not used, the counter i, and the number j of elements written.  Local 0 also takes the
result. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Result : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Modulus : ℕ := 2
@[inherit_doc Len] abbrev Out : ℕ := 3
@[inherit_doc Len] abbrev Count : ℕ := 4
@[inherit_doc Len] abbrev Free : ℕ := 5
@[inherit_doc Len] abbrev Res : ℕ := 6
@[inherit_doc Len] abbrev Idx : ℕ := 7
@[inherit_doc Len] abbrev Written : ℕ := 8

end Heavy

open Heavy in
/-- A round of the loop of heavy: if 1 < mem[cnt + mem[fr + i]] then mem[out + j] := mem[s + i] and
j := j + 1. -/
def heavyRound : Stmt :=
  .ite (k 1 <' M (v Count +' M (v Free +' v Idx)))
    (.store (v Out +' v Written) (M (v Src +' v Idx)) ;; .set Written (v Written +' k 1)) .skip

open Heavy in
/-- The part of heavy that copies: j := 0; a round for each i < len. -/
def heavyCopy : Stmt :=
  .set Written (k 0) ;;
  .for Idx (v Len) heavyRound

open Heavy in
/-- heavy(len, s, M, out, cnt, fr) writes the remainders to fr, counts them, copies the heavy
elements, removes the remainders from the table, and returns the number of heavy elements. -/
def heavyBody (pResid pTally : ℕ) : Stmt :=
  .call pResid [v Len, v Src, k 1, v Modulus, v Free, v Free +' v Len] Res ;;
  .call pTally [v Len, v Free, v Count, k 1] Res ;;
  heavyCopy ;;
  .call pTally [v Len, v Free, v Count, k 0 -' k 1] Res ;;
  .set Result (v Written)















end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Distinct
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: distinct values, doubles of repeated values, a triple zero

Theorem 21(a), after [CH20, Theorem 5.1].  The three-set inputs of the
reduction for n numbers are made from the set of the values, from the doubles of the values that are
not 0 and occur at least twice (`ChanHe.twiceSet`), and from the set that is {0} if 0 occurs at
least three times and empty if not (`ChanHe.zeroSet`).  Three passes prepare these sets.

* zeroThree passes over the values and their multiplicities and answers whether 0 occurs at least
  three times (`zeroThree_spec`).
* twice passes over the same two lists and writes the doubles of the values that are not 0 and occur
  at least twice (`twice_spec`, with `twiceRound_runs` for one round).
* distinct passes over the sorted input and writes these two lists: the distinct values, and how
  often each occurs (`distinct_spec`, with `distinctRound_runs` for one round).

Each section first says what the pass has written or found after the first i elements, and how one
more element changes it.  The invariant of the loop is this, and the proof of a round compares the
tests of the program with the cases of that step.  The body of each loop is a block: a goal
`s.Runs lim σ R` is a pair, which says that the block s, started in σ, stays within the limits, and
that R holds of the state after it.  A procedure returns what its local 0 holds at the end.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## zeroThree -/









namespace ZeroThree







end ZeroThree







/-! ## twice -/







namespace Twice








end Twice











/-! ## distinct -/



namespace DistinctMem

variable {μ μ' : ℕ → ℤ} {val mul i : ℕ} {L D : List ℤ}





end DistinctMem

namespace Distinct

/-- The locals of distinct: the arguments n, a, val and mul, the counter, and the number of distinct
values so far. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Val : ℕ := 2
@[inherit_doc Len] abbrev Mul : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4
@[inherit_doc Len] abbrev Values : ℕ := 5

end Distinct

open Distinct in
/-- A new value opens a new cell of val and of mul. -/
def distinctOpen : Stmt :=
  .store (v Val +' v _root_.Light.Sec3.ChanHe.Distinct.Values) (M (v Src +' v Idx)) ;;
  .store (v Mul +' v _root_.Light.Sec3.ChanHe.Distinct.Values) (k 1) ;;
  .set _root_.Light.Sec3.ChanHe.Distinct.Values (v _root_.Light.Sec3.ChanHe.Distinct.Values +' k 1)

open Distinct in
/-- One round of distinct: the next element opens a cell if there is no value yet or if it differs
from the last value, and raises the last cell of mul if not. -/
def distinctRound : Stmt :=
  .ite (v _root_.Light.Sec3.ChanHe.Distinct.Values =' k 0) distinctOpen
    (.iteNe (M (v Src +' v Idx)) (M (v Val +' v _root_.Light.Sec3.ChanHe.Distinct.Values -' k 1)) distinctOpen
      (.store (v Mul +' v _root_.Light.Sec3.ChanHe.Distinct.Values -' k 1) (M (v Mul +' v _root_.Light.Sec3.ChanHe.Distinct.Values -' k 1) +' k 1))) ;;
  .set Idx (v Idx +' k 1)

open Distinct in
/-- distinct(n, a, val, mul): a sorted list of n numbers stands at a.  Writes its distinct values to
val and how often each occurs to mul, and returns the number of distinct values. -/
def distinctBody : Stmt :=
  .set Idx (k 0) ;;
  .set _root_.Light.Sec3.ChanHe.Distinct.Values (k 0) ;;
  .while (v Idx <' v Len) distinctRound ;;
  .set Len (v _root_.Light.Sec3.ChanHe.Distinct.Values)







end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.FrontFacts
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: what the lists that the first routines produce stand for

Theorem 21(a), after [CH20, Theorem 5.1].  The routines that run before the
recursion trees produce lists: the table of binary digits (`bitTable`), the selections by digits
(`pickList`), the distinct values with their multiplicities, and the doubles of the repeated values
(`twiceList`). This file has no program.  It shows that these lists represent the sets from which
the reduction makes its three-set inputs.

* A selection by one digit is `ChanHe.splitA`, a selection by two digits is `ChanHe.splitB`
  (`pick_splitA`, `pick_splitB`).
* `Values n X D C` says that `D` lists the distinct values of the input `X` and `C` how often each
  occurs.  Then `twiceList D C` represents `ChanHe.twiceSet` (`Values.twice`), and the test of
  zeroThree decides whether 0 occurs at least three times (`Values.zeroThree`).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-! ## The table of binary digits -/















/-! ## Selecting by binary digits -/













/-! ## The values of the input and how often they occur -/







/-- `D` lists the distinct values of the input `X`, and `C` how often each occurs. -/
structure Values (n : ℕ) (X D C : List ℤ) : Prop where
  /-- No value stands twice. -/
  nodup : D.Nodup
  /-- The members of `D` are the values of the input. -/
  values : D.toFinset = univ.image (vecOf n X)
  /-- `C` says at how many positions each value stands. -/
  counts : C = D.map fun a => ((#{i : Fin n | vecOf n X i = a} : ℕ) : ℤ)













end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.GridContracts
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: the loop over the splittings.  Specifications

round handles one splitting `(β, β', v)`: three selections and one call of the recursive procedure.
row runs through `β'` and `v` for a fixed `β`, and grid runs through `β`.  This file fixes their
specifications.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe Finset

/-- What the routines that run through the splittings are given, besides what the routines below
the recursion tree share: the number `Λ` of binary digits, the number `nd` of the distinct values
`D`, their address `val`, the addresses `bt` of the table of digits, `A` of the cells for the three
sets and `cx` of the block of parameters. -/
structure FrontArgs : Type extends Env where
  (Λ nd val bt A cx : ℕ)
  D : List ℤ



/-- What the memory holds while the splittings are run through: the `nd` distinct values `D` at
`val`, the table of their binary digits at `bt`, the block of parameters at `cx`, the primes, the
count table, and `3n` cells from `A` for the three sets of a splitting.  Everything lies below the
free pointer, and the cells from `A` and the count table meet nothing else. -/
structure FrontMem (μ : ℕ → ℤ) (a : FrontArgs) : Prop where
  lenD : a.D.length = a.nd
  nd_le : a.nd ≤ a.n
  nodup : a.D.Nodup
  bdd : Bdd a.V a.D.toFinset
  segVal : Seg μ a.val a.D
  segBt : Seg μ a.bt (bitTable a.V a.Λ a.D)
  ctx : CtxAt μ a.cx a.V a.m a.Λ a.np a.pr a.cnt
  primes : PrimesAt μ a.pr a.np a.m
  zero : ZeroAt μ a.cnt (a.m * a.m)
  belowVal : a.val + a.nd ≤ a.fr
  belowBt : a.bt + a.nd * a.Λ ≤ a.fr
  belowCx : a.cx + 6 ≤ a.fr
  belowPr : a.pr + a.np ≤ a.fr
  belowCnt : a.cnt + a.m * a.m ≤ a.fr
  belowA : a.A + 3 * a.n ≤ a.fr
  apartVal : Apart a.A (3 * a.n) a.val a.nd
  apartBt : Apart a.A (3 * a.n) a.bt (a.nd * a.Λ)
  apartCx : Apart a.A (3 * a.n) a.cx 6
  apartPr : Apart a.A (3 * a.n) a.pr a.np
  apartCnt : Apart a.A (3 * a.n) a.cnt (a.m * a.m)
  cntVal : Apart a.val a.nd a.cnt (a.m * a.m)
  cntCx : Apart a.cx 6 a.cnt (a.m * a.m)
  cntPr : Apart a.pr a.np a.cnt (a.m * a.m)











/-- The need of round, row (`extra = 1`) and grid (`extra = 2`): that of the recursive procedure,
and the levels of calls above it. -/
def gridNeed (r : ℕ → ℕ → Need) (n V m f extra : ℕ) : Need :=
  ⟨(nodesNeed r n V m f).word + 4 * V + 16, (nodesNeed r n V m f).cells,
    (nodesNeed r n V m f).depth + 1 + extra⟩

/-- What round (`extra = 0`), row (`extra = 1`) and grid (`extra = 2`) assume besides the memory. -/
structure GridPre (lim : Limits) (r : ℕ → ℕ → Need) (a : FrontArgs) (f extra d : ℕ) : Prop where
  V_pos : 1 ≤ a.V
  m_pos : 1 ≤ a.m
  lam : a.Λ = Lam a.V
  primes : (Nat.primesLE a.m).Nonempty
  ok : (gridNeed r a.n a.V a.m f extra).Ok lim a.fr d







end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Time
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: the time and the need of the host

The host s3(n, U, x, fr) has a parameter `κ` (a natural number, fixed with the program): it first
replaces the bound `U` by `max U (n^κ)`. So on all inputs with `U ≤ n^κ` it asks the
Convolution-3SUM solver for instances of one and the same length and bound, `8 m²` and
`120 n^κ + 40` with `m = mPar n (2 n^κ)`. (A running time `T N B` of an arbitrary solver need not be
monotone in `N`.)

The time is split into the host's own work and the number of calls of the solver. This file has the
definitions and one identity (`tNodes_eq`); the arithmetic (`claim_CH20_Theorem_5_1_of_host`) starts
from them.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset







/-- The time of params: four logarithms and a square root. -/
def tParams (n V : ℕ) : ℕ :=
  tLog2 (2 * V) + (18 * Nat.sqrt n + 12) + tLog2 (wPar n V + 1) + tLog2 n +
    (tLog2 (Nat.log 2 n + 2) + 30) + 160

/-- The time of prep: primes, count table, a copy, sorting, distinct values, binary digits. -/
def tPrep (n Λ m : ℕ) : ℕ :=
  tPrimes m + (13 * (m * m) + 6) + (16 * n + 6) + tSort n + tDistinct n + tBits n Λ + 240



















end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: the memory map of core; specifications of params, prep, core

Theorem 21(a), after [CH20, Theorem 5.1].  core decides 3SUM with a solver
of Convolution-3SUM.  It first calls params, which computes the three parameters of the reduction,
and prep, which fills the arrays that the rest of core works on.  The arrays stand one after the
other from a base address `b`.  This file fixes their layout (`Map`) and the specifications of
params, prep and core.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-! ## The memory map -/

/-- The addresses of the arrays of core, for the base address `b`, `n` numbers, `Λ` binary digits
and primes up to `m`. -/
structure Map : Type where
  /-- The base address. -/
  b : ℕ
  /-- The number of integers of the input. -/
  n : ℕ
  /-- The number of binary digits of a label. -/
  Λ : ℕ
  /-- The bound on the primes. -/
  m : ℕ

namespace Map
variable (a : Map)
/-- The block of parameters of the recursive procedure, 6 cells. -/
def cx : ℕ := a.b
/-- The primes, `m` cells. -/
def pr : ℕ := a.b + 6
/-- The count table, `m²` cells. -/
def cnt : ℕ := a.pr + a.m
/-- The sorted copy of the input, `n` cells. -/
def srt : ℕ := a.cnt + a.m * a.m
/-- The distinct values, `n` cells. -/
def val : ℕ := a.srt + a.n
/-- How often they occur, `n` cells. -/
def mul : ℕ := a.val + a.n
/-- The binary digits of the labels, `n Λ` cells. -/
def bt : ℕ := a.mul + a.n
/-- The three sets of a splitting, `3n` cells. -/
def A : ℕ := a.bt + a.n * a.Λ
/-- The doubles of the repeated values, `n` cells. -/
def tw : ℕ := a.A + 3 * a.n
/-- One cell that holds 0: the set {0}. -/
def one : ℕ := a.tw + a.n
/-- The free pointer behind the arrays. -/
def top : ℕ := a.one + 1



end Map

/-! ## params -/

/-- params(n, V, out) writes `Lam V`, `mPar n V` and `fuel n` to the three cells from `out`. -/
def ParamsSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d n V out : ℕ) (μ : ℕ → ℤ), out + 3 ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    ((8 * (mPar n V + 1) ^ 2 + 8 * V + 4 * n + 64 : ℕ) : ℤ) ≤ lim.word → d + 1 ≤ lim.depth →
    Meets lim P p d [n, V, out] μ (tParams n V) fun _ μ' =>
      Seg μ' out [(Lam V : ℤ), mPar n V, fuel n] ∧ SameOutside μ μ' out 3

/-! ## prep -/

/-- What prep needs: the size of a word, the number of cells behind the arrays (the sieve's table
and the scratch space of sorting stand there), and the depth of calls. -/
def prepNeed (n V Λ m : ℕ) : Need :=
  ⟨8 * (m + 1) ^ 2 + 8 * V + 4 * n + 64, m + n + Λ + 4, Nat.log 2 n + 3⟩

/-- What prep assumes about its arguments: the input `X` has `n` numbers of absolute value at most
`V` and stands below the base; `Λ` is the number of binary digits for `V`; and the limits allow for
what prep needs behind the arrays. -/
structure Prep.Ctx (lim : Limits) (d : ℕ) (a : Map) (V x : ℕ) (X : List ℤ) : Prop where
  /-- The input has `n` numbers. -/
  len : X.length = a.n
  /-- They have absolute value at most `V`. -/
  bounded : AbsLe X V
  /-- The input stands below the base. -/
  below : x + a.n ≤ a.b
  /-- `V` is not 0. -/
  bound_pos : 1 ≤ V
  /-- `Λ` is the number of binary digits for `V`. -/
  digits : a.Λ = Lam V
  /-- The limits allow for what prep needs. -/
  ok : (prepNeed a.n V a.Λ a.m).Ok lim a.top d

/-- What the routines that run through the splittings are given, for the arrays of a map and the
distinct values `D`. -/
@[simp] def Map.front (a : Map) (V : ℕ) (D : List ℤ) : FrontArgs where
  fr := a.top
  n := a.n
  V := V
  m := a.m
  np := #(Nat.primesLE a.m)
  pr := a.pr
  cnt := a.cnt
  Λ := a.Λ
  nd := D.length
  val := a.val
  bt := a.bt
  A := a.A
  cx := a.cx
  D := D

/-- prep(n, V, Λ, m, x, b): the input `X` stands at `x`.  Fills the arrays of the map `a` with base
`b`: the primes, zeros in the count table, the distinct values `D` and how often they occur, the
binary digits of their labels, the block of parameters, and 0 in the cell `one`.  Returns the number
of distinct values. -/
def PrepSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d : ℕ) (a : Map) (V x : ℕ) (X : List ℤ) (μ : ℕ → ℤ), Prep.Ctx lim d a V x X → Seg μ x X →
    Meets lim P p d [a.n, V, a.Λ, a.m, x, a.b] μ (tPrep a.n a.Λ a.m) fun res μ' =>
      (∃ D C : List ℤ, res = (D.length : ℤ) ∧ Values a.n X D C ∧ Seg μ' a.mul C ∧ μ' a.one = 0 ∧
        FrontMem μ' (a.front V D)) ∧
      Kept μ μ' a.b

/-! ## core -/



end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Modulus
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The reduction from 3SUM to Convolution-3SUM: the modulus of a node

For Theorem 21(a).  The modulus of a node of the recursion tree of
[CH20, Theorem 5.1] is the product of two primes up to m: p₁ is the least prime q such that the
three sets have few colliding pairs modulo q (`firstP`), and p₂ the least prime q such that few of
these pairs still collide modulo p₁ q (`secondP`).

* search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr) runs through the primes q in
  ascending order and returns the first one for which each of the three sets has at most bᵢ / np
  colliding pairs modulo mult · q (`Good`), and 1 if there is none (`search_spec`).  It always runs
  through all candidates.  A round (`searchRound_ends`) makes three tests (`check_ends`,
  `searchChecks_ends`) and records the candidate; that the first good element of the sorted list is
  the least good element of the set is `pick_filter`.
* modulus calls search twice, as in the definitions of the two primes, with three calls of coll in
  between, and returns the product; if there is no prime at all it returns 1 (`modulus_spec`).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

variable {lim : Limits} {P : Program}

namespace FirstGood

/-! ## The least good element of a set is the first good element of its sorted list -/



variable {good : ℕ → Prop} [DecidablePred good]









end FirstGood

open FirstGood

/-! ## One test of a candidate -/

namespace Search

/-- The local variables of search: the arguments mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr,
cnt, fr; the number of the candidate; the first good candidate found so far (0 if none); the modulus
mult · q; a number of colliding pairs; and whether the candidate has passed all tests so far.  Local
0 also takes the result. -/
abbrev Mult : ℕ := 0
@[inherit_doc Mult] abbrev Result : ℕ := 0
@[inherit_doc Mult] abbrev Set1 : ℕ := 1
@[inherit_doc Mult] abbrev Len1 : ℕ := 2
@[inherit_doc Mult] abbrev Set2 : ℕ := 3
@[inherit_doc Mult] abbrev Len2 : ℕ := 4
@[inherit_doc Mult] abbrev Set3 : ℕ := 5
@[inherit_doc Mult] abbrev Len3 : ℕ := 6
@[inherit_doc Mult] abbrev Bound1 : ℕ := 7
@[inherit_doc Mult] abbrev Bound2 : ℕ := 8
@[inherit_doc Mult] abbrev Bound3 : ℕ := 9
@[inherit_doc Mult] abbrev NumPrimes : ℕ := 10
@[inherit_doc Mult] abbrev Primes : ℕ := 11
@[inherit_doc Mult] abbrev Count : ℕ := 12
@[inherit_doc Mult] abbrev Free : ℕ := 13
@[inherit_doc Mult] abbrev Idx : ℕ := 14
@[inherit_doc Mult] abbrev Found : ℕ := 15
@[inherit_doc Mult] abbrev Modulus : ℕ := 16
@[inherit_doc Mult] abbrev Pairs : ℕ := 17
@[inherit_doc Mult] abbrev Passed : ℕ := 18

end Search

open Search in
/-- One test: pairs := coll(len, s, modulus, cnt, fr); if b < pairs * np then passed := 0.  The set
has its length in local xl and its address in local xs, and the bound b is in local xb. -/
def checkStmt (pColl xl xs xb : ℕ) : Stmt :=
  .call pColl [v xl, v xs, v Modulus, v Count, v Free] Pairs ;;
  .ite (v xb <' v Pairs *' v NumPrimes) (.set Passed (k 0)) .skip



/-! ## The search -/

open Search in
/-- The three tests of a candidate. -/
def searchChecks (pColl : ℕ) : Stmt :=
  checkStmt pColl Len1 Set1 Bound1 ;;
  checkStmt pColl Len2 Set2 Bound2 ;;
  checkStmt pColl Len3 Set3 Bound3

open Search in
/-- The candidate is recorded: if passed = 1 and found = 0 then found := mem[pr + t]. -/
def searchRecord : Stmt :=
  .ite (v Passed =' k 1) (.ite (v Found =' k 0) (.set Found (M (v Primes +' v Idx))) .skip) .skip

open Search in
/-- A round of search, for candidate number t: modulus := mult * mem[pr + t]; passed := 1; the three
tests; the candidate is recorded. -/
def searchRound (pColl : ℕ) : Stmt :=
  .set Modulus (v Mult *' M (v Primes +' v Idx)) ;;
  .set Passed (k 1) ;;
  searchChecks pColl ;;
  searchRecord

open Search in
/-- search(mult, s₁, l₁, s₂, l₂, s₃, l₃, b₁, b₂, b₃, np, pr, cnt, fr): found := 0; a round for each
t < np; return found, or 1 if found = 0. -/
def searchBody (pColl : ℕ) : Stmt :=
  .set Found (k 0) ;;
  .for Idx (v NumPrimes) (searchRound pColl) ;;
  .ite (v Found =' k 0) (.set Result (k 1)) (.set Result (v Found))

section search

variable {d pColl : ℕ} {x : SearchArgs} {μ : ℕ → ℤ}



















end search

/-! ## The modulus -/

namespace Modulus

/-- The local variables of modulus: the arguments s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr; the
two primes; and the numbers of colliding pairs of the three sets modulo the first prime.  Local 0
also takes the result. -/
abbrev Set1 : ℕ := 0
@[inherit_doc Set1] abbrev Result : ℕ := 0
@[inherit_doc Set1] abbrev Len1 : ℕ := 1
@[inherit_doc Set1] abbrev Set2 : ℕ := 2
@[inherit_doc Set1] abbrev Len2 : ℕ := 3
@[inherit_doc Set1] abbrev Set3 : ℕ := 4
@[inherit_doc Set1] abbrev Len3 : ℕ := 5
@[inherit_doc Set1] abbrev Digits : ℕ := 6
@[inherit_doc Set1] abbrev NumPrimes : ℕ := 7
@[inherit_doc Set1] abbrev Primes : ℕ := 8
@[inherit_doc Set1] abbrev Count : ℕ := 9
@[inherit_doc Set1] abbrev Free : ℕ := 10
@[inherit_doc Set1] abbrev Prime1 : ℕ := 11
@[inherit_doc Set1] abbrev Prime2 : ℕ := 12
@[inherit_doc Set1] abbrev Pairs1 : ℕ := 13
@[inherit_doc Set1] abbrev Pairs2 : ℕ := 14
@[inherit_doc Set1] abbrev Pairs3 : ℕ := 15

end Modulus

open Modulus in
/-- The numbers of colliding pairs of the three sets modulo the first prime. -/
def modulusColls (pColl : ℕ) : Stmt :=
  .call pColl [v Len1, v Set1, v Prime1, v Count, v Free] Pairs1 ;;
  .call pColl [v Len2, v Set2, v Prime1, v Count, v Free] Pairs2 ;;
  .call pColl [v Len3, v Set3, v Prime1, v Count, v Free] Pairs3

open Modulus in
/-- The two searches of modulus, with the three calls of coll between them, and the product. -/
def modulusMain (pSearch pColl : ℕ) : Stmt :=
  .call pSearch
    [k 1, v Set1, v Len1, v Set2, v Len2, v Set3, v Len3,
      k 3 *' v Digits *' v Len1 *' v Len1,
      k 3 *' v Digits *' v Len2 *' v Len2,
      k 3 *' v Digits *' v Len3 *' v Len3,
      v NumPrimes, v Primes, v Count, v Free] Prime1 ;;
  modulusColls pColl ;;
  .call pSearch
    [v Prime1, v Set1, v Len1, v Set2, v Len2, v Set3, v Len3,
      k 3 *' v Digits *' v Pairs1,
      k 3 *' v Digits *' v Pairs2,
      k 3 *' v Digits *' v Pairs3,
      v NumPrimes, v Primes, v Count, v Free] Prime2 ;;
  .set Result (v Prime1 *' v Prime2)

open Modulus in
/-- modulus(s₁, l₁, s₂, l₂, s₃, l₃, Λ, np, pr, cnt, fr) returns 1 if there is no prime, and the
product of the two primes otherwise. -/
def modulusBody (pSearch pColl : ℕ) : Stmt :=
  .ite (v NumPrimes =' k 0) (.set Result (k 1)) (modulusMain pSearch pColl)

section modulus

variable {d Λ pSearch pColl : ℕ} {a : NodeArgs} {μ : ℕ → ℤ}









section words

variable {n V m : ℕ}







end words











end modulus

end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeArray
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The reduction from 3SUM to Convolution-3SUM: the array of a node

Theorem 21(a), after [CH20, Theorem 5.1].
nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr) writes the first `8 m²` cells of the
one-array instance of the node `(S₁, S₂, S₃, M)` (`ChanHe.Node.oneArray`) to `y`
(`nodeArray_spec`).  The array consists of c = 2m² groups of four cells; cell t of group i is the
cell y + 4i + t.

* With `W = 2V + 1` and `G = 3W + 1` the padding pattern `10G, W + G, W + 3G, -W + 4G` (`padVal`) is
  written to all groups (`pad_ends`).
* Then, for each of the three sets, a pass (`placeStmt`, `place_ends`) computes the remainders of
  the numbers sg · x, where x runs through the set and sg is 1 for the first two sets and -1 for the
  third; counts them in the count table; writes sg · x + g, for every x whose remainder r has the
  count 1, to cell off of group r (and of group r + M, for the third set; `placeRound_ends`,
  `PlaceInv`); and removes the counts again.  Here g is G, 3G, 4G and off is 1, 2, 3.
* In terms of the arrays of the reduction (`place_arr`): afterwards cell off of group i holds entry
  i of the array of the set, plus g (`place_col` for the first two sets, `place_colZ` for the
  third).
* The four kinds of cells make up the one-array instance (`oneArray_of_cells`); the parts are put
  together in `nodeArrayBody_ends`.

The three passes are the same piece of text, which reads its parameters from local variables.  It is
not a procedure of its own, so that the depth of calls is the one that the specification allows for.

From other files: `keys M L` is the list of the remainders of the numbers of L, as natural numbers;
`arr S M pd r` is the element of S with the remainder r if there is exactly one, and the padding
value pd otherwise; `arrZ` is the same for the negatives of S, repeated at r + M; `BucketPre` is
what coll and heavy assume about a set and the count table; `Counted` says that the remainders stand
at the free pointer and that the table holds how often each occurs.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The local variables -/

namespace ArrLocals

/-- The local variables of nodeArray: the arguments M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr; the
numbers W and G; a counter, an address, a remainder, a value and the result of a call, which the
padding loop and the passes use; the number 2m² of groups; the parameters of a pass, which are the
sign sg, the number g that is added, the address and the length of the set, the number of the cell
in its group, and the distance to the second cell; the free pointer behind the remainders; and the
padding pattern. -/
abbrev MOD : ℕ := 0
@[inherit_doc MOD] abbrev SET1 : ℕ := 1
@[inherit_doc MOD] abbrev LEN1 : ℕ := 2
@[inherit_doc MOD] abbrev SET2 : ℕ := 3
@[inherit_doc MOD] abbrev LEN2 : ℕ := 4
@[inherit_doc MOD] abbrev SET3 : ℕ := 5
@[inherit_doc MOD] abbrev LEN3 : ℕ := 6
@[inherit_doc MOD] abbrev VMAX : ℕ := 7
@[inherit_doc MOD] abbrev MMAX : ℕ := 8
@[inherit_doc MOD] abbrev ARRAY : ℕ := 9
@[inherit_doc MOD] abbrev CNT : ℕ := 10
@[inherit_doc MOD] abbrev FREE : ℕ := 11
@[inherit_doc MOD] abbrev WIDTH : ℕ := 12
@[inherit_doc MOD] abbrev GAP : ℕ := 13
@[inherit_doc MOD] abbrev IDX : ℕ := 14
@[inherit_doc MOD] abbrev ADDR : ℕ := 15
@[inherit_doc MOD] abbrev KEY : ℕ := 16
@[inherit_doc MOD] abbrev VAL : ℕ := 17
@[inherit_doc MOD] abbrev RES : ℕ := 18
@[inherit_doc MOD] abbrev GROUPS : ℕ := 19
@[inherit_doc MOD] abbrev SIGN : ℕ := 20
@[inherit_doc MOD] abbrev SHIFT : ℕ := 21
@[inherit_doc MOD] abbrev SRC : ℕ := 22
@[inherit_doc MOD] abbrev LEN : ℕ := 23
@[inherit_doc MOD] abbrev OFF : ℕ := 24
@[inherit_doc MOD] abbrev DIST : ℕ := 25
@[inherit_doc MOD] abbrev FR2 : ℕ := 26
@[inherit_doc MOD] abbrev PAD0 : ℕ := 27
@[inherit_doc MOD] abbrev PAD1 : ℕ := 28
@[inherit_doc MOD] abbrev PAD2 : ℕ := 29
@[inherit_doc MOD] abbrev PAD3 : ℕ := 30

end ArrLocals

/-- The arguments of nodeArray. -/
structure ArrArgs : Type where
  Mo : ℕ
  s₁ : ℕ
  l₁ : ℕ
  s₂ : ℕ
  l₂ : ℕ
  s₃ : ℕ
  l₃ : ℕ
  V : ℕ
  m : ℕ
  y : ℕ
  cnt : ℕ
  fr : ℕ







/-! ## The padding pattern -/

open ArrLocals in
/-- For i < 2m²: the four cells of group i become the padding pattern. -/
def padStmt : Stmt :=
  .for IDX (v GROUPS) (
    .store (v ARRAY +' k 4 *' v IDX) (v PAD0) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 1) (v PAD1) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 2) (v PAD2) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 3) (v PAD3))







/-! ## One pass over a set -/

open ArrLocals in
/-- A round of the loop of a pass: key := mem[fr + j]; if mem[cnt + key] = 1 then
sg * mem[s + j] + g is written to the cells y + 4 key + off and y + 4 key + off + δ. -/
def placeRound : Stmt :=
  .set KEY (M (v FREE +' v IDX)) ;;
  .ite (M (v CNT +' v KEY) =' k 1)
    (.set ADDR (v ARRAY +' k 4 *' v KEY +' v OFF) ;;
     .set VAL (v SIGN *' M (v SRC +' v IDX) +' v SHIFT) ;;
     .store (v ADDR) (v VAL) ;;
     .store (v ADDR +' v DIST) (v VAL))
    .skip

open ArrLocals in
/-- The loop of a pass: a round for each j < len. -/
def placeLoop : Stmt := .for IDX (v LEN) placeRound

open ArrLocals in
/-- One pass.  The remainders of the numbers sg · x go to the cells from the free pointer and are
counted; the loop writes sg · x + g for every x whose remainder has the count 1; the counts are
removed. -/
def placeStmt (pResid pTally : ℕ) : Stmt :=
  .set FR2 (v FREE +' v LEN) ;;
  .call pResid [v LEN, v SRC, v SIGN, v MOD, v FREE, v FR2] RES ;;
  .call pTally [v LEN, v FREE, v CNT, k 1] RES ;;
  placeLoop ;;
  .call pTally [v LEN, v FREE, v CNT, k 0 -' k 1] RES







namespace PlaceInv

variable {μ μ' : ℕ → ℤ} {y off δ Mo j : ℕ} {K : List ℕ} {val : ℕ → ℤ}











end PlaceInv

/-- What a pass assumes: what coll and heavy assume about the set and the count table; sg is 1
or -1; the array of ylen cells from y lies below the free pointer, apart from the set and the table,
and has room for the cells that the pass writes; off is the number of a cell in its group; the
second cell is the first one (δ = 0) or lies behind the first M groups; and sg · x + g fits in a
word. -/
structure PassPre (lim : Limits) (μ : ℕ → ℤ) (d : ℕ) (a : ArrArgs) (sg g : ℤ) (s off δ cap ylen : ℕ)
    (L : List ℤ) : Prop where
  bucket : BucketPre lim μ d a.fr a.V a.Mo s a.cnt cap L
  sign : sg = 1 ∨ sg = -1
  belowArr : a.y + ylen ≤ a.fr
  apartSet : Apart a.y ylen s L.length
  apartTable : Apart a.y ylen a.cnt cap
  room : 4 * a.Mo + δ ≤ ylen
  off_lt : off < 4
  dist : δ = 0 ∨ 4 * a.Mo ≤ δ
  value_le : |g| + a.V ≤ lim.word

section pass

variable {μ μ₀ : ℕ → ℤ} {a : ArrArgs} {sg g : ℤ} {s off δ cap ylen : ℕ} {L : List ℤ} {K : List ℕ}
  {val : ℕ → ℤ}











end pass

/-! ## A pass, in terms of the cells number off of the groups -/







section column

variable {μ : ℕ → ℤ} {a : ArrArgs} {g pd : ℤ} {s off cap c : ℕ} {L : List ℤ} {pResid pTally : ℕ}





end column

/-! ## The routine -/

open ArrLocals in
/-- The constants: W = 2V + 1, G = 3W + 1, the number 2m² of groups, and the padding pattern. -/
def arrConsts : Stmt :=
  .set WIDTH (k 2 *' v VMAX +' k 1) ;;
  .set GAP (k 3 *' v WIDTH +' k 1) ;;
  .set GROUPS (k 2 *' (v MMAX *' v MMAX)) ;;
  .set PAD0 (k 10 *' v GAP) ;;
  .set PAD1 (v WIDTH +' v GAP) ;;
  .set PAD2 (v WIDTH +' k 3 *' v GAP) ;;
  .set PAD3 (k 4 *' v GAP -' v WIDTH)

open ArrLocals in
/-- The pass for the first set: x + G goes to cell 1 of the group of its remainder. -/
def arrPass₁ (pResid pTally : ℕ) : Stmt :=
  .set SIGN (k 1) ;;
  .set SHIFT (v GAP) ;;
  .set SRC (v SET1) ;;
  .set LEN (v LEN1) ;;
  .set OFF (k 1) ;;
  .set DIST (k 0) ;;
  placeStmt pResid pTally

open ArrLocals in
/-- The pass for the second set: x + 3G goes to cell 2 of the group of its remainder.  The sign 1
and the distance 0 are as the first pass left them. -/
def arrPass₂ (pResid pTally : ℕ) : Stmt :=
  .set SHIFT (k 3 *' v GAP) ;; .set SRC (v SET2) ;; .set LEN (v LEN2) ;; .set OFF (k 2) ;;
  placeStmt pResid pTally

open ArrLocals in
/-- The pass for the third set: -x + 4G goes to cell 3 of the groups r and r + M, where r is the
remainder of -x. -/
def arrPass₃ (pResid pTally : ℕ) : Stmt :=
  .set SIGN (k 0 -' k 1) ;; .set SHIFT (k 4 *' v GAP) ;; .set SRC (v SET3) ;; .set LEN (v LEN3) ;;
  .set OFF (k 3) ;; .set DIST (k 4 *' v MOD) ;;
  placeStmt pResid pTally

/-- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr), over the procedures number pResid and
pTally. -/
def nodeArrayBody (pResid pTally : ℕ) : Stmt :=
  arrConsts ;; padStmt ;; arrPass₁ pResid pTally ;; arrPass₂ pResid pTally ;;
  arrPass₃ pResid pTally

/-- What nodeArray assumes, apart from the three sets: the modulus, the count table, the place of
the array, and the limits. -/
structure ArrPre (lim : Limits) (μ : ℕ → ℤ) (d n : ℕ) (a : ArrArgs) : Prop where
  modulus_pos : 1 ≤ a.Mo
  modulus_le : a.Mo ≤ a.m * a.m
  zero : ZeroAt μ a.cnt (a.m * a.m)
  belowTable : a.cnt + a.m * a.m ≤ a.fr
  belowArr : a.y + 4 * (2 * (a.m * a.m)) ≤ a.fr
  apartTable : Apart a.y (4 * (2 * (a.m * a.m))) a.cnt (a.m * a.m)
  ok : (nodeArrayNeed n a.V a.m).Ok lim a.fr d

/-- What nodeArray assumes about one of the three sets, given as the list L at s. -/
structure ArrSet (μ : ℕ → ℤ) (n : ℕ) (a : ArrArgs) (s : ℕ) (L : List ℤ) : Prop where
  list : Seg μ s L
  nodup : L.Nodup
  bounded : AbsLe L a.V
  le : L.length ≤ n
  below : s + L.length ≤ a.fr
  apartTable : Apart s L.length a.cnt (a.m * a.m)
  apartArr : Apart a.y (4 * (2 * (a.m * a.m))) s L.length

section routine

variable {μ μ' : ℕ → ℤ} {n : ℕ} {a : ArrArgs} {s : ℕ} {L : List ℤ} {pResid pTally : ℕ}





















end routine



end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Parameters
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The parameters of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1].  params(n, V, out) computes the
three parameters of the reduction for n numbers of absolute value at most V: the number Λ =
⌊log₂(2V)⌋ + 1 of binary digits (`ChanHe.Lam`), the bound m on the primes (`ChanHe.mPar`), and the
number of levels of the recursion tree (`ChanHe.fuel`).  The program follows the definitions of the
three numbers line by line, so the proof (`params_spec`) only has to check that each intermediate
value fits in a word: each is at most a small multiple of V, of m or of n + 2 (first section).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

variable {lim : Limits} {P : Program}

/-! ## The sizes of the intermediate values -/









/-! ## The program -/

namespace Params

/-- The locals of params.  The arguments: the number n of integers, the bound V on their absolute
values, and the address of the three cells for the results.  Then, in the order in which they are
computed: ⌊log₂(2V)⌋; Λ; ⌊√n⌋; w + 1 with w = 5Λ(⌊√n⌋ + 1); ⌊log₂(w + 1)⌋; m; ⌊log₂ n⌋;
⌈log₂(⌊log₂ n⌋ + 2)⌉; the number of levels. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Out : ℕ := 2
@[inherit_doc Len] abbrev LogBound : ℕ := 3
@[inherit_doc Len] abbrev Digits : ℕ := 4
@[inherit_doc Len] abbrev Root : ℕ := 5
@[inherit_doc Len] abbrev Want : ℕ := 6
@[inherit_doc Len] abbrev LogWant : ℕ := 7
@[inherit_doc Len] abbrev PrimeBound : ℕ := 8
@[inherit_doc Len] abbrev LogLen : ℕ := 9
@[inherit_doc Len] abbrev Height : ℕ := 10
@[inherit_doc Len] abbrev Levels : ℕ := 11

end Params

open Params in
/-- params(n, V, out), over the procedures pLog2, pClog2 (logarithms, rounded down and up) and pSqrt
(the integer square root): writes Λ, m and the number of levels to the three cells from out. -/
def paramsBody (pLog2 pClog2 pSqrt : ℕ) : Stmt :=
  .call pLog2 [v Bound +' v Bound] LogBound ;;
  .set Digits (v LogBound +' k 1) ;;
  .call pSqrt [v Len] Root ;;
  .set Want (k 5 *' v Digits *' (v Root +' k 1) +' k 1) ;;
  .call pLog2 [v Want] LogWant ;;
  .set PrimeBound (v Want *' (k 2 *' v LogWant +' k 4)) ;;
  .call pLog2 [v Len] LogLen ;;
  .call pClog2 [v LogLen +' k 2] Height ;;
  .set Levels (k 3 *' v Height -' k 2) ;;
  .store (v Out) (v Digits) ;;
  .store (v Out +' k 1) (v PrimeBound) ;;
  .store (v Out +' k 2) (v Levels)



end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Prepare
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: filling the arrays of the host

Theorem 21(a), after [CH20, Theorem 5.1].  prep(n, V, Λ, m, x, b) fills
those arrays of the memory map `Map` with base b that do not depend on a splitting; the cells for
the three sets and for the doubles are left as they are.  It has five parts.

* prepAddr computes the addresses of the arrays (`prepAddr_runs`).
* prepTables writes the primes up to m and zeros into the count table (`prepTables_ends`).
* prepSorted writes a sorted copy of the input (`prepSorted_ends`).
* prepValues writes the distinct values, how often each occurs, and the binary digits of the labels
  of the values (`prepValues_ends`).
* prepTail writes the block of parameters of the recursive procedure and the cell that holds 0, and
  returns the number of distinct values (`prepTail_ends`).

The sieve and sorting use cells behind the arrays as scratch space.  The arrays are filled in the
order of their addresses, and a part changes no cell below the first array that it fills, except
that prepTail writes the block of parameters at the base.  So what an earlier part has written is
still there at the end (`PrepValues.frontMem`), and the arrays lie as the loop over the splittings
wants them (`FrontMem.of_map`).  `prepBody_ends` puts the five parts together, and `prep_spec` is
the specification.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace Prep

/-- The locals of prep.  The arguments: n, V, Λ, m, x and the base b.  Then the address of the
primes, the number m², the addresses of the count table, the sorted copy, the values, their
multiplicities, the table of digits, the three sets, the doubles and the cell that holds 0, and the
free pointer behind the arrays.  Then the number of primes, a local for results that are not read,
and the number of distinct values. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Bound : ℕ := 1
@[inherit_doc Len] abbrev Digits : ℕ := 2
@[inherit_doc Len] abbrev PrimeBound : ℕ := 3
@[inherit_doc Len] abbrev Src : ℕ := 4
@[inherit_doc Len] abbrev Base : ℕ := 5
@[inherit_doc Len] abbrev Primes : ℕ := 6
@[inherit_doc Len] abbrev Square : ℕ := 7
@[inherit_doc Len] abbrev Count : ℕ := 8
@[inherit_doc Len] abbrev Sorted : ℕ := 9
@[inherit_doc Len] abbrev Val : ℕ := 10
@[inherit_doc Len] abbrev Mul : ℕ := 11
@[inherit_doc Len] abbrev Table : ℕ := 12
@[inherit_doc Len] abbrev Sets : ℕ := 13
@[inherit_doc Len] abbrev Doubles : ℕ := 14
@[inherit_doc Len] abbrev Zero : ℕ := 15
@[inherit_doc Len] abbrev Top : ℕ := 16
@[inherit_doc Len] abbrev NumPrimes : ℕ := 17
@[inherit_doc Len] abbrev Unread : ℕ := 18
@[inherit_doc Len] abbrev NumValues : ℕ := 19

end Prep

open Prep in
/-- The addresses of the arrays. -/
def prepAddr : Stmt :=
  .set Primes (v Base +' k 6) ;;
  .set Square (v PrimeBound *' v PrimeBound) ;;
  .set Count (v Primes +' v PrimeBound) ;;
  .set Sorted (v Count +' v Square) ;;
  .set Val (v Sorted +' v Len) ;;
  .set Mul (v Val +' v Len) ;;
  .set Table (v Mul +' v Len) ;;
  .set Sets (v Table +' v Len *' v Digits) ;;
  .set Doubles (v Sets +' k 3 *' v Len) ;;
  .set Zero (v Doubles +' v Len) ;;
  .set Top (v Zero +' k 1)

open Prep in
/-- The primes, and zeros in the count table. -/
def prepTables (pPrimes pFill : ℕ) : Stmt :=
  .call pPrimes [v PrimeBound, v Primes, v Top] NumPrimes ;;
  .call pFill [v Count, v Square, k 0] Unread

open Prep in
/-- The sorted copy of the input. -/
def prepSorted (pCopy pSort : ℕ) : Stmt :=
  .call pCopy [v Src, v Sorted, v Len] Unread ;;
  .call pSort [v Len, v Sorted, v Top] Unread

open Prep in
/-- The distinct values with their multiplicities, and the binary digits of their labels. -/
def prepValues (pDistinct pBits : ℕ) : Stmt :=
  .call pDistinct [v Len, v Sorted, v Val, v Mul] NumValues ;;
  .call pBits [v NumValues, v Val, v Bound, v Digits, v Table, v Top] Unread

open Prep in
/-- The block of parameters, the cell that holds 0, and the result. -/
def prepTail : Stmt :=
  .store (v Base) (v Bound) ;;
  .store (v Base +' k 1) (v PrimeBound) ;;
  .store (v Base +' k 2) (v Digits) ;;
  .store (v Base +' k 3) (v NumPrimes) ;;
  .store (v Base +' k 4) (v Primes) ;;
  .store (v Base +' k 5) (v Count) ;;
  .store (v Zero) (k 0) ;;
  .set Len (v NumValues)

/-- prep(n, V, Λ, m, x, b), over the procedures pPrimes, pFill, pCopy, pSort, pDistinct, pBits. -/
def prepBody (pPrimes pFill pCopy pSort pDistinct pBits : ℕ) : Stmt :=
  prepAddr ;;
  prepTables pPrimes pFill ;;
  prepSorted pCopy pSort ;;
  prepValues pDistinct pBits ;;
  prepTail



/-! ## The five parts -/



















/-- What prepValues leaves in the memory: the distinct values D of the input X, how often each
occurs, and the binary digits of their labels. -/
structure PrepValues (μ : ℕ → ℤ) (a : Map) (V : ℕ) (X D C : List ℤ) : Prop where
  /-- D lists the distinct values, and C how often each occurs. -/
  values : Values a.n X D C
  /-- The values have absolute value at most V. -/
  bounded : AbsLe D V
  /-- The values stand at val. -/
  segVal : Seg μ a.val D
  /-- Their multiplicities stand at mul. -/
  segMul : Seg μ a.mul C
  /-- The binary digits of their labels stand at bt. -/
  segTable : Seg μ a.bt (bitTable V a.Λ D)





/-! ## The whole routine -/









end Light.Sec3.ChanHe

end
end


-- Original source module: ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Reduction
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: the core of the host

Theorem 21(a), after [CH20, Theorem 5.1].  core(n, V, x, b), with V = 2U,
decides 3SUM for the n numbers of absolute value at most U at x.  It has six parts.

* coreSetup computes the parameters and fills the arrays of the memory map (`coreSetup_ends`).
* coreAddr computes the addresses of the arrays that the rest uses (`coreAddr_runs`).
* coreSplit runs through the splittings (`coreSplit_ends`).
* coreDoubles and coreZero form and decide the two three-set inputs for the solutions that repeat a
  value (`coreDoubles_ends`, `coreZero_ends`).
* coreAnswer adds up the three answers (`coreAnswer_runs`).

That the three answers decide 3SUM is `threeSum_iff_trees`.  The routines that the three middle
parts call write only to the cells for the three sets of a splitting, to the cells for the doubles,
and behind the arrays; so the arrays that they read are still there at each call (`Core.Arrays`,
`Core.Arrays.of_sameOn`), and each three-set input lies in the memory as the recursive procedure
wants it (`Core.Placed`, `Core.Arrays.nodesPre`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-! ## The three answers, and the time -/







/-! ## The program -/

namespace Core

























end Core















variable {lim : Limits} {P : Program} {d : ℕ}

namespace Core





end Core

open Core

/-! ## The addresses -/





/-! ## The arrays, and a three-set input in the memory -/

namespace Core

/-- The parameters are those of the reduction. -/
structure Par (a : Map) (V f : ℕ) : Prop where
  len_pos : 1 ≤ a.n
  bound_pos : 1 ≤ V
  primeBound : a.m = mPar a.n V
  digits : a.Λ = Lam V
  levels : f = fuel a.n







/-- The arrays that the parts after coreAddr read: the distinct values D, how often they occur, the
block of parameters, the primes, the zeros of the count table, and the cell that holds 0. -/
structure Arrays (a : Map) (V : ℕ) (D C : List ℤ) (ν : ℕ → ℤ) : Prop where
  val : Seg ν a.val D
  mul : Seg ν a.mul C
  ctx : CtxAt ν a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt
  primes : PrimesAt ν a.pr #(Nat.primesLE a.m) a.m
  zero : ZeroAt ν a.cnt (a.m * a.m)
  one : ν a.one = 0
  val_le : D.length ≤ a.n
  mul_le : C.length ≤ a.n

section

variable {a : Map} {V : ℕ} {D C : List ℤ} {μ ν : ℕ → ℤ}



/-- A set of at most n numbers of absolute value at most V, in the l cells from s, which lie among
the arrays from the values on. -/
structure Placed (a : Map) (V : ℕ) (ν : ℕ → ℤ) (s l : ℕ) (S : Finset ℤ) : Prop where
  set : SetAt ν s l S
  le : l ≤ a.n
  bdd : Bdd V S
  from_val : a.val ≤ s
  below : s + l ≤ a.top









end

end Core

/-! ## The three answers -/

namespace Core

/-- What the parts after coreAddr assume: the parameters, the values of the input X, the arrays in
the memory μ, and what the limits must allow. -/
structure Ctx (lim : Limits) (r : ℕ → ℕ → Need) (d : ℕ) (a : Map) (V f : ℕ) (X D C : List ℤ)
    (μ : ℕ → ℤ) : Prop where
  par : Par a V f
  values : Values a.n X D C
  arrays : Arrays a V D C μ
  bddVal : Bdd V D.toFinset
  bddDoubles : Bdd V (twiceSet (vecOf a.n X))
  space : (lim.space : ℤ) ≤ lim.word
  cells : a.top + (nodesNeed r a.n V a.m f).cells ≤ lim.space
  word : ((nodesNeed r a.n V a.m f).word : ℤ) + 8 * V + 4 * a.n + 64 ≤ lim.word
  depth : d + (nodesNeed r a.n V a.m f).depth + 4 ≤ lim.depth

section

variable {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}









end

end Core

section parts

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {a : Map} {V f : ℕ} {X D C : List ℤ} {μ ν : ℕ → ℤ}
  {x b unread : ℤ}













end parts

/-! ## The parameters and the arrays -/

namespace Core

/-- What coreSetup leaves in the memory μ': the arrays for the values D of the input X, with how
often they occur; nothing below the free pointer b has changed. -/
structure Setup (a : Map) (V b : ℕ) (X D C : List ℤ) (μ μ' : ℕ → ℤ) : Prop where
  values : Values a.n X D C
  mul : Seg μ' a.mul C
  one : μ' a.one = 0
  front : FrontMem μ' (a.front V D)
  kept : Kept μ μ' b

end Core





/-! ## The routine -/





end Light.Sec3.ChanHe

end
end


