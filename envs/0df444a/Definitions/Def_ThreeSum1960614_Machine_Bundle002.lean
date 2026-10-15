-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle002
-- name    : ThreeSum1960614_Machine_Bundle002
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T04:57:26.272178+00:00
-- url     : https://prove2.me/theorems/3ea40045-e1bd-481b-af51-213e14f9f998
-- title:
--   Tensor recursion, boxes, and word-RAM problem interfaces
-- statement:
--   This bundle retains the paper interfaces needed from the formalization of Alman and Vassilevska Williams, *Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs*. The finite alphabets contain seven left variables, seven right variables, ten output variables, and ten terms of Schoenhage's identity. For $i,j\in\{0,1,2\}$, its output forms satisfy $\chi_{P_{ij}}=z_{ij}+z_0$ and $\chi_{P_0}=z_0$. A length-$L$ leaf contributes to an output string exactly when every coordinate contributes.
--
--   A cube is a length-$L$ string of terms and stars. If $S(\pi)$ and $Z(\pi)$ are its star and $P_0$ coordinate sets, the box predicate with natural parameters $m,t$ requires
--
--   $$|S(\pi)|+|Z(\pi)|\le m-t,\qquad \ell<\ell'\ \text{for every }\ell\in S(\pi),\ \ell'\in Z(\pi).$$
--
--   The graph interface has two parts of $n$ vertices, a finite middle part, two adjacency relations, and a finite set of query pairs. The machine interface defines solving a problem on a domain with a real time bound: every permitted input and admissible word size must have a terminating run within that bound, with a correct verdict and output. The derived bound for an integer-magnitude exponent $\kappa\in\mathbb N$, real time exponent $a$, and logarithmic exponent $e\in\mathbb N$ is $C(n^a(\log n)^e+1)$ for some fixed program, word-size slope, and constant $C$; the unrestricted predicate quantifies over every $\kappa$. Thin matrix inputs have dimensions $N\times D$ and $D\times N$, integer entries bounded in absolute value by $U$, and a repetition-free list of requested positions; their encoding stores the dimensions, fixed extra parameters, and row-major matrix entries.
--
--   These are specifications and data interfaces, not assertions that the corresponding algorithms already meet their bounds. They connect the combinatorial recursion and its matrix queries to the exact word-RAM semantics used by the complete deterministic integer 3SUM proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/PaperStatements.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

namespace Asymptotics
end Asymptotics
namespace ComparisonCounts
end ComparisonCounts
namespace Filter
end Filter
namespace Finset
end Finset
namespace PaperStatements
end PaperStatements
namespace ThreeSum1960614.Machine.PaperStatements
end ThreeSum1960614.Machine.PaperStatements
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.ChanHe
end ThreeSum1960614.Machine.ThreeSumApsp.ChanHe
namespace ThreeSum1960614.Machine.ThreeSumApsp.ComparisonCounts
end ThreeSum1960614.Machine.ThreeSumApsp.ComparisonCounts
namespace ThreeSum1960614.Machine.ThreeSumApsp.HintedMv
end ThreeSum1960614.Machine.ThreeSumApsp.HintedMv
namespace ThreeSum1960614.Machine.ThreeSumApsp.TriangleInstance
end ThreeSum1960614.Machine.ThreeSumApsp.TriangleInstance
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Items
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Items
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.ChanHe
end ThreeSumApsp.ChanHe
namespace ThreeSumApsp.ComparisonCounts
end ThreeSumApsp.ComparisonCounts
namespace ThreeSumApsp.HintedMv
end ThreeSumApsp.HintedMv
namespace ThreeSumApsp.TriangleInstance
end ThreeSumApsp.TriangleInstance
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam.Items
end ThreeSumApsp.WordRam.Items

namespace ThreeSum1960614.Machine

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

open _root_.Finset

namespace ThreeSumApsp
open _root_.ThreeSumApsp


/-! ### 2.2 Schönhage's identity for an inner product and an outer product -/

/-- Section 2.2: "We call x₁, x₂, x₃, p₁₁, p₁₂, p₂₁, p₂₂ the seven left variables". -/
inductive LeftVar : Type
  | x (i : Fin 3)
  | p (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Section 2.2: "and y₁, y₂, y₃, q₁₁, q₁₂, q₂₁, q₂₂ the seven right variables". -/
inductive RightVar : Type
  | y (j : Fin 3)
  | q (i j : Fin 2)
  deriving DecidableEq, Fintype

/-- Section 2.2: "We will also use ten output variables z_ij (for 1 ≤ i, j ≤ 3) and z₀". -/
inductive OutVar : Type
  | z (i j : Fin 3)
  | z0
  deriving DecidableEq, Fintype

/-- Section 2.2: "Schönhage's identity has ten terms, which we name P_ij (for 1 ≤ i, j ≤ 3,
corresponding to the entries of p̂ and q̂) and P₀". -/
inductive Term : Type
  | P (i j : Fin 3)
  | P0
  deriving DecidableEq, Fintype





/-- The linear form consisting of the single output variable `z_ij`. -/
def zForm (i j : Fin 3) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar → ℤ := Pi.single (_root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar.z i j) 1
/-- The linear form consisting of the single output variable `z₀`. -/
def z0Form : _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar → ℤ := Pi.single _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar.z0 1









/-- Section 2.2: the linear form `χ_λ` in the output variables,
"χ_{P_ij} = z_ij + z₀" and "χ_{P₀} = z₀". -/
def chi : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term → _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar → ℤ
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term.P i j => _root_.ThreeSum1960614.Machine.ThreeSumApsp.zForm i j + _root_.ThreeSum1960614.Machine.ThreeSumApsp.z0Form
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term.P0 => _root_.ThreeSum1960614.Machine.ThreeSumApsp.z0Form

















/-- Section 2.2: "We call the variables of the inner product, p, q, and z₀, inner". -/
def LeftVar.IsInner : _root_.ThreeSum1960614.Machine.ThreeSumApsp.LeftVar → Prop
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.LeftVar.x _ => False
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.LeftVar.p _ _ => True
/-- Section 2.2: the right variables `q` are inner, the `y` are outer. -/
def RightVar.IsInner : _root_.ThreeSum1960614.Machine.ThreeSumApsp.RightVar → Prop
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.RightVar.y _ => False
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.RightVar.q _ _ => True
/-- Section 2.2: the output variable `z₀` is inner, the `z_ij` are outer. -/
def OutVar.IsInner : _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar → Prop
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar.z _ _ => False
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar.z0 => True

instance LeftVar.instDecidablePredIsInner : DecidablePred _root_.ThreeSum1960614.Machine.ThreeSumApsp.LeftVar.IsInner
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.LeftVar.x _ => isFalse fun h => h
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.LeftVar.p _ _ => isTrue trivial
instance RightVar.instDecidablePredIsInner : DecidablePred _root_.ThreeSum1960614.Machine.ThreeSumApsp.RightVar.IsInner
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.RightVar.y _ => isFalse fun h => h
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.RightVar.q _ _ => isTrue trivial
instance OutVar.instDecidablePredIsInner : DecidablePred _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar.IsInner
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar.z _ _ => isFalse fun h => h
  | _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar.z0 => isTrue trivial

/-- Section 2.2: "We say that a term λ contributes to an output variable z if z appears in χ_λ." -/
def Term.Contributes (lam : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term) (z : _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar) : Prop := _root_.ThreeSum1960614.Machine.ThreeSumApsp.chi lam z ≠ 0

instance Term.instDecidableContributes (lam : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term) (z : _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar) : Decidable (lam.Contributes z) :=
  inferInstanceAs (Decidable (_root_.ThreeSum1960614.Machine.ThreeSumApsp.chi lam z ≠ 0))

/-! ### 2.3.1 The recursion -/



/-- Section 2.3.1: output strings of length `L`. -/
abbrev OutStr (L : ℕ) : Type := Fin L → _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutVar
/-- Section 2.3.1: "We refer to the call reached by choosing the terms τ₁, …, τ_k at levels 1, …, k
as the vertex τ₁ ⋯ τ_k, a string of k terms. It is at depth k". -/
abbrev Vertex (k : ℕ) : Type := Fin k → _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term
/-- Section 2.3.1: "the leaves, the vertices τ = τ₁ ⋯ τ_L at depth L". -/
abbrev Leaf (L : ℕ) : Type := _root_.ThreeSum1960614.Machine.ThreeSumApsp.Vertex L













/-! ### 2.3.2 Unraveling the recursion computation -/





/-- Section 2.3.2: "a vertex τ₁ ⋯ τ_k contributes to an output string w if τ_ℓ contributes to w_ℓ at
every level ℓ ≤ k", for a leaf, that is, for `k = L`: the leaf `τ` contributes to `w` if `τ_ℓ`
contributes to `w_ℓ` at every level `ℓ`. -/
def Leaf.Contributes {L : ℕ} (τ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Leaf L) (w : _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutStr L) : Prop :=
  ∀ ℓ, (τ ℓ).Contributes (w ℓ)

instance Leaf.instDecidableContributes {L : ℕ} (τ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Leaf L) (w : _root_.ThreeSum1960614.Machine.ThreeSumApsp.OutStr L) :
    Decidable (_root_.ThreeSum1960614.Machine.ThreeSumApsp.Leaf.Contributes τ w) :=
  inferInstanceAs (Decidable (∀ ℓ, (τ ℓ).Contributes (w ℓ)))





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

open _root_.Finset

namespace PaperStatements
open _root_.PaperStatements


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

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
open _root_.ThreeSumApsp


/-! ### 3.1 The Lopsided All-Edges Sparse Triangle problem -/

/-- **Definition 13**, the input: "an unweighted undirected tripartite graph with two parts
A and B of n vertices each and a middle part M [...], with arbitrary edges in M × A and M × B.  Let
W ⊆ A × B be the set of edges between A and B."  The bound "of at most D vertices" on the middle
part is `LopInstance.MiddleAtMost`. -/
structure LopInstance (n : ℕ) where
  /-- The middle part `M`. -/
  M : Type
  /-- The middle part is finite. -/
  [fintypeM : Fintype M]
  /-- `adjA a v`: the vertex `a ∈ A` and the middle vertex `v ∈ M` are adjacent. -/
  adjA : Fin n → M → Prop
  /-- `adjB v b`: the middle vertex `v ∈ M` and the vertex `b ∈ B` are adjacent. -/
  adjB : M → Fin n → Prop
  /-- The set `W ⊆ A × B` of edges between `A` and `B`; Section 3.1 calls its elements the query
  pairs. -/
  W : Finset (Fin n × Fin n)

attribute [instance] _root_.ThreeSum1960614.Machine.ThreeSumApsp.LopInstance.fintypeM













/-! #### Cutting a set of pairs into sets of bounded size

Corollary 15 ("splitting W into sets of at most n²/√D query pairs") and the proof of Theorem 17
("cut it into chunks of at most n²/√D query pairs") cut a set of pairs into smaller sets.  The paper
does not say how; we cut along the row-major order of the pairs. -/











/-! ### 3.2 A deterministic reduction from Exact Triangle to Lop-AE-SparseTri -/



namespace TriangleInstance
open _root_.ThreeSumApsp.TriangleInstance














end TriangleInstance



/-! #### Hashing modulo a prime (proof of Theorem 17) -/



namespace TriangleInstance
open _root_.ThreeSumApsp.TriangleInstance






end TriangleInstance

/-! #### The instances (proof of Theorem 17) -/











namespace TriangleInstance
open _root_.ThreeSumApsp.TriangleInstance










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
open _root_.ThreeSumApsp


namespace ChanHe
open _root_.ThreeSumApsp.ChanHe


open _root_.Finset

/-! ### Collisions and heavy elements -/





/-! ### The arrays of one node -/











/-! ### The choice of the modulus -/









/-! ### The recursion tree -/





/-! ### The parameters -/











/-! ### The reduction for three sets -/



/-! ### From n numbers to three sets -/











/-! ### Three arrays in one -/





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
open _root_.PaperStatements


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

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

open _root_.Finset





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

open _root_.Finset

namespace ThreeSumApsp
open _root_.ThreeSumApsp


/-! ### Notions from Section 2 -/



/-! ### 4.2 Boxes -/

/-- Section 4.2: the symbols of a cube, "each of which is one of the ten terms of Schönhage's
identity or a star ∗". -/
inductive CubeSymbol : Type
  | term (lam : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term)
  | star
  deriving DecidableEq, Fintype

/-- Section 4.2: "A cube is a string π = π₁ ⋯ π_L of L symbols, each of which is one of the ten
terms of Schönhage's identity or a star ∗." -/
abbrev Cube (L : ℕ) : Type := Fin L → _root_.ThreeSum1960614.Machine.ThreeSumApsp.CubeSymbol

/-- Section 4.2: "Its leaves are the leaves obtained by replacing each star by any of the ten
terms". So `τ` is a leaf of `π` if at every level `π` has a star or has the term of `τ`. -/
def Cube.HasLeaf {L : ℕ} (π : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube L) (τ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Leaf L) : Prop :=
  ∀ ℓ, π ℓ = _root_.ThreeSum1960614.Machine.ThreeSumApsp.CubeSymbol.star ∨ π ℓ = _root_.ThreeSum1960614.Machine.ThreeSumApsp.CubeSymbol.term (τ ℓ)

instance Cube.instDecidableHasLeaf {L : ℕ} (π : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube L) (τ : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Leaf L) :
    Decidable (_root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.HasLeaf π τ) :=
  inferInstanceAs (Decidable (∀ ℓ, π ℓ = _root_.ThreeSum1960614.Machine.ThreeSumApsp.CubeSymbol.star ∨ π ℓ = _root_.ThreeSum1960614.Machine.ThreeSumApsp.CubeSymbol.term (τ ℓ)))



/-- The set of levels at which a cube has a star. -/
def Cube.starLevels {L : ℕ} (π : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = _root_.ThreeSum1960614.Machine.ThreeSumApsp.CubeSymbol.star

/-- The set of levels at which a cube has the symbol `P₀`. -/
def Cube.P0Levels {L : ℕ} (π : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = _root_.ThreeSum1960614.Machine.ThreeSumApsp.CubeSymbol.term _root_.ThreeSum1960614.Machine.ThreeSumApsp.Term.P0



/-- Section 4.2: "A box is a cube π = π₁ ⋯ π_L such that (i) at most m - t of its symbols are P₀ or
stars, and (ii) every star is at a lower level than every P₀." -/
def IsBox {L : ℕ} (m t : ℕ) (π : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube L) : Prop :=
  (_root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.starLevels π).card + (_root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.starLevels π, ∀ ℓ' ∈ _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.P0Levels π, ℓ < ℓ'

instance IsBox.instDecidable {L : ℕ} (m t : ℕ) (π : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube L) : Decidable (_root_.ThreeSum1960614.Machine.ThreeSumApsp.IsBox m t π) :=
  inferInstanceAs (Decidable ((_root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.starLevels π).card + (_root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.starLevels π, ∀ ℓ' ∈ _root_.ThreeSum1960614.Machine.ThreeSumApsp.Cube.P0Levels π, ℓ < ℓ'))

















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

open _root_.Finset

namespace PaperStatements
open _root_.PaperStatements


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

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

open _root_.Finset

namespace ThreeSumApsp
open _root_.ThreeSumApsp


/-! ### Blocks of consecutive rows and columns (used in 5.1, 5.2 and 5.4) -/





/-! ### 5.2 Comparison counts -/

namespace ComparisonCounts
open _root_.ThreeSumApsp.ComparisonCounts






























/-! #### The objects in the proof of Lemma 36 -/

















/-! #### The construction of Lemma 37 -/



























/-! #### The parameters of Corollary 38 and of the proof of Theorem 35 -/







end ComparisonCounts

/-! ### 5.4 Three conjectures of van den Brand, Nanongkai, and Saranurak -/

namespace HintedMv
open _root_.ThreeSumApsp.HintedMv


















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

open _root_.Finset
open _root_.Asymptotics
open _root_.Filter

namespace PaperStatements
open _root_.PaperStatements


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

/-! ### 5.1 Directed APSP with small integer weights -/









/-! ### 5.2 3SUM, APSP, and Exact Triangle with real inputs -/

section ComparisonCounts

open _root_.ComparisonCounts

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
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

/-! ### What it means to solve a problem

**The order of the choices.**  In every statement the order is: the constants of the problem (the
exponent `κ` of the magnitude of the numbers, the `k` of `k`-Clique); then the program, the slope
`b` of the word size and the constant `C` of the time bound; then the instance; then the word size,
any number of bits that is admissible for the slope.  So the program cannot depend on the instance
or on its size, and it cannot rely on long words. -/

/-! #### The word size and the output cells -/





/-! #### Problems, and solving a problem within a time bound -/



/-- **Solving a problem within a time bound.**  The program `P` with slope `b` solves the problem on
the instances in `dom` within time `T`: on every such instance `x` and at every admissible word size
`bits`, the run from the first instruction on the starting memory (input in the cells 0, 1, 2, …,
zeros elsewhere) gives a verdict after at most `T x` steps, and the verdict and the output are a
correct answer. -/
def Solves (prob : _root_.ThreeSumApsp.WordRam.Problem) (P : List _root_.EndStatement.Instr) (b : ℕ) (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) :
    Prop :=
  ∀ x : prob.Inst, dom x → ∀ bits : ℕ, _root_.ThreeSumApsp.WordRam.Admissible b (prob.params x) bits →
    ∃ (t : ℕ) (verdict : Bool) (c : ℤ → BitVec bits), (t : ℝ) ≤ T x ∧
      _root_.EndStatement.exec P t 0 (_root_.EndStatement.loadWords bits (prob.input x)) = some (verdict, c) ∧
      prob.IsAnswer x verdict (_root_.ThreeSumApsp.WordRam.output c (prob.input x).length)

/-! #### Time bounds in one size `n`, for the problems of `EndStatement.lean` -/



/-- The problem `Q`, a value of `EndStatement.Problem`, is solved by a deterministic algorithm in
`O(n^a (log n)^e)` time when all numbers are integers of absolute value at most `n^κ`: there are a
program, a slope and a constant `C` such that the program solves `Q` within `C (n^a (log n)^e + 1)`
steps.  (For `a ≥ 0` the `+ 1` matters only at `n ≤ 1`, where `n^a (log n)^e` may be 0.) -/
def SolvedInTimeAt (Q : _root_.EndStatement.Problem) (κ : ℕ) (a : ℝ) (e : ℕ) : Prop :=
  ∃ (P : List _root_.EndStatement.Instr) (b : ℕ) (C : ℝ),
    _root_.ThreeSumApsp.WordRam.SolvesWithin Q κ P b fun n => C * ((n : ℝ) ^ a * Real.log n ^ e + 1)

/-- The same for every constant `κ`: "all numbers in the input are integers of absolute value
n^{O(1)}" (Theorem 2).  The program, the slope and the constant may depend on `κ`.

NOTE.  `κ` is the paper's ν.  Where the paper has ν ≥ 1 (Theorem 19, Corollary 39), `κ = 0` is
included here. -/
def SolvedInTime (Q : _root_.EndStatement.Problem) (a : ℝ) (e : ℕ) : Prop :=
  ∀ κ : ℕ, _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.SolvedInTimeAt Q κ a e





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

/-- Two matrices `X ∈ ℤ^{N×D}` and `Y ∈ ℤ^{D×N}` with entries of absolute value at most `U`. -/
structure ThinPair where
  /-- The long side. -/
  N : ℕ
  /-- The short side. -/
  D : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The first matrix. -/
  X : Matrix (Fin N) (Fin D) ℤ
  /-- The second matrix. -/
  Y : Matrix (Fin D) (Fin N) ℤ
  /-- The entries of `X` are bounded. -/
  boundX : ∀ i j, |X i j| ≤ (U : ℤ)
  /-- The entries of `Y` are bounded. -/
  boundY : ∀ i j, |Y i j| ≤ (U : ℤ)

/-- Theorem 5: two such matrices and "a set W of [...] positions of an N × N matrix".

NOTE.  The paper does not say how a set is given.  Here it is a list without repetitions, in any
order. -/
structure ThinInstance extends _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.ThinPair where
  /-- The wanted positions. -/
  W : List (Fin N × Fin N)
  /-- No position is listed twice. -/
  nodup : W.Nodup





/-! #### The two-stage data structure for a thin matrix product (Section 4) -/

/-- The input of the preprocessing: `N`, `D`, further parameters `extra` (none, except in
Theorem 30), then `X`, then `Y`.  The list `extra` is fixed before the instance. -/
def ThinPair.input (x : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.ThinPair) (extra : List ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ)] ++ extra ++ _root_.ThreeSumApsp.WordRam.rowMajor x.X ++ _root_.ThreeSumApsp.WordRam.rowMajor x.Y



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

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace PaperStatements
open _root_.PaperStatements


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp



















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
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr

namespace Items
open _root_.ThreeSumApsp.WordRam.Items


/-! ### Section 2: Theorem 5 -/



/-! ### Section 3: Corollaries 15 and 16, Theorems 19 and 22 -/













/-! ### Section 4: Theorems 24 and 25, Corollary 26, Theorem 30, Corollaries 31 and 32 -/



























/-! ### Section 5: Corollaries 39 and 40 -/











/-! ### Section 1, the introduction: Theorems 1 to 4 -/











end Items

end ThreeSumApsp.WordRam

end WordRamItems

end

end ThreeSum1960614.Machine


