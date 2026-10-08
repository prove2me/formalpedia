-- Prove2me | Definitions.Def_APSPSource_PaperStatements
-- name    : APSPSource_PaperStatements
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:24:40.221001+00:00
-- url     : https://prove2.me/theorems/3e3e5b1e-36fa-4dd4-934c-a8bee98be713
-- title:
--   Algebraic, graph, and word-RAM specifications for the APSP development
-- statement:
--   This bundle collects the mathematical objects used to state the source development's reductions and cost bounds.
--
--   1. The algebraic encoding uses seven left variables, seven right variables, ten output variables, and ten terms of Schönhage's identity. For strings of length $L$, a leaf $\tau$ chooses a term at every level. If $a$ and $b$ are integer arrays on left and right strings, and $\phi_\lambda,\psi_\lambda$ are the specified coefficient functions, their leaf encodings and the associated output sum are
--
--   $$
--   \Phi_\tau(a)=\sum_u a[u]\prod_{\ell=1}^{L}\phi_{\tau_\ell}(u_\ell),\qquad
--   \Psi_\tau(b)=\sum_v b[v]\prod_{\ell=1}^{L}\psi_{\tau_\ell}(v_\ell),\qquad
--   \operatorname{Mult}(a,b)[w]=\sum_{\tau\text{ contributing to }w}\Phi_\tau(a)\Psi_\tau(b).
--   $$
--
--   Here a term contributes when its output coefficient is nonzero, and a leaf contributes when this holds at every level. The bundle also defines the recursive full computation, inner and outer string indices, matrix encodings, private leaves, and their counting parameters. Cubes allow a star in place of a term; their values sum the products over all leaves extending the cube. Boxes, query sums, and a recurrence for cube values provide the corresponding data for the later query algorithms.
--
--   2. Graph specifications include tripartite integer-weighted triangle instances, query pairs for lopsided sparse-triangle instances, and residue classes and chunks. For three edge-weight arrays, the triangle sum is
--
--   $$S(a,b,c)=w_{AB}(a,b)+w_{BC}(b,c)+w_{AC}(a,c).$$
--
--   Exact and negative triangles mean, respectively, $S=0$ and $S<0$. For matrices with entries in an ordered additive type extended by $+\infty$, the min-plus product is
--
--   $$ (A\star B)_{ij}=\min_k(A_{ik}+B_{kj}). $$
--
--   The empty minimum is $+\infty$. Directed walks have the sum of their edge weights, with the empty walk of weight zero; missing edges have weight $+\infty$. A distance matrix assigns each ordered pair the least weight of a walk between its vertices. No negative cycle means every closed walk has nonnegative weight. Zero-diagonal weight matrices and repeated min-plus squaring are defined separately.
--
--   3. A word-RAM problem consists of instances, size parameters, an integer input list, and a predicate specifying the correct verdict and output. For a slope $b$, size parameters $p_1,\ldots,p_r$, and word length $W$, admissibility means
--
--   $$W\ge b\left(1+\sum_{i=1}^{r}\lfloor\log_2 p_i\rfloor\right).$$
--
--   The logarithm convention at zero is $\log_2 0=0$. The time predicates require one program and one word-size slope to handle every instance and every admissible word length. For each fixed input-magnitude exponent $\kappa\in\mathbb N$, the program, slope, and time constant may depend on $\kappa$; a polylogarithmic time predicate also permits the logarithm exponent to depend on $\kappa$. The bundle further defines polynomial and polylogarithmic asymptotic predicates, row-major encodings, and the explicit cost and entropy expressions used later.
--
--   These definitions give shared meanings to the later correctness and running-time statements. The bundle does not itself assert the existence of a truly subcubic APSP algorithm.
--
--   References:
--
--   1. [Source formalization: algebraic encodings](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L85-L438).
--   2. [Source formalization: triangle, min-plus, and shortest-path specifications](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L797-L1182).
--   3. [Source formalization: cubes, queries, and cost expressions](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1839-L2027).
--   4. [Source formalization: word-RAM problems and time predicates](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L3275-L3351).
--   5. [Source formalization: row-major matrix encoding](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L3431-L3433).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L85-L155; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L188-L215; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L219-L275; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L283-L307; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L311-L344; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L354-L396; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L406-L424; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L428-L429; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L433-L438; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L532-L557; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L797-L812; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L858-L859; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L870-L876; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L880-L891; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L895-L917; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L937-L940; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L944-L953; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L959-L963; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L971-L977; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L981-L984; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1004-L1011; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1053-L1068; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1077-L1081; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1088-L1128; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1132-L1139; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1176-L1182; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1242-L1243; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1839-L1841; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1845-L1940; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1944-L1983; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L1993-L2006; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L2020-L2027; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L3275-L3287; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L3291-L3313; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L3317-L3351; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/PaperStatements.lean#L3431-L3433

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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

set_option autoImplicit false
set_option relaxedAutoImplicit false


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

/-- The linear form consisting of the single left variable `x_i`. -/
def xForm (i : Fin 3) : LeftVar → ℤ := Pi.single (LeftVar.x i) 1
/-- The linear form consisting of the single left variable `p_ij`. -/
def pForm (i j : Fin 2) : LeftVar → ℤ := Pi.single (LeftVar.p i j) 1
/-- The linear form consisting of the single right variable `y_j`. -/
def yForm (j : Fin 3) : RightVar → ℤ := Pi.single (RightVar.y j) 1
/-- The linear form consisting of the single right variable `q_ij`. -/
def qForm (i j : Fin 2) : RightVar → ℤ := Pi.single (RightVar.q i j) 1
/-- The linear form consisting of the single output variable `z_ij`. -/
def zForm (i j : Fin 3) : OutVar → ℤ := Pi.single (OutVar.z i j) 1
/-- The linear form consisting of the single output variable `z₀`. -/
def z0Form : OutVar → ℤ := Pi.single OutVar.z0 1

/-- Section 2.2: the 3 × 3 matrix `p̂` of linear forms,
"p̂ = (p₁₁, p₁₂, 0; p₂₁, p₂₂, 0; -p₁₁-p₂₁, -p₁₂-p₂₂, 0)". -/
def pHat : Matrix (Fin 3) (Fin 3) (LeftVar → ℤ) :=
  !![pForm 0 0, pForm 0 1, 0;
     pForm 1 0, pForm 1 1, 0;
     -pForm 0 0 - pForm 1 0, -pForm 0 1 - pForm 1 1, 0]

/-- Section 2.2: the 3 × 3 matrix `q̂` of linear forms,
"q̂ = (q₁₁, q₁₂, -q₁₁-q₁₂; q₂₁, q₂₂, -q₂₁-q₂₂; 0, 0, 0)". -/
def qHat : Matrix (Fin 3) (Fin 3) (RightVar → ℤ) :=
  !![qForm 0 0, qForm 0 1, -qForm 0 0 - qForm 0 1;
     qForm 1 0, qForm 1 1, -qForm 1 0 - qForm 1 1;
     0, 0, 0]

/-- Section 2.2: the linear form `φ_λ` in the left variables,
"φ_{P_ij} = x_i + p̂_ij" and "φ_{P₀} = -(x₁ + x₂ + x₃)".
Section 2.3.1: "let φ_λ(s) ∈ {0, ±1} denote the coefficient of s in φ_λ"; this is `phi lam s`. -/
def phi : Term → LeftVar → ℤ
  | .P i j => xForm i + pHat i j
  | .P0 => -(xForm 0 + xForm 1 + xForm 2)

/-- Section 2.2: the linear form `ψ_λ` in the right variables,
"ψ_{P_ij} = y_j + q̂_ij" and "ψ_{P₀} = y₁ + y₂ + y₃".
Section 2.3.1: `ψ_λ(t)`, the coefficient of `t` in `ψ_λ`, is `psi lam t`. -/
def psi : Term → RightVar → ℤ
  | .P i j => yForm j + qHat i j
  | .P0 => yForm 0 + yForm 1 + yForm 2

/-- Section 2.2: the linear form `χ_λ` in the output variables,
"χ_{P_ij} = z_ij + z₀" and "χ_{P₀} = z₀". -/
def chi : Term → OutVar → ℤ
  | .P i j => zForm i j + z0Form
  | .P0 => z0Form
































/-- Section 2.2: "We call the variables of the inner product, p, q, and z₀, inner". -/
def LeftVar.IsInner : LeftVar → Prop
  | .x _ => False
  | .p _ _ => True
/-- Section 2.2: the right variables `q` are inner, the `y` are outer. -/
def RightVar.IsInner : RightVar → Prop
  | .y _ => False
  | .q _ _ => True
/-- Section 2.2: the output variable `z₀` is inner, the `z_ij` are outer. -/
def OutVar.IsInner : OutVar → Prop
  | .z _ _ => False
  | .z0 => True

instance LeftVar.instDecidablePredIsInner : DecidablePred LeftVar.IsInner
  | .x _ => isFalse fun h => h
  | .p _ _ => isTrue trivial
instance RightVar.instDecidablePredIsInner : DecidablePred RightVar.IsInner
  | .y _ => isFalse fun h => h
  | .q _ _ => isTrue trivial
instance OutVar.instDecidablePredIsInner : DecidablePred OutVar.IsInner
  | .z _ _ => isFalse fun h => h
  | .z0 => isTrue trivial

/-- Section 2.2: "We say that a term λ contributes to an output variable z if z appears in χ_λ." -/
def Term.Contributes (lam : Term) (z : OutVar) : Prop := chi lam z ≠ 0

instance Term.instDecidableContributes (lam : Term) (z : OutVar) : Decidable (lam.Contributes z) :=
  inferInstanceAs (Decidable (chi lam z ≠ 0))

/-! ### 2.3.1 The recursion -/

/-- Section 2.3.1: "A left string of length L is a string u = u₁ u₂ ⋯ u_L of L left variables, and
we call u_ℓ its variable at level ℓ." -/
abbrev LeftStr (L : ℕ) : Type := Fin L → LeftVar
/-- Section 2.3.1: right strings of length `L`. -/
abbrev RightStr (L : ℕ) : Type := Fin L → RightVar
/-- Section 2.3.1: output strings of length `L`. -/
abbrev OutStr (L : ℕ) : Type := Fin L → OutVar
/-- Section 2.3.1: "We refer to the call reached by choosing the terms τ₁, …, τ_k at levels 1, …, k
as the vertex τ₁ ⋯ τ_k, a string of k terms. It is at depth k". -/
abbrev Vertex (k : ℕ) : Type := Fin k → Term
/-- Section 2.3.1: "the leaves, the vertices τ = τ₁ ⋯ τ_L at depth L". -/
abbrev Leaf (L : ℕ) : Type := Vertex L

/-- Section 2.3.1: "An array a on the left strings of length L assigns an integer a[u] to each u
that is a left string of length L."  So such an array is a function `LeftStr L → ℤ`, and likewise
for right strings, output strings and leaves.

"the slice of a at a left variable s is the array a_s on the strings of length L - 1 given by
a_s[u'] := a[s u']"; the same definition is used for every alphabet. -/
def sliceAt {α β : Type} {L : ℕ} (a : (Fin (L + 1) → α) → β) (s : α) : (Fin L → α) → β :=
  fun u' => a (Fin.cons s u')

/-- Section 2.3.1, step (2) of `Full`: "A_λ := ∑_s φ_λ(s) a_s". -/
def encodeStepL {L : ℕ} (lam : Term) (a : LeftStr (L + 1) → ℤ) : LeftStr L → ℤ :=
  fun u' => ∑ s, phi lam s * sliceAt a s u'

/-- Section 2.3.1, step (2) of `Full`: "B_λ := ∑_t ψ_λ(t) b_t". -/
def encodeStepR {L : ℕ} (lam : Term) (b : RightStr (L + 1) → ℤ) : RightStr L → ℤ :=
  fun v' => ∑ t, psi lam t * sliceAt b t v'

/-- Section 2.3.1: "The recursion Full(a, b), for arrays a, b on the left and right strings of
length L, returns an array on the output strings of length L:
(1) If L = 0, return the number ab.
(2) For each term λ of Schönhage's identity, form A_λ := ∑_s φ_λ(s) a_s and B_λ := ∑_t ψ_λ(t) b_t.
(3) For each term λ, recursively compute C_λ := Full(A_λ, B_λ).
(4) Return the array c whose slices are c_{z_ij} := C_{P_ij} and c_{z₀} := ∑_λ C_λ."

`Full.run` is this recursion, and it also keeps a record of the multiplications.  Its first
component is the array that is returned.  Its second component gives, for each leaf `τ`, the two
numbers that step (1) multiplies at `τ`: the leaf `λ τ'` of a call is the leaf `τ'` of its recursive
call for `λ`.

An array on the strings of length 0 has one entry, at the empty string `Fin.elim0`; that entry is
"the number". -/
def Full.run : (L : ℕ) → (LeftStr L → ℤ) → (RightStr L → ℤ) → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ)
  | 0, a, b => (fun _ => a Fin.elim0 * b Fin.elim0, fun _ => (a Fin.elim0, b Fin.elim0))
  | L + 1, a, b =>
    let R : Term → (OutStr L → ℤ) × (Leaf L → ℤ × ℤ) := fun lam =>
      Full.run L (encodeStepL lam a) (encodeStepR lam b)
    (fun w =>
        match w 0 with
        | .z i j => (R (.P i j)).1 (Fin.tail w)
        | .z0 => ∑ lam, (R lam).1 (Fin.tail w),
      fun τ => (R (τ 0)).2 (Fin.tail τ))

/-- The array that `Full(a, b)` returns. -/
def Full (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ := (Full.run L a b).1





/-! ### 2.3.2 Unraveling the recursion computation -/

/-- Section 2.3.2: "Φ_τ(a) := ∑_u a[u] ∏_{ℓ=1}^{L} φ_{τ_ℓ}(u_ℓ)", the sum over all left strings
`u`. -/
def Phi {L : ℕ} (τ : Leaf L) (a : LeftStr L → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, phi (τ ℓ) (u ℓ)

/-- Section 2.3.2: "Ψ_τ(b) := ∑_v b[v] ∏_{ℓ=1}^{L} ψ_{τ_ℓ}(v_ℓ)", the sum over all right strings
`v`. -/
def Psi {L : ℕ} (τ : Leaf L) (b : RightStr L → ℤ) : ℤ := ∑ v, b v * ∏ ℓ, psi (τ ℓ) (v ℓ)

/-- Section 2.3.2: "a vertex τ₁ ⋯ τ_k contributes to an output string w if τ_ℓ contributes to w_ℓ at
every level ℓ ≤ k", for a leaf, that is, for `k = L`: the leaf `τ` contributes to `w` if `τ_ℓ`
contributes to `w_ℓ` at every level `ℓ`. -/
def Leaf.Contributes {L : ℕ} (τ : Leaf L) (w : OutStr L) : Prop :=
  ∀ ℓ, (τ ℓ).Contributes (w ℓ)

instance Leaf.instDecidableContributes {L : ℕ} (τ : Leaf L) (w : OutStr L) :
    Decidable (Leaf.Contributes τ w) :=
  inferInstanceAs (Decidable (∀ ℓ, (τ ℓ).Contributes (w ℓ)))

/-- Equation (2): "Mult(a, b)[w] := ∑_{τ contributing to w} Φ_τ(a) Ψ_τ(b)". -/
def Mult {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) : OutStr L → ℤ :=
  fun w => ∑ τ : Leaf L with Leaf.Contributes τ w, Phi τ a * Psi τ b

/-- Equation (3): "γ(s, t, z) := ∑_{λ contributing to z} φ_λ(s) ψ_λ(t)". -/
def gamma (s : LeftVar) (t : RightVar) (z : OutVar) : ℤ :=
  ∑ lam : Term with lam.Contributes z, phi lam s * psi lam t

/-! ### 2.3.3 Batch computation of multiple matrix products -/

/-- Section 2.3.3: "The inner set of a left string is the set of levels at which it has a p (as
opposed to an x)." -/
def innerSetL {L : ℕ} (u : LeftStr L) : Finset (Fin L) := univ.filter fun ℓ => (u ℓ).IsInner
/-- Section 2.3.3: "the inner set of a right string is the set of levels at which it has a q (as
opposed to a y)". -/
def innerSetR {L : ℕ} (v : RightStr L) : Finset (Fin L) := univ.filter fun ℓ => (v ℓ).IsInner
/-- Section 2.3.3: "the inner set of an output string is the set of levels at which it has z₀ (as
opposed to a z_ij)". -/
def innerSetO {L : ℕ} (w : OutStr L) : Finset (Fin L) := univ.filter fun ℓ => (w ℓ).IsInner

/-- Section 2.3.3: "N₀ := 3^{L-m}".  Meant for `m ≤ L`; for `m > L` the subtraction of natural
numbers is cut off at 0 and the value is 1. -/
def N0 (L m : ℕ) : ℕ := 3 ^ (L - m)
/-- Section 2.3.3: "D := 4^m". -/
def D (m : ℕ) : ℕ := 4 ^ m
/-- Section 2.3.3: "K := binom(L, m)", the number of subsets of `{1, …, L}` of size `m`. -/
def K (L m : ℕ) : ℕ := L.choose m

/-- The index `i` of an outer left variable `x_i` (the value at a `p` is never used). -/
def LeftVar.outerIndex : LeftVar → Fin 3
  | .x i => i
  | .p _ _ => 0
/-- The index pair `(i, j)` of an inner left variable `p_ij` (the value at an `x` is never used). -/
def LeftVar.innerIndex : LeftVar → Fin 2 × Fin 2
  | .x _ => (0, 0)
  | .p i j => (i, j)
/-- The index `j` of an outer right variable `y_j` (the value at a `q` is never used). -/
def RightVar.outerIndex : RightVar → Fin 3
  | .y j => j
  | .q _ _ => 0
/-- The index pair `(i, j)` of an inner right variable `q_ij` (the value at a `y` is never used). -/
def RightVar.innerIndex : RightVar → Fin 2 × Fin 2
  | .y _ => (0, 0)
  | .q i j => (i, j)









/-- A string of `L - m` outer left variables `x_{i₁} ⋯ x_{i_{L-m}}`, written as the string of its
indices `i₁ ⋯ i_{L-m}`.  The same type is used for strings `y_{j₁} ⋯ y_{j_{L-m}}` of outer right
variables.  Section 2.3.3: these strings index the `N₀` rows of an `N₀ × D` matrix and the `N₀`
columns of a `D × N₀` matrix. -/
abbrev OuterStr (L m : ℕ) : Type := Fin (L - m) → Fin 3

/-- A string of `m` inner left variables `π = p_{i₁j₁} ⋯ p_{i_m j_m}`, written as the string of its
index pairs.  The same type is used for strings `π' = q_{i₁j₁} ⋯ q_{i_m j_m}` of inner right
variables, so that the paper's `π'`, "with the same indices" as `π`, is the same element of this
type as `π`. Section 2.3.3: these strings index the `D` columns of an `N₀ × D` matrix and the `D`
rows of a `D × N₀` matrix. With this convention the paper's "(AB)[r, c] := ∑_π A[r, π] B[π', c]" is
the usual matrix product. -/
abbrev InnerStr (m : ℕ) : Type := Fin m → Fin 2 × Fin 2

/-- The levels of a set `Q` of `m` levels "in the order of the levels" (Section 2.3.3): the `k`-th
lowest level of `Q`. -/
def innerLevel {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Fin m ↪o Fin L :=
  Q.orderEmbOfFin hQ

/-- The number of levels outside a set of `m` levels is `L - m`. -/
theorem card_compl_of_card_eq {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) :
    Qᶜ.card = L - m := by
  rw [Finset.card_compl, Fintype.card_fin, hQ]

/-- The levels outside a set `Q` of `m` levels, in the order of the levels: the `k`-th lowest level
outside `Q`. -/
def outerLevel {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m) : Fin (L - m) ↪o Fin L :=
  Qᶜ.orderEmbOfFin (card_compl_of_card_eq Q hQ)

/-- Section 2.3.3: "its outer part is the string of its variables at the other levels", for a left
string whose inner set has `m` elements. -/
def outerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : OuterStr L m :=
  fun k => (u (outerLevel (innerSetL u) h k)).outerIndex
/-- Section 2.3.3: "The inner part of a string is the string of its variables at the levels of its
inner set, in the order of the levels", for a left string whose inner set has `m` elements. -/
def innerPartL {L m : ℕ} (u : LeftStr L) (h : (innerSetL u).card = m) : InnerStr m :=
  fun k => (u (innerLevel (innerSetL u) h k)).innerIndex
/-- The outer part of a right string whose inner set has `m` elements. -/
def outerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : OuterStr L m :=
  fun k => (v (outerLevel (innerSetR v) h k)).outerIndex
/-- The inner part of a right string whose inner set has `m` elements. -/
def innerPartR {L m : ℕ} (v : RightStr L) (h : (innerSetR v).card = m) : InnerStr m :=
  fun k => (v (innerLevel (innerSetR v) h k)).innerIndex









/-- An `N₀ × D` matrix, its rows and columns indexed by strings as in Section 2.3.3. -/
abbrev LeftMat (L m : ℕ) : Type := Matrix (OuterStr L m) (InnerStr m) ℤ
/-- A `D × N₀` matrix, its rows and columns indexed by strings as in Section 2.3.3. -/
abbrev RightMat (L m : ℕ) : Type := Matrix (InnerStr m) (OuterStr L m) ℤ

/-- Section 2.3.3: "a[u] := X_Q[u] […] for all the left strings u […] whose inner set Q has exactly
m elements, and a[u] := 0 […] at every other string", where "X_Q[u]" is the entry of `X_Q` "at the
row and the column of u": the row is the outer part of `u` and the column is its inner part. The
family `X` gives a matrix `X Q` for every set `Q` of levels; only those with `|Q| = m` are used. -/
def arrayL {L : ℕ} (m : ℕ) (X : Finset (Fin L) → LeftMat L m) : LeftStr L → ℤ :=
  fun u =>
    if h : (innerSetL u).card = m then X (innerSetL u) (outerPartL u h) (innerPartL u h) else 0

/-- Section 2.3.3: "b[v] := Y_Q[v]" for the right strings `v` whose inner set `Q` has exactly `m`
elements, "the row given by the inner part of v and the column by the outer part", and `b[v] := 0`
at every other string. -/
def arrayR {L : ℕ} (m : ℕ) (Y : Finset (Fin L) → RightMat L m) : RightStr L → ℤ :=
  fun v =>
    if h : (innerSetR v).card = m then Y (innerSetR v) (innerPartR v h) (outerPartR v h) else 0

/-! ### 2.3.4 Tiling the N × D × N product by products of shape N₀ × D × N₀: the number `M` -/

/-- Section 2.3.4: "M := K N₀²". -/
def M (L m : ℕ) : ℕ := K L m * N0 L m ^ 2

/-! ### 2.4.1 Sharing the encoding -/

/-- Section 2.4.1: "The encoding of a is the array of the 10^L numbers Φ_τ(a), indexed by the leaves
τ." -/
def encodingL {L : ℕ} (a : LeftStr L → ℤ) : Leaf L → ℤ := fun τ => Phi τ a

/-- Section 2.4.1: "The encoding of b, the array of the numbers Ψ_τ(b)". -/
def encodingR {L : ℕ} (b : RightStr L → ℤ) : Leaf L → ℤ := fun τ => Psi τ b

/-! ### 2.4.2 Skipping the calls that are not needed -/

























































































/-! ### 2.4.3 Few leaves contribute to a sparse set of entries -/

/-- The term that the private leaf has at a level where the output string has the variable `z`:
`P₀` for `z₀` and `P_ij` for `z_ij`. -/
def OutVar.privateTerm : OutVar → Term
  | .z i j => .P i j
  | .z0 => .P0

/-- Section 2.4.3: "the leaves contributing to an output string with inner set Q are the 10^m leaves
that choose any term at each of the m levels of Q, but P_ij at every level outside Q where the
output string has z_ij. We call the one that chooses P₀ at every level of Q the private leaf of the
output string." -/
def privateLeaf {L : ℕ} (w : OutStr L) : Leaf L := fun ℓ => (w ℓ).privateTerm

/-- The set of levels at which a leaf chooses `P₀`. -/
def P0Levels {L : ℕ} (τ : Leaf L) : Finset (Fin L) := univ.filter fun ℓ => τ ℓ = Term.P0

/-- Section 2.4.3: "we define the order of a leaf as m minus the number of levels at which it
chooses P₀." The order is an integer; it is negative for a leaf that chooses `P₀` at more than `m`
levels. -/
def order {L : ℕ} (m : ℕ) (τ : Leaf L) : ℤ := (m : ℤ) - ((P0Levels τ).card : ℤ)

/-- Section 2.4.3: "α_d := binom(m, d) 9^d". -/
def alpha (m d : ℕ) : ℕ := m.choose d * 9 ^ d

/-- Section 2.4.3: "β_d := binom(L, m-d) 9^{L-m+d}".  Meant for `d ≤ m ≤ L`; outside this range the
subtractions of natural numbers are cut off at 0 and the value has no meaning. -/
def beta (L m d : ℕ) : ℕ := L.choose (m - d) * 9 ^ (L - m + d)

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

attribute [instance] LopInstance.fintypeM





































/-! #### Cutting a set of pairs into sets of bounded size

Corollary 15 ("splitting W into sets of at most n²/√D query pairs") and the proof of Theorem 17
("cut it into chunks of at most n²/√D query pairs") cut a set of pairs into smaller sets.  The paper
does not say how; we cut along the row-major order of the pairs. -/

/-- The position of the pair `(a, b)` in the row-major order of `A × B`. -/
def pairIndex {n : ℕ} (q : Fin n × Fin n) : ℕ := q.1.val * n + q.2.val










/-- The number `⌈|S| / cap⌉` of nonempty chunks of `S` (for `cap ≥ 1`). -/
noncomputable def numChunks {n : ℕ} (S : Finset (Fin n × Fin n)) (cap : ℕ) : ℕ :=
  ⌈(S.card : ℝ) / (cap : ℝ)⌉₊

/-- The largest number of query pairs that is "at most n²/√D" (Corollary 15 and Theorem 17;
Theorem 5 has "at most N²/√D"): `⌊n²/√D⌋`. -/
noncomputable def queryCap (n D : ℕ) : ℕ := ⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊

/-! ### 3.2 A deterministic reduction from Exact Triangle to Lop-AE-SparseTri -/

/-- Section 3.2: "An instance of Exact Triangle [...] consists of a complete tripartite graph on
vertex parts A, B, C of n vertices each, and an integer weight w(e) on every edge".  The three
fields are the weights `w(a,b)`, `w(b,c)` and `w(a,c)`.  The type `R` of the weights is `ℤ` in
Section 3; Section 5 also uses real weights.  The bound on the weights is a separate predicate
(`WeightsBoundedBy`, `WeightsPolyBounded`). -/
structure TriangleInstance (R : Type) (n : ℕ) where
  /-- `wAB a b` is the weight `w(a,b)` of the edge between `a ∈ A` and `b ∈ B`. -/
  wAB : Fin n → Fin n → R
  /-- `wBC b c` is the weight `w(b,c)` of the edge between `b ∈ B` and `c ∈ C`. -/
  wBC : Fin n → Fin n → R
  /-- `wAC a c` is the weight `w(a,c)` of the edge between `a ∈ A` and `c ∈ C`. -/
  wAC : Fin n → Fin n → R

namespace TriangleInstance

/-- Section 3.2: "Let S(a,b,c) := w(a,b) + w(b,c) + w(a,c)." -/
def S {R : Type} [Add R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) : R :=
  T.wAB a b + T.wBC b c + T.wAC a c

/-- Section 3.2: "A zero triangle is a triangle (a,b,c) ∈ A × B × C with S(a,b,c) = 0". -/
def IsZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) (a b c : Fin n) :
    Prop :=
  T.S a b c = 0

/-- Section 3.2: "the task is to decide whether one exists". -/
def HasZeroTriangle {R : Type} [Add R] [Zero R] {n : ℕ} (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.IsZeroTriangle a b c

/-- Every weight has absolute value at most `U`. -/
def WeightsBoundedBy {R : Type} [Lattice R] [AddGroup R] {n : ℕ} (T : TriangleInstance R n)
    (U : R) : Prop :=
  (∀ a b, |T.wAB a b| ≤ U) ∧ (∀ b c, |T.wBC b c| ≤ U) ∧ (∀ a c, |T.wAC a c| ≤ U)

/-- Section 3.2: "with |w(e)| ≤ n^ν for some constant ν ≥ 1".  `κ`, the paper's ν, is a real
number. -/
def WeightsPolyBounded {n : ℕ} (T : TriangleInstance ℤ n) (κ : ℝ) : Prop :=
  (∀ a b, ((|T.wAB a b| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ) ∧ (∀ b c, ((|T.wBC b c| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ) ∧
    (∀ a c, ((|T.wAC a c| : ℤ) : ℝ) ≤ (n : ℝ) ^ κ)








end TriangleInstance








/-! #### Hashing modulo a prime (proof of Theorem 17) -/

open Classical in
/-- Proof of Theorem 17: the primes "p ∈ [√D/2, √D)", called "the primes in the range". -/
noncomputable def primesInRange (D : ℕ) : Finset ℕ :=
  (Finset.range D).filter fun p => p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D

namespace TriangleInstance

/-- Proof of Theorem 17: "For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod
p)."  This is that count. -/
def countZeroMod {n : ℕ} (T : TriangleInstance ℤ n) (p : ℕ) : ℕ :=
  (Finset.univ.filter fun ((a, b, c) : Fin n × Fin n × Fin n) => T.S a b c ≡ 0 [ZMOD (p : ℤ)]).card

/-- Proof of Theorem 17: "We select the prime with the smallest count [...] and call it p."  The
paper does not say how ties are broken, so this is a predicate: `p` is a prime in the range whose
count is smallest. -/
def IsSelectedPrime {n : ℕ} (T : TriangleInstance ℤ n) (D p : ℕ) : Prop :=
  p ∈ primesInRange D ∧ ∀ q ∈ primesInRange D, T.countZeroMod p ≤ T.countZeroMod q

end TriangleInstance

/-! #### The instances (proof of Theorem 17) -/

/-- Proof of Theorem 17: "let s := ⌊√D⌋". -/
noncomputable def sOf (D : ℕ) : ℕ := ⌊Real.sqrt D⌋₊

/-- Proof of Theorem 17: the bound "⌈s/g⌉" on the number of vertices of a piece. -/
noncomputable def pieceSize (D g : ℕ) : ℕ := ⌈(sOf D : ℝ) / (g : ℝ)⌉₊







/-- Proof of Theorem 17: the number `h` of pieces, `⌈n / ⌈s/g⌉⌉` for the blocks of `piece`
(meaningful when `⌈s/g⌉ ≥ 1`). -/
noncomputable def numPieces (n D g : ℕ) : ℕ := ⌈(n : ℝ) / (pieceSize D g : ℝ)⌉₊

/-- The index of an instance built by the reduction of Theorem 17: a residue `ϱ ∈ ℤ_p`, the number
`j` of a chunk of `W_ϱ`, and the number `k` of a piece of `C`. -/
abbrev InstanceIndex (p : ℕ) : Type := Fin p × ℕ × ℕ

namespace TriangleInstance

/-- Proof of Theorem 17: "For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod
p)". -/
def residueClass {n : ℕ} (T : TriangleInstance ℤ n) (p : ℕ) (ϱ : Fin p) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun q : Fin n × Fin n => T.wAB q.1 q.2 ≡ ((ϱ : ℕ) : ℤ) [ZMOD (p : ℤ)]



















/-- Proof of Theorem 17: "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k" there is an instance; these
are the indices of all the instances. This set depends only on the Exact Triangle instance and on
`D`, `g`, `p`, not on any answer of the oracle. -/
noncomputable def instanceIndices {n : ℕ} (T : TriangleInstance ℤ n) (D g p : ℕ) :
    Finset (InstanceIndex p) :=
  Finset.univ.biUnion fun ϱ : Fin p =>
    ((Finset.range (numChunks (T.residueClass p ϱ) (queryCap n D))) ×ˢ
      (Finset.range (numPieces n D g))).image fun jk => (ϱ, jk)

/-! #### Witnesses (proof of Theorem 17) -/



































end TriangleInstance

/-! ### 3.4 3SUM and APSP reduce to Exact Triangle: the problems -/

/-- **3SUM**, Section 1: "Given n numbers, decide whether three of them sum to 0."  This is the
question that the problem `EndStatement.ThreeSum` asks.

NOTE.  We read "three of them" as three numbers at three different positions of the input. -/
abbrev ThreeSum {n : ℕ} (x : Fin n → ℤ) : Prop := EndStatement.ThreeSum.yes x

/-- **Convolution-3SUM**, Section 1.2: "do x₀, …, x_{n−1} satisfy x_i + x_j = x_{i+j} for some
i, j?" -/
def Convolution3SUM {R : Type} [Add R] {N : ℕ} (x : Fin N → R) : Prop :=
  ∃ (i j : Fin N) (h : i.val + j.val < N), x i + x j = x ⟨i.val + j.val, h⟩

/-- **Negative Triangle**, Section 1.2: "asks whether an edge-weighted graph has a triangle of
negative total weight".  The instances here are those of Exact Triangle. -/
def TriangleInstance.HasNegativeTriangle {R : Type} [Add R] [Zero R] [LT R] {n : ℕ}
    (T : TriangleInstance R n) : Prop :=
  ∃ a b c : Fin n, T.S a b c < 0








/-- The (min,+)-product as a function, for matrices whose entries may be `+∞` (`⊤`): the minimum
over the empty set, and any sum with `+∞`, is `+∞`. -/
def minPlus {R : Type} [Add R] [LinearOrder R] {n m l : ℕ} (A : Matrix (Fin n) (Fin m) (WithTop R))
    (B : Matrix (Fin m) (Fin l) (WithTop R)) : Matrix (Fin n) (Fin l) (WithTop R) :=
  Matrix.of fun i j => Finset.univ.inf fun k => A i k + B k j

/-! A directed graph on the vertices `Fin n` with edge weights in `R` is a function
`w : Fin n → Fin n → WithTop R`: `w i j` is the weight of the edge from `i` to `j`, and `⊤` (that
is, `+∞`) if there is no such edge.  A walk that starts at `i` is given by the list of the vertices
it visits after `i`. -/

/-- The vertex at which the walk that starts at `i` and then visits `rest` ends. -/
def walkEnd {n : ℕ} : Fin n → List (Fin n) → Fin n
  | i, [] => i
  | _, j :: rest => walkEnd j rest

/-- The total weight of the walk that starts at `i` and then visits `rest`; it is `⊤` if one of its
edges is missing, and the empty walk has weight 0. -/
def walkWeight {R : Type} [Add R] [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Fin n → List (Fin n) → WithTop R
  | _, [] => 0
  | i, j :: rest => w i j + walkWeight w j rest

/-- Section 1 and Theorems 21 and 22: "no negative cycles".  Stated for closed walks, which is the
same thing: a closed walk decomposes into cycles. -/
def NoNegativeCycle {R : Type} [Add R] [Zero R] [LE R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Prop :=
  ∀ (i : Fin n) (rest : List (Fin n)), walkEnd i rest = i → 0 ≤ walkWeight w i rest

/-- **APSP**, Section 1: "compute the shortest-path distance between every pair of vertices".  `d i
j` is the least weight of a walk from `i` to `j`, and `⊤` if `j` cannot be reached from `i`. -/
def IsDistanceMatrix {R : Type} [Add R] [Zero R] [Preorder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (d : Fin n → Fin n → WithTop R) : Prop :=
  ∀ i j, IsLeast {x | ∃ rest : List (Fin n), walkEnd i rest = j ∧ walkWeight w i rest = x} (d i j)

/-- Every edge weight of the directed graph has absolute value at most `U`. -/
def EdgeWeightsBoundedBy {R : Type} [Lattice R] [AddGroup R] {n : ℕ} (w : Fin n → Fin n → WithTop R)
    (U : R) : Prop :=
  ∀ (i j : Fin n) (x : R), w i j = (x : WithTop R) → |x| ≤ U

/-- The weight matrix of the graph, for the repeated squaring behind Theorem 21(b).  Its diagonal
entries are 0, without which repeated squaring would compute walks of exactly `2^t` edges. -/
def weightMatrix {R : Type} [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Matrix (Fin n) (Fin n) (WithTop R) :=
  Matrix.of fun i j => if i = j then 0 else w i j

/-- Repeated squaring, for Theorem 21(b): `minPlusSquares w t` is the weight matrix after `t`
squarings in the (min,+)-product. -/
def minPlusSquares {R : Type} [Add R] [Zero R] [LinearOrder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) : ℕ → Matrix (Fin n) (Fin n) (WithTop R)
  | 0 => weightMatrix w
  | t + 1 => minPlus (minPlusSquares w t) (minPlusSquares w t)

/-! #### The shape of the two reductions of [VW13] that Theorem 21 cites -/

/-- The instance on the same vertices obtained from `T` by applying one function to every weight
`w(a,b)`, one to every `w(b,c)` and one to every `w(a,c)`. -/
def TriangleInstance.mapWeights {n : ℕ} (T : TriangleInstance ℤ n) :
    (ℤ → ℤ) × (ℤ → ℤ) × (ℤ → ℤ) → TriangleInstance ℤ n
  | (fAB, fBC, fAC) =>
    { wAB := fun a b => fAB (T.wAB a b)
      wBC := fun b c => fBC (T.wBC b c)
      wAC := fun a c => fAC (T.wAC a c) }


























/-! #### Asymptotic notation of Section 3 -/









/-- `f(n) = O(n^a (log n)^{O(1)})`. -/
def IsPowPolylog (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ e : ℕ, Asymptotics.IsBigO Filter.atTop f fun n : ℕ => (n : ℝ) ^ a * Real.log n ^ e

/-- `f(n) = O(n^a)`. -/
def IsBigOPow (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop f fun n : ℕ => (n : ℝ) ^ a

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

/-- The number of ordered pairs of distinct elements of `S` that are congruent modulo `M`. -/
def coll (S : Finset ℤ) (M : ℕ) : ℕ := #{p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2}







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

/-- Section 4: "For a leaf τ of a tile with input arrays a and b, we call Φ_τ(a) Ψ_τ(b) the product
at τ." -/
def productAt {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (τ : Leaf L) : ℤ := Phi τ a * Psi τ b

/-! ### 4.2 Boxes -/

/-- Section 4.2: the symbols of a cube, "each of which is one of the ten terms of Schönhage's
identity or a star ∗". -/
inductive CubeSymbol : Type
  | term (lam : Term)
  | star
  deriving DecidableEq, Fintype

/-- Section 4.2: "A cube is a string π = π₁ ⋯ π_L of L symbols, each of which is one of the ten
terms of Schönhage's identity or a star ∗." -/
abbrev Cube (L : ℕ) : Type := Fin L → CubeSymbol

/-- Section 4.2: "Its leaves are the leaves obtained by replacing each star by any of the ten
terms". So `τ` is a leaf of `π` if at every level `π` has a star or has the term of `τ`. -/
def Cube.HasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) : Prop :=
  ∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ)

instance Cube.instDecidableHasLeaf {L : ℕ} (π : Cube L) (τ : Leaf L) :
    Decidable (Cube.HasLeaf π τ) :=
  inferInstanceAs (Decidable (∀ ℓ, π ℓ = CubeSymbol.star ∨ π ℓ = CubeSymbol.term (τ ℓ)))

/-- Section 4.2: the set of the leaves of a cube. -/
def Cube.leaves {L : ℕ} (π : Cube L) : Finset (Leaf L) := univ.filter fun τ => Cube.HasLeaf π τ

/-- The set of levels at which a cube has a star. -/
def Cube.starLevels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = CubeSymbol.star

/-- The set of levels at which a cube has the symbol `P₀`. -/
def Cube.P0Levels {L : ℕ} (π : Cube L) : Finset (Fin L) :=
  univ.filter fun ℓ => π ℓ = CubeSymbol.term Term.P0

/-- Section 4.2: "The value of a cube π is the sum of the products at its leaves,
val(π) := ∑_{τ a leaf of π} Φ_τ(a) Ψ_τ(b)." -/
def Cube.val {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (π : Cube L) : ℤ :=
  ∑ τ ∈ Cube.leaves π, productAt a b τ

/-- Section 4.2: "A box is a cube π = π₁ ⋯ π_L such that (i) at most m - t of its symbols are P₀ or
stars, and (ii) every star is at a lower level than every P₀." -/
def IsBox {L : ℕ} (m t : ℕ) (π : Cube L) : Prop :=
  (Cube.starLevels π).card + (Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ'

instance IsBox.instDecidable {L : ℕ} (m t : ℕ) (π : Cube L) : Decidable (IsBox m t π) :=
  inferInstanceAs (Decidable ((Cube.starLevels π).card + (Cube.P0Levels π).card ≤ m - t ∧
    ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ'))

/-- The `k` lowest levels of `S` (Section 4.2 and Lemma 27: "the m - t - |Z| lowest levels of Q ∖
Z"): the levels of `S` with fewer than `k` levels of `S` below them. (All of `S` if `S` has at most
`k` levels.) -/
def lowest {L : ℕ} (k : ℕ) (S : Finset (Fin L)) : Finset (Fin L) :=
  S.filter fun ℓ => (S.filter fun ℓ' => ℓ' < ℓ).card < k

/-- Proof of Lemma 29: "the leaf we get by replacing its stars with P₀". -/
def Cube.starsToP0 {L : ℕ} (π : Cube L) : Leaf L :=
  fun ℓ =>
    match π ℓ with
    | .term lam => lam
    | .star => Term.P0

/-- Section 4.2: "V := Z ∪ {the m - t - |Z| lowest levels of Q ∖ Z} (Z padded from the bottom)". -/
def Vof {L : ℕ} (m t : ℕ) (Q Z : Finset (Fin L)) : Finset (Fin L) :=
  Z ∪ lowest (m - t - Z.card) (Q \ Z)

/-- Section 4.2: "F_V := {ℓ ∈ Q : ℓ < min(Q ∖ V)} (the levels that we have not reached)", and "We
define F_V by the same formula for every V ⊆ Q, with F_V := Q if V = Q." The condition "ℓ < min(Q ∖
V)" is written as "ℓ is below every level of Q ∖ V", which also gives the convention `F_V = Q` when
`Q ∖ V` is empty. (That this agrees with the paper's formula in both cases is the library's lemma
`FV_eq`.) -/
def FV {L : ℕ} (Q V : Finset (Fin L)) : Finset (Fin L) := Q.filter fun ℓ => ∀ ℓ' ∈ Q \ V, ℓ < ℓ'

/-- Section 4.2: "For V ⊆ Q with |V| = m - t, let 𝓑_V be the set of the 9^t cubes π with π_ℓ = ∗ if
ℓ ∈ F_V, P₀ if ℓ ∈ V ∖ F_V, one of the nine terms P_ij if ℓ ∈ Q ∖ V, the term P_ij with w_ℓ = z_ij
if ℓ ∉ Q", where `Q` is the inner set of the output string w, here `η`. The term of the last case is
the term of the private leaf of `η` (so the caption of Figure 10: "at every other level, they have
the term of the private leaf of w"). The boxes in these sets are "the boxes of w". -/
def BV {L : ℕ} (η : OutStr L) (V : Finset (Fin L)) : Finset (Cube L) :=
  univ.filter fun π => ∀ ℓ,
    (ℓ ∈ FV (innerSetO η) V → π ℓ = CubeSymbol.star) ∧
    (ℓ ∈ V \ FV (innerSetO η) V → π ℓ = CubeSymbol.term Term.P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, π ℓ = CubeSymbol.term (Term.P i j)) ∧
    (ℓ ∉ innerSetO η → π ℓ = CubeSymbol.term (privateLeaf η ℓ))

/-- Lemma 28: the index set of the union and of the sum, "all V ⊆ Q with |V| = m - t". -/
def Vsets {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Finset (Fin L)) :=
  (innerSetO η).powersetCard (m - t)

/-- Lemma 28: the leaves "τ contributing to w of order < t". -/
def lowLeaves {L : ℕ} (m t : ℕ) (η : OutStr L) : Finset (Leaf L) :=
  univ.filter fun τ => Leaf.Contributes τ η ∧ order m τ < (t : ℤ)

/-- The right-hand side of the equation of Lemma 28: "∑_{τ contributing to w, of order < t} Φ_τ(a)
Ψ_τ(b) + ∑_{V ⊆ Q, |V| = m - t} ∑_{π ∈ 𝓑_V} val(π)". It is what a query computes in its steps (2)
and (3) (Section 4.3): "Add up the products at the leaves of order below t contributing to w", "Add
to this the values of the α_t boxes of w". -/
def querySum {L : ℕ} (m t : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (η : OutStr L) : ℤ :=
  ∑ τ ∈ lowLeaves m t η, productAt a b τ + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, Cube.val a b π

/-! ### 4.3 The data structure, in terms of the parameters -/

/-- The set of all boxes (of a tile), for the parameters `L`, `m`, `t`. -/
def boxes (L m t : ℕ) : Finset (Cube L) := univ.filter fun π => IsBox m t π

/-- "the boxes with e stars" (proof of Lemma 29, which computes "the values of the boxes in
increasing order of their number of stars"). -/
def boxesWithStars (L m t e : ℕ) : Finset (Cube L) :=
  (boxes L m t).filter fun π => (Cube.starLevels π).card = e

/-- Proof of Lemma 29: "the ten strings π[ℓ ← λ] obtained by replacing that star by a term λ". -/
def Cube.replace {L : ℕ} (π : Cube L) (ℓ : Fin L) (lam : Term) : Cube L :=
  Function.update π ℓ (CubeSymbol.term lam)

/-- The dynamic program of Lemma 29 (proof, "The values"), which computes the value of a box with
`e` stars from the two encodings of the tile, `encA τ = Φ_τ(a)` and `encB τ = Ψ_τ(b)`: "The boxes
without stars are the leaves with at most m - t symbols P₀, and the value of each of them is the
product of its two numbers in the encodings. For a box π with e ≥ 1 stars, let ℓ be the highest
level at which π has a star. […] Hence we compute val(π) = ∑_λ val(π[ℓ ← λ]) with ten lookups in the
trie". A cube without stars is the leaf `Cube.starsToP0 π`. (The last case, a cube without stars
when `e ≥ 1`, does not occur for a box with `e` stars.) `dpValue` is the recurrence of this dynamic
program, not a program with a trie: where the paper looks a value up, `dpValue` computes it
again. -/
def dpValue {L : ℕ} (encA encB : Leaf L → ℤ) : ℕ → Cube L → ℤ
  | 0, π => encA (Cube.starsToP0 π) * encB (Cube.starsToP0 π)
  | e + 1, π =>
    if h : (Cube.starLevels π).Nonempty then
      ∑ lam : Term, dpValue encA encB e (Cube.replace π ((Cube.starLevels π).max' h) lam)
    else 0

/-- The decay rate of the `β_d` (Table 1, and Section 4.3): "ρ := 9m / (L - m + 1)". -/
noncomputable def rho (L m : ℕ) : ℝ := 9 * (m : ℝ) / ((L : ℝ) - (m : ℝ) + 1)

/-- The expression inside the `O(·)` of (8) (preprocessing time and space of Theorem 30):
"L m ρ^t/(1 - ρ) N² + N · 10^L / (√K N₀)". -/
noncomputable def cost8 (L m t N : ℕ) : ℝ :=
  (L : ℝ) * (m : ℝ) * (rho L m ^ t / (1 - rho L m)) * (N : ℝ) ^ 2
    + (N : ℝ) * (10 : ℝ) ^ L / (Real.sqrt (K L m : ℝ) * (N0 L m : ℝ))

/-- The expression inside the `O(·)` of the query time of Theorem 30:
"L ∑_{d=0}^{t} α_d". -/
noncomputable def costQuery (L m t : ℕ) : ℝ := (L : ℝ) * ∑ d ∈ range (t + 1), (alpha m d : ℝ)







/-! ### 4.4 Choosing the parameters -/

/-- Proof of Corollary 26: "pad the inner dimension to 4^m < 4D with zero columns of X". The padded
matrix has `D'` columns. This is a padding if `D₀ ≤ D'`; for `D' < D₀` the function drops the last
columns. -/
def padInnerCols {N D₀ : ℕ} (D' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) : Matrix (Fin N) (Fin D') ℤ :=
  fun I k => if h : (k : ℕ) < D₀ then X I ⟨k, h⟩ else 0

/-- Proof of Corollary 26: "and zero rows of Y".  The padded matrix has `D'` rows.  This is a
padding if `D₀ ≤ D'`; for `D' < D₀` the function drops the last rows. -/
def padInnerRows {N D₀ : ℕ} (D' : ℕ) (Y : Matrix (Fin D₀) (Fin N) ℤ) : Matrix (Fin D') (Fin N) ℤ :=
  fun k J => if h : (k : ℕ) < D₀ then Y ⟨k, h⟩ J else 0

/-- Section 4.4: "let H(x) := -x ln x - (1 - x) ln(1 - x) be the entropy function (with natural
logarithms)". (Lean's `Real.log 0 = 0` gives `H(0) = H(1) = 0`, the usual convention.) -/
noncomputable def entropy (θ : ℝ) : ℝ := -θ * Real.log θ - (1 - θ) * Real.log (1 - θ)













/-- Corollary 31: "ρ_c := 9/(c - 1)". -/
noncomputable def rhoC (c : ℝ) : ℝ := 9 / (c - 1)

/-- Corollary 31: "γ := θ ln(1/ρ_c) / ln 4". -/
noncomputable def gammaOf (c θ : ℝ) : ℝ := θ * Real.log (1 / rhoC c) / Real.log 4

/-- Corollary 31: "q := (H(θ) + θ ln 9) / ln 4". -/
noncomputable def qOf (θ : ℝ) : ℝ := (entropy θ + θ * Real.log 9) / Real.log 4





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

/-- The word size `W` is admissible against the slope `b` for an input with the parameters `params`
(its sizes): `W` is at least `b · (⌊log₂ p₁⌋ + ⌊log₂ p₂⌋ + … + 1)`.  If every parameter is at most a
fixed power of the size `n`, the smallest admissible word size is a constant times `log n`: "O(log
n)-bit words".  A statement fixes only the slope `b`, together with the program, and the program has
to work, within the same bound on the number of steps, at every admissible word size. -/
def Admissible (b : Nat) (params : List Nat) (W : Nat) : Prop :=
  b * ((params.map Nat.log2).sum + 1) ≤ W

/-- The output of a function problem: the cells right after the input, read as signed words.
`output c len i` is the number in the `i`-th cell of the memory `c` after an input of `len`
cells. -/
def output {W : Nat} (c : Int → BitVec W) (len : Nat) (i : Nat) : Int :=
  (c ((len : Int) + (i : Int))).toInt

/-! #### Problems, and solving a problem within a time bound -/

/-- A computational problem on the word RAM. -/
structure Problem where
  /-- The instances. -/
  Inst : Type
  /-- The parameters of an instance on which the word size depends: its sizes. -/
  params : Inst → List ℕ
  /-- The input: the numbers written into the cells 0, 1, 2, … -/
  input : Inst → List ℤ
  /-- `IsAnswer x verdict out`: the verdict, and the numbers `out 0, out 1, …` in the cells right
  after the input, are a correct answer to the instance `x`. -/
  IsAnswer : Inst → Bool → (ℕ → ℤ) → Prop

/-- **Solving a problem within a time bound.**  The program `P` with slope `b` solves the problem on
the instances in `dom` within time `T`: on every such instance `x` and at every admissible word size
`bits`, the run from the first instruction on the starting memory (input in the cells 0, 1, 2, …,
zeros elsewhere) gives a verdict after at most `T x` steps, and the verdict and the output are a
correct answer. -/
def Solves (prob : Problem) (P : List Instr) (b : ℕ) (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) :
    Prop :=
  ∀ x : prob.Inst, dom x → ∀ bits : ℕ, Admissible b (prob.params x) bits →
    ∃ (t : ℕ) (verdict : Bool) (c : ℤ → BitVec bits), (t : ℝ) ≤ T x ∧
      exec P t 0 (loadWords bits (prob.input x)) = some (verdict, c) ∧
      prob.IsAnswer x verdict (output c (prob.input x).length)

/-! #### Time bounds in one size `n`, for the problems of `EndStatement.lean` -/

/-- The program `P` with slope `b` solves the problem `Q` within `T(n)` steps when all numbers are
integers of absolute value at most `n^κ`.  This is what `EndStatement.Problem.SolvedInTime` asks of
the runs of `P`, for a real bound `T`: on every such instance, of any size `n`, and at every word
size of at least `b (⌊log₂ n⌋ + 1)` bits, `P` halts within `T(n)` steps with the right verdict and
output (`EndStatement.Problem.SolvedBy`).

NOTE.  As in `EndStatement.Problem.SolvedInTime`, the bound speaks of every number of the input
list.  Where the input contains an adjacency matrix, its entries 1 count too; `n^κ` is at least 1 as
soon as there is a vertex. -/
def SolvesWithin (Q : EndStatement.Problem) (κ : ℕ) (P : List Instr) (b : ℕ) (T : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
    ∃ t : ℕ, (t : ℝ) ≤ T n ∧ Q.SolvedBy x P W t

/-- The problem `Q`, a value of `EndStatement.Problem`, is solved by a deterministic algorithm in
`O(n^a (log n)^e)` time when all numbers are integers of absolute value at most `n^κ`: there are a
program, a slope and a constant `C` such that the program solves `Q` within `C (n^a (log n)^e + 1)`
steps.  (For `a ≥ 0` the `+ 1` matters only at `n ≤ 1`, where `n^a (log n)^e` may be 0.) -/
def SolvedInTimeAt (Q : EndStatement.Problem) (κ : ℕ) (a : ℝ) (e : ℕ) : Prop :=
  ∃ (P : List Instr) (b : ℕ) (C : ℝ),
    SolvesWithin Q κ P b fun n => C * ((n : ℝ) ^ a * Real.log n ^ e + 1)

/-- The same for every constant `κ`: "all numbers in the input are integers of absolute value
n^{O(1)}" (Theorem 2).  The program, the slope and the constant may depend on `κ`.

NOTE.  `κ` is the paper's ν.  Where the paper has ν ≥ 1 (Theorem 19, Corollary 39), `κ = 0` is
included here. -/
def SolvedInTime (Q : EndStatement.Problem) (a : ℝ) (e : ℕ) : Prop :=
  ∀ κ : ℕ, SolvedInTimeAt Q κ a e

/-- The same in `O(n^a (log n)^{O(1)})` time, which Theorem 22 writes Õ(n^a).

NOTE.  The exponent of the logarithm may depend on `κ` too: this is the weaker reading of the
Õ of Theorem 22. -/
def SolvedInPolylogTime (Q : EndStatement.Problem) (a : ℝ) : Prop :=
  ∀ κ : ℕ, ∃ e : ℕ, SolvedInTimeAt Q κ a e










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

/-- A matrix written row by row. -/
def rowMajor {n m : ℕ} (A : Fin n → Fin m → ℤ) : List ℤ :=
  (List.finRange n).flatMap fun i => (List.finRange m).map fun j => A i j




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


