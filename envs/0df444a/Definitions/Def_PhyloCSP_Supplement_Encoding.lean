-- Prove2me | Definitions.Def_PhyloCSP_Supplement_Encoding
-- name    : PhyloCSP_Supplement_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:23:14.8497+00:00
-- url     : https://prove2.me/theorems/91e32dd6-b755-42c8-9dd9-dd745e2b708d
-- title:
--   Binary codes of instances (variable count in unary) and of solution trees
-- statement:
--   Machines read and write words over $\{0,1\}$.
--
--   1. The **code of an instance** $I$ with $n$ variables is the unary code $1^n0$ of $n$, followed, for each constraint in order, by the unary code of the position of its predicate in a fixed enumeration of the (finite) language and the unary codes of the indices of its argument variables.
--   2. The **code of a solution** $T$ is its rooted-triplet table: the $n^3$ bits $[\,a\mid_T bc\,]$ for $a,b,c\in\{x_1,\dots,x_n\}$ in lexicographic order. A tree is determined by its rooted triplets.
--   3. The output word announcing $T$ is a leading $1$ followed by the code of $T$; the empty word is reserved for "no solution" or "failure".
--
--   These codes fix what "polynomial time" means in Theorems 5.2 and 6.2.
--
--   **Formalization Note** The number of variables must not be written in binary: a solution is a tree on all $n$ variables, so with $n$ in binary and few constraints even writing the output would take time exponential in the input length, and every tractability claim would fail. Since $n$ is in unary, writing the other numbers (all below $n$ or below the fixed size of the language) in unary changes the code length by at most a polynomial factor, so no polynomial-time notion changes. The enumeration of the predicates is `Fintype.equivFin`.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 1.2, p.1 (PDF p.3); polynomial time in Section 1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_PhyloCSP_Supplement_Instance

set_option autoImplicit false

namespace PhyloCSP

namespace Supplement

/-- The unary code of a natural number `m`: `m` ones followed by a zero. -/
def unary (m : ℕ) : List Bool := List.replicate m true ++ [false]

/-- **Binary encoding of instances, for machines.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 1.2, p.1 (PDF p.3), and the notion of polynomial
time in Section 1, p.2 (PDF p.4): "There is a polynomial-time algorithm that distinguishes
satisfiable from unsatisfiable instances and finds a solution satisfying all constraints whenever
the instance is satisfiable."

The code of an instance with `n` variables is the unary code of `n`, followed, for every
constraint in order, by the unary code of its predicate's position in a fixed enumeration of the
(finite) language and the unary codes of its argument variables.

**Formalization Note.** The number of variables is written in unary: a solution is a tree on all
`n` variables, so with `n` in binary and few constraints even writing the output would take time
exponential in the input length. All other numbers are also in unary; since each is below `n` or
below the (fixed) size of the language, this code is within a polynomial of the usual code with
binary variable indices (and `n` given as a list of variables), so it changes no polynomial-time
notion. The enumeration of the predicates is `Fintype.equivFin`. The code determines the instance:
the arity of each constraint is determined by its predicate index. -/
noncomputable def encInstance {L : ConstraintLanguage} (I : Instance L) : List Bool :=
  unary I.n ++ I.constraints.flatMap (fun c =>
    unary (Fintype.equivFin L.ι c.1 : ℕ) ++ (List.ofFn fun j => unary (c.2 j : ℕ)).flatten)

/-- **Binary encoding of a solution tree**: its rooted-triplet table, `n³` bits listing
`C(a; b, c)` for `a, b, c ∈ {x₁, …, xₙ}` in lexicographic order. A tree is determined by its
rooted triplet relations (p.1, PDF p.3). -/
def encTree {n : ℕ} (T : Pattern (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun a => (List.finRange n).flatMap fun b =>
    (List.finRange n).map fun c => T.1 a b c

/-- The output word announcing the solution `T`: a leading `1`, then `encTree T`. The empty word
is reserved for "no solution" (`IsPolyTractable`) and for "failure" (`RandApproxOnSat`). -/
def treeWord {n : ℕ} (T : Pattern (Fin n)) : List Bool := true :: encTree T

end Supplement

end PhyloCSP


