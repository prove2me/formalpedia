-- Prove2me | Definitions.Def_PfaffianRecognition_CoRP_ListLinAlg
-- name    : PfaffianRecognition_CoRP_ListLinAlg
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T21:14:46.562369+00:00
-- url     : https://prove2.me/theorems/f2cd0882-6fdc-4bbd-8678-5eddbf7d7e45
-- title:
--   List Gaussian elimination: determinants and $\mathbb F_2$ systems
-- statement:
--   Exact linear algebra on matrices stored as lists of rows, written with plain list operations so that it can be compiled to polynomial-time Boolean-stack machines.
--
--   1. A record $F$ of field operations (zero, one, addition, negation, multiplication, inversion, zero test) on a representation type, and the standard record of a field $K$.
--   2. $\mathrm{detAlg}_F(M)$: Gaussian elimination on a square matrix $M$. At each step the first row whose leading entry $p$ is nonzero is the pivot (index $k$); every other row $r$ is replaced by $r_{\ge 1}-r_0\,p^{-1}\,\mathrm{piv}_{\ge1}$, the pivot row is removed, and the accumulated product is multiplied by $(-1)^k p$. If the first column vanishes, the result is $0$. For the standard operations of a field this is the determinant
--   $$\mathrm{detAlg}(M)=\det M .$$
--   3. $\mathrm{solveF2}(n,\mathcal E)$: Gaussian elimination over $\mathbb F_2$ for equations $\sum_i c_i x_i=b$ in $n$ unknowns. A forward pass over the columns records pivots; the system is reported inconsistent exactly when a reduced equation $0=1$ remains; otherwise back substitution returns a solution of length $n$.
--
--   These routines evaluate the determinant formula of Lemma 2.3 (§2.2, p. 6) over a finite field and maintain the linear system of orientation constraints in the formalized recognition algorithm.
--
--   **Formalization Note** Absent pivots of the $\mathbb F_2$ elimination are recorded as the empty equation, so that the data stay within lists, pairs, Booleans and natural numbers.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf, §2.2 Lemma 2.3 (p. 6) and §3.1 Theorem 3.2 (p. 7): determinant evaluations; standard Gaussian elimination

import Mathlib

/-!
List-based exact linear algebra used by the randomized Pfaffian recognition algorithm.

* `FieldOps α`: the field operations on a concrete representation type `α`.
* `detAlg F M`: Gaussian elimination with first-nonzero pivoting on a square matrix given as a list
  of rows; it returns the determinant (the pivot sign `(-1)^k` is tracked explicitly).
* `listSum F xs`: left fold of `F.add`.
* `solveF2 n eqs`: Gaussian elimination over `𝔽₂` for a system of linear equations in `n`
  unknowns, each equation a coefficient list with a right-hand side; `none` certifies
  inconsistency, `some x` is a solution.

Everything is written with plain list operations (`foldl`, `map`, `findIdx`, `getD`, `eraseIdx`)
so that the routines can be compiled to Boolean-stack machines.
-/

namespace PfaffianRecognition.CoRP

/-- The field operations on a representation type. -/
structure FieldOps (α : Type) where
  zero : α
  one : α
  add : α → α → α
  neg : α → α
  mul : α → α → α
  inv : α → α
  isZero : α → Bool

/-- The standard operations of a field with decidable equality. -/
def stdOps (K : Type) [Field K] [DecidableEq K] : FieldOps K where
  zero := 0
  one := 1
  add := (· + ·)
  neg := fun a => -a
  mul := (· * ·)
  inv := fun a => a⁻¹
  isZero := fun a => decide (a = 0)

/-- Sum of a list of field elements (left fold, starting at `zero`). -/
def listSum {α : Type} (F : FieldOps α) (xs : List α) : α :=
  xs.foldl F.add F.zero

/-- Index of the first row whose leading entry is nonzero (`rows.length` if there is none). -/
def pivotIdx {α : Type} (F : FieldOps α) (rows : List (List α)) : ℕ :=
  rows.findIdx (fun r => !F.isZero (r.headD F.zero))

/-- Eliminate the first column of `row` using the pivot row `piv` with inverse pivot `pinv`,
and drop that column: `row.tail - (row₀ · pinv) · piv.tail`. -/
def elimRow {α : Type} (F : FieldOps α) (pinv : α) (piv row : List α) : List α :=
  (row.tail.zip piv.tail).map
    (fun ab => F.add ab.1 (F.neg (F.mul (F.mul (row.headD F.zero) pinv) ab.2)))

/-- One elimination step on the state `(rows, acc)`. With no rows the state is unchanged; with no
pivot in the first column the determinant is zero, recorded as `([], zero)`. Otherwise the pivot row
`k` is removed, the other rows are reduced, and `acc` is multiplied by `(-1)^k · pivot`. -/
def elimStep {α : Type} (F : FieldOps α) (st : List (List α) × α) : List (List α) × α :=
  if st.1.isEmpty then st
  else if pivotIdx F st.1 < st.1.length then
    ((st.1.eraseIdx (pivotIdx F st.1)).map
        (elimRow F (F.inv ((st.1.getD (pivotIdx F st.1) []).headD F.zero))
          (st.1.getD (pivotIdx F st.1) [])),
      F.mul st.2
        (if pivotIdx F st.1 % 2 = 0 then (st.1.getD (pivotIdx F st.1) []).headD F.zero
          else F.neg ((st.1.getD (pivotIdx F st.1) []).headD F.zero)))
  else ([], F.zero)

/-- Determinant of a square matrix given as a list of rows, by Gaussian elimination
(`rows.length` elimination steps starting from accumulator `one`). -/
def detAlg {α : Type} (F : FieldOps α) (M : List (List α)) : α :=
  ((List.range M.length).foldl (fun st _ => elimStep F st) (M, F.one)).2

/-! ### Linear systems over `𝔽₂` -/

/-- An equation over `𝔽₂`: coefficient list and right-hand side. -/
abbrev Eqn := List Bool × Bool

/-- `x` satisfies the equation: the `𝔽₂` inner product of coefficients and `x` equals the
right-hand side (coefficients beyond `x` are paired with `false`). -/
def satisfiesEqn (x : List Bool) (e : Eqn) : Bool :=
  ((((List.range e.1.length).filter (fun i => e.1.getD i false && x.getD i false)).length % 2
    == 1) == e.2)

/-- Coordinatewise sum (xor) of two equations, padding with `false`. -/
def addEqn (e f : Eqn) : Eqn :=
  ((List.range (max e.1.length f.1.length)).map (fun i => xor (e.1.getD i false) (f.1.getD i false)),
    xor e.2 f.2)

/-- Forward elimination step for column `j`: state `(rest, pivots)`. If some remaining equation has
coefficient `1` at column `j`, the first such one becomes the pivot of column `j` and is added to every
other remaining equation having coefficient `1` at column `j`; otherwise the empty equation
`([], false)` is recorded as the (absent) pivot of column `j`. -/
def f2Forward (st : List Eqn × List Eqn) (j : ℕ) : List Eqn × List Eqn :=
  if st.1.findIdx (fun e => e.1.getD j false) < st.1.length then
    ((st.1.eraseIdx (st.1.findIdx (fun e => e.1.getD j false))).map
        (fun e => if e.1.getD j false then
          addEqn e (st.1.getD (st.1.findIdx (fun e => e.1.getD j false)) ([], false)) else e),
      st.2 ++ [st.1.getD (st.1.findIdx (fun e => e.1.getD j false)) ([], false)])
  else (st.1, st.2 ++ [([], false)])

/-- Back substitution step for column `j` (columns are processed from `n - 1` down to `0`): with
pivot equation `p` for column `j`, set `x_j := rhs(p) + Σ_{l ≠ j} p_l x_l`. For an absent pivot
`p = ([], false)` this sets `x_j := false`. The assignment is a full-length list updated at `j`. -/
def f2Back (pivots : List Eqn) (x : List Bool) (j : ℕ) : List Bool :=
  x.set j
    (xor (pivots.getD j ([], false)).2
      (((List.range (pivots.getD j ([], false)).1.length).filter
        (fun l => l != j && (pivots.getD j ([], false)).1.getD l false && x.getD l false)).length
          % 2 == 1))

/-- Solve a system of `𝔽₂` linear equations in `n` unknowns by Gaussian elimination. The first
component is `false` if the reduced system contains an equation `0 = 1` (inconsistency); otherwise it
is `true` and the second component is a solution of length `n`. -/
def solveF2 (n : ℕ) (eqs : List Eqn) : Bool × List Bool :=
  ((((List.range n).foldl f2Forward (eqs, [])).1.all (fun e => !e.2)),
    (List.range n).reverse.foldl (f2Back ((List.range n).foldl f2Forward (eqs, [])).2)
      (List.replicate n false))

end PfaffianRecognition.CoRP


