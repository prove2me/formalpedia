-- Prove2me | Definitions.Def_DisjointPathsDAG_SLP
-- name    : DisjointPathsDAG_SLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:38.64056+00:00
-- url     : https://prove2.me/theorems/a7835a7a-7325-4a17-9373-e9f374f914fd
-- title:
--   Division-free straight-line programs, constant tables, and matrix-product specifications
-- statement:
--   A **division-free straight-line program** over a commutative ring $R$ is a list of gates acting on registers $r_0,r_1,\dots$, all initially $0$: $r_d:=c$ for a constant $c$ of $R$, $r_d:=x_i$ for an input, and $r_d:=r_a+r_b$, $r_d:=r_a-r_b$, $r_d:=r_a\cdot r_b$; its outputs are some registers. Its **size** is the number of gates, every constant and input gate counting $1$ (the size "counts gates and input occurrences"); its **space** is one more than the largest register index it mentions.
--
--   Constants are named by an index into a **constant table** $c\mapsto\mathrm{cst}(c)$, so that a program written by a machine as natural-number words can use constants of any ring. The table of integer constants names $c\mapsto c\cdot1_R$; the mixed table names the integer $c$ at index $2c$ and $\mathrm{cst}(c)$ at index $2c+1$.
--
--   A program **computes** the polynomials obtained by running it over $R[x_0,x_1,\dots]$ with inputs $x_i$ (formal polynomials), and it can be **evaluated** at a point $x\in R^{\mathbb N}$. A program computes the product of an $a\times b$ and a $b\times c$ matrix (entries $(i,l)$ and $(l,j)$ at inputs $ib+l$ and $ab+lc+j$, entry $(i,j)$ of the product at output $ic+j$) either as an identity of formal polynomials or as a function on $R$-matrices. Programs are encoded as words (gate count, four words per gate, output count, outputs) and decoded back.
--
--   This is the circuit model of Section 2.2, used by every algebraic statement of the paper.
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2.2, p.6; Section 2.3, p.7

import Mathlib

set_option autoImplicit false

namespace DisjointPathsDAG

open MvPolynomial

/-!
# Division-free straight-line programs

Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2.2, p.6: "An arithmetic circuit, or
straight-line program, over a commutative ring R is division-free if it uses only additions,
subtractions, multiplications, inputs, and constants of R. Its size counts gates and input
occurrences. A circuit computes a formal polynomial in its inputs, and the identities of this paper are
identities of formal polynomials."

**Formalization Note** This module bundles the straight-line-program layer (gates, programs, size,
space, semantics, constant tables, matrix-product specifications, and the word encoding).
* A program is a list of gates acting on registers `ℕ → R`, all initially `0`, with overwriting
  allowed; its outputs are a list of registers. A gate is `r := const c`, `r := input i`,
  `r := r_a + r_b`, `r := r_a - r_b` or `r := r_a * r_b`.
* Constants are **indices into a constant table** `cst : ℕ → R`, which is part of the semantics, so a
  program written by a machine (as words) can name constants of any ring. Inputs are indexed by `ℕ`.
* `size` is the number of gates, every constant and input gate counting `1` ("counts gates and input
  occurrences"). `space` is one more than the largest register index the program mentions.
* `formal cst P` runs `P` over `MvPolynomial ℕ R` with input `i ↦ X i` and constants `C (cst c)`:
  the formal polynomials computed. `eval cst x P` runs `P` at the point `x : ℕ → R`.
* `natTable R` names the integer constants `c ↦ (c : R)`. `mixTable cst` names both: even index
  `2c` is the integer `c`, odd index `2c + 1` is `cst c`.
* `SLP.encode` writes a program as natural-number words (gate count, four words per gate, output
  count, outputs); `SLP.decode` reads it back and is total (malformed words decode to some program).
-/

/-- A gate of a division-free straight-line program; `dst` is the register written. -/
inductive Gate where
  | const (dst c : ℕ)
  | input (dst i : ℕ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)

/-- A straight-line program: its gates, executed in order, and its output registers. -/
structure SLP where
  code : List Gate
  outs : List ℕ

/-- The largest register index a gate mentions. -/
def Gate.maxReg : Gate → ℕ
  | .const d _ => d
  | .input d _ => d
  | .add d a b => max d (max a b)
  | .sub d a b => max d (max a b)
  | .mul d a b => max d (max a b)

/-- One gate executed on the registers `r`, with constant table `cst` and input point `x`. -/
def Gate.exec {A : Type} [CommRing A] (cst : ℕ → A) (x : ℕ → A) (r : ℕ → A) : Gate → (ℕ → A)
  | .const d c => Function.update r d (cst c)
  | .input d i => Function.update r d (x i)
  | .add d a b => Function.update r d (r a + r b)
  | .sub d a b => Function.update r d (r a - r b)
  | .mul d a b => Function.update r d (r a * r b)

namespace SLP

/-- The size: the number of gates, constant and input gates included. -/
def size (P : SLP) : ℕ := P.code.length

/-- The space: one more than the largest register index mentioned by a gate or an output. -/
def space (P : SLP) : ℕ := ((P.code.map Gate.maxReg) ++ P.outs).foldr max 0 + 1

/-- The registers after running all gates from the all-zero registers. -/
def regsAfter {A : Type} [CommRing A] (cst : ℕ → A) (x : ℕ → A) (P : SLP) : ℕ → A :=
  P.code.foldl (fun r g => g.exec cst x r) (fun _ => 0)

/-- The output values at the point `x`. -/
def eval {A : Type} [CommRing A] (cst : ℕ → A) (x : ℕ → A) (P : SLP) : List A :=
  P.outs.map (P.regsAfter cst x)

/-- Output number `o` at the point `x` (`0` if there is no such output). -/
def out {A : Type} [CommRing A] (cst : ℕ → A) (x : ℕ → A) (P : SLP) (o : ℕ) : A :=
  (P.eval cst x).getD o 0

/-- The formal polynomials computed: the run over `MvPolynomial ℕ R` with inputs `X i`. -/
noncomputable def formal {R : Type} [CommRing R] (cst : ℕ → R) (P : SLP) :
    List (MvPolynomial ℕ R) :=
  P.eval (fun c => C (cst c)) X

/-- Formal output number `o` (`0` if there is no such output). -/
noncomputable def formalOut {R : Type} [CommRing R] (cst : ℕ → R) (P : SLP) (o : ℕ) :
    MvPolynomial ℕ R :=
  (P.formal cst).getD o 0

end SLP

/-- The table of integer constants: index `c` names `(c : R)`. -/
def natTable (R : Type) [CommRing R] : ℕ → R := fun c => (c : R)

/-- Integer constants at even indices and the table `cst` at odd indices. -/
def mixTable {R : Type} [CommRing R] (cst : ℕ → R) : ℕ → R :=
  fun c => if c % 2 = 0 then (((c / 2 : ℕ) : R)) else cst (c / 2)

/-- `P` computes the product of an `a × b` and a `b × c` matrix as an identity of formal
polynomials: entry `(i, l)` of the first factor is input `i * b + l`, entry `(l, j)` of the second is
input `a * b + l * c + j`, and output `i * c + j` is entry `(i, j)` of the product. -/
def ComputesMatMul (R : Type) [CommRing R] (cst : ℕ → R) (a b c : ℕ) (P : SLP) : Prop :=
  P.outs.length = a * c ∧ ∀ i < a, ∀ j < c,
    P.formalOut cst (i * c + j) = ∑ l ∈ Finset.range b, X (i * b + l) * X (a * b + l * c + j)

/-- `P` computes the matrix product as a function on `R`-matrices (same layout as
`ComputesMatMul`). -/
def ComputesMatMulFun (R : Type) [CommRing R] (cst : ℕ → R) (a b c : ℕ) (P : SLP) : Prop :=
  P.outs.length = a * c ∧ ∀ (x : ℕ → R), ∀ i < a, ∀ j < c,
    P.out cst x (i * c + j) = ∑ l ∈ Finset.range b, x (i * b + l) * x (a * b + l * c + j)

/-- A gate as four words: opcode, destination, two operands. -/
def Gate.encode : Gate → List ℕ
  | .const d c => [0, d, c, 0]
  | .input d i => [1, d, i, 0]
  | .add d a b => [2, d, a, b]
  | .sub d a b => [3, d, a, b]
  | .mul d a b => [4, d, a, b]

/-- Four words read back as a gate (any opcode `≥ 4` is a multiplication). -/
def Gate.decode (l : List ℕ) : Gate :=
  match l.getD 0 0 with
  | 0 => .const (l.getD 1 0) (l.getD 2 0)
  | 1 => .input (l.getD 1 0) (l.getD 2 0)
  | 2 => .add (l.getD 1 0) (l.getD 2 0) (l.getD 3 0)
  | 3 => .sub (l.getD 1 0) (l.getD 2 0) (l.getD 3 0)
  | _ => .mul (l.getD 1 0) (l.getD 2 0) (l.getD 3 0)

/-- A program as words: the gate count, four words per gate, the output count, the outputs. -/
def SLP.encode (P : SLP) : List ℕ :=
  P.code.length :: (P.code.flatMap Gate.encode ++ (P.outs.length :: P.outs))

/-- Words read back as a program (total: missing words read as `0`). -/
def SLP.decode (ws : List ℕ) : SLP :=
  let g := ws.headD 0
  let rest := ws.tail
  let r2 := rest.drop (4 * g)
  { code := (List.range g).map fun t => Gate.decode ((rest.drop (4 * t)).take 4)
    outs := r2.tail.take (r2.headD 0) }

end DisjointPathsDAG


