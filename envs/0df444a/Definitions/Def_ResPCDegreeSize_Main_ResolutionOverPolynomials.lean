-- Prove2me | Definitions.Def_ResPCDegreeSize_Main_ResolutionOverPolynomials
-- name    : ResPCDegreeSize_Main_ResolutionOverPolynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:48.413325+00:00
-- url     : https://prove2.me/theorems/388155db-0237-4b3c-a797-31ff90d34361
-- title:
--   The proof system $\mathrm{Res}(\mathrm{PC}_r/\mathbb F_p)$: lines, rules, refutations and size
-- statement:
--   A line of $\mathrm{Res}(\mathrm{PC}_r/\mathbb F_p)$ is a disjunction $\bigvee_{h\in L}(h=0)$ of polynomial equations with $\deg h\le r$.
--
--   The default axioms are $(0=0)$ and $(x_i=0)\vee(x_i-1=0)$, and the initial line of a clause $J\in F$ is $\bigvee_{l\in J}(1-l=0)$. The deduction rules are syntactic:
--
--   1. weakening: from $A$ derive any line containing it;
--   2. deletion of a false constant equation: from $A\vee(c=0)$ with a nonzero constant $c\in\mathbb F_p$ derive $A$;
--   3. linear combination: from $A\vee(f=0)$ and $B\vee(g=0)$ derive $A\vee B\vee(\alpha f+\beta g=0)$;
--   4. multiplication: from $A\vee(f=0)$ derive $A\vee(fg=0)$.
--
--   All displayed polynomials have degree at most $r$. A refutation of $F$ is a finite DAG of such lines ending with the empty clause, and its size $S$ is its number of nodes. Proofs need not be tree-like or regular, and a line may have any number of disjuncts.
--
--   The system is the one introduced by Krajíček over $\mathbb F_2$ and studied over finite rings by Khaniki. With $r=1$ and $p=2$ it is resolution over parities.
--
--   **Formalization Note** A line is a `Finset` of polynomials, so contraction and reordering are built in and weakening is the subset relation. A refutation is a list in which every entry is a line of degree at most $r$ that is an initial line or follows from strictly earlier entries, ending with the empty line; such a list is a topological order of a DAG. `ResRefutation.size` is the list length and `ResRefutation.line` the line at a node. The same polynomial line at two nodes gives two nodes.
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Section 1, PDF p. 2 (printed p. 1); initial lines in the proof of Proposition 5.1, PDF p. 10 (printed p. 9)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus

namespace ResPCDegreeSize.Main

open MvPolynomial

noncomputable section

/-- A line `⋁_{h ∈ L} (h = 0)` is a finite set of polynomials; contraction and reordering of
disjuncts are therefore built in. -/
abbrev Line (n p : ℕ) := Finset (Poly n p)

/-- A line of `Res(PC_r/F_p)`: all its polynomials have total degree at most `r`. -/
def IsResLine {n p : ℕ} (r : ℕ) (L : Line n p) : Prop :=
  ∀ h ∈ L, h.totalDegree ≤ r

open scoped Classical in
/-- The initial line of a clause `J`: `⋁_{l ∈ J} (1 - l = 0)`. -/
def clauseLine {n : ℕ} (p : ℕ) (J : Clause n) : Line n p :=
  J.image fun l => 1 - litPoly p l

open scoped Classical in
/-- Lines available without premises: `(0 = 0)`, `(xᵢ = 0) ∨ (xᵢ - 1 = 0)`, and the initial line
of each clause of `F`. -/
inductive ResInitial {n p : ℕ} (F : CNF n) : Line n p → Prop
  | zero : ResInitial F {0}
  | bool (i : Fin n) : ResInitial F {X i, X i - 1}
  | clause (J : Clause n) (hJ : J ∈ F) : ResInitial F (clauseLine p J)

open scoped Classical in
/-- `L` follows in one step of `Res(PC_r/F_p)` from the lines of `prev`: it is an initial line, or
it comes by syntactic weakening, deletion of a false constant equation `c = 0` with `c ≠ 0`,
linear combination, or multiplication. -/
inductive ResInfers {n p : ℕ} (F : CNF n) (prev : List (Line n p)) : Line n p → Prop
  | initial {L : Line n p} (hL : ResInitial F L) : ResInfers F prev L
  | weaken {A B : Line n p} (hA : A ∈ prev) (hAB : A ⊆ B) : ResInfers F prev B
  | deleteConst {A : Line n p} (c : ZMod p) (hc : c ≠ 0) (hA : insert (C c) A ∈ prev) :
      ResInfers F prev A
  | linComb {A B : Line n p} {f g : Poly n p} (α β : ZMod p)
      (hA : insert f A ∈ prev) (hB : insert g B ∈ prev) :
      ResInfers F prev (insert (C α * f + C β * g) (A ∪ B))
  | mul {A : Line n p} {f : Poly n p} (g : Poly n p) (hA : insert f A ∈ prev) :
      ResInfers F prev (insert (f * g) A)

/-- `π` is a `Res(PC_r/F_p)` derivation from `F`: every entry is a line of degree at most `r`
and follows from strictly earlier entries. A list is a topological ordering of a DAG; an entry
may be used as a premise any number of times. -/
def IsResDerivation {n p : ℕ} (F : CNF n) (r : ℕ) (π : List (Line n p)) : Prop :=
  ∀ (i : ℕ) (hi : i < π.length), IsResLine r π[i] ∧ ResInfers F (π.take i) π[i]

/-- A `Res(PC_r/F_p)` refutation of `F`: a derivation whose last line is the empty clause. -/
structure ResRefutation {n : ℕ} (p : ℕ) (F : CNF n) (r : ℕ) where
  lines : List (Line n p)
  derivation : IsResDerivation F r lines
  ends_empty : lines.getLast? = some ∅

/-- The size `S` of a refutation: its number of nodes. -/
abbrev ResRefutation.size {n p r : ℕ} {F : CNF n} (R : ResRefutation p F r) : ℕ := R.lines.length

/-- The line at node `ν`. -/
def ResRefutation.line {n p r : ℕ} {F : CNF n} (R : ResRefutation p F r) (ν : Fin R.size) :
    Line n p := R.lines.get ν

end

end ResPCDegreeSize.Main


