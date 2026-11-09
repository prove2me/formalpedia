-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_CNF
-- name    : ParityBarrier563_Trilinear_CNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:24.466076+00:00
-- url     : https://prove2.me/theorems/9e63069e-5d7c-47cb-bbac-1c7415d2591a
-- title:
--   §2 — literals, clauses, terms, k-CNFs and k-DNFs
-- statement:
--   A **literal** over $V$ is a variable $v$ or its negation $\neg v$. A **clause** is an OR of literals, a **term** is an AND of literals, a **CNF** is an AND of clauses and a **DNF** is an OR of terms. The empty clause is false, the empty term is true, the empty CNF is the constant $1$ and the empty DNF is the constant $0$. Repeated literals are removed, so the **width** of a clause or a term is the number of variables in it. A **$k$-CNF** is a Boolean function computed by a CNF all of whose clauses have width at most $k$; $k$-DNFs are defined in the same way with terms. In particular "width at most $k$" is meant, and constants are $k$-CNFs for every $k\ge0$.
--
--   We also record the number of clauses (or terms): a function is a $k$-CNF with at most $M$ clauses if some CNF of width at most $k$ with at most $M$ clauses computes it. A function $F$ is an **OR of at most $M$ $k$-CNFs** if there are $m\le M$ functions $H_1,\dots,H_m$, each a $k$-CNF, with $F=H_1\vee\dots\vee H_m$.
--
--   These notions are the language of the switching lemma (Lemma 2.1), of the depth reduction (Lemma 2.2) and of all correlation bounds.
--
--   **Formalization Note** A literal is a pair $(v,c)$ satisfied by $x$ iff $x_v=c$, and clauses and terms are finite sets of literals. A tautological clause is identically true and a contradictory term identically false; dropping such a clause from a CNF increases neither width nor clause count, so "computed by a CNF of width at most $k$ with at most $M$ clauses" is the same predicate with or without the source's normalization.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, §2 Preliminaries, 'CNFs and correlation', printed p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Cube

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-! §2, printed p.10 / PDF 12: literals, clauses, terms, CNFs and DNFs, and their widths.

A literal is a pair `(v, c)`: it is satisfied by `x` iff `x v = c` (so `(v, true)` is `v` and
`(v, false)` is `¬v`). Clauses and terms are finite sets of literals, so a literal never repeats.
The width of a clause or term is the number of distinct variables in it. A tautological clause
(containing `v` and `¬v`) is identically true and can be dropped from any CNF without increasing
its width or its number of clauses, so "is computed by a CNF of width `≤ b` with `≤ M` clauses"
is the same predicate whether or not tautological clauses are first removed; likewise a term with
`v` and `¬v` is identically false. -/

variable {V : Type}

/-- A literal: variable and the value that satisfies it. -/
abbrev Literal (V : Type) := V × Bool

/-- A clause or a term: a finite set of literals. -/
abbrev LitSet (V : Type) := Finset (Literal V)

/-- The width of a clause or term: the number of distinct variables in it. -/
def width [DecidableEq V] (C : LitSet V) : ℕ := (C.image Prod.fst).card

/-- `x` satisfies the clause `C` (an OR of literals; the empty clause is false). -/
def ClauseSat (C : LitSet V) (x : V → Bool) : Prop := ∃ l ∈ C, x l.1 = l.2

/-- `x` satisfies the term `π` (an AND of literals; the empty term is true). -/
def TermSat (π : LitSet V) (x : V → Bool) : Prop := ∀ l ∈ π, x l.1 = l.2

/-- The Boolean function of a term. -/
noncomputable def termFn (π : LitSet V) : BoolFn V := by
  classical exact fun x => decide (TermSat π x)

/-- The Boolean function of a clause. -/
noncomputable def clauseFn (C : LitSet V) : BoolFn V := by
  classical exact fun x => decide (ClauseSat C x)

/-- `H` is computed by a CNF (an AND of clauses) whose clauses have width at most `k` and whose
number of clauses is at most `M` (`M = ⊤`: no bound on the number of clauses). The empty CNF is
the constant true; a CNF containing the empty clause is the constant false. -/
def IsCNFWith [DecidableEq V] (k : ℕ) (M : ℕ∞) (H : BoolFn V) : Prop :=
  ∃ F : Finset (LitSet V), ((F.card : ℕ∞) ≤ M) ∧ (∀ C ∈ F, width C ≤ k) ∧
    ∀ x, (H x = true ↔ ∀ C ∈ F, ClauseSat C x)

/-- `H` is computed by a DNF (an OR of terms) whose terms have width at most `k` and whose
number of terms is at most `M`. The empty DNF is the constant false. -/
def IsDNFWith [DecidableEq V] (k : ℕ) (M : ℕ∞) (H : BoolFn V) : Prop :=
  ∃ F : Finset (LitSet V), ((F.card : ℕ∞) ≤ M) ∧ (∀ π ∈ F, width π ≤ k) ∧
    ∀ x, (H x = true ↔ ∃ π ∈ F, TermSat π x)

/-- `H` is a `k`-CNF: a CNF of width at most `k` (any number of clauses). -/
def IsCNF [DecidableEq V] (k : ℕ) (H : BoolFn V) : Prop := IsCNFWith k ⊤ H

/-- `H` is a `k`-DNF: a DNF of width at most `k` (any number of terms). -/
def IsDNF [DecidableEq V] (k : ℕ) (H : BoolFn V) : Prop := IsDNFWith k ⊤ H

/-- `F` is the OR of at most `M` functions, each a `k`-CNF (`M` a real number). -/
def IsOrOfCNFs [DecidableEq V] (k : ℕ) (M : ℝ) (F : BoolFn V) : Prop :=
  ∃ (m : ℕ) (H : Fin m → BoolFn V), (m : ℝ) ≤ M ∧ (∀ i, IsCNF k (H i)) ∧
    ∀ x, (F x = true ↔ ∃ i, H i x = true)

end ParityBarrier563.Trilinear


