-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Supplement_BinaryCSP
-- name    : NogoodColoring1137_Main_Supplement_BinaryCSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:56:16.915875+00:00
-- url     : https://prove2.me/theorems/8644507a-9d6f-418f-87d4-6c3c69a7675e
-- title:
--   Binary CSPs in merged relation-table form
-- statement:
--   A binary constraint satisfaction problem on an ordered set of $n$ variables and a common alphabet $D$ specifies a finite unary set $L(v)\subseteq D$ at every variable and a finite allowed relation $R_{vw}\subseteq D\times D$ for each pair $v<w$. An assignment $x$ satisfies the instance precisely when
--
--   $$
--   (\forall v,\ x(v)\in L(v))\quad\text{and}\quad
--   (\forall v<w,\ (x(v),x(w))\in R_{vw}).
--   $$
--
--   This is the general data layer; the three-value instance is its specialization to $D=\{0,1,2\}$. Empty unary sets and empty relations are allowed. On a finite alphabet an unconstrained pair has the full relation. Intersect repeated constraints, transpose their relation when reversing endpoints, and fold repeated-variable constraints into the unary set. No symmetry of a relation on values is required.
--
--   **Formalization Note** Variables are `Fin n`; `VariablePair n` contains exactly the increasing pairs. The structure contains data only, with no solver, consistency promise, or nonemptiness condition. The shared alphabet is a type, and the unary and binary tables are finite sets.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Section 8.1, p. 23 (printed = PDF)

import Mathlib

namespace NogoodColoring1137.Main.Supplement

/-- One representative for each pair of distinct variables, in increasing order. -/
abbrev VariablePair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- General finite binary CSP data in merged relation-table form (§8.1, p.23).
Reversed constraints are transposed before merging; self-constraints are unary.
There is no closure, consistency, nonemptiness or symmetry condition on values. -/
structure BinaryCSP (n : ℕ) (α : Type) where
  unary : Fin n → Finset α
  relation : VariablePair n → Finset (α × α)

/-- The usual conjunction of all unary and binary constraints. -/
def BinaryCSP.Satisfies {n : ℕ} {α : Type} (I : BinaryCSP n α)
    (x : Fin n → α) : Prop :=
  (∀ v, x v ∈ I.unary v) ∧
    ∀ p : VariablePair n, (x p.val.1, x p.val.2) ∈ I.relation p

end NogoodColoring1137.Main.Supplement


