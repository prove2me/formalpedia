-- Prove2me | Definitions.Def_BiAbduction_Systematic_Syntax
-- name    : BiAbduction_Systematic_Syntax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:09.20865+00:00
-- url     : https://prove2.me/theorems/e85bbf95-d3f6-480a-be64-b7debba47921
-- title:
--   §3.1.1, §3.4 — symbolic heaps of the Points-to Instantiation, disjunctions, and their semantics
-- statement:
--   This file defines the syntax of the **Points-to Instantiation** of symbolic heaps and its forcing semantics.
--
--   **Syntax.** Expressions are $E ::= x \mid \kappa$: variables and natural-number constants, the constant $0$ being nil. Pure atoms are $E=E'$ and $E\neq E'$; a pure formula $\Pi$ is a finite conjunction of atoms. The only spatial atom is the points-to fact $E\mapsto E'$. A quantifier-free symbolic heap is $\Delta=\Pi\wedge\Sigma$, where $\Sigma$ is a $*$-conjunction of points-to facts, possibly with a $*\,\mathsf{true}$ conjunct ($\mathsf{emp}$ is the empty conjunction). A symbolic heap is $H=\exists\vec X.\,\Delta$, and a disjunction is $D=H_1\vee\dots\vee H_n$ (the empty disjunction being $\mathsf{false}$). The left-hand side $\Delta$ of the abduction question (5), $\Delta * D\models H$, is a quantifier-free symbolic heap $\Pi\wedge L_1\mapsto R_1*\dots*L_n\mapsto R_n$ without $\mathsf{true}$.
--
--   **Semantics.** With $[\![x]\!]s=s(x)$ and $[\![\kappa]\!]s=\kappa$,
--   $$s,h\models E=E' \iff [\![E]\!]s=[\![E']\!]s,\qquad s,h\models E\neq E'\iff [\![E]\!]s\neq[\![E']\!]s,$$
--   $$s,h\models E\mapsto E' \iff [\![E]\!]s\neq 0\ \text{ and }\ h=[\,[\![E]\!]s\mapsto[\![E']\!]s\,],$$
--   a pure formula holds in any heap, $\Pi\wedge\Sigma$ is the intersection of the pure and spatial parts, $*$-conjunctions, $\mathsf{emp}$ and $\mathsf{true}$ are interpreted by the semantic operations of the Semantics file, $\exists\vec X$ is iterated existential quantification, and a disjunction is a union.
--
--   The file also records the variables occurring in pure formulae and in $\Delta$, and the standing bound-variable convention of pp. 14 and 17: no variable bound in $H$ occurs in $\Delta$.
--
--   **Formalization Note** Program and logical variables form one sort, the natural numbers; in §3.3–§3.4 nothing distinguishes the two sorts beyond which variables are bound. The condition $[\![E]\!]s\neq0$ in the points-to clause makes explicit that $[\![E]\!]s$ must be a location, which the page's clause $h=[\,[\![E]\!]s\mapsto[\![E']\!]s\,]$ presupposes. All syntax is built from `ℕ`, `Bool`, `Sum`, `Prod` and `List` by abbreviations: an atom is `(flag, E, E')` with flag `true` for $=$, a quantifier-free symbolic heap is (atoms, points-to list, `true`-flag), a symbolic heap prefixes a list of bound variables, a disjunction is a list. Computability statements therefore refer to Mathlib's standard `Primcodable` encodings.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 12 (§3.1.1 grammar), p. 14 (convention), p. 15 (§3.1.2 forcing relation), p. 26 (Points-to Instantiation, (5), disjunctions D)

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Semantics

namespace BiAbduction.Systematic

/-!
Symbolic heaps of the Points-to Instantiation (§3.1.1, p. 12; §3.4, p. 26) and their semantics
(§3.1.2, p. 15). All syntax is built from `ℕ`, `Bool`, `Sum`, `Prod` and `List` by `abbrev`, so
Mathlib's standard `Primcodable` instances apply.
-/

/-- Expressions `E ::= x | κ`: `Sum.inl x` is the variable `x`, `Sum.inr κ` the constant `κ`
(`Sum.inr 0` is nil). -/
abbrev Expr := ℕ ⊕ ℕ

/-- `[[E]]s`. -/
def evalE (s : Stack) : Expr → ℕ
  | Sum.inl x => s x
  | Sum.inr k => k

/-- Pure atoms `E = E'` (flag `true`) and `E ≠ E'` (flag `false`). -/
abbrev PureAtom := Bool × Expr × Expr

/-- A points-to fact `E ↦ E'`. -/
abbrev PtsTo := Expr × Expr

/-- The left-hand side `Δ` of (5): a conjunction of pure atoms and a `∗`-conjunction of points-to
facts (`emp` when the list is empty); no `true` conjunct. -/
abbrev LHS := List PureAtom × List PtsTo

/-- A quantifier-free symbolic heap `Π ∧ Σ`: pure atoms, points-to facts and a flag recording a
`∗ true` conjunct (flag `false`: the spatial part ends in `emp`). -/
abbrev QF := List PureAtom × List PtsTo × Bool

/-- A symbolic heap `∃X⃗. Δ`. -/
abbrev SH := List ℕ × QF

/-- A disjunction `H₁ ∨ … ∨ Hₙ` of symbolic heaps (`[]` is `false`). -/
abbrev Disj := List SH

/-- `s ⊨ A` for a pure atom. -/
def atomHolds (s : Stack) (a : PureAtom) : Prop :=
  if a.1 then evalE s a.2.1 = evalE s a.2.2 else evalE s a.2.1 ≠ evalE s a.2.2

/-- A pure formula `Π` (a conjunction of atoms), read with any heap (`Π ∧ true`). -/
def pureDen (pi : List PureAtom) : Pred := {p | ∀ a ∈ pi, atomHolds p.1 a}

/-- `s, h ⊨ E ↦ E'` iff `[[E]]s` is a location (nonzero) and `h = [[[E]]s ↦ [[E']]s]`. -/
def ptsDen (pt : PtsTo) : Pred :=
  {p | evalE p.1 pt.1 ≠ 0 ∧
    ∀ l, p.2.cell l = if l = evalE p.1 pt.1 then some (evalE p.1 pt.2) else none}

/-- The spatial part `L₁↦R₁ ∗ ⋯ ∗ Lₙ↦Rₙ ∗ emp` (or `∗ true` when the flag is set). -/
def spatialDen (sig : List PtsTo) (tr : Bool) : Pred :=
  sig.foldr (fun pt acc => sepConj (ptsDen pt) acc) (if tr then Set.univ else emp)

/-- `Π ∧ Σ`. -/
def qfDen (q : QF) : Pred := pureDen q.1 ∩ spatialDen q.2.1 q.2.2

/-- `∃X⃗. Δ`. -/
def shDen (H : SH) : Pred := H.1.foldr exQ (qfDen H.2)

/-- `H₁ ∨ … ∨ Hₙ`. -/
def disjDen (D : Disj) : Pred := {p | ∃ H ∈ D, p ∈ shDen H}

/-- The left-hand side `Π ∧ L₁↦R₁ ∗ ⋯ ∗ Lₙ↦Rₙ`. -/
def lhsDen (Δ : LHS) : Pred := qfDen (Δ.1, Δ.2, false)

/-- Variables of an expression. -/
def exprVars : Expr → List ℕ
  | Sum.inl x => [x]
  | Sum.inr _ => []

/-- Variables of a pure formula. -/
def pureVars (pi : List PureAtom) : List ℕ :=
  pi.flatMap (fun a => exprVars a.2.1 ++ exprVars a.2.2)

/-- Variables of a list of points-to facts. -/
def ptsVars (sig : List PtsTo) : List ℕ :=
  sig.flatMap (fun pt => exprVars pt.1 ++ exprVars pt.2)

/-- Variables of the left-hand side `Δ`. -/
def lhsVars (Δ : LHS) : List ℕ := pureVars Δ.1 ++ ptsVars Δ.2

/-- The standing bound-variable convention (pp. 14, 17): no variable bound in `H` occurs in `Δ`. -/
def Conv (Δ : LHS) (H : SH) : Prop := ∀ x ∈ H.1, x ∉ lhsVars Δ

end BiAbduction.Systematic


