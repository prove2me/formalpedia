-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Supplement_Formula
-- name    : NCFactorClosure607_Circuits_Supplement_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:37.01107+00:00
-- url     : https://prove2.me/theorems/38a086f8-172a-480b-a288-887c3420b369
-- title:
--   Noncommutative formulas: trees of $+$ and ordered $\times$, size counted with every node
-- statement:
--   A **noncommutative formula** over a field $F$ in the noncommuting variables $X$ is a circuit whose underlying computation is a tree: its leaves are field constants $a\in F$ or variables $x\in X$, and its internal nodes are binary additions $\Phi+\Psi$ and ordered binary multiplications $\Phi\cdot\Psi$. Repeated uses of a subexpression are counted separately.
--
--   The **size** $|\Phi|$ of a formula is its number of nodes, leaves included:
--   $$|a|=|x|=1,\qquad |\Phi+\Psi|=|\Phi\cdot\Psi|=|\Phi|+|\Psi|+1 .$$
--   The polynomial computed by a formula is its value in the free algebra $F\langle X\rangle$: a constant leaf $a$ computes $a\cdot 1$, a variable leaf $x$ computes $x$, and the internal nodes add or multiply (left factor first) the polynomials of their children. These are the conventions of the base circuits, without sharing of subexpressions.
--
--   Formulas are the input and output model of Lemma 5.1, Corollary 5.2 and the formula clauses of Theorem 1.2.
--
--   **Formalization Note** A formula is an inductive tree `Formula F X`; `size` and `eval` are defined by recursion on it.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.5, §2, paragraph Circuit conventions; p.12, proof of Lemma 5.1 (|U| counts the nodes including leaves); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Circuit

/-!
# Noncommutative formulas

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, §2, paragraph "Circuit conventions", p.5, and §5.1, p.10–12.

A formula is a circuit whose underlying computation is a tree: every node is used as an operand
at most once, and repeated uses of a subexpression are counted separately. It is represented as
an inductive tree whose leaves are field constants or variables and whose internal nodes are
binary additions and ordered binary multiplications. Its size is its number of nodes, leaves
included (`|U|`, p.12). Its value is computed exactly as the value of a circuit gate (base
definition `NCFactorClosure607_Circuits_Circuit`): a constant `a` is `a · 1`, a variable `x` is
`x`, and the internal nodes add or multiply (left times right) the values of their children.
-/

namespace NCFactorClosure607.Circuits.Supplement

/-- A noncommutative formula over `F` in the variables `X`. `mul Φ Ψ` computes `Φ · Ψ` in this
order. -/
inductive Formula (F : Type*) (X : Type*) where
  | const (a : F)
  | var (x : X)
  | add (Φ Ψ : Formula F X)
  | mul (Φ Ψ : Formula F X)

namespace Formula

variable {F : Type*} {X : Type*}

/-- The size of a formula: its number of nodes, leaves included (§5.1, p.12: `|U|`). -/
def size : Formula F X → ℕ
  | const _ => 1
  | var _ => 1
  | add Φ Ψ => Φ.size + Ψ.size + 1
  | mul Φ Ψ => Φ.size + Ψ.size + 1

/-- The polynomial computed by a formula, in `F⟨X⟩ = FreeAlgebra F X`. -/
noncomputable def eval [Field F] : Formula F X → FreeAlgebra F X
  | const a => algebraMap F (FreeAlgebra F X) a
  | var x => FreeAlgebra.ι F x
  | add Φ Ψ => Φ.eval + Ψ.eval
  | mul Φ Ψ => Φ.eval * Ψ.eval

end Formula

end NCFactorClosure607.Circuits.Supplement


