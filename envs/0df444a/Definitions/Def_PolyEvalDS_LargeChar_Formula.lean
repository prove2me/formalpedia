-- Prove2me | Definitions.Def_PolyEvalDS_LargeChar_Formula
-- name    : PolyEvalDS_LargeChar_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:44.044199+00:00
-- url     : https://prove2.me/theorems/18137fcd-b3bd-4bc1-aeb2-0e47bf2ffd68
-- title:
--   Division-free arithmetic formulas with size and evaluation
-- statement:
--   An **arithmetic formula** over a set $V$ of variables is a finite tree whose leaves are variables $v\in V$ or natural-number constants $c$, and whose inner nodes are sums and products of two subformulas. There is no division node. The **size** of a formula is its number of nodes. Given a semiring $F$ and an assignment $\rho:V\to F$, the **value** of a formula is computed by the tree, with a constant $c$ read as the image of $c$ in $F$.
--
--   For a formula whose variables are natural numbers, *all variables below $m$* means that every variable leaf $j$ satisfies $j<m$.
--
--   This is the model of the circuits in Definition 2.2. When $F$ contains $\mathbb F_p$, every element of $\mathbb F_p$ is a constant of this form.
--
--   **Formalization Note** A tree is a circuit with fan-out one, and subtraction is not needed: $-1$ is the constant $p-1$ in characteristic $p$.
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Definition 2.2, p. 5

import Mathlib

namespace PolyEvalDS.LargeChar

/-- Division-free arithmetic formulas over variables `V`: variables, natural-number constants,
sums and products. There is no division node. Okada, Player, Pohmann, STOC 2027 submission #463
(October 2026), Definition 2.2, p. 5: "The circuits are considered to be division-free and may
contain constants from F." -/
inductive AF (V : Type) : Type
  | var (v : V) : AF V
  | const (c : ℕ) : AF V
  | add (a b : AF V) : AF V
  | mul (a b : AF V) : AF V

namespace AF

variable {V : Type}

/-- The number of nodes of a formula. -/
def size : AF V → ℕ
  | var _ => 1
  | const _ => 1
  | add a b => a.size + b.size + 1
  | mul a b => a.size + b.size + 1

/-- Evaluation in a semiring under an assignment `ρ` of the variables. A constant `c` evaluates to
the cast of `c`; in a field `F` with `Algebra (ZMod p) F` that is the image of `c` in `F_p ⊆ F`. -/
def eval {F : Type*} [Semiring F] (ρ : V → F) : AF V → F
  | var v => ρ v
  | const c => (c : F)
  | add a b => a.eval ρ + b.eval ρ
  | mul a b => a.eval ρ * b.eval ρ

/-- Every variable of a formula with natural-number variables is below `m`. -/
def VarsBelow (m : ℕ) : AF ℕ → Prop
  | var j => j < m
  | const _ => True
  | add a b => a.VarsBelow m ∧ b.VarsBelow m
  | mul a b => a.VarsBelow m ∧ b.VarsBelow m

end AF

end PolyEvalDS.LargeChar


