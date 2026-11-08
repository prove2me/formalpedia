-- Prove2me | Definitions.Def_OneOfManyCC_Protocol
-- name    : OneOfManyCC_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:06.395665+00:00
-- url     : https://prove2.me/theorems/b6d4ae1d-be04-4879-b899-209935cd2a60
-- title:
--   Deterministic two-party protocol tree, its depth, its output, and solving a relation on a rectangle
-- statement:
--   A **deterministic protocol** with input sets $A$, $B$ and output set $O$ is a binary tree. Every inner node belongs to Alice or to Bob, and every leaf is labelled by an output $o\in O$. A node of Alice carries a function $A\to\{0,1\}$ and a node of Bob a function $B\to\{0,1\}$; the value tells which child to go to. On inputs $x\in A$, $y\in B$ the players start at the root and move as their functions dictate until they reach a leaf, whose label is the output $P(x,y)$. The **depth** is the maximum length of a path from the root to a leaf.
--
--   For $A'\subseteq A$ and $B'\subseteq B$, the protocol **solves** a relation $R\subseteq A\times B\times O$ on $A'\times B'$ if
--
--   $$(x,y,P(x,y))\in R\quad\text{for all }x\in A',\ y\in B'.$$
--
--   This is the model of all the communication bounds in the paper. Leaf labels are fixed outputs, so both players know the output and every bit counts.
--
--   **Formalization Note** The value `false` selects the child `p₀` and `true` the child `p₁`. A relation is a predicate `R : A → B → O → Prop`.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.1, p.7; §5, p.10

import Mathlib

namespace OneOfManyCC

/-- **Deterministic two-party protocol tree.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.1, p.7:
"A deterministic protocol for R is a binary tree in which every inner node belongs to Alice or to
Bob and every leaf is labeled by an output o ∈ O. Each node of Alice is labeled by a function
A → {0, 1}, and each node of Bob by a function B → {0, 1}, which tells which child to go to."

**Formalization Note.** `{0, 1}` is `Bool`; value `false` selects the child `p₀`, value `true` the
child `p₁`. Leaves carry a fixed label, so the output depends on the leaf only. The sets are in
`Type`. -/
inductive Protocol (A B O : Type) : Type
  | leaf (o : O) : Protocol A B O
  | alice (f : A → Bool) (p₀ p₁ : Protocol A B O) : Protocol A B O
  | bob (g : B → Bool) (p₀ p₁ : Protocol A B O) : Protocol A B O

namespace Protocol

variable {A B O : Type}

/-- The depth of a protocol: "the maximum length of a path from the root to a leaf, that is, the
number of bits sent in the worst case" (§3.1, p.7). A leaf has depth `0`. -/
def depth : Protocol A B O → ℕ
  | leaf _ => 0
  | alice _ p₀ p₁ => max p₀.depth p₁.depth + 1
  | bob _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- The output of the protocol on inputs `x`, `y`: "the players start at the root and repeatedly go
to the child chosen by the owner of the current node on its own input, until they reach a leaf,
whose label is the output" (§3.1, p.7). -/
def eval : Protocol A B O → A → B → O
  | leaf o, _, _ => o
  | alice f p₀ p₁, x, y => if f x = true then p₁.eval x y else p₀.eval x y
  | bob g p₀ p₁, x, y => if g y = true then p₁.eval x y else p₀.eval x y

/-- `P.SolvesOn R A' B'`: the protocol solves `R` on `A' × B'` (§5, p.10): "whenever Alice receives
x ∈ A′ and Bob receives y ∈ B′, the output o at the leaf they reach satisfies (x, y, o) ∈ R".
With `A' = B' = univ` this is "the protocol solves R" of §3.1, p.7. -/
def SolvesOn (P : Protocol A B O) (R : A → B → O → Prop) (A' : Set A) (B' : Set B) : Prop :=
  ∀ x ∈ A', ∀ y ∈ B', R x y (P.eval x y)

end Protocol

end OneOfManyCC


