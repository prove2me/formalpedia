-- Prove2me | Definitions.Def_PrecDTree_Main_Order
-- name    : PrecDTree_Main_Order
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:49:55.921285+00:00
-- url     : https://prove2.me/theorems/8ae3cefc-7cef-4372-81ea-6947aa1be621
-- title:
--   Partial orders, precedence-closed sets and precedence-closed sequences (§2)
-- statement:
--   A **partial order** on a set $X$ is a reflexive, transitive and antisymmetric relation $\preceq$. A finite subset $S\subseteq X$ is **precedence-closed** if for all $x\in S$ and all $y\preceq x$ we have $y\in S$. A sequence $(X_1,\dots,X_k)$ of elements of $X$ is **precedence-closed** if every strict predecessor of each $X_i$ occurs earlier:
--   $$\forall i,\ \forall y\in X:\quad y\preceq X_i,\ y\neq X_i\ \Longrightarrow\ \exists j<i,\ X_j=y .$$
--   Repetitions are allowed in a sequence.
--
--   **Formalization Note.** The relation is an arbitrary `le : α → α → Prop` (`le y x` reads $y\preceq x$), with `IsPartialOrderRel le` the three axioms; sequences are lists with 0-based indices.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 4, §2 'Partial orders and precedence constraints'

import Mathlib

set_option autoImplicit false

/-!
# Partial orders and precedence-closed sets and sequences (§2, p. 4)

Szyfelbein, Dereniowski, *Precedence-Constrained Decision Trees and Coverings*, arXiv:2602.21312
(STOC 2027 submission version), p. 4, §2 "Partial orders and precedence constraints".
-/

namespace PrecDTree.Main

/-- `le` is a partial order: reflexive, transitive and antisymmetric (p. 4). `le y x` reads
`y ⪯ x`. -/
def IsPartialOrderRel {α : Type} (le : α → α → Prop) : Prop :=
  (∀ a, le a a) ∧ (∀ a b c, le a b → le b c → le a c) ∧ (∀ a b, le a b → le b a → a = b)

/-- A finite subset `S` is precedence-closed: for all `x ∈ S` and all `y ⪯ x`, `y ∈ S` (p. 4). -/
def PrecClosedSet {α : Type} (le : α → α → Prop) (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y, le y x → y ∈ S

/-- A sequence `(X₁, …, X_k)` is precedence-closed: every strict predecessor of each `Xᵢ` occurs
earlier, i.e. for every `y ⪯ Xᵢ` with `y ≠ Xᵢ` there is `j < i` with `Xⱼ = y` (p. 4).
Repetitions are allowed. Indices are 0-based. -/
def PrecClosedSeq {α : Type} (le : α → α → Prop) (s : List α) : Prop :=
  ∀ i : Fin s.length, ∀ y, le y s[i] → y ≠ s[i] → ∃ j : Fin s.length, j < i ∧ s[j] = y

end PrecDTree.Main


