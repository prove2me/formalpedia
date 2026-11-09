-- Prove2me | Definitions.Def_ShiAuthentication_BA_Graph
-- name    : ShiAuthentication_BA_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:54.10984+00:00
-- url     : https://prove2.me/theorems/627fad95-68c2-43f3-a72d-802277453c45
-- title:
--   Authentication graphs, verifier sets and the three-set condition
-- statement:
--   Let $P$ be a set of $n$ parties and $t$ a fault bound. An **authentication graph** is a directed graph $G=(P,E)$ without self-loops. An edge $x\to y$ means that $y$ is a **verifier** of $x$: the designated verification key of $x$ is initially authenticated to $y$. It is not a communication edge; communication always takes place over a complete network. For a party $x$ and a party $j$ write
--   $$V_x=\{y : x\to y\},\qquad K_j=\{x : j\in V_x\}$$
--   for the verifiers of $x$ and for the parties whose keys are initially authenticated to $j$. The graph is **complete** if $x\to y$ for all distinct $x,y$ (a complete PKI).
--
--   $G$ satisfies the **three-set condition** for $t$ if for every three pairwise disjoint sets $A,B,C\subseteq P$ with
--   $$n-2t\le |A|,|B|,|C|\le t,\qquad |A|+|B|+|C|\ge 2n-3t,$$
--   there is a signer $x\in C$ with $V_x\cap A\neq\emptyset$ and $V_x\cap B\neq\emptyset$. The sets need not cover $P$.
--
--   These are the combinatorial objects of the characterization of Byzantine agreement: agreement is possible exactly when $n>2t$ and the three-set condition holds.
--
--   **Formalization Note** The parties are `Fin n`; the edge relation is a Boolean matrix `adj` with `adj x x = false`. The lower bounds $n-2t$ and $2n-3t$ are compared in $\mathbb Z$, so they keep their meaning when they are negative. Feasibility of agreement is *not* defined through this condition; it is defined operationally in the execution model.
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), §1.1 p. 2, §3.1 pp. 15–16 (authentication graph, V_x, K_j), Main Theorem 1 (ii), p. 3

import Mathlib

set_option autoImplicit false

namespace ShiAuthentication.BA

/-! # Authentication graphs and the three-set condition

Kecheng Shi, *The Authentication Complexity of Byzantine Consensus*, STOC 2027 submission #203,
§1.1 (p. 2), §3.1 (pp. 15–16), Main Theorem 1 (p. 3) and Theorem 4.1 (p. 17).

The party set `P` of size `n` is `Fin n`. An authentication edge `x → y` means that `y` is a
verifier of `x`: the designated verification key of `x` is initially authenticated to `y`. It is
not a communication edge (communication is always over a complete network). -/

/-- A loopless directed authentication graph `G = (P, E)` on the parties `P = Fin n`
(§3.1, p. 15). `adj x y = true` means `x → y`, i.e. `y` is a verifier of `x`. -/
structure AuthGraph (n : ℕ) where
  /-- `adj x y = true` iff `x → y`. -/
  adj : Fin n → Fin n → Bool
  /-- No self-loops. -/
  loopless : ∀ x, adj x x = false

namespace AuthGraph

variable {n : ℕ}

/-- `V_x = {y : x → y}`, the verifiers of `x` (p. 2, p. 16). -/
def verifiers (G : AuthGraph n) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun y => G.adj x y = true)

/-- `K_j = {x : j ∈ V_x}`, the parties whose designated keys are initially authenticated to
`j` (p. 15). -/
def signersOf (G : AuthGraph n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => G.adj x j = true)

/-- `G` is the complete directed graph: `x → y` for all distinct `x, y` (complete PKI). -/
def IsComplete (G : AuthGraph n) : Prop :=
  ∀ x y : Fin n, x ≠ y → G.adj x y = true

end AuthGraph

/-- The **three-set condition** of Main Theorem 1 (ii) (p. 3) for the fault bound `t`: for every
three pairwise disjoint sets `A, B, C ⊆ P` with
`n − 2t ≤ |A|, |B|, |C| ≤ t` and `|A| + |B| + |C| ≥ 2n − 3t`
there is a signer `x ∈ C` with `V_x ∩ A ≠ ∅` and `V_x ∩ B ≠ ∅`.
The sets need not cover `P`. The lower bounds are computed in `ℤ`, so they keep their meaning
when `n − 2t` or `2n − 3t` is negative. -/
def ThreeSetCondition {n : ℕ} (G : AuthGraph n) (t : ℕ) : Prop :=
  ∀ A B C : Finset (Fin n), Disjoint A B → Disjoint A C → Disjoint B C →
    (n : ℤ) - 2 * t ≤ A.card → (n : ℤ) - 2 * t ≤ B.card → (n : ℤ) - 2 * t ≤ C.card →
    A.card ≤ t → B.card ≤ t → C.card ≤ t →
    2 * (n : ℤ) - 3 * t ≤ (A.card : ℤ) + B.card + C.card →
    ∃ x ∈ C, (G.verifiers x ∩ A).Nonempty ∧ (G.verifiers x ∩ B).Nonempty

end ShiAuthentication.BA


