-- Prove2me | Definitions.Def_AKSSorting_Core_IsChain
-- name    : AKSSorting_Core_IsChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:49:45.214377+00:00
-- url     : https://prove2.me/theorems/7ed050a8-523a-46f1-8b95-3768317c0ee1
-- title:
--   Levels of the binary tree T, chains C, N(C), ∪C, and subtree unions
-- statement:
--   Let $T$ be the set of finite $0$-$1$ sequences, viewed as a binary tree whose levels (sequences of equal length) are ordered lexicographically. For sequences $t=\langle a_1,\dots,a_i\rangle$ and $t'=\langle b_1,\dots,b_k\rangle$ write $t\prec t'$ if $i\ge k$ and $a_m=b_m$ for all $m\le k$, i.e. $t$ extends $t'$.
--
--   Let $\mathcal R$ be a set of registers. A **chain** on level $i$ is a function $C$ assigning to every sequence $x$ of length $i$ a finite set $C(x)\subseteq\mathcal R$ such that
--   $$ C(x)\cap C(y)=\emptyset \ (x\neq y), \qquad |C(x)|=|C(y)| . $$
--   For a chain write $N(C)=|C(x)|$ for some (all) $x$, and $\cup C=\bigcup_{t} C(t)$. For a node $t'$ of level $k\le i$ the **subtree union** of $C$ below $t'$ is
--   $$ \bigcup_{l(t)=i,\ t\prec t'} C(t). $$
--
--   Chains are the data structure of the Ajtai–Komlós–Szemerédi construction: at each stage the registers are distributed over one level of the tree, the same number to each node.
--
--   **Formalization Note** The level of sequences of length $i$ is encoded as `Fin (2^i)`: the sequence $\langle a_1,\dots,a_i\rangle$ is the number with binary digits $a_1\dots a_i$, most significant first. Numeric order is then the paper's lexicographic order, appending a bit $b$ to $t$ gives $2t+b$, and $u$ of length $i$ extends $t'$ of length $k\le i$ exactly when $\lfloor u/2^{i-k}\rfloor=t'$. The paper's "for all $x,y\in\mathrm{Dom}(C)$, $C(x)\cap C(y)=0$" is read for $x\neq y$ (otherwise every $C(x)$ would be empty). $N(C)$ is evaluated at the node $0$, which exists on every level. The subtree union is intended for $k\le i$.
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), pp. 2-3, Section 2, Definitions

import Mathlib

namespace AKSSorting.Core

/-!
Levels of the tree `T` of finite 0-1 sequences (Ajtai–Komlós–Szemerédi 1983, pp. 2–3).
The level of sequences of length `i` is encoded as `Fin (2 ^ i)`: the sequence
`⟨a₁, …, aᵢ⟩` is the number with binary digits `a₁ … aᵢ` (`a₁` most significant). Numeric order
on `Fin (2 ^ i)` is then the lexicographic order of the paper, appending the bit `b` to `t` gives
`2t + b`, and a sequence `u` of length `i` extends `t` of length `k ≤ i` (`u ≺ t`) iff
`u / 2 ^ (i - k) = t`.
-/

variable {R : Type} [DecidableEq R]

/-- `C` is a chain on level `i` (p. 3): `C(x) ⊆ ℛ` for every node `x` of the level, distinct
nodes carry disjoint sets, and all `C(x)` have the same cardinality. -/
def IsChain {i : ℕ} (C : Fin (2 ^ i) → Finset R) : Prop :=
  (∀ x y, x ≠ y → Disjoint (C x) (C y)) ∧ ∀ x y, (C x).card = (C y).card

/-- `N(C) = |C(x)|` for some (all) `x ∈ Dom(C)`; evaluated at the first node. -/
def chainN {i : ℕ} (C : Fin (2 ^ i) → Finset R) : ℕ :=
  (C ⟨0, Nat.two_pow_pos i⟩).card

/-- `∪C = ⋃_{t ∈ Dom(C)} C(t)`. -/
def chainUnion {i : ℕ} (C : Fin (2 ^ i) → Finset R) : Finset R :=
  Finset.univ.biUnion C

/-- For a chain `C` on level `i` and a node `t'` on level `k ≤ i`:
`⋃_{l(t) = i, t ≺ t'} C(t)`, the union of `C` over the level-`i` descendants of `t'`. -/
def subtreeUnion {i : ℕ} (C : Fin (2 ^ i) → Finset R) (k : ℕ) (t' : Fin (2 ^ k)) : Finset R :=
  (Finset.univ.filter fun u : Fin (2 ^ i) => u.val / 2 ^ (i - k) = t'.val).biUnion C

end AKSSorting.Core


