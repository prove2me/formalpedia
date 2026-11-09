-- Prove2me | Definitions.Def_MinCostMaj_BlowUp
-- name    : MinCostMaj_BlowUp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:13:51.86105+00:00
-- url     : https://prove2.me/theorems/46e84298-4ebb-41b1-a996-c2a31f32968e
-- title:
--   Blow-ups of unions of directed cycles and of grids; $R_{00}$, $R_{11}$, $\ne$
-- statement:
--   A **directed cycle** is $Z_k=\{(a,a+1\bmod k)\}$ on $\{0,\dots,k-1\}$, where $k=1$ (a loop) is allowed, and a **union of directed cycles** is a disjoint union of directed cycles. A **grid** of size $k$ is the digraph on $\{0,\dots,k-1\}^2$ with an arc $((a,b),(c,d))$ iff $b=c$. A **blow-up** of a digraph replaces each vertex by a nonempty set and each arc by a complete directed bipartite graph.
--
--   A relation $\rho$ on a set $P$ *defines a blow-up of a union of directed cycles, at least one of length $\ge2$* if $P$ is partitioned into nonempty blocks indexed by the vertices of such a digraph and $a\,\rho\,b$ holds exactly when there is an arc from the block of $a$ to the block of $b$; similarly for a grid of size $k\ge2$, where all $k^2$ blocks are nonempty.
--
--   For two values $0,1$, $R_{ij}=\{0,1\}^2\setminus\{(i,j)\}$ and $\ne=\{(0,1),(1,0)\}$. A closed pattern $p$ at $x$ *defines $T$ after restricting intermediate potatoes to two-element subsets* if a two-element subset of the potato is chosen at every position of $p$, equal to $\{0,1\}$ at both ends, and the relation connected by $p$ through these subsets is $T$.
--
--   These are the three outcomes of Theorem 4.1 that the reduction from $\mathrm{cUG}(k)$ uses.
--
--   **Formalization Note** A disjoint union of directed cycles on $m$ vertices is the functional graph $j\mapsto\sigma(j)$ of a permutation $\sigma$ of $\{0,\dots,m-1\}$; fixed points are the loops $Z_1$, and "at least one of length $\ge2$" is $\sigma\ne\mathrm{id}$.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §4.1, p.7, and Theorem 4.1, pp.7–8 (PDF pp.8–9)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst
import Definitions.Def_MinCostMaj_Pattern

namespace MinCostMaj

/-- **A relation on `P` defines a blow-up of a disjoint union of directed cycles, at least one of
length ≥ 2** (§4.1, p.7, and Theorem 4.1 Item 2, p.8).

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, p.7: "a directed cycle is … Zk = {(a, a + 1 mod k) : a ∈
{0, . . . , k − 1}} (in this section we allow k = 1, which makes Z1 a digraph with one vertex and a
self-loop), and a union of directed cycles is a disjoint union of some directed cycles. … a blow-up
of a digraph is obtained by replacing each vertex by a non-empty set and each arc by a complete
directed bipartite graph."

The blocks `blk⁻¹(j) ∩ P` (`j < m`) partition `P` and are all nonempty; `a` is related to `b`
exactly when the block of `b` is `σ` of the block of `a`.

**Formalization Note.** A disjoint union of directed cycles on `m` vertices is the functional graph
`j ↦ σ j` of a permutation `σ` of `Fin m` (its cycles are the `Z_k`, fixed points the loops `Z₁`);
"at least one of length ≥ 2" is `σ ≠ 1`. -/
def IsBlowUpOfCycles {D : Type*} (P : Set D) (Rl : D → D → Prop) : Prop :=
  ∃ (m : ℕ) (blk : D → Fin m) (σ : Equiv.Perm (Fin m)),
    (∀ j, ∃ a ∈ P, blk a = j) ∧ σ ≠ 1 ∧
    ∀ a ∈ P, ∀ b ∈ P, (Rl a b ↔ blk b = σ (blk a))

/-- **A relation on `P` defines a blow-up of a grid of size ≥ 2** (p.7: "A grid is a directed graph
on {0, . . . , k − 1}² with an arc ((a, b), (c, d)) if and only if b = c"), with the blocks
`blk⁻¹(i, j) ∩ P` partitioning `P`, all `k²` of them nonempty, and `k ≥ 2`. -/
def IsBlowUpOfGrid {D : Type*} (P : Set D) (Rl : D → D → Prop) : Prop :=
  ∃ (k : ℕ) (blk : D → Fin k × Fin k), 2 ≤ k ∧
    (∀ j, ∃ a ∈ P, blk a = j) ∧
    ∀ a ∈ P, ∀ b ∈ P, (Rl a b ↔ (blk a).2 = (blk b).1)

/-- The variable at position `i` of the pattern with start `u` and steps `l` (`w₀ = u`). -/
def patVertex {V D : Type*} (u : V) (l : List (Set (D × D) × V)) (i : ℕ) : V :=
  (u :: l.map Prod.snd).getD i u

/-- **"After restricting intermediate potatoes to suitable two-element subsets, the closed pattern
`p` at `x` defines `T`"** (Theorem 4.1 Item 3, p.8): there are sets `S i ⊆ A^I_{wᵢ}` with exactly
two elements, for every position `i` of the pattern, with `S 0 = S n = {e₀, e₁}`, such that the
relation connected by `p` with every value restricted to its `S i` is `T`. -/
def DefinesRestricted {V D : Type*} (I : BinInst V D) (x : V) (e₀ e₁ : D)
    (l : List (Set (D × D) × V)) (T : Set (D × D)) : Prop :=
  ∃ S : ℕ → Set D,
    (∀ i ≤ l.length, S i ⊆ I.pot (patVertex x l i) ∧ (S i).ncard = 2) ∧
    S 0 = {e₀, e₁} ∧ S l.length = {e₀, e₁} ∧
    {ab : D × D | ab.1 ∈ S 0 ∧ ConnectsPos S 0 ab.1 l ab.2} = T

/-- `R₀₀ = {0,1}² ∖ {(0,0)}` on the two values `0 = e₀`, `1 = e₁` (p.7: `Rij = {0, 1}² ∖ {(i, j)}`). -/
def R00 {D : Type*} (e₀ e₁ : D) : Set (D × D) := {(e₀, e₁), (e₁, e₀), (e₁, e₁)}

/-- `R₁₁ = {0,1}² ∖ {(1,1)}` on `0 = e₀`, `1 = e₁`. -/
def R11 {D : Type*} (e₀ e₁ : D) : Set (D × D) := {(e₀, e₀), (e₀, e₁), (e₁, e₀)}

/-- The disequality `≠` on `{0, 1} = {e₀, e₁}`. -/
def Ne2 {D : Type*} (e₀ e₁ : D) : Set (D × D) := {(e₀, e₁), (e₁, e₀)}

end MinCostMaj


