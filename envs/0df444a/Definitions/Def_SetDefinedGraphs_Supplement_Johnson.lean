-- Prove2me | Definitions.Def_SetDefinedGraphs_Supplement_Johnson
-- name    : SetDefinedGraphs_Supplement_Johnson
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:42:04.980231+00:00
-- url     : https://prove2.me/theorems/51f9ab5d-ec24-439f-8002-bff0b113d00a
-- title:
--   Generalized Johnson graphs $J(d,A)$, shift graphs $S_D$, and $\chi$-boundedness of graph classes
-- statement:
--   Let $d\in\mathbb N$ and $A\subseteq[0,d-1]$. The class $J(d,A)$ of **$(d,A)$-generalized Johnson graphs** consists of all finite graphs admitting an assignment of a set $S_v$ of size $d$ to each vertex $v$, all assigned sets distinct, such that distinct vertices $u,v$ are adjacent if and only if $|S_u\cap S_v|\in A$. Kneser graphs, Johnson graphs and line graphs of $k$-uniform hypergraphs are examples.
--
--   A **$D$-dimensional shift graph** is a graph isomorphic to an induced subgraph of the canonical shift graph $S(n,D)$, the underlying graph of $\vec S(n,D)$; $S_D$ denotes the class of these graphs, and $S_D\subseteq\mathcal X$ means that every $D$-dimensional shift graph is in $\mathcal X$. A graph class is **$\chi$-bounded** if $\chi(G)\le h(\omega(G))$ for some $h:\mathbb N\to\mathbb N$ and all its members, and **$\chi$-unbounded** otherwise.
--
--   **Formalization Note** The sets $S_v$ are finite sets of natural numbers; a finite graph needs only finitely many ground elements, so the choice of ground set does not matter. $\chi$ and $\omega$ are Mathlib's `chromaticNumber` and `cliqueNum`.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.5 (PDF p.7) and §8.2 p.76 (PDF p.78): J(d, A); §1.1 p.2 (PDF p.4) and §3.2 p.15 (PDF p.17): S(n, d), S_d; p.3 (PDF p.5): χ-bounded

import Mathlib
import Definitions.Def_FASTournament_induce
import Definitions.Def_SetDefinedGraphs_ShiftDigraph

set_option autoImplicit false

namespace SetDefinedGraphs.Supplement

/-- A **class of (undirected) graphs**: a predicate on simple graphs over arbitrary vertex types. -/
abbrev GraphClass : Type 1 := ∀ (W : Type), SimpleGraph W → Prop

/-- A class `X` of graphs is **χ-bounded** (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes:
χ-boundedness meets tropical algebra*, arXiv:2607.23754 (held version, sha256 642c0d70…), p.3 and §3.5 p.18) if there
is `h : ℕ → ℕ` with `χ(G) ≤ h(ω(G))` for every `G ∈ X`; it is **χ-unbounded** otherwise.

**Formalization Note** `χ` and `ω` are Mathlib's `chromaticNumber` (in `ℕ∞`) and `cliqueNum`. The paper quantifies over
induced subgraphs of members; the classes the mission applies this to are hereditary and contain only finite graphs. -/
def IsChiBoundedGraphClass (C : GraphClass) : Prop :=
  ∃ h : ℕ → ℕ, ∀ (W : Type) (G : SimpleGraph W), C W G → G.chromaticNumber ≤ (h G.cliqueNum : ℕ∞)

/-- The class `J(d, A)` of **`(d, A)`-generalized Johnson graphs** (arXiv:2607.23754, §1.1 p.5, PDF p.7; §8.2 p.76):
all graphs admitting an assignment of a set `S_v` of size `d` to each vertex `v`, all assigned sets distinct, such that
distinct vertices `u, v` are adjacent iff `|S_u ∩ S_v| ∈ A`.

**Formalization Note** Graphs are finite (`Finite W`), as everywhere in the paper; the sets `S_v` are finite sets of
natural numbers (a finite graph uses finitely many ground elements, so the ground set is immaterial). -/
def InJohnson (d : ℕ) (A : Set ℕ) (W : Type) (G : SimpleGraph W) : Prop :=
  Finite W ∧ ∃ S : W → Finset ℕ, Function.Injective S ∧ (∀ v, (S v).card = d) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (S u ∩ S v).card ∈ A)

/-- `G` is a **`D`-dimensional shift graph** (`G ∈ S_D`, arXiv:2607.23754, §1.1 p.2 and §3.2 p.15): it is isomorphic
to the underlying graph of an induced subdigraph of the canonical shift digraph `S⃗(n, D)` for some `n`, i.e. to an
induced subgraph of the canonical shift graph `S(n, D)`. -/
def IsShiftGraphDim (D : ℕ) {W : Type} (G : SimpleGraph W) : Prop :=
  ∃ n : ℕ, ∃ S : Set (ShiftVertex n D),
    Nonempty (G ≃g SimpleGraph.fromRel (FASTournament.induce (shiftDigraph n D) S).Adj)

/-- A graph class `X` **contains `S_D`** (`S_D ⊆ X`, arXiv:2607.23754, p.5): every `D`-dimensional shift graph is
in `X`. -/
def ContainsShiftGraphs (D : ℕ) (C : GraphClass) : Prop :=
  ∀ (W : Type) (G : SimpleGraph W), IsShiftGraphDim D G → C W G

end SetDefinedGraphs.Supplement


