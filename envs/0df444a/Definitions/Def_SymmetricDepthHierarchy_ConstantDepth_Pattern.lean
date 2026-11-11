-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
-- name    : SymmetricDepthHierarchy_ConstantDepth_Pattern
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:30:59.282537+00:00
-- url     : https://prove2.me/theorems/38bd0833-87b9-40f3-9b0b-04f1c278bb40
-- title:
--   Patterns, homomorphism polynomials $\mathrm{hom}_{F,n}$, the span $H_N(\mathcal F)$ and the full tree $T_{\Delta,k}$
-- statement:
--   A **pattern** is a finite bipartite multigraph $F$ with a fixed bipartition $A\uplus B$ (isolated vertices and parallel edges allowed). For $n\ge 1$ its $n$-th **homomorphism polynomial** is
--   $$\mathrm{hom}_{F,n}(X)=\sum_{\substack{h_A:A\to[n]\\ h_B:B\to[n]}}\ \prod_{ab\in E(F)}x_{h_A(a),h_B(b)},$$
--   the product counting edges with multiplicity. The underlying simple graph of $F$ forgets multiplicities; $|V(F)|=|A|+|B|$ and $|E(F)|$ counts edges with multiplicity.
--
--   For a class $\mathcal F$ of simple graphs and $N\ge1$, $H_N(\mathcal F)$ is the $K$-linear span of the polynomials $\mathrm{hom}_{F,N}$ for all bipartite multigraphs $F$ whose underlying simple graph lies in $\mathcal F$.
--
--   The **full $k$-ary tree** $T_{\Delta,k}$ of depth $\Delta$ has as vertices all words of length $0,\dots,\Delta$ over a $k$-letter alphabet, each word adjacent to its one-letter extensions; the root is the empty word. As a pattern, its left side consists of the words of even length (containing the root) and its right side of those of odd length.
--
--   These are the polynomials of the characterisation (Theorem 3.5) and the goal polynomial $\mathrm{hom}_{T_{\Delta,n},n}$.
--
--   **Formalization Note.** A pattern consists of finite types $A,B$ and multiplicities $\mathrm{mult}(a,b)\in\mathbb N$; the product is $\prod_{a,b}x_{h_A(a),h_B(b)}^{\mathrm{mult}(a,b)}$. Finite simple graphs are `FinGraph`s, graph classes are sets of them. A word of length $j$ is a vector `List.Vector (Fin k) j`.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), §2.4, p. 8 (PDF p. 11); definition of H_N after Theorem 3.7, p. 11 (PDF p. 14); Theorem 3.1, p. 9 (PDF p. 12)

import Mathlib

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# Patterns, homomorphism polynomials, graph classes and the full `k`-ary tree

STOC 2027 submission #1521, §2.4 (printed p. 8, PDF p. 11), the span `H_N(𝓕)` after Theorem 3.7
(printed p. 11, PDF p. 14), and the full `k`-ary tree `T_{Δ,k}` of Theorem 3.1 / Example 3.4.

* A *pattern* is a finite bipartite multigraph `F` with a fixed bipartition `A ⊎ B`: finite types
  `A`, `B` and an edge multiplicity `mult a b ∈ ℕ` for every `a ∈ A`, `b ∈ B` (isolated vertices
  and parallel edges allowed).
* `hom_{F,n}(X) = ∑_{h_A : A → [n], h_B : B → [n]} ∏_{ab ∈ E(F)} x_{h_A(a), h_B(b)}`, the
  product counting edges with multiplicity.
* A finite simple graph is a `FinGraph`; a graph class is a set of `FinGraph`s.
-/

/-- A finite simple graph. -/
structure FinGraph where
  V : Type
  [fintype : Fintype V]
  [decEq : DecidableEq V]
  G : SimpleGraph V

attribute [instance] FinGraph.fintype FinGraph.decEq

/-- A class of finite simple graphs. -/
abbrev GraphClass := Set FinGraph

/-- A pattern: a finite bipartite multigraph with fixed bipartition `A ⊎ B`;
`mult a b` is the number of edges between `a ∈ A` and `b ∈ B`. -/
structure Pattern where
  A : Type
  B : Type
  [fintypeA : Fintype A]
  [fintypeB : Fintype B]
  [decEqA : DecidableEq A]
  [decEqB : DecidableEq B]
  mult : A → B → ℕ

attribute [instance] Pattern.fintypeA Pattern.fintypeB Pattern.decEqA Pattern.decEqB

namespace Pattern

/-- The `n`-th homomorphism polynomial `hom_{F,n} ∈ K[X_n]` (edges counted with multiplicity). -/
def homPoly (K : Type) [Field K] (F : Pattern) (n : ℕ) : MvPolynomial (Fin n × Fin n) K :=
  ∑ hA : F.A → Fin n, ∑ hB : F.B → Fin n,
    ∏ a : F.A, ∏ b : F.B, (MvPolynomial.X (hA a, hB b)) ^ F.mult a b

/-- The underlying simple graph of `F` on `A ⊕ B` (edge multiplicities forgotten). -/
def graph (F : Pattern) : SimpleGraph (F.A ⊕ F.B) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl a, Sum.inr b => 0 < F.mult a b
    | _, _ => False

/-- The underlying simple graph of `F` as a member of the universe of finite graphs. -/
def toFinGraph (F : Pattern) : FinGraph := ⟨F.A ⊕ F.B, F.graph⟩

/-- The number of vertices `|V(F)| = |A| + |B|`. -/
def numVertices (F : Pattern) : ℕ := Fintype.card F.A + Fintype.card F.B

/-- The number of edges `|E(F)|`, counted with multiplicity. -/
def numEdges (F : Pattern) : ℕ := ∑ a : F.A, ∑ b : F.B, F.mult a b

end Pattern

/-- `H_N(𝓕)`: the `K`-linear span of the homomorphism polynomials `hom_{F,N}` of all bipartite
multigraphs `F` whose underlying simple graph is in `𝓕`. -/
def homSpan (K : Type) [Field K] (N : ℕ) (𝓕 : GraphClass) :
    Submodule K (MvPolynomial (Fin N × Fin N) K) :=
  Submodule.span K {p | ∃ F : Pattern, F.toFinGraph ∈ 𝓕 ∧ p = F.homPoly K N}

/-! ### The full `k`-ary tree of depth `Δ` -/

/-- The vertices of `T_{Δ,k}`: all words of length `0, …, Δ` over the alphabet `Fin k`
(a word of length `j` is a vector `List.Vector (Fin k) j`). -/
abbrev TreeVertex (Δ k : ℕ) : Type := Σ j : Fin (Δ + 1), List.Vector (Fin k) j

/-- The full `k`-ary tree `T_{Δ,k}` of depth `Δ`: every word is adjacent to its one-letter
extensions; the root is the empty word. -/
def fullTree (Δ k : ℕ) : SimpleGraph (TreeVertex Δ k) :=
  SimpleGraph.fromRel fun u v => ∃ a : Fin k, v.2.toList = u.2.toList ++ [a]

/-- `T_{Δ,k}` as a finite graph. -/
def fullTreeGraph (Δ k : ℕ) : FinGraph := ⟨TreeVertex Δ k, fullTree Δ k⟩

/-- `T_{Δ,k}` as a pattern: left side the words of even length (containing the root), right side
the words of odd length, one edge between a word and each of its one-letter extensions. -/
def treePattern (Δ k : ℕ) : Pattern where
  A := {v : TreeVertex Δ k // Even v.1.val}
  B := {v : TreeVertex Δ k // ¬ Even v.1.val}
  mult a b := if (fullTree Δ k).Adj a.1 b.1 then 1 else 0

end SymmetricDepthHierarchy.ConstantDepth


