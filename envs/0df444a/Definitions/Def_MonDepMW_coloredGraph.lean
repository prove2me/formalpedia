-- Prove2me | Definitions.Def_MonDepMW_coloredGraph
-- name    : MonDepMW_coloredGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:02.33544+00:00
-- url     : https://prove2.me/theorems/c282b2e4-54d4-449e-8e84-2a4b9bef7068
-- title:
--   The signature of $k$-colored graphs and the structure $G^+$
-- statement:
--   First-order logic on graphs has the binary relation $\mathrm{adj}(x,y)$. A **$k$-colored graph** is a graph with $k$ unary predicates $U_1,\dots,U_k$, and a **$k$-coloring** (or expansion) $G^+$ of a graph $G$ interprets these predicates on $V(G)$; the predicates need not be disjoint. This item defines the signature, the structure $G^+=(G,c)$ with $U_i$ interpreted as $c(i)$, and the truth of a formula $\varphi(x,y)$ at a pair of vertices.
--
--   It is the logical layer of transductions, hence of monadic dependence.
--
--   **Formalization Note** The signature is a Mathlib `FirstOrder.Language` without function symbols. Equality is part of Mathlib's first-order logic. The free variables $x,y$ are `0, 1 : Fin 2`.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12

import Mathlib

set_option autoImplicit false

namespace MonDepMW

/-- The relation symbols of `k`-colored graphs: `adj` and the unary predicates `U₁, …, U_k`. -/
inductive ColoredRel (k : ℕ) : ℕ → Type
  | adj : ColoredRel k 2
  | col : Fin k → ColoredRel k 1

/-- **The signature of `k`-colored graphs.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "We use first-order logic on graphs, with adjacency
represented by the relation adj(x, y). For k ∈ N, a k-colored graph is a graph equipped with k unary predicates
U1, . . . , Uk." No function symbols. Equality is part of first-order logic in Mathlib. -/
def coloredGraph (k : ℕ) : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := ColoredRel k

/-- **The `k`-colored graph `G⁺ = (G, c)` as a first-order structure.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "A k-coloring, or expansion,
G+ of a graph G assigns interpretations of these predicates on V (G); the predicates need not be disjoint."
`c i` is the interpretation of `U_i`; the sets `c i` are arbitrary. -/
abbrev coloredStructure {k : ℕ} {V : Type*} (G : SimpleGraph V) (c : Fin k → Set V) :
    (coloredGraph k).Structure V where
  funMap := fun f _ => f.elim
  RelMap := fun {n} R xs =>
    match n, R, xs with
    | _, .adj, xs => G.Adj (xs 0) (xs 1)
    | _, .col i, xs => xs 0 ∈ c i

/-- `φ(u, v)` holds in the colored graph `(G, c)`; the free variables `x, y` of `φ(x, y)` are `0, 1 : Fin 2`. -/
def Holds {k : ℕ} {V : Type*} (φ : (coloredGraph k).Formula (Fin 2)) (G : SimpleGraph V)
    (c : Fin k → Set V) (u v : V) : Prop :=
  letI := coloredStructure G c
  φ.Realize ![u, v]

end MonDepMW


