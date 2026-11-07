-- Prove2me | Definitions.Def_MonDepMW_MonadicallyDependent
-- name    : MonDepMW_MonadicallyDependent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:42.304295+00:00
-- url     : https://prove2.me/theorems/e3fb177d-96b8-4005-a534-8fe3ce65ef66
-- title:
--   Transductions and monadic dependence (Definition 3.1)
-- statement:
--   For a $k$-colored graph $H$ and a formula $\varphi(x,y)$, the graph $\varphi(H)$ has vertex set $V(H)$, and distinct vertices $u,v$ are adjacent iff $\varphi(u,v)\vee\varphi(v,u)$ holds in $H$.
--
--   A graph class $\mathcal C$ **transduces** a class $\mathcal D$ if there are $k$ and a formula $\varphi(x,y)$ in the signature of $k$-colored graphs such that every $H\in\mathcal D$ is an induced subgraph of $\varphi(G^+)$ for some $G\in\mathcal C$ and some $k$-coloring $G^+$ of $G$. A class is **monadically dependent** if it does not transduce the class of all graphs.
--
--   Monadic dependence is the class this mission is about; the goal theorem bounds the merge-width of every such class.
--
--   **Formalization Note** A class is a family of sets of graphs on `Fin n`, with no closure under isomorphism assumed. Induced subgraphs are embeddings `↪g`, which reflect adjacency. Allowing $k=0$ changes nothing, as a $0$-coloring is a $1$-coloring with an unused color.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12, Definition 3.1

import Mathlib
import Definitions.Def_MonDepMW_coloredGraph

set_option autoImplicit false

namespace MonDepMW

/-- **The graph `φ(G⁺)`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "define φ(H) to be the graph with vertex set V (H) in which distinct
vertices u, v are adjacent if and only if φ(u, v)∨φ(v, u) holds in H." -/
def interp {k : ℕ} {V : Type*} (φ : (coloredGraph k).Formula (Fin 2)) (G : SimpleGraph V)
    (c : Fin k → Set V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (Holds φ G c u v ∨ Holds φ G c v u)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **Graph classes.** A class is given by its members on each vertex set `Fin n`.

**Formalization Note.** No closure under isomorphism is assumed. Every finite graph is isomorphic to one on some
`Fin n`, and a class of the paper is represented by its members' copies on `Fin n`; monadic dependence and all the
quantities of this mission are isomorphism invariant. Graph classes are not assumed hereditary, as in the paper's
Theorem 1.1. -/
abbrev GraphClass := ∀ n : ℕ, Set (SimpleGraph (Fin n))

/-- **Transductions.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.12: "we say that C transduces D [...] if there are k ∈ N and a first-order formula
φ(x, y) in the signature of k-colored graphs such that every graph H ∈ D can be obtained from some graph G ∈ C by first
choosing a k-coloring G+ of G and then taking an induced subgraph of φ(G+)."

**Formalization Note.** `↪g` is an embedding that preserves and reflects adjacency, so its image is an induced
subgraph. `k = 0` is allowed: a `0`-coloring is a `1`-coloring with an unused color, so this changes nothing. -/
def Transduces (𝒞 𝒟 : GraphClass) : Prop :=
  ∃ (k : ℕ) (φ : (coloredGraph k).Formula (Fin 2)), ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ∈ 𝒟 m →
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Fin k → Set (Fin n)),
      G ∈ 𝒞 n ∧ Nonempty (H ↪g interp φ G c)

/-- **Definition 3.1.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.12: "A graph class C is monadically dependent if C does not transduce the class of all
graphs." -/
def MonadicallyDependent (𝒞 : GraphClass) : Prop :=
  ¬ Transduces 𝒞 (fun _ => Set.univ)

end MonDepMW


