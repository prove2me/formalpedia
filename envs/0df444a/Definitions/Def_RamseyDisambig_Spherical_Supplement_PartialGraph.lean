-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Supplement_PartialGraph
-- name    : RamseyDisambig_Spherical_Supplement_PartialGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:23:34.327427+00:00
-- url     : https://prove2.me/theorems/8e980794-ca8f-4b60-9511-062f5ea438b8
-- title:
--   Partial graphs, their disambiguations, VC-dimension and uniform fillings
-- statement:
--   A **partial graph** $G$ on a vertex set $V$ splits the unordered pairs of distinct vertices into 1-edges (edges), $\star$-edges and 0-edges (non-edges). Its adjacency matrix $A_G$ has $A_G[u,v]\in\{0,1,\star\}$ for $u\ne v$ and $\star$ on the diagonal. A **disambiguation** of $G$ is a graph $G'$ on $V$ that contains every edge of $G$ and no non-edge of $G$. The **VC-dimension** of $G$ is the partial-matrix VC-dimension of $A_G$, so a vertex never witnesses itself.
--
--   A set of three distinct vertices is a **pure** induced subgraph if its three pairs are specified, and it is **homogeneous** if the three specified values agree (a triangle or an independent triple). A graph $G'$ **contains every $k$-vertex graph as an induced subgraph** if every graph $F$ on $\{1,\dots,k\}$ has an induced embedding into $G'$.
--
--   For a partial graph $U$, casting all $\star$s into edges gives the graph in which distinct $u,v$ are adjacent unless $uv$ is a non-edge of $U$; casting them into non-edges gives the graph whose edges are exactly the edges of $U$. *No vertex of $U$ is incident to both an edge and a non-edge* is the condition of Lemma 19.
--
--   These notions are the vocabulary of Theorem 5 and Lemma 19.
--
--   **Formalization Note** A partial graph is a symmetric map `V → V → Option Bool` that is `none` on the diagonal, which is precisely its adjacency matrix with $\star$ on the diagonal; every partial graph has exactly one such representation. Induced embeddings are Mathlib's `F ↪g G'`.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §1, p. 5; §3.4, pp. 18–19 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Supplement_PartialVC

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- A partial graph on `V` (pp. 5, 18): every unordered pair of distinct vertices is a 1-edge
(`some true`), a ⋆-edge (`none`) or a 0-edge (`some false`). Stored as its adjacency matrix
with `⋆` on the diagonal (p. 5), so the encoding is symmetric and loopless; each partial graph
of the paper has exactly one such representation. -/
structure PartialGraph (V : Type*) where
  adj : V → V → Option Bool
  symm : ∀ u v, adj u v = adj v u
  diag : ∀ v, adj v v = none

/-- A disambiguation of a partial graph (p. 19): a graph `G'` on the same vertex set containing
every 1-edge and no 0-edge. -/
def IsGraphDisambiguation {V : Type*} (G : PartialGraph V) (G' : SimpleGraph V) : Prop :=
  ∀ u v, (G.adj u v = some true → G'.Adj u v) ∧ (G.adj u v = some false → ¬ G'.Adj u v)

/-- The VC-dimension of a partial graph: that of its adjacency matrix with `⋆` on the
diagonal (pp. 5, 19), so a vertex never witnesses itself. -/
def graphVCDim {V : Type*} (G : PartialGraph V) : ℕ∞ :=
  partialVCDim G.adj

/-- "Every pure induced subgraph of `G` on three vertices is homogeneous" (p. 5): for three
pairwise distinct vertices whose three pairs are all specified, the three values agree (the
triple is complete or edgeless). -/
def PureTriplesHomogeneous {V : Type*} (G : PartialGraph V) : Prop :=
  ∀ u v w : V, u ≠ v → u ≠ w → v ≠ w →
    ∀ a b c : Bool, G.adj u v = some a → G.adj u w = some b → G.adj v w = some c →
      a = b ∧ a = c

/-- `G'` contains every `k`-vertex graph as an induced subgraph: `SimpleGraph.Embedding`
(`↪g`) is an induced embedding (adjacency is reflected as well as preserved). -/
def ContainsAllInduced {V : Type*} (G' : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ F : SimpleGraph (Fin k), Nonempty (F ↪g G')

/-- "No vertex of `U` is incident to both an edge and a non-edge" (Lemma 19, p. 19). -/
def NoVertexMixed {V : Type*} (U : PartialGraph V) : Prop :=
  ∀ v u w : V, U.adj v u = some true → U.adj v w ≠ some false

/-- The graph obtained by casting every ⋆ of `U` into an edge (p. 19). -/
def castToEdges {V : Type*} (U : PartialGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ U.adj u v ≠ some false
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [U.symm]; exact h.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

/-- The graph obtained by casting every ⋆ of `U` into a non-edge (p. 19). -/
def castToNonEdges {V : Type*} (U : PartialGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ U.adj u v = some true
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [U.symm]; exact h.2⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

end RamseyDisambig.Spherical.Supplement


