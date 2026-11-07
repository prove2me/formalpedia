-- Prove2me | Definitions.Def_GyoriLovasz_DG
-- name    : GyoriLovasz_DG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:33.571856+00:00
-- url     : https://prove2.me/theorems/c08dc97b-f6a0-498b-bde7-0acccb44e99b
-- title:
--   Finite directed graph, vertex deletion, edge deletion, contraction of a pre-terminal, out-degree
-- statement:
--   A **finite directed graph** $G=(V,E)$ is given by a finite vertex set $V$ and a finite set $E\subseteq V\times V$ of directed edges whose endpoints lie in $V$; since $E$ is a set, there are no parallel edges. The vertices are drawn from an ambient type, so that a graph can lose vertices without changing type.
--
--   Three operations are used throughout the paper:
--
--   1. **Vertex deletion** $G\setminus\{x\}$ removes $x$ and every edge incident to $x$.
--   2. **Edge deletion** $G\setminus e$ removes the edge $e$ (and leaves $G$ unchanged if $e\notin E$).
--   3. **Contraction of a pre-terminal $p$ into a terminal $t$** (Definition 2.1): remove $p$, redirect every incoming edge $(x,p)$ to $(x,t)$, delete all outgoing edges of $p$, and remove duplicate edges.
--
--   The **out-degree** $d^+(x)=|N^+(x)|$ is the number of edges leaving $x$.
--
--   **Formalization Note** The contraction keeps only edges whose head is still a vertex; when $(p,t)$ is an edge and $p\neq t$ this removes nothing. Loops are excluded separately by the standing assumption `Std`.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), §2, p.14; Definition 2.1, p.14

import Mathlib

namespace GyoriLovasz

/-- **Finite directed graph.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), §2, p.14: a directed graph `G = (V, E)` with no parallel edges.

`verts` is the vertex set and `arcs` the edge set; `wf` says every arc has both endpoints in `verts`.

**Formalization Note.** `V` is an ambient type, so an instance can lose vertices with no change of
type. Arcs form a `Finset`, so parallel edges cannot occur. Loops are excluded separately by `Std`. -/
structure DG (V : Type*) where
  verts : Finset V
  arcs : Finset (V × V)
  wf : ∀ a ∈ arcs, a.1 ∈ verts ∧ a.2 ∈ verts

namespace DG

variable {V : Type*} [DecidableEq V]

/-- `G \ {x}`: delete the vertex `x` and every arc at `x` (§2, p.14; Algorithm 2, line 4). -/
def deleteVertex (G : DG V) (x : V) : DG V where
  verts := G.verts.erase x
  arcs := G.arcs.filter fun a => a.1 ≠ x ∧ a.2 ≠ x
  wf := by
    intro a ha
    obtain ⟨ha, h1, h2⟩ := Finset.mem_filter.mp ha
    exact ⟨Finset.mem_erase.mpr ⟨h1, (G.wf a ha).1⟩, Finset.mem_erase.mpr ⟨h2, (G.wf a ha).2⟩⟩

/-- `G \ e`: delete the arc `e` (p.24). If `e` is not an arc, the graph is unchanged. -/
def deleteArc (G : DG V) (e : V × V) : DG V where
  verts := G.verts
  arcs := G.arcs.erase e
  wf := fun a ha => G.wf a (Finset.mem_of_mem_erase ha)

/-- **Contracting the pre-terminal `p` into the terminal `t`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e),
Definition 2.1, p.14: "removing p, redirecting every incoming edge of p to t, deleting all outgoing
edges of p, and removing any duplicate directed edges created by this redirection."

**Formalization Note.** The image in a `Finset` removes duplicates. The final filter only keeps `wf`
total: it removes nothing when `(p, t)` is an arc and `p ≠ t`. On graphs satisfying `Std` no loop and
no arc out of a terminal arises, because `t` has no outgoing arc. -/
def contract (G : DG V) (p t : V) : DG V where
  verts := G.verts.erase p
  arcs := ((G.arcs.filter fun a => a.1 ≠ p).image fun a => (a.1, if a.2 = p then t else a.2)).filter
    fun a => a.2 ∈ G.verts.erase p
  wf := by
    intro a ha
    obtain ⟨ha, h2⟩ := Finset.mem_filter.mp ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, h1⟩ := Finset.mem_filter.mp hb
    exact ⟨Finset.mem_erase.mpr ⟨h1, (G.wf b hb).1⟩, h2⟩

/-- The out-degree `d⁺(x) = |N⁺(x)|` (§2, p.14). -/
def outDeg (G : DG V) (x : V) : ℕ := (G.arcs.filter fun a => a.1 = x).card

end DG

end GyoriLovasz


