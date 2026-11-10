-- Prove2me | Definitions.Def_SetDefinedGraphs_DigraphBasics
-- name    : SetDefinedGraphs_DigraphBasics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:24:49.392408+00:00
-- url     : https://prove2.me/theorems/e53f9a11-013a-4941-81b4-7f19ee269d36
-- title:
--   Digraph basics: homomorphisms, clique number $\omega$, independent sets
-- statement:
--   Throughout, a **digraph** $G$ on a vertex set $W$ is a binary arc relation on $W$. This module fixes the elementary notions of §1.1 and §3 used by every statement of the mission.
--
--   1. A map $\varphi:V(G)\to V(H)$ is a **homomorphism** if $(u,w)\in E(G)$ implies $(\varphi(u),\varphi(w))\in E(H)$; $G$ is **homomorphic** to $H$ if a homomorphism exists.
--   2. The **clique number** $\omega(G)$ of a digraph is the clique number of its underlying graph (orientations and loops ignored).
--   3. A set $S$ is **independent** in $G$ if no arc has both endpoints in $S$.
--
--   Induced subdigraphs $G[S]$ (vertex set $S$, exactly the arcs of $G$ with both endpoints in $S$) and isomorphism of digraphs (a bijection preserving and reflecting arcs) are the published definitions `FASTournament.induce` and `FASTournament.Isomorphic`, which the mission references.
--
--   **Formalization Note** The underlying graph is Mathlib's `SimpleGraph.fromRel G.Adj` and $\omega$ is `cliqueNum`; every digraph to which the mission applies $\omega$ is finite, so the value is the true maximum clique size ($\omega$ of the empty digraph is $0$).
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.2 (homomorphism), §3 Preliminaries p.14 (homomorphism, ω of a digraph), p.3 (ω of a digraph)

import Mathlib

set_option autoImplicit false

namespace SetDefinedGraphs

/-- A map `φ : V(G) → V(H)` is a **homomorphism** from the digraph `G` to the digraph `H` if it maps arcs to arcs:
`(u, v) ∈ E(G)` implies `(φ u, φ v) ∈ E(H)` (arXiv:2607.23754, p.2 and p.14). -/
def IsHom {W W' : Type} (G : Digraph W) (H : Digraph W') (φ : W → W') : Prop :=
  ∀ a b, G.Adj a b → H.Adj (φ a) (φ b)

/-- `G` is **homomorphic** to `H` if there exists a homomorphism from `G` to `H` (arXiv:2607.23754, p.14). -/
def Homomorphic {W W' : Type} (G : Digraph W) (H : Digraph W') : Prop :=
  ∃ φ : W → W', IsHom G H φ

/-- The **clique number** `ω(G)` of a digraph `G`: the clique number of its underlying graph, the simple graph obtained
by ignoring orientations and loops (arXiv:2607.23754, p.3 and p.14).

**Formalization Note** The underlying graph is `SimpleGraph.fromRel G.Adj` (symmetrised, loops removed) and `ω` is
Mathlib's `cliqueNum`. Every digraph to which the mission applies `omega` is finite, so the supremum in `cliqueNum`
is attained and is not a junk value; `ω` of the empty digraph is `0`. -/
noncomputable def omega {W : Type} (G : Digraph W) : ℕ :=
  (SimpleGraph.fromRel G.Adj).cliqueNum

/-- A vertex set `S` is **independent** in a digraph `G` if no arc of `G` has both endpoints in `S`. -/
def IsIndependent {W : Type} (G : Digraph W) (S : Set W) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

end SetDefinedGraphs


