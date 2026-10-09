-- Prove2me | Definitions.Def_NicerEars_TSP_Ears
-- name    : NicerEars_TSP_Ears
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:39.641759+00:00
-- url     : https://prove2.me/theorems/48a80511-28c1-45a2-8e4a-7168cbbf4a0f
-- title:
--   §2, pp. 6–8 — ears, ear-decompositions, even/short/pendant ears, ϕ(G), nice ear-decompositions, clean ears and the associated eardrum
-- statement:
--   This file fixes the ear-decomposition vocabulary of §2 of Sebő and Vygen's paper.
--
--   1. **Ears.** An *ear* $P$ of $G$ is either a path or a circuit, given by its vertex sequence $v_0,\dots,v_l$ and edge sequence $e_1,\dots,e_l$ ($l\ge 1$), where $e_i$ joins $v_{i-1}$ and $v_i$, the edges are distinct, and the vertices are distinct except that $v_0=v_l$ is allowed (a *closed* ear, i.e. a circuit). An *open* ear is a path. $l=|E(P)|$ is its *length*; an $l$-ear with $l>1$ is *nontrivial*; 2-ears and 3-ears are *short*; $P$ is *even* ($\varphi(P)=1$) if $l$ is even. The *internal vertices* $\mathrm{in}(P)$ are $v_1,\dots,v_{l-1}$.
--   2. **Ear-decompositions (p. 6).** An ear-decomposition of $G$ is a sequence $P_0,P_1,\dots,P_k$ where $P_0$ is a single vertex and each ear $P_i$ is either a circuit sharing exactly one vertex with $V(P_0)\cup\dots\cup V(P_{i-1})$ or a path sharing exactly its two distinct endpoints with it; the ears partition $E(G)$ and cover $V(G)$.
--   3. **Attached and pendant ears.** If $q\in\mathrm{in}(Q)$ is an endpoint of $P$, then $P$ is *attached* to $Q$ at $q$. An ear is *pendant* if it is nontrivial and no nontrivial ear is attached to it; $\pi$ denotes the number of pendant ears.
--   4. **$\varphi(G)$ (p. 6).** For a 2-edge-connected graph $G$, $\varphi(G)$ is the minimum number of even ears in an ear-decomposition of $G$.
--   5. **Nice ear-decompositions (Definition 9, p. 8).** An ear-decomposition is *nice* if (i) it has $\varphi(G)$ even ears; (ii) all short ears are pendant; (iii) internal vertices of different short ears are non-adjacent in $G$.
--   6. **Clean ears and the associated eardrum (p. 8).** Given $T\subseteq V(G)$, an ear is *clean* if it is short and $\mathrm{in}(P)\cap T=\emptyset$. The eardrum $M$ associated with the nice ear-decomposition and $T$ is the set of components of the subgraph induced by the internal vertices of the clean ears.
--
--   These are the structures on which all three approximation algorithms of the paper operate.
--
--   **Formalization Note.** An ear is stored with its vertex list indexed by $\{0,\dots,l\}$ and its edge list indexed by $\{1,\dots,l\}$ (shifted to $\{0,\dots,l-1\}$). The eardrum associated with a nice ear-decomposition is formalized as the family of the internal vertex sets of the clean ears; by condition (iii) of Definition 9 these sets are exactly the components of the induced subgraph described on p. 8 (the paper says so on p. 9). $\varphi(G)$ is an infimum of natural numbers; it would be $0$ for a graph without an ear-decomposition, so every statement using it assumes 2-edge-connectivity or supplies an ear-decomposition.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, pp. 6–8, §2 (ear-decompositions, §2.1 even and short ears), Definition 9 and the definition of clean ears and the associated eardrum

import Mathlib
import Definitions.Def_NicerEars_TSP_Setting

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §2, p. 6: an ear, as its vertex sequence v₀, …, v_l and edge sequence e₁, …, e_l (l ≥ 1) with
ends eᵢ = s(vᵢ₋₁, vᵢ). Edges are distinct; vertices are distinct except that v₀ = v_l is allowed
(a closed ear, i.e. a circuit). An open ear (v₀ ≠ v_l) is a path. -/
structure Ear (G : Graph V E) where
  len : ℕ
  len_pos : 0 < len
  vert : Fin (len + 1) → V
  edge : Fin len → E
  link : ∀ i : Fin len, G.ends (edge i) = s(vert i.castSucc, vert i.succ)
  edge_inj : Function.Injective edge
  vert_inj : ∀ i j, vert i = vert j → i = j ∨ ({i, j} : Set (Fin (len + 1))) = {0, Fin.last len}

namespace Ear

variable {G : Graph V E}

/-- The first vertex v₀. -/
def first (P : Ear G) : V := P.vert 0

/-- The last vertex v_l. -/
def last (P : Ear G) : V := P.vert (Fin.last P.len)

/-- An open ear (a path): its two ends differ. -/
def IsOpen (P : Ear G) : Prop := P.first ≠ P.last

/-- V(P). -/
def verts (P : Ear G) : Finset V := univ.image P.vert

/-- in(P): the internal vertices v₁, …, v_{l-1}. -/
def inner (P : Ear G) : Finset V :=
  (univ.filter (fun i : Fin (P.len + 1) => 0 < i.val ∧ i.val < P.len)).image P.vert

/-- E(P). -/
def edges (P : Ear G) : Finset E := univ.image P.edge

/-- ϕ(P) = 1: the length |E(P)| is even. -/
def IsEven (P : Ear G) : Prop := Even P.len

/-- An l-ear with l > 1 is nontrivial (p. 6). -/
def IsNontrivial (P : Ear G) : Prop := 1 < P.len

/-- 2-ears and 3-ears are short (p. 6). -/
def IsShort (P : Ear G) : Prop := P.len = 2 ∨ P.len = 3

end Ear

/-- §2, p. 6: an ear-decomposition P₀, P₁, …, P_k: P₀ is the vertex `root`, every ear meets the
vertices of the earlier ones exactly in its endpoints (a closed ear in one vertex, an open ear in
its two distinct ends), the ears partition E(G), and they cover V(G). -/
structure EarDecomposition (G : Graph V E) where
  root : V
  k : ℕ
  ear : Fin k → Ear G
  attach : ∀ i, let old := insert root ((univ.filter (· < i)).biUnion (fun j => (ear j).verts))
    (ear i).first ∈ old ∧ (ear i).last ∈ old ∧ Disjoint (ear i).inner old
  edge_part : ∀ e, ∃! i, e ∈ (ear i).edges
  vert_cover : ∀ v, v = root ∨ ∃ i, v ∈ (ear i).verts

namespace EarDecomposition

variable {G : Graph V E}

open scoped Classical in
/-- The number of even ears, Σᵢ ϕ(Pᵢ). -/
noncomputable def numEven (D : EarDecomposition G) : ℕ := #(univ.filter (fun i => (D.ear i).IsEven))

/-- Ear `j` is attached to ear `i` at `q` (p. 6): `q ∈ in(Pᵢ)` is an endpoint of `Pⱼ`. -/
def Attached (D : EarDecomposition G) (j i : Fin D.k) (q : V) : Prop :=
  q ∈ (D.ear i).inner ∧ ((D.ear j).first = q ∨ (D.ear j).last = q)

/-- p. 6: ear `i` is pendant if it is nontrivial and no nontrivial ear is attached to it. -/
def IsPendant (D : EarDecomposition G) (i : Fin D.k) : Prop :=
  (D.ear i).IsNontrivial ∧ ∀ j q, (D.ear j).IsNontrivial → ¬ D.Attached j i q

open scoped Classical in
/-- π: the number of pendant ears. -/
noncomputable def numPendant (D : EarDecomposition G) : ℕ := #(univ.filter (fun i => D.IsPendant i))

/-- p. 8: ear `i` is clean (for T) if it is short and `in(Pᵢ) ∩ T = ∅`. -/
def IsClean (D : EarDecomposition G) (T : Finset V) (i : Fin D.k) : Prop :=
  (D.ear i).IsShort ∧ Disjoint (D.ear i).inner T

open scoped Classical in
/-- p. 8: the eardrum associated with a nice ear-decomposition and T, as the family of internal
vertex sets of the clean ears. Under condition (iii) of Definition 9 these sets are exactly the
components of the subgraph induced by the internal vertices of the clean ears. -/
noncomputable def eardrumOf (D : EarDecomposition G) (T : Finset V) : Finset (Finset V) :=
  (univ.filter (fun i => D.IsClean T i)).image (fun i => (D.ear i).inner)

end EarDecomposition

/-- §2.1, p. 6: ϕ(G), the minimum number of even ears in an ear-decomposition of G. (Junk value 0
if G has no ear-decomposition; every statement using it assumes G 2-edge-connected.) -/
noncomputable def Graph.phi (G : Graph V E) : ℕ :=
  sInf {n | ∃ D : EarDecomposition G, D.numEven = n}

/-- Definition 9, p. 8: a nice ear-decomposition: (i) it has ϕ(G) even ears; (ii) all short ears
are pendant; (iii) internal vertices of different short ears are non-adjacent in G. -/
def EarDecomposition.IsNice {G : Graph V E} (D : EarDecomposition G) : Prop :=
  D.numEven = G.phi ∧
  (∀ i, (D.ear i).IsShort → D.IsPendant i) ∧
  ∀ i j, i ≠ j → (D.ear i).IsShort → (D.ear j).IsShort →
    ∀ u ∈ (D.ear i).inner, ∀ w ∈ (D.ear j).inner, ¬ (G.spanGraph univ).Adj u w

end NicerEars.TSP


