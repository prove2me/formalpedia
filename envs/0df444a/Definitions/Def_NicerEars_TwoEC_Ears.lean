-- Prove2me | Definitions.Def_NicerEars_TwoEC_Ears
-- name    : NicerEars_TwoEC_Ears
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:54.063116+00:00
-- url     : https://prove2.me/theorems/880863c3-8c94-4d0b-9de4-59482d5b5ed8
-- title:
--   §2, pp. 6–8 — ears, ear-decompositions, ϕ(G), pendant ears, nice ear-decompositions (Definition 9), clean ears, the associated eardrum
-- statement:
--   An **ear** of $G$ is a path or circuit given by vertices $v_0,v_1,\dots,v_l$ ($l\ge1$) and distinct edges $e_1,\dots,e_l$ with $e_i$ joining $v_{i-1}$ and $v_i$; the vertices are distinct except that $v_0=v_l$ is allowed (a closed ear). Its **length** is $l$, its **internal vertices** $\mathrm{in}(P)=\{v_1,\dots,v_{l-1}\}$. An $l$-ear with $l>1$ is **nontrivial**, it is **even** if $l$ is even, and 2-ears and 3-ears are **short**.
--
--   An **ear-decomposition** of $G$ is a vertex $P_0$ together with a sequence of ears $P_1,\dots,P_k$ such that every $P_i$ meets $V(P_0)\cup\dots\cup V(P_{i-1})$ exactly in its ends $v_0, v_l$, the edge sets of the ears partition $E(G)$, and the ears and $P_0$ cover $V(G)$. An ear $P$ is **attached** to an ear $Q$ (at $q$) if $q\in\mathrm{in}(Q)$ is an end of $P$; a nontrivial ear is **pendant** if no nontrivial ear is attached to it. $\pi$ denotes the number of pendant ears, and
--
--   $$\varphi(G)=\min\{\text{number of even ears of } D : D \text{ an ear-decomposition of } G\}.$$
--
--   The decomposition is **nice** (Definition 9) if (i) it has $\varphi(G)$ even ears, (ii) every short ear is pendant, and (iii) internal vertices of different short ears are non-adjacent in $G$. For $T\subseteq V(G)$ an ear is **clean** if it is short and $\mathrm{in}(P)\cap T=\emptyset$, and the **eardrum associated** with the decomposition and $T$ is the family of the sets $\mathrm{in}(P)$ of the clean ears.
--
--   These notions carry every construction of the paper's §5.
--
--   **Formalization Note** Ears are indexed by `Fin (len + 1)` (vertices) and `Fin len` (edges). $\varphi(G)$ is an infimum over ear-decompositions and is the junk value $0$ when $G$ has none; every statement using it assumes $G$ 2-edge-connected, which guarantees one. The paper defines the associated eardrum as the components of the subgraph induced by the internal vertices of the clean ears; under (iii) these components are exactly the internal-vertex sets of the clean ears, which is how the eardrum is encoded. Adjacency in (iii) is adjacency in $G$ regardless of edge multiplicity.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, §2, pp. 6–8 (ears, ϕ(G), pendant ears, Definition 9, clean ears and the associated eardrum)

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

namespace NicerEars.TwoEC

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §2, p. 6: an ear, as its vertex sequence v₀, …, v_l and edge sequence e₁, …, e_l (l ≥ 1) with
ends eᵢ = s(vᵢ₋₁, vᵢ). Edges are distinct; vertices are distinct except that v₀ = v_l is allowed
(a closed ear, i.e. a circuit). -/
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

/-- The first vertex v₀ of the ear. -/
def first (P : Ear G) : V := P.vert 0

/-- The last vertex v_l of the ear. -/
def last (P : Ear G) : V := P.vert (Fin.last P.len)

/-- An open ear (a path): its two ends differ. Otherwise the ear is closed (a circuit). -/
def IsOpen (P : Ear G) : Prop := P.first ≠ P.last

/-- V(P). -/
def verts (P : Ear G) : Finset V := univ.image P.vert

/-- in(P): the internal vertices v₁, …, v_{l−1}. -/
def inner (P : Ear G) : Finset V :=
  (univ.filter (fun i : Fin (P.len + 1) => 0 < i.val ∧ i.val < P.len)).image P.vert

/-- E(P). -/
def edges (P : Ear G) : Finset E := univ.image P.edge

/-- ϕ(P) = 1: the ear has even length (p. 6). -/
def IsEven (P : Ear G) : Prop := Even P.len

/-- An l-ear with l > 1 is nontrivial (p. 6). -/
def IsNontrivial (P : Ear G) : Prop := 1 < P.len

/-- Short ears are 2-ears and 3-ears (p. 6). -/
def IsShort (P : Ear G) : Prop := P.len = 2 ∨ P.len = 3

end Ear

/-- §2, p. 6: an ear-decomposition P₀, P₁, …, P_k: P₀ is the vertex `root`, every ear meets the
vertices of the earlier ones exactly in its endpoints, and the ears partition E(G) and cover V(G). -/
structure EarDecomposition (G : Graph V E) where
  root : V
  k : ℕ
  ear : Fin k → Ear G
  attach : ∀ i,
    (ear i).first ∈ insert root ((univ.filter (· < i)).biUnion (fun j => (ear j).verts)) ∧
    (ear i).last ∈ insert root ((univ.filter (· < i)).biUnion (fun j => (ear j).verts)) ∧
    Disjoint (ear i).inner (insert root ((univ.filter (· < i)).biUnion (fun j => (ear j).verts)))
  edge_part : ∀ e, ∃! i, e ∈ (ear i).edges
  vert_cover : ∀ v, v = root ∨ ∃ i, v ∈ (ear i).verts

namespace EarDecomposition

variable {G : Graph V E}

open Classical in
/-- The number of even ears of the decomposition, Σᵢ ϕ(Pᵢ) (p. 6). -/
noncomputable def numEven (D : EarDecomposition G) : ℕ :=
  #(univ.filter (fun i => (D.ear i).IsEven))

/-- Ear `j` is attached to ear `i` (at q): q ∈ in(Pᵢ) is an endpoint of Pⱼ (p. 6). -/
def Attached (D : EarDecomposition G) (j i : Fin D.k) : Prop :=
  ∃ q ∈ (D.ear i).inner, q = (D.ear j).first ∨ q = (D.ear j).last

/-- p. 6: an ear is pendant if it is nontrivial and no nontrivial ear is attached to it. -/
def IsPendant (D : EarDecomposition G) (i : Fin D.k) : Prop :=
  (D.ear i).IsNontrivial ∧ ∀ j, (D.ear j).IsNontrivial → ¬ D.Attached j i

open Classical in
/-- π: the number of pendant ears. -/
noncomputable def numPendant (D : EarDecomposition G) : ℕ :=
  #(univ.filter (fun i => D.IsPendant i))

open Classical in
/-- The union of the edge sets of the nontrivial ears. -/
noncomputable def nontrivialEdges (D : EarDecomposition G) : Finset E :=
  (univ.filter (fun i => (D.ear i).IsNontrivial)).biUnion (fun i => (D.ear i).edges)

end EarDecomposition

/-- p. 6: ϕ(G), the minimum number of even ears in an ear-decomposition of G. This is the junk
value 0 when G has no ear-decomposition; every statement using it assumes G 2-edge-connected. -/
noncomputable def Graph.phi (G : Graph V E) : ℕ :=
  sInf {n | ∃ D : EarDecomposition G, D.numEven = n}

namespace EarDecomposition

variable {G : Graph V E}

/-- Definition 9 (p. 8): a nice ear-decomposition: (i) it has ϕ(G) even ears; (ii) all short ears
are pendant; (iii) internal vertices of different short ears are non-adjacent in G. -/
def IsNice (D : EarDecomposition G) : Prop :=
  D.numEven = G.phi ∧
  (∀ i, (D.ear i).IsShort → D.IsPendant i) ∧
  ∀ i j, i ≠ j → (D.ear i).IsShort → (D.ear j).IsShort →
    ∀ u ∈ (D.ear i).inner, ∀ w ∈ (D.ear j).inner, ¬ (G.spanGraph univ).Adj u w

/-- p. 8: given T, an ear is clean if it is short and in(P) ∩ T = ∅. -/
def IsClean (D : EarDecomposition G) (T : Finset V) (i : Fin D.k) : Prop :=
  (D.ear i).IsShort ∧ Disjoint (D.ear i).inner T

open Classical in
/-- p. 8: the eardrum associated with the (nice) ear-decomposition and T: the internal-vertex sets
of the clean ears. Under (iii) these are exactly the components of the subgraph induced by the
internal vertices of the clean ears. -/
noncomputable def eardrumOf (D : EarDecomposition G) (T : Finset V) : Finset (Finset V) :=
  (univ.filter (fun i => D.IsClean T i)).image (fun i => (D.ear i).inner)

end EarDecomposition

end NicerEars.TwoEC


