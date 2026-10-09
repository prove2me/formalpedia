-- Prove2me | Definitions.Def_NicerEars_TJoin_Ears
-- name    : NicerEars_TJoin_Ears
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:44.317986+00:00
-- url     : https://prove2.me/theorems/d6baaa8b-4570-48a9-bd07-2aa5cbfe511b
-- title:
--   §2, pp. 6–8 — ears, ear-decompositions, ϕ(G), pendant, short and clean ears, nice ear-decompositions
-- statement:
--   (Sebő–Vygen, §2, p. 6.) An **ear** of $G$ is a path or circuit $P$ of $G$ of length $l=|E(P)|\ge1$, given by its vertex sequence $v_0,\dots,v_l$ and its distinct edges $e_1,\dots,e_l$ with $e_i$ joining $v_{i-1}$ and $v_i$; the vertices are distinct except that $v_0=v_l$ is allowed (a **closed ear**); otherwise the ear is **open**. Its **internal vertices** $\mathrm{in}(P)$ are $v_1,\dots,v_{l-1}$.
--
--   An **ear-decomposition** of $G$ is a sequence $P_0,P_1,\dots,P_k$ where $P_0$ is a single vertex and, for each $i\ge1$, either $P_i$ is a circuit sharing exactly one vertex with $V(P_0)\cup\dots\cup V(P_{i-1})$, or $P_i$ is a path sharing exactly its two different endpoints with it; the ears $P_1,\dots,P_k$ partition $E(G)$ and together with $P_0$ cover $V(G)$.
--
--   1. $P$ is an **$l$-ear** if $|E(P)|=l$; **nontrivial** if $l>1$; **short** if $l\in\{2,3\}$; **even** if $l$ is even, and $\varphi(P)=1$ if $P$ is even, $\varphi(P)=0$ otherwise.
--   2. $P$ is **attached** to $Q$ (at $q$) if $q\in\mathrm{in}(Q)$ is an endpoint of $P$. An ear is **pendant** if it is nontrivial and no nontrivial ear is attached to it; $\pi$ is the number of pendant ears and $\pi_2$ the number of 2-ears.
--   3. $\varphi(G)$ is the minimum number of even ears in an ear-decomposition of a 2-edge-connected graph $G$ (Frank 1993).
--   4. (p. 7) $\gamma(P)=1$ if $P$ is short and $\mathrm{in}(P)\cap T=\emptyset$, and $\gamma(P)=0$ otherwise.
--   5. (Definition 9, p. 8) An ear-decomposition is **nice** if (i) its number of even ears is $\varphi(G)$; (ii) all short ears are pendant; (iii) internal vertices of different short ears are non-adjacent in $G$.
--   6. Given $T$, an ear is **clean** if it is short and $\mathrm{in}(P)\cap T=\emptyset$; the **eardrum associated with** the ear-decomposition and $T$ is the set of components of the subgraph induced by the internal vertices of the clean ears.
--
--   These are the combinatorial objects on which the upper-bound constructions of the paper rest.
--
--   **Formalization Note.** Ears are indexed by `Fin k` (the paper's $P_1,\dots,P_k$) and the vertex sequence by `Fin (l+1)`. $\varphi(G)$ is an infimum over ear-decompositions and is $0$ when none exists; every statement using it assumes 2-edge-connectivity or supplies an ear-decomposition. The associated eardrum is formalized as the family of internal vertex sets of the clean ears; for a nice ear-decomposition these are exactly the components named in Definition 9 (the paper's remark on p. 9), and every statement using it assumes niceness.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, §2, p. 6 (ears, ear-decompositions, pendant, ϕ), p. 7 (γ(P)), p. 8 (Definition 9)

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

namespace NicerEars.TJoin

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- §2, p. 6: an ear of `G`, given by its vertex sequence `v₀, …, v_l` and edge sequence
`e₁, …, e_l` (`l ≥ 1`) with `ends eᵢ = {vᵢ₋₁, vᵢ}`. The edges are distinct; the vertices are distinct
except that `v₀ = v_l` is allowed (a closed ear, i.e. a circuit). Otherwise it is a path. -/
structure Ear (G : Graph V E) where
  len : ℕ
  len_pos : 0 < len
  vert : Fin (len + 1) → V
  edge : Fin len → E
  link : ∀ i : Fin len, G.ends (edge i) = s(vert i.castSucc, vert i.succ)
  edge_inj : Function.Injective edge
  vert_inj : ∀ i j, vert i = vert j →
    i = j ∨ (i = 0 ∧ j = Fin.last len) ∨ (i = Fin.last len ∧ j = 0)

namespace Ear

variable {G : Graph V E}

/-- The first endpoint `v₀`. -/
def first (P : Ear G) : V := P.vert 0

/-- The last endpoint `v_l`. -/
def last (P : Ear G) : V := P.vert (Fin.last P.len)

/-- An open ear (a path): its two endpoints differ. -/
def IsOpen (P : Ear G) : Prop := P.first ≠ P.last

/-- `V(P)`. -/
def verts (P : Ear G) : Finset V := univ.image P.vert

/-- `in(P)`: the internal vertices `v₁, …, v_{l-1}`. -/
def inner (P : Ear G) : Finset V :=
  (univ.filter (fun i : Fin (P.len + 1) => 0 < i.val ∧ i.val < P.len)).image P.vert

/-- `E(P)`. -/
def edges (P : Ear G) : Finset E := univ.image P.edge

/-- An even ear: `|E(P)|` is even (ϕ(P) = 1, p. 6). -/
def IsEven (P : Ear G) : Prop := Even P.len

/-- A nontrivial ear: length at least 2 (p. 6). -/
def IsNontrivial (P : Ear G) : Prop := 1 < P.len

/-- A short ear: a 2-ear or a 3-ear (p. 6). -/
def IsShort (P : Ear G) : Prop := P.len = 2 ∨ P.len = 3

/-- ϕ(P) (p. 6): `1` if `|E(P)|` is even, `0` if it is odd. -/
def phiEar (P : Ear G) : ℕ := if Even P.len then 1 else 0

open Classical in
/-- γ(P) (p. 7): `1` if `P` is short and `in(P) ∩ T = ∅`, `0` otherwise. -/
noncomputable def gamma (P : Ear G) (T : Finset V) : ℕ :=
  if P.IsShort ∧ Disjoint P.inner T then 1 else 0

end Ear

/-- §2, p. 6: an ear-decomposition `P₀, P₁, …, P_k` of `G`. `P₀` is the single vertex `root`; the
ears `P₁, …, P_k` are `ear 0, …, ear (k-1)`. Every ear meets the vertices of the earlier ears (and
`root`) exactly in its endpoints (one endpoint if closed, two different ones if open), the edge sets
of the ears partition `E(G)`, and the ears cover `V(G)`. -/
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

open Classical in
/-- The number of even ears of the ear-decomposition. -/
noncomputable def numEven (D : EarDecomposition G) : ℕ := #(univ.filter (fun i => (D.ear i).IsEven))

open Classical in
/-- π₂: the number of 2-ears. -/
noncomputable def num2Ears (D : EarDecomposition G) : ℕ := #(univ.filter (fun i => (D.ear i).len = 2))

/-- p. 6: ear `j` is attached to ear `i` (at `q`): some `q ∈ in(Pᵢ)` is an endpoint of `Pⱼ`. -/
def Attached (D : EarDecomposition G) (j i : Fin D.k) : Prop :=
  ∃ q ∈ (D.ear i).inner, q = (D.ear j).first ∨ q = (D.ear j).last

/-- p. 6: ear `i` is pendant: it is nontrivial and no nontrivial ear is attached to it. -/
def IsPendant (D : EarDecomposition G) (i : Fin D.k) : Prop :=
  (D.ear i).IsNontrivial ∧ ∀ j, (D.ear j).IsNontrivial → ¬ D.Attached j i

open Classical in
/-- π: the number of pendant ears. -/
noncomputable def numPendant (D : EarDecomposition G) : ℕ := #(univ.filter (fun i => D.IsPendant i))

/-- Definition 9 (p. 8), (iii): the ear-decomposition has internal vertices of different short ears
pairwise non-adjacent in `G`. -/
def ShortEarsNonadjacent (D : EarDecomposition G) : Prop :=
  ∀ i j, i ≠ j → (D.ear i).IsShort → (D.ear j).IsShort →
    ∀ u ∈ (D.ear i).inner, ∀ w ∈ (D.ear j).inner, ¬ (G.spanGraph univ).Adj u w

/-- p. 8, Definition 9 (given `G` and `T`, p. 8): ear `i` is clean if it is short and
`in(Pᵢ) ∩ T = ∅`. -/
def IsClean (D : EarDecomposition G) (T : Finset V) (i : Fin D.k) : Prop :=
  (D.ear i).IsShort ∧ Disjoint (D.ear i).inner T

open Classical in
/-- Definition 9 (p. 8): the eardrum associated with the ear-decomposition and `T`, given as the
family of internal-vertex sets of the clean ears. For a nice ear-decomposition these sets are
exactly the components of the subgraph induced by the internal vertices of the clean ears (p. 9,
"Another way of saying (iii)"). -/
noncomputable def eardrumOf (D : EarDecomposition G) (T : Finset V) : Finset (Finset V) :=
  (univ.filter (fun i => D.IsClean T i)).image (fun i => (D.ear i).inner)

end EarDecomposition

/-- ϕ(G) (p. 6): the minimum number of even ears in an ear-decomposition of `G`. It is only
meaningful when `G` has an ear-decomposition, i.e. when `G` is 2-edge-connected (`0` otherwise). -/
noncomputable def phi (G : Graph V E) : ℕ :=
  sInf {n | ∃ D : EarDecomposition G, D.numEven = n}

/-- Definition 9 (p. 8): a nice ear-decomposition: (i) the number of even ears is ϕ(G); (ii) all short
ears are pendant; (iii) internal vertices of different short ears are non-adjacent in `G`. -/
def EarDecomposition.IsNice {G : Graph V E} (D : EarDecomposition G) : Prop :=
  D.numEven = phi G ∧ (∀ i, (D.ear i).IsShort → D.IsPendant i) ∧ D.ShortEarsNonadjacent

end NicerEars.TJoin


