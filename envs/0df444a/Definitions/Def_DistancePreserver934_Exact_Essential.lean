-- Prove2me | Definitions.Def_DistancePreserver934_Exact_Essential
-- name    : DistancePreserver934_Exact_Essential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:56.981412+00:00
-- url     : https://prove2.me/theorems/195929aa-b028-471b-aa4f-a37f30018594
-- title:
--   §3 and Definition 8 — essential edges, private edges, private lengths, demand cover
-- statement:
--   Let $H$ be a graph on $V$ and $R$ a set of unordered demand pairs. A walk is **shortest** if its length equals the distance of its ends.
--
--   1. An edge $e$ is **essential** to $q=\{s,t\}$ in $H$ if every shortest $s$–$t$ walk in $H$ contains $e$.
--   2. $D_H^R(e)=\{q\in R: e \text{ is essential to } q \text{ in } H\}$.
--   3. The **private edges** are $\Lambda_H=\{e\in E_H:|D_H^R(e)|=1\}$; for a demand $q$, $\Lambda_H(q)=\{e\in E_H: D_H^R(e)=\{q\}\}$, and the **private length** of $q$ is $\lambda_H(q)=|\Lambda_H(q)|$ (it counts private edges, not the length of a shortest path).
--   4. (Definition 8, demand cover) A vertex $x$ **covers** a demand $q$ if $x$ is an endpoint of an edge of $H$ essential to $q$; a vertex set $S$ **covers** $Q$ if every $q\in Q$ is covered by some vertex of $S$.
--
--   The paper's shorthand $D(e)=q$ means $D(e)=\{q\}$. Essentiality of an edge to a fixed demand depends on $H$; $D_H^R(e)$, private edges and private lengths depend on both $H$ and $R$ and are recomputed whenever either changes.
--
--   **Formalization Note** "Every shortest path" is quantified over all walks of minimal length (these are automatically paths). For an unreachable pair there is no shortest walk, so essentiality is vacuous; this is why the theorems carry the paper's standing assumption that demands are reachable pairs of distinct vertices.
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, §3 Essential Edges and Node Cover of Demands, printed p. 9 (PDF p. 10); §5 opening paragraph and Definition 8, printed p. 13 (PDF p. 14)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers

namespace DistancePreserver934.Exact

open Classical

variable {V : Type} [Fintype V]

/-- A walk is a shortest walk when its length equals the (extended) distance of its ends. -/
def IsShortest {H : SimpleGraph V} {s t : V} (w : H.Walk s t) : Prop :=
  (w.length : ℕ∞) = H.edist s t

/-- The edge `e` is essential to the demand `q = {s,t}` in `H` (§3): every shortest `s`–`t` walk
in `H` contains `e` (both orientations of `q` are quantified; they are equivalent). -/
def IsEssential (H : SimpleGraph V) (q e : Sym2 V) : Prop :=
  ∀ s t : V, s(s, t) = q → ∀ w : H.Walk s t, IsShortest w → e ∈ w.edges

/-- `D_H^R(e) = {q ∈ R : e is essential to q in H}`. -/
noncomputable def essSet (H : SimpleGraph V) (R : Finset (Sym2 V)) (e : Sym2 V) :
    Finset (Sym2 V) :=
  R.filter (fun q => IsEssential H q e)

/-- `Λ_H = {e ∈ E_H : |D(e)| = 1}`, the private edges. -/
noncomputable def privEdges (H : SimpleGraph V) (R : Finset (Sym2 V)) : Finset (Sym2 V) :=
  (edgesF H).filter (fun e => (essSet H R e).card = 1)

/-- `Λ_H(q) = {e ∈ Λ_H : D(e) = {q}}`. -/
noncomputable def privOf (H : SimpleGraph V) (R : Finset (Sym2 V)) (q : Sym2 V) :
    Finset (Sym2 V) :=
  (edgesF H).filter (fun e => essSet H R e = {q})

/-- The private length `λ_H(q) = |Λ_H(q)|`. -/
noncomputable def privLen (H : SimpleGraph V) (R : Finset (Sym2 V)) (q : Sym2 V) : ℕ :=
  (privOf H R q).card

/-- Definition 8 (demand cover): `S` covers `Q` in `H` if every `q ∈ Q` has a vertex `x ∈ S`
incident to an edge of `H` essential to `q`. -/
def Covers (H : SimpleGraph V) (S : Finset V) (Q : Finset (Sym2 V)) : Prop :=
  ∀ q ∈ Q, ∃ x ∈ S, ∃ e ∈ H.edgeSet, x ∈ e ∧ IsEssential H q e

end DistancePreserver934.Exact


