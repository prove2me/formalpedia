-- Prove2me | Definitions.Def_DecrNbhdCover_Emulator
-- name    : DecrNbhdCover_Emulator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:41.447342+00:00
-- url     : https://prove2.me/theorems/98ae3a5a-d7ef-4047-88df-186d1846f444
-- title:
--   Properties P1–P4, Q1, Q′1, partial and proper emulators, dynamic well-structured graphs
-- statement:
--   Let $G$ be a graph and $H=(V,U,E(H),\ell_H)$ a well-structured graph with $V=V(G)$, and let $0<\epsilon<1$, $0<d\le D$, with $d$ an integer.
--
--   1. **P2:** every $\ell_H(e)$ is an integral multiple of $d$.
--   2. **P3:** $\mathrm{dist}_H(u,v)\le(1+\epsilon)\mathrm{dist}_G(u,v)+\epsilon D$ for $u,v\in V(G)$.
--   3. **P4:** $\mathrm{dist}_H(u,v)\ge\mathrm{dist}_G(u,v)$ for $u,v\in V(G)$.
--   4. **Q1:** for every simple path $P$ in $G$ connecting distinct $v,v'$ there are $a\in V(P)\setminus\{v\}$ and a supernode $u$ with $(v,u),(a,u)\in E(H)$ such that one of the following holds: $a=v'$ and $\ell_H(v,u)+\ell_H(a,u)\le(1+\epsilon)\ell_G(P)+\epsilon D$; or $a$ is an endpoint of an edge $e\in P$ with $\ell_G(e)\ge d$ and $\ell_H(v,u)+\ell_H(a,u)\le(1+\epsilon)\ell_G(P[v,a])$; or $\ell_G(P[v,a]),\ell_G(P[a,v'])\ge d/2$ and for every $a'\in V(P)$ with $\ell_G(P[a,a'])\le\epsilon d$ there is an edge $(a',u)$ with $\ell_H(v,u)+\ell_H(a',u)\le(1+\epsilon)\ell_G(P[v,a'])$.
--   5. **Q′1:** for all distinct $v,v'$ in one component of $G$ there are a shortest $v$-$v'$ path $P$, $a\in V(P)\setminus\{v\}$ and $u$ with $(v,u),(a,u)\in E(H)$ such that either $a=v'$ and $\ell_H(v,u)+\ell_H(a,u)\le(1+\epsilon)\mathrm{dist}_G(v,a)+\epsilon D$, or $a\ne v'$ and $\ell_H(v,u)+\ell_H(a,u)\le(1+\epsilon)\mathrm{dist}_G(v,a)$.
--
--   $H$ is a **partial** $(\epsilon,d,D)$-emulator if $V=V(G)$ and P2, P3, Q1 hold at all times, and **proper** if also P4 holds. A **decremental** graph only loses vertices and edges. A **dynamic well-structured graph** only undergoes edge deletions, vertex deletions, and insertions of a new supernode with a nonempty set of new edges, and its **dynamic degree bound** counts the edges ever incident to a regular vertex.
--
--   The two emulator notions are the common language of all the algorithmic statements.
--
--   **Formalization Note** A dynamic object is a sequence of snapshots, and the permitted updates are grouped per time step. P1 is contained in $V=V(G)$.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 3.1, pp.15–16 (PDF 19–20); Definition 3.2, p.16 (PDF 20); Q1, p.18 (PDF 22); Definition 3.7, p.19 (PDF 23); Q′1, Theorem 3.15, p.21 (PDF 25)

import Mathlib
import Definitions.Def_DecrNbhdCover_Graph

set_option autoImplicit false

namespace DecrNbhdCover

open scoped ENNReal

/-! # Emulators: Properties P1–P4, Q1, Q′1, partial and proper emulators, dynamic well-structured graphs

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 3.1, pp.15–16; Definition 3.2, p.16;
Property Q1, p.18; Definition 3.7, p.19; Property Q′1 in Theorem 3.15, p.21.

**Formalization Note.** All properties are stated for one snapshot; "at all times" is a `∀ τ` over snapshots
`G τ`, `H τ`. `ε` and `D` are real and `d` a natural number. Paths in Q1 are **simple** (reading): `P[v, a]` is
well defined only on a simple path, and the proof of Observation 3.5 (C.2) speaks of "the vertex that lies
furthest from v on P" and takes `a` a vertex after `v`, which fails on a walk returning to `v`. In the
third bullet, `a′` may lie on either side of `a`, as C.2 uses. The bound on `ℓH(v, u) + ℓH(a, u)` is
compared in `ℝ≥0∞`. A dynamic well-structured graph (`IsDynWS`) is a snapshot sequence in which regular vertices
are only deleted, and in which every edge or supernode not present before is new, with edges that first appear incident
to a supernode that first appears, and each such supernode with at least one edge: these are exactly the
updates of Definition 3.1, grouped per time step. -/

variable {α β ε η : Type}

/-- P2: every edge length of `H` is an integral multiple of `d`. -/
def P2 (H : WSGraph α β η) (d : ℕ) : Prop :=
  ∀ e ∈ H.E, d ∣ H.len e

/-- P3: `distH(u, v) ≤ (1 + ε)·distG(u, v) + ε·D` for all `u, v ∈ V(G)`. -/
def P3 (G : Graph α ε) (H : WSGraph α β η) (eps D : ℝ) : Prop :=
  ∀ u ∈ G.V, ∀ v ∈ G.V,
    ((H.dist u v : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 + eps) * ((G.dist u v : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (eps * D)

/-- P4: `distH(u, v) ≥ distG(u, v)` for all `u, v ∈ V(G)`. -/
def P4 (G : Graph α ε) (H : WSGraph α β η) : Prop :=
  ∀ u ∈ G.V, ∀ v ∈ G.V, G.dist u v ≤ H.dist u v

/-- Property Q1, p.18. -/
def Q1 (G : Graph α ε) (H : WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ) : Prop :=
  ∀ (vs : List α) (es : List ε) (v v' : α), G.IsPath vs es →
    vs.head? = some v → vs.getLast? = some v' → v ≠ v' →
    ∃ (i : ℕ) (a : α) (u : β), vs[i]? = some a ∧ a ≠ v ∧ u ∈ H.U ∧ H.Adj v u ∧ H.Adj a u ∧
      ((a = v' ∧ ((H.ell v u + H.ell a u : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal ((1 + eps) * (G.walkLen es : ℝ) + eps * D)) ∨
       ((∃ e ∈ es, d ≤ G.len e ∧ ((G.ends e).1 = a ∨ (G.ends e).2 = a)) ∧
          ((H.ell v u + H.ell a u : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal ((1 + eps) * (G.segLen es 0 i : ℝ))) ∨
       ((d : ℝ) / 2 ≤ (G.segLen es 0 i : ℝ) ∧ (d : ℝ) / 2 ≤ (G.segLen es i es.length : ℝ) ∧
          ∀ (j : ℕ) (a' : α), vs[j]? = some a' → (G.segLen es i j : ℝ) ≤ eps * d →
            H.Adj a' u ∧ ((H.ell v u + H.ell a' u : ℕ∞) : ℝ≥0∞) ≤
              ENNReal.ofReal ((1 + eps) * (G.segLen es 0 j : ℝ))))

/-- Property Q′1, Theorem 3.15, p.21. -/
def Q1' (G : Graph α ε) (H : WSGraph α β η) (eps D : ℝ) : Prop :=
  ∀ v ∈ G.V, ∀ v' ∈ G.V, v ≠ v' → G.dist v v' ≠ ⊤ →
    ∃ (vs : List α) (es : List ε) (i : ℕ) (a : α) (u : β),
      G.IsWalk vs es ∧ vs.head? = some v ∧ vs.getLast? = some v' ∧
      ((G.walkLen es : ℕ) : ℕ∞) = G.dist v v' ∧
      vs[i]? = some a ∧ a ≠ v ∧ u ∈ H.U ∧ H.Adj v u ∧ H.Adj a u ∧
      ((a = v' ∧ ((H.ell v u + H.ell a u : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (1 + eps) * ((G.dist v a : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (eps * D)) ∨
       (a ≠ v' ∧ ((H.ell v u + H.ell a u : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (1 + eps) * ((G.dist v a : ℕ∞) : ℝ≥0∞)))

/-- One snapshot of a partial `(ε, d, D)`-emulator (Definition 3.7): `H` is well-structured, `V = V(G)`, and
P1–P3 and Q1 hold (P1 is contained in `V = V(G)`). -/
structure IsPartial (G : Graph α ε) (H : WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ) : Prop where
  wf : H.WF
  V_eq : H.V = G.V
  p2 : P2 H d
  p3 : P3 G H eps D
  q1 : Q1 G H eps d D

/-- One snapshot of a proper `(ε, d, D)`-emulator (Definition 3.7): partial, and P4 holds. -/
structure IsProper (G : Graph α ε) (H : WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ) : Prop
    extends IsPartial G H eps d D where
  p4 : P4 G H

/-- The promise of the weak ApproxBall problem under Theorem 3.15: a partial emulator with Q1 replaced by Q′1. -/
structure IsPartialQ1' (G : Graph α ε) (H : WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ) : Prop where
  wf : H.WF
  V_eq : H.V = G.V
  p2 : P2 H d
  p3 : P3 G H eps D
  q1' : Q1' G H eps D

/-- A decremental graph, as a snapshot sequence (§2.1): vertices and edges are only deleted, and endpoints and
lengths do not change. -/
structure IsDecr (G : ℕ → Graph α ε) : Prop where
  V_sub : ∀ τ, (G (τ + 1)).V ⊆ (G τ).V
  E_sub : ∀ τ, (G (τ + 1)).E ⊆ (G τ).E
  ends_eq : ∀ τ, (G (τ + 1)).ends = (G τ).ends
  len_eq : ∀ τ, (G (τ + 1)).len = (G τ).len

/-- A dynamic well-structured graph, as a snapshot sequence (Definition 3.1). -/
structure IsDynWS (H : ℕ → WSGraph α β η) : Prop where
  /-- In the initial graph, every supernode is incident to at least one edge. -/
  init_sup : ∀ u ∈ (H 0).U, ∃ e ∈ (H 0).E, (H 0).sup e = u
  /-- Regular vertices are only deleted. -/
  V_sub : ∀ τ, (H (τ + 1)).V ⊆ (H τ).V
  /-- A supernode that appears is new, and has at least one edge (`E_u ≠ ∅`). -/
  new_sup : ∀ τ, ∀ u ∈ (H (τ + 1)).U, u ∉ (H τ).U →
    (∀ s ≤ τ, u ∉ (H s).U) ∧ ∃ e ∈ (H (τ + 1)).E, (H (τ + 1)).sup e = u
  /-- An edge that appears is new and is incident to a supernode that appears at that time. -/
  new_edge : ∀ τ, ∀ e ∈ (H (τ + 1)).E, e ∉ (H τ).E →
    (∀ s ≤ τ, e ∉ (H s).E) ∧ (H (τ + 1)).sup e ∉ (H τ).U
  /-- An edge keeps its endpoints and its length. -/
  attrs : ∀ τ, ∀ e ∈ (H τ).E, e ∈ (H (τ + 1)).E →
    (H (τ + 1)).reg e = (H τ).reg e ∧ (H (τ + 1)).sup e = (H τ).sup e ∧
      (H (τ + 1)).len e = (H τ).len e

/-- The dynamic degree bound (Definition 3.1): for every regular vertex, the number of edges incident to it that ever
belonged to `H` is at most `μ`. -/
def DynDegLe (H : ℕ → WSGraph α β η) (μ : ℝ) : Prop :=
  ∀ v, ({e | ∃ τ, e ∈ (H τ).E ∧ (H τ).reg e = v}.encard : ℕ∞) ≠ ⊤ ∧
    (({e | ∃ τ, e ∈ (H τ).E ∧ (H τ).reg e = v}.ncard : ℕ) : ℝ) ≤ μ

/-- A partial `(ε, d, D)`-emulator of dynamic graphs (Definition 3.7). -/
structure IsPartialDyn (G : ℕ → Graph α ε) (H : ℕ → WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ) : Prop where
  decr : IsDecr G
  dyn : IsDynWS H
  partial' : ∀ τ, IsPartial (G τ) (H τ) eps d D

/-- A proper `(ε, d, D)`-emulator of dynamic graphs (Definition 3.7). -/
structure IsProperDyn (G : ℕ → Graph α ε) (H : ℕ → WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ) : Prop where
  decr : IsDecr G
  dyn : IsDynWS H
  proper : ∀ τ, IsProper (G τ) (H τ) eps d D

end DecrNbhdCover


