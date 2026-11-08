-- Prove2me | Definitions.Def_ZeroExtensionGap_extGraph
-- name    : ZeroExtensionGap_extGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:18.091115+00:00
-- url     : https://prove2.me/theorems/554aba7d-79ab-4f60-91ca-a48b7e62839d
-- title:
--   Randomized extension $\mathrm{Ext}(Q,H)$, its pruned version, outer matchings and core-sparse sets
-- statement:
--   Let $Q$ and $H$ be finite graphs, $Q$ without self-loops. A realization of the **randomized extension** $\mathrm{Ext}(Q,H)$ has vertex set $V(Q)\times V(H)$. It contains $\{(u,a),(u,b)\}$ for every $u\in V(Q)$ and $\{a,b\}\in E(H)$, and, for every edge $e=\{u,v\}$ of $Q$ with fixed ordered endpoints $(u,v)$ and a bijection $\varphi_e:V(H)\to V(H)$, the **outer matching** $\{\{(u,a),(v,\varphi_e(a))\}:a\in V(H)\}$. In the randomized extension the $\varphi_e$ are independent and uniform.
--
--   The **core** $H_u$ is the subgraph induced on $\{u\}\times V(H)$. An edge is an **inter edge** if it lies in a core and an **outer edge** otherwise. The **pruned extension** with threshold $g$ deletes every outer edge lying on a cycle of the extension with fewer than $g$ edges. A set $S$ is **core-sparse** if $|S\cap V(H_u)|\le n^{0.9}$ for every $u$, where $n=|V(H)|$.
--
--   **Formalization Note.** `extGraph` is one realization. `pruneOuter` refers to cycles of the unpruned graph, so deletion is simultaneous, and inter edges are never deleted. The law is uniform on `ExtSample Q B`, the type of families of bijections. The endpoint ordering is `edgeTail`, `edgeHead`.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Definition 1, p.7 (PDF p.9); §3.2, p.8 (PDF p.10); Definition 2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_ZeroExtensionGap_fractionalArboricity

namespace ZeroExtensionGap

variable {A B : Type*}

/-- A realization of the randomized extension `Ext(Q, H)`: one bijection `φ_e : V(H) → V(H)` per edge
of `Q`, read from `edgeTail e` to `edgeHead e`. The law of `Ext(Q, H)` is uniform on this type. -/
abbrev ExtSample (Q : SimpleGraph A) (B : Type*) := Q.edgeSet → Equiv.Perm B

/-- The realization of the randomized extension `Ext(Q, H)` for given bijections, on the vertex set
`V(Q) × V(H)`. Definition 1, p.7 (PDF p.9) (Chen, Zhu, *Almost Tight Hardness of Approximation for
0-Extension*, STOC 2027 submission, manuscript sha256 0cdea87b…): the edge `{(u,a),(u,b)}` for every
`u` and `{a,b} ∈ E(H)`, and the matching `{(u,a),(v,φ_e(a))}` for every edge `e = {u,v}` of `Q` with
fixed ordered endpoints `(u,v)`.
**Formalization Note.** "We fix an ordering of the endpoints" is `edgeTail`, `edgeHead`. The law of
the uniform bijection does not see the ordering, because `φ ↦ φ⁻¹` preserves it. A `SimpleGraph` `Q`
has no self-loops, as Definition 1 assumes. -/
def extGraph (Q : SimpleGraph A) (H : SimpleGraph B) (φ : ExtSample Q B) : SimpleGraph (A × B) where
  Adj x y := (x.1 = y.1 ∧ H.Adj x.2 y.2) ∨
    ∃ e : Q.edgeSet,
      (edgeTail e.1 = x.1 ∧ edgeHead e.1 = y.1 ∧ φ e x.2 = y.2) ∨
      (edgeTail e.1 = y.1 ∧ edgeHead e.1 = x.1 ∧ φ e y.2 = x.2)
  symm := ⟨by
    rintro x y (⟨h, h'⟩ | ⟨e, he | he⟩)
    · exact Or.inl ⟨h.symm, h'.symm⟩
    · exact Or.inr ⟨e, Or.inr he⟩
    · exact Or.inr ⟨e, Or.inl he⟩⟩
  loopless := ⟨by
    rintro x (⟨-, h⟩ | ⟨e, ⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩⟩)
    · exact H.irrefl h
    all_goals
      have he : Q.Adj (edgeTail e.1) (edgeHead e.1) := by
        have := e.2
        rwa [← mk_edgeTail_edgeHead e.1, SimpleGraph.mem_edgeSet] at this
      rw [h₁, h₂] at he
      exact Q.irrefl he⟩

open Classical in
noncomputable instance extSampleFintype [Fintype A] [Fintype B] (Q : SimpleGraph A) :
    Fintype (ExtSample Q B) := inferInstance

/-- An outer edge of a realization of `Ext(Q, H)`: an edge not inside a core (p.8, PDF p.10). The
core `H_u` is the induced subgraph on `{u} × V(H)`, so an edge is outer iff the first coordinates of
its endpoints differ. -/
def IsOuterPair (x y : A × B) : Prop := x.1 ≠ y.1

/-- The pruning step of Definition 2, p.11 (PDF p.13), on an arbitrary graph `Y` on `A × B`: delete
every outer edge that lies on a cycle of `Y` with fewer than `g` edges.
**Formalization Note.** Deletion is simultaneous: every cycle is a cycle of `Y`, not of a partly pruned
graph. Inter edges are never deleted. -/
def pruneOuter (Y : SimpleGraph (A × B)) (g : ℕ) : SimpleGraph (A × B) where
  Adj x y := Y.Adj x y ∧ ¬ (IsOuterPair x y ∧
    ∃ (z : A × B) (c : Y.Walk z z), c.IsCycle ∧ c.length < g ∧ s(x, y) ∈ c.edges)
  symm := ⟨by
    rintro x y ⟨h, h'⟩
    refine ⟨h.symm, fun ⟨ho, z, c, hc, hl, he⟩ => h' ⟨Ne.symm ho, z, c, hc, hl, ?_⟩⟩
    rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => Y.irrefl h.1⟩

/-- The realization of the pruned extension `Êxt(Q, H)` with threshold `g` for given bijections
(Definition 2, p.11, PDF p.13; the paper's `g` is `⌊γ log n⌋`). -/
def prunedExt (Q : SimpleGraph A) (H : SimpleGraph B) (g : ℕ) (φ : ExtSample Q B) :
    SimpleGraph (A × B) :=
  pruneOuter (extGraph Q H φ) g

open Classical in
/-- The outer matching generated by the edge `e` of `Q` (p.8, PDF p.10):
`{{(u,a),(v,φ_e(a))} : a ∈ V(H)}` with `(u,v)` the ordered endpoints of `e`. -/
noncomputable def outerMatching [Fintype B]
    (Q : SimpleGraph A) (φ : ExtSample Q B) (e : Q.edgeSet) : Finset (Sym2 (A × B)) :=
  Finset.univ.image fun a : B => s((edgeTail e.1, a), (edgeHead e.1, φ e a))

open Classical in
/-- The number of edges of the matching `M` that are not in the graph `Y`, `|M \ E(Y)|`. -/
noncomputable def deletedCount [Fintype A] [Fintype B] (Y : SimpleGraph (A × B))
    (M : Finset (Sym2 (A × B))) : ℕ :=
  (M.filter fun e => e ∉ Y.edgeSet).card

open Classical in
/-- `|S ∩ V(H_u)|`, the number of vertices of `S` in the core of `u`. -/
noncomputable def coreCount (S : Finset (A × B)) (u : A) : ℕ := (S.filter fun x => x.1 = u).card

/-- `S ⊆ V(Y)` is core-sparse (p.8, PDF p.10): `|S ∩ V(H_u)| ≤ n^{0.9}` for every `u ∈ V(Q)`. -/
def IsCoreSparse (n : ℕ) (S : Finset (A × B)) : Prop :=
  ∀ u, (coreCount S u : ℝ) ≤ (n : ℝ) ^ (0.9 : ℝ)

end ZeroExtensionGap


