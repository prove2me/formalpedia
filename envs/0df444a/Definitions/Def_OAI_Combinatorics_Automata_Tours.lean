-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Tours
-- name    : OAI_Combinatorics_Automata_Tours
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:53:33.586689+00:00
-- url     : https://prove2.me/theorems/e5e79573-0fc3-4466-ab75-fc147246fb46
-- title:
--   Cyclic orders on fibres, functional edge graphs and tour permutations
-- statement:
--   This file sets up rotation systems on directed graphs in which every vertex has at most one outgoing edge, together with the tour permutation of a rotation system.
--
--   1. **Cyclic orders on fibres.** Let $\nu:D\to V$ be a map. A cyclic order of $\nu$ is a permutation $\tau$ of $D$ such that
--   $$\nu(\tau(d))=\nu(d)\ \text{ for all } d\in D,\qquad \nu(d)=\nu(d')\ \Longrightarrow\ d'=\tau^{k}(d)\ \text{ for some } k\in\mathbb{Z}.$$
--   Thus $\tau$ preserves every fibre $\nu^{-1}(v)$ and acts on each nonempty fibre as a single cycle. When $D$ is finite, a cyclic order of $\nu$ exists, and a definite one is chosen. The file also records that conjugating a permutation by a bijection carries pairs lying in a common cycle to pairs lying in a common cycle.
--
--   2. **Functional edge graphs.** A functional edge graph with vertex set $V$ and edge set $E$ consists of maps $\mathrm{src},\mathrm{dst}:E\to V$ with $\mathrm{src}$ injective, so every vertex is the source of at most one edge; loops and several edges with the same endpoints are allowed. A step $v\to w$ means that some edge has source $v$ and target $w$, and reachability is the reflexive–transitive closure of the step relation.
--
--   3. **Edge ends.** The ends of the edges are the pairs $(e,b)\in E\times\{0,1\}$, where $(e,0)$ is the end at $\mathrm{src}(e)$ and $(e,1)$ the end at $\mathrm{dst}(e)$. Accordingly the vertex map is $\nu(e,0)=\mathrm{src}(e)$, $\nu(e,1)=\mathrm{dst}(e)$, and the flip $\phi(e,b)=(e,1-b)$ exchanges the two ends of every edge.
--
--   4. **Rotations and tours.** A rotation of the graph is a cyclic order $\tau$ of the vertex map $\nu$ on edge ends, that is, a cyclic order of the edge ends at each vertex. Its tour is the permutation
--   $$T=\tau\circ\phi,\qquad T(e,b)=\tau(e,1-b),$$
--   which crosses an edge to its other end and then passes to the next end in the cyclic order at that vertex. In particular $T(\phi(d))=\tau(d)$ for every edge end $d$.
--
--   The tour is the combinatorial form of walking around a graph along both sides of every edge. The computation graph of a deterministic two-way machine is a functional edge graph, since every configuration has at most one successor, and the lanes and joins of the cell diagrams realize the tour of a rotation of that graph. It is shown separately that, if a vertex $t$ has no outgoing edge, then for every edge $e$ whose source reaches $t$ the two ends $(e,0)$ and $(e,1)$ lie in one cycle of the tour; this is how acceptance is read off from the connections of the wiring.
--
--   **Formalization Note** `CyclicOrder vertex` has fields `perm`, `vertex_eq` and `cyclic`, the last expressed with Mathlib's `Equiv.Perm.SameCycle`; the chosen order is `CyclicOrder.choose` (assuming `[Fintype D]`), and the conjugation fact is `sameCycle_permCongr`. `FunctionalEdges V E` has fields `src`, `dst` and `src_injective`, with `Step`, `Reach`, `vertex`, `flip`, `Rotation := CyclicOrder G.vertex` and `Rotation.tour R := R.perm * G.flip`, where the product of permutations is composition, $(\sigma\tau)(x)=\sigma(\tau(x))$. The Boolean `false` marks the source end and `true` the target end; no finiteness is built into `FunctionalEdges`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Tours.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Tours.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells

namespace OAI

namespace OneWayLiveness

/-- A cyclic order on every nonempty fiber of a finite incidence map. -/
structure CyclicOrder {D V : Type*} (vertex : D → V) where
  perm : Equiv.Perm D
  vertex_eq : ∀ d, vertex (perm d) = vertex d
  cyclic : ∀ d d', vertex d = vertex d' → perm.SameCycle d d'

noncomputable def CyclicOrder.choose {D V : Type*} [Fintype D] (vertex : D → V) :
    CyclicOrder vertex := by
  classical
  have hex (v : V) := (Finset.univ.filter fun d => vertex d = v).exists_cycleOn
  choose p hp _hps using hex
  have hpres (v : V) (d : D) (hd : vertex d = v) : vertex (p v d) = v := by
    have := (hp v).1.mapsTo (by simpa using hd)
    simpa using this
  have hinv (v : V) (d : D) (hd : vertex d = v) : vertex ((p v).symm d) = v := by
    have := (hp v).1.perm_inv.mapsTo (by simpa using hd)
    simpa using this
  let τ : Equiv.Perm D := {
    toFun d := p (vertex d) d
    invFun d := (p (vertex d)).symm d
    left_inv d := by simp only [hpres _ _ rfl]; exact (p (vertex d)).symm_apply_apply d
    right_inv d := by simp only [hinv _ _ rfl]; exact (p (vertex d)).apply_symm_apply d }
  refine ⟨τ, fun d => hpres _ _ rfl, ?_⟩
  intro d d' hdd'
  have hc : (p (vertex d)).SameCycle d d' :=
    (hp (vertex d)).2 (by simp) (by simpa using hdd'.symm)
  obtain ⟨n, hn⟩ := hc.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, (τ ^ n) d = (p (vertex d) ^ n) d ∧ vertex ((τ ^ n) d) = vertex d := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      constructor
      · change p (vertex ((τ ^ n) d)) ((τ ^ n) d) = _
        rw [ih.2, ih.1]
      · exact (hpres _ _ rfl).trans ih.2
  exact ⟨n, by simpa only [zpow_natCast, (hpow n).1] using hn⟩

lemma sameCycle_permCongr {D D' : Type*} (e : D ≃ D') (τ : Equiv.Perm D)
    {d d' : D} (h : τ.SameCycle d d') : (e.permCongrHom τ).SameCycle (e d) (e d') := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← map_zpow]
  change e ((τ ^ n) (e.symm (e d))) = e d'
  simpa only [Equiv.symm_apply_apply] using congrArg e hn

/-- Oriented edges of a finite functional graph. Loops and distinct parallel
edges are permitted a priori; the source map nevertheless is injective. -/
structure FunctionalEdges (V E : Type*) where
  src : E → V
  dst : E → V
  src_injective : Function.Injective src

namespace FunctionalEdges
variable {V E : Type*} (G : FunctionalEdges V E)
def Step (v w : V) : Prop := ∃ e, G.src e = v ∧ G.dst e = w
abbrev Reach := Relation.ReflTransGen G.Step
def flip (_G : FunctionalEdges V E) : Equiv.Perm (E × Bool) where
  toFun d := (d.1, !d.2)
  invFun d := (d.1, !d.2)
  left_inv d := by simp
  right_inv d := by simp

def vertex (d : E × Bool) : V := if d.2 then G.dst d.1 else G.src d.1

@[simp] lemma vertex_false (e : E) : G.vertex (e, false) = G.src e := rfl
@[simp] lemma vertex_true (e : E) : G.vertex (e, true) = G.dst e := rfl
@[simp] lemma flip_apply (d : E × Bool) : G.flip d = (d.1, !d.2) := rfl

/-- Every incoming-to-outgoing cyclic order at a vertex is permitted. -/
abbrev Rotation := CyclicOrder G.vertex

namespace Rotation
variable {G} (R : G.Rotation)
def tour : Equiv.Perm (E × Bool) := R.perm * G.flip

@[simp] lemma tour_flip (d : E × Bool) : R.tour (G.flip d) = R.perm d := by
  rcases d with ⟨e, b⟩
  simp [tour, flip]

end Rotation
end FunctionalEdges
end OneWayLiveness

end OAI


