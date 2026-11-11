-- Prove2me | Definitions.Def_IncApproxVC_Oblivious_Cuts
-- name    : IncApproxVC_Oblivious_Cuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:42:34.211411+00:00
-- url     : https://prove2.me/theorems/eba8b60d-1f28-4d8f-b4ae-efe99dfafda8
-- title:
--   Edge cuts, the $\alpha$-penalty score $|\partial^+(S)|+\alpha\,\mathrm{vol}^+(S)$ and the split graph $G_{\mathrm{split}}$
-- statement:
--   Let $G=(V,E)$ be a directed graph.
--
--   An **edge cut** is an ordered partition $(S,T)$ of $V$ into two disjoint nonempty sets; it is **$s$-rooted** if $s\in S$ and an **$s$–$t$ cut** if moreover $t\in T$, and its size is $|\partial^+_G(S)|=|E_G(S,T)|$.
--
--   For $\alpha>0$ the **$\alpha$-penalty score** of a set $S\subseteq V$ (Definition 3.8) is
--   $$|\partial^+_G(S)|+\alpha\cdot\mathrm{vol}^+_G(S).$$
--   Definitions 3.8–3.10 allow $S=V$; the score is defined for every set.
--
--   The **split graph** $G_{\mathrm{split}}=(V',E')$ (Definition 6.2) splits every vertex $v$ into $v^-$ and $v^+$:
--   $$V'=\{v^-,v^+\mid v\in V\},\qquad E'=\{(v^-,v^+)\mid v\in V\}\cup\{(u^+,v^-)\mid (u,v)\in E\}.$$
--
--   **Formalization Note.** An edge cut is the predicate `IsEdgeCut S T` on two vertex sets. The vertex set of $G_{\mathrm{split}}$ is `V × Bool`, with $v^-=(v,\mathrm{false})$ (`minus v`) and $v^+=(v,\mathrm{true})$ (`plus v`).
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 4 (edge cuts), p. 7 (Definitions 3.8, 3.9), p. 19 (Definition 6.2)

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph

/-!
# Edge cuts, the `α`-penalty score and the split graph

Adena, Henzinger, Rutschmann, *Incremental Approximate Vertex Connectivity via Almost-Linear Time
Local Cut Algorithms*, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 4 (edge cuts), p. 7
(Definitions 3.8–3.9), p. 19 (Definition 6.2).

* `IsEdgeCut S T`: "an ordered partition of the vertex set `V` into two disjoint sets `(S, T)`",
  both sides nonempty. It is `s`-rooted if `s ∈ S` and `s–t` if moreover `t ∈ T`; its size is
  `|∂⁺_G(S)| = |E_G(S, T)|`.
* `penaltyScore G α S` is the `s`-rooted `α`-penalty score `|∂⁺_G(S)| + α · vol⁺_G(S)` of
  Definition 3.8 (any `S`, including `S = V`, as Definitions 3.8–3.10 allow).
* `split G` is the split graph `G_split` of Definition 6.2 on the vertex type `V × Bool`: the
  vertex `(v, false)` is `v⁻` and `(v, true)` is `v⁺`; the edges are `(v⁻, v⁺)` for every vertex
  `v` and `(u⁺, v⁻)` for every edge `(u, v)` of `G`.
-/

namespace IncApproxVC.Oblivious

namespace Digraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge cut (p. 4): an ordered partition `(S, T)` of `V` into two disjoint nonempty sets. -/
def IsEdgeCut (S T : Finset V) : Prop :=
  S ∪ T = Finset.univ ∧ Disjoint S T ∧ S.Nonempty ∧ T.Nonempty

/-- The `α`-penalty score `|∂⁺_G(S)| + α · vol⁺_G(S)` of a set `S` (Definition 3.8). -/
def penaltyScore (G : Digraph V) (α : ℝ) (S : Finset V) : ℝ :=
  ((G.outBoundary S).card : ℝ) + α * (G.vol S : ℝ)

/-- The vertex `v⁻` of the split graph. -/
def minus (v : V) : V × Bool := (v, false)

/-- The vertex `v⁺` of the split graph. -/
def plus (v : V) : V × Bool := (v, true)

/-- The split graph `G_split = (V′, E′)` (Definition 6.2): `V′ = {v⁻, v⁺ | v ∈ V}` and
`E′ = {(v⁻, v⁺) | v ∈ V} ∪ {(u⁺, v⁻) | (u, v) ∈ E}`. -/
def split (G : Digraph V) : Digraph (V × Bool) :=
  ⟨(Finset.univ.image fun v : V => (minus v, plus v)) ∪
    G.edges.image fun e => (plus e.1, minus e.2)⟩

end Digraph

end IncApproxVC.Oblivious


