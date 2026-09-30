-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_Target
-- name    : CorrColoring_ThreeChoosable_Target
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:02:38.005637+00:00
-- url     : https://prove2.me/theorems/24089f1a-9c68-455d-a50a-ef716e6872cb
-- title:
--   Targets, counterexamples and minimal counterexamples for Theorem 8
-- statement:
--   A **target** is a quadruple $B = (G, S, C, \varphi_0)$ where
--
--   1. $G$ is a finite plane graph (a graph with a fixed straight-line plane drawing) without cycles of lengths 4 to 8;
--   2. $S \subseteq V(G)$ consists either of at most one vertex incident with the outer face of $G$, or of all vertices incident with the outer face of $G$;
--   3. $C$ is a 3-correspondence assignment for $G$ that is consistent on every closed walk of length three in $G$;
--   4. $\varphi_0$ is a $C$-coloring of the induced subgraph $G[S]$;
--   5. $|S| \le 12$.
--
--   Let $e(B) = |E(G)| - |E(G[S])|$ be the number of edges not joining two vertices of $S$, and
--
--   $$s(B) = \Big(|V(G)|,\ e(B),\ -\sum_{uv \in E(G)} |E(C_{uv})|\Big),$$
--
--   ordered lexicographically. A target $B$ is a **counterexample** if no $C$-coloring $\varphi$ of $G$ restricts to $\varphi_0$ on $S$, and a **minimal counterexample** if it is a counterexample and no counterexample $B'$ has $s(B') < s(B)$.
--
--   These objects organize the proof of Theorem 8 of Dvořák and Postle by minimal counterexample: Lemmas 9 to 12 derive structural properties of a minimal counterexample, and a discharging argument shows that none exists.
--
--   **Formalization Note** The vertex type of a target lives in the universe `Type` and carries a `Fintype` instance; minimality compares against every target on every such type, which covers all finite graphs up to isomorphism. $\varphi_0$ is a map on all vertices whose values off $S$ are irrelevant. The second and third coordinates of $s(B)$ count ordered pairs (each edge of $G$ and each matching edge twice), which leaves the lexicographic order unchanged. Since Theorem 8 holds, no minimal counterexample exists; the lemmas about minimal counterexamples are, like the paper's, statements about a hypothetical object.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, p. 11, §3 (definition of target, e(B), s(B), counterexample, minimal counterexample)

import Mathlib
import Definitions.Def_CorrColoring_ThreeChoosable_NoCycleLengthsFourToEight
import Definitions.Def_CorrColoring_ThreeChoosable_StraightLineDrawing
import Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment
import Definitions.Def_CorrColoring_ThreeChoosable_ConsistentOn

namespace CorrColoring.ThreeChoosable

/-- A target `B = (G, S, C, φ₀)` (Dvořák–Postle, p. 11): `G` is a finite plane graph (with a
fixed straight-line drawing `D`) without cycles of lengths 4 to 8; `S` is either a set of at
most one vertex incident with the outer face, or the set of all vertices incident with the outer
face; `C` is a 3-correspondence assignment consistent on every closed walk of length 3; `φ₀` is a
`C`-colouring of `G[S]` (its values off `S` are irrelevant); and `|S| ≤ 12`. -/
structure Target where
  V : Type
  [instFintype : Fintype V]
  G : SimpleGraph V
  D : StraightLineDrawing G
  S : Finset V
  C : KCorrAssignment G 3
  φ₀ : V → Fin 3
  noCycles : NoCycleLengthsFourToEight G
  outer : (S.card ≤ 1 ∧ ∀ v ∈ S, D.IncidentOuter v) ∨ (∀ v, v ∈ S ↔ D.IncidentOuter v)
  consistent : ConsistentOnTriangles C
  precoloring : ∀ u v, u ∈ S → v ∈ S → G.Adj u v → ¬ C.M u (φ₀ u) v (φ₀ v)
  card_le : S.card ≤ 12

attribute [instance] Target.instFintype

namespace Target

/-- `B` is a counterexample: no `C`-colouring of `G` restricts to `φ₀` on `S`. -/
def IsCounterexample (B : Target) : Prop :=
  ¬ ∃ φ : B.V → Fin 3, IsCColoring B.C φ ∧ ∀ v ∈ B.S, φ v = B.φ₀ v

/-- The measure `s(B) = (|V(G)|, e(B), −∑_{uv ∈ E(G)} |E(C_{uv})|)`, ordered
lexicographically. The last two coordinates count ordered pairs, i.e. twice the paper's
numbers, which does not change the lexicographic order. -/
noncomputable def measure (B : Target) : Lex (ℕ × Lex (ℕ × ℤ)) :=
  toLex (Nat.card B.V,
    toLex (Nat.card {p : B.V × B.V // B.G.Adj p.1 p.2 ∧ ¬ (p.1 ∈ B.S ∧ p.2 ∈ B.S)},
      -(Nat.card {q : B.V × Fin 3 × B.V × Fin 3 // B.C.M q.1 q.2.1 q.2.2.1 q.2.2.2} : ℤ)))

/-- `B` is a minimal counterexample: a counterexample whose `s(B)` is lexicographically minimum
among all counterexamples. -/
def IsMinimalCounterexample (B : Target) : Prop :=
  B.IsCounterexample ∧ ∀ B' : Target, B'.IsCounterexample → ¬ B'.measure < B.measure

end Target

end CorrColoring.ThreeChoosable


