-- Prove2me | Definitions.Def_BonnetTerrain_NPC_Geometry
-- name    : BonnetTerrain_NPC_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T04:18:52.457983+00:00
-- url     : https://prove2.me/theorems/77d1911c-ed63-4411-bd35-94e335be728b
-- title:
--   Terrain geometry, visibility and vertex guarding
-- statement:
--   A nonempty finite simple polygonal chain in the real plane has distinct vertices in nondecreasing horizontal order. Orthogonality requires each edge to be horizontal or vertical and permits straight-through subdivisions. Visibility means the closed segment lies in the vertical upward closure of the chain, including its boundary. A finite subset of listed vertex indices guards the chain when each real point of each edge and every vertex is visible from some chosen vertex. Integer guard budgets are at-most bounds. Downward visibility additionally requires the target height to be at most the guard height. The indexing uses n edges and n+1 vertices, retaining singleton chains. The simple-chain and non-strict boundary conventions interpret the source model; no visibility or reduction theorem is assumed.
-- source:
--   Bonnet and Giannopoulos (2019), Orthogonal Terrain Guarding is NP-complete, Journal of Computational Geometry 10(2), 21–44, DOI 10.20382/jocg.v10i2a3 (published version), §1, printed pp.21–22 / PDF pp.1–2; Observation 6, printed p.26 / PDF p.6.

import Mathlib

namespace BonnetTerrain.NPC

abbrev Point := ℝ × ℝ

/-- Closed straight segment, including both endpoints and zero-length segments. -/
def closedSegment (a b : Point) : Set Point :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    p = ((1 - t) * a.1 + t * b.1, (1 - t) * a.2 + t * b.2)}

/-- Nonempty finite polygonal chain data. Validity is a separate predicate. -/
structure Chain where
  edgeCount : ℕ
  vertex : Fin (edgeCount + 1) → Point

def Chain.edge (T : Chain) (i : Fin T.edgeCount) : Set Point :=
  closedSegment (T.vertex i.castSucc) (T.vertex i.succ)

def Chain.carrier (T : Chain) : Set Point :=
  Set.range T.vertex ∪ {p | ∃ i : Fin T.edgeCount, p ∈ T.edge i}

/-- Distinct vertices, nondecreasing horizontal coordinates, and no edge intersections
except the shared endpoint of consecutive edges. Straight-through subdivisions are allowed. -/
def Chain.IsTerrain (T : Chain) : Prop :=
  Function.Injective T.vertex ∧
  Monotone (fun i => (T.vertex i).1) ∧
  ∀ i j : Fin T.edgeCount, i < j →
    ∀ p, p ∈ T.edge i → p ∈ T.edge j →
      j.val = i.val + 1 ∧ p = T.vertex i.succ

def Chain.IsOrthogonal (T : Chain) : Prop :=
  ∀ i : Fin T.edgeCount,
    (T.vertex i.castSucc).1 = (T.vertex i.succ).1 ∨
    (T.vertex i.castSucc).2 = (T.vertex i.succ).2

/-- The closed region on or above the terrain, within its horizontal span.
Vertical sides are included in their entirety. -/
def Chain.above (T : Chain) : Set Point :=
  {p | ∃ q ∈ T.carrier, q.1 = p.1 ∧ q.2 ≤ p.2}

/-- Geometric visibility between two points of the chain, allowing boundary contact. -/
def Chain.Sees (T : Chain) (a b : Point) : Prop :=
  a ∈ T.carrier ∧ b ∈ T.carrier ∧ closedSegment a b ⊆ T.above

/-- Listed vertex guards cover every real point of the chain. -/
def Chain.Guards (T : Chain) (S : Finset (Fin (T.edgeCount + 1))) : Prop :=
  ∀ p ∈ T.carrier, ∃ i ∈ S, T.Sees (T.vertex i) p

/-- Coverage with the additional restriction that targets have height at most the guard's. -/
def Chain.GuardsDownward (T : Chain) (S : Finset (Fin (T.edgeCount + 1))) : Prop :=
  ∀ p ∈ T.carrier, ∃ i ∈ S, T.Sees (T.vertex i) p ∧ p.2 ≤ (T.vertex i).2

/-- An integer budget is an at-most bound; negative budgets admit no guarding set. -/
def Chain.Guardable (T : Chain) (k : ℤ) : Prop :=
  ∃ S : Finset (Fin (T.edgeCount + 1)), (S.card : ℤ) ≤ k ∧ T.Guards S

end BonnetTerrain.NPC


