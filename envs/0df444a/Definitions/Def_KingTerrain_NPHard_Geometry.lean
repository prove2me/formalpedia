-- Prove2me | Definitions.Def_KingTerrain_NPHard_Geometry
-- name    : KingTerrain_NPHard_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T23:51:55.652479+00:00
-- url     : https://prove2.me/theorems/23636bf9-a352-4295-a1e9-2517a6479fb2
-- title:
--   Strict terrains and guarding their full real carrier
-- statement:
--   A terrain is a nonempty finite polygonal chain in the real plane whose listed vertices have strictly increasing horizontal coordinates. Heights, slopes, horizontal edges, collinear subdivisions and singleton chains are unrestricted. The shared carrier contains every vertex and every real point of every closed edge. Visibility uses the shared closed-segment predicate: the connecting segment lies on or above the terrain, with boundary contact allowed.
--
--   A finite point set guards the terrain when its members lie on the carrier and every carrier point is visible from some member. A continuous guarding with budget $b$ uses at most $b$ such real points. A discrete guarding uses at most $b$ listed vertex indices, still covering the entire real carrier. The target point may select a different guard each time. These predicates define feasibility independently of any reduction or gadget construction.
-- source:
--   King and Krohn, Terrain Guarding is NP-Hard, DOI 10.1137/100791506, supplied PDF dated October 20, 2009, PDF p.1, §1 model.

import Definitions.Def_BonnetTerrain_NPC_Geometry

set_option autoImplicit false

namespace KingTerrain.NPHard

/-- Strict horizontal order, as in §1; no condition on heights or slopes. -/
def StrictTerrain (T : BonnetTerrain.NPC.Chain) : Prop :=
  StrictMono (fun i => (T.vertex i).1)

/-- Finite arbitrary-point guards on the carrier, covering its entire real continuum. -/
def PointGuards (T : BonnetTerrain.NPC.Chain)
    (G : Finset BonnetTerrain.NPC.Point) : Prop :=
  (∀ g ∈ G, g ∈ T.carrier) ∧
    ∀ q ∈ T.carrier, ∃ g ∈ G, T.Sees g q

/-- Continuous guarding with an at-most natural budget. -/
def ContinuousGuardable (T : BonnetTerrain.NPC.Chain) (b : ℕ) : Prop :=
  ∃ G : Finset BonnetTerrain.NPC.Point, G.card ≤ b ∧ PointGuards T G

/-- Vertex guards still cover every real point, including edge interiors. -/
def DiscreteGuardable (T : BonnetTerrain.NPC.Chain) (b : ℕ) : Prop :=
  ∃ S : Finset (Fin (T.edgeCount + 1)), S.card ≤ b ∧ T.Guards S

end KingTerrain.NPHard


