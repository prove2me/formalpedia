-- Prove2me | Definitions.Def_KingTerrain_NPHard_Languages
-- name    : KingTerrain_NPHard_Languages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T23:52:45.196072+00:00
-- url     : https://prove2.me/theorems/45a4fdfe-d6ad-4a33-a077-8e9964c8bc18
-- title:
--   Binary decision languages for discrete and continuous terrain guarding
-- statement:
--   An input consists of a positive number of vertices, an ordered list of exact rational coordinate pairs, and a natural guard budget. Its canonical binary code records the vertex count, every normalized rational numerator and positive denominator, and the budget, using the shared self-delimiting scalar codes. Coordinate bits are part of the input length; there is no fixed grid, precision or vertex bound.
--
--   Each input chain is embedded exactly in the real plane. The discrete language contains precisely the codes of strictly horizontally ordered chains admitting a vertex guarding of size at most the budget. The continuous language uses the same codes and accepts when a finite set of arbitrary real points of the carrier guards it within that budget. Both languages require coverage of all real carrier points. Malformed words and chains violating strict horizontal order are rejected. An empty guarding cannot cover a singleton terrain; budget zero is represented without a special acceptance convention.
-- source:
--   King and Krohn, Terrain Guarding is NP-Hard, DOI 10.1137/100791506, supplied PDF dated October 20, 2009, PDF pp.1–2, model and Theorem 1; explicit finite-input encoding convention.

import Definitions.Def_KingTerrain_NPHard_Geometry
import Definitions.Def_KingTerrain_NPHard_Complexity
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

set_option autoImplicit false

namespace KingTerrain.NPHard

/-- Finite exact input data; geometry is interpreted over the real plane. -/
structure RationalTerrain where
  edgeCount : ℕ
  vertex : Fin (edgeCount + 1) → ℚ × ℚ

def RationalTerrain.toReal (T : RationalTerrain) : BonnetTerrain.NPC.Chain :=
  ⟨T.edgeCount, fun i => ((T.vertex i).1, (T.vertex i).2)⟩

/-- Positive vertex count, normalized coordinate pairs, and binary natural budget. -/
def terrainCode (T : RationalTerrain) (b : ℕ) : List Bool :=
  OptimalQueuingComplexity.Restless.encNat (T.edgeCount + 1) ++
    OptimalQueuingComplexity.Restless.encTable
      (fun p : ℚ × ℚ => OptimalQueuingComplexity.Restless.encRat p.1 ++
        OptimalQueuingComplexity.Restless.encRat p.2) T.vertex ++
    OptimalQueuingComplexity.Restless.encNat b

/-- Invalid words and chains are rejected; vertex guards cover the entire carrier. -/
def discreteTerrainLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ (T : RationalTerrain) (b : ℕ),
    w = terrainCode T b ∧ StrictTerrain T.toReal ∧ DiscreteGuardable T.toReal b}

/-- The same input code; guard locations and targets range over real carrier points. -/
def continuousTerrainLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ (T : RationalTerrain) (b : ℕ),
    w = terrainCode T b ∧ StrictTerrain T.toReal ∧ ContinuousGuardable T.toReal b}

end KingTerrain.NPHard


