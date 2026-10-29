-- Prove2me | Definitions.Def_BonnetTerrain_NPC_DecisionLanguage
-- name    : BonnetTerrain_NPC_DecisionLanguage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T04:19:38.185001+00:00
-- url     : https://prove2.me/theorems/91464bbe-fff5-4bc9-bdeb-a3a815c5d7dc
-- title:
--   Binary language of orthogonal terrain guarding
-- statement:
--   Input coordinates are rational and are embedded exactly in the real geometric model. A canonical binary word contains the positive vertex count, all coordinate pairs in order, then the signed integer budget, using the published self-delimiting scalar encoding. The language consists of exact codes of valid orthogonal chains admitting at most the budget many listed vertex guards covering every real carrier point. Malformed codes, zero-vertex encodings, nonsimple and nonorthogonal chains, and negative-budget instances are rejected. Coordinate and budget bits contribute to input length. This makes the finite digit representation implicit in the computational statement concrete; it does not bound the coordinate grid or restrict targets to rational points.
-- source:
--   Bonnet and Giannopoulos (2019), Orthogonal Terrain Guarding is NP-complete, Journal of Computational Geometry 10(2), 21–44, DOI 10.20382/jocg.v10i2a3 (published version), §1, printed pp.21–22 / PDF pp.1–2; finite-description discussion, printed pp.26,37 / PDF pp.6,17.

import Definitions.Def_BonnetTerrain_NPC_Geometry
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

namespace BonnetTerrain.NPC

/-- Finite rational input data, embedded exactly in the real plane for geometry. -/
structure RationalChain where
  edgeCount : ℕ
  vertex : Fin (edgeCount + 1) → ℚ × ℚ

def RationalChain.toReal (T : RationalChain) : Chain :=
  ⟨T.edgeCount, fun i => ((T.vertex i).1, (T.vertex i).2)⟩

/-- Number of vertices, coordinates in vertex order, then the signed integer budget.
Every scalar uses the referenced self-delimiting binary encoding. -/
def terrainCode (T : RationalChain) (k : ℤ) : List Bool :=
  OptimalQueuingComplexity.Restless.encNat (T.edgeCount + 1) ++
  (List.finRange (T.edgeCount + 1)).flatMap (fun i =>
    OptimalQueuingComplexity.Restless.encRat (T.vertex i).1 ++
    OptimalQueuingComplexity.Restless.encRat (T.vertex i).2) ++
  OptimalQueuingComplexity.Restless.encInt k

/-- The full vertex-guard, full-terrain decision language. A word outside the
canonical encoding, or encoding an invalid or nonorthogonal chain, is rejected. -/
def orthogonalTerrainLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ (T : RationalChain) (k : ℤ),
    w = terrainCode T k ∧ T.toReal.IsTerrain ∧ T.toReal.IsOrthogonal ∧
      T.toReal.Guardable k}

end BonnetTerrain.NPC


