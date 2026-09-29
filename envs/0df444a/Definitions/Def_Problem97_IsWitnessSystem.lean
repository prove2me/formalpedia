-- Prove2me | Definitions.Def_Problem97_IsWitnessSystem
-- name    : Problem97_IsWitnessSystem
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-13T02:19:46.128444+00:00
-- url     : https://prove2.me/theorems/b7f0555c-d8db-4d5e-a0f0-bc07e43126ce
-- title:
--   Witness systems for four equidistant neighbours
-- statement:
--   A witness system for a finite planar set assigns to each point a subset of the other points containing at least four points all at one common positive distance from it.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/387e5b44ae26906725a4898b0a01c2d7345ddb38/lean/Erdos9796Proof/P97/K4WitnessDeletion.lean#L35-L41

/- Rehosted from Erdos9796Proof.P97.K4WitnessDeletion at source commit
   387e5b44ae26906725a4898b0a01c2d7345ddb38. -/
import Definitions.Def_Erdos9796Mission

open scoped EuclideanGeometry
open Erdos9796Mission

namespace Problem97

/-- A witness system assigns each point a positive-radius class of at least
four other points from the configuration. -/
def IsWitnessSystem (A : Finset Plane) (S : Plane → Finset Plane) : Prop :=
  ∀ y ∈ A, S y ⊆ A.erase y ∧ 4 ≤ (S y).card ∧
    ∃ r > 0, ∀ q ∈ S y, dist y q = r

end Problem97


