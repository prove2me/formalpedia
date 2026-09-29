-- Prove2me | Definitions.Def_Erdos9796Mission_RemovableVertex
-- name    : Erdos9796Mission_RemovableVertex
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-12T21:04:34.546658+00:00
-- url     : https://prove2.me/theorems/a6f9d176-48d7-4025-bde1-e8b9a859b349
-- title:
--   Removable vertex for the repeated-distance property
-- statement:
--   A vertex of a finite planar point set is removable when deleting it preserves the property that every remaining vertex has four other points at some common positive distance; the radius may depend on the remaining vertex.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/743b102037e9c43dd610a4db761433ce35862a99/lean/Erdos9796Proof/P97/SmallerCounterexample.lean#L25-L26

import Definitions.Def_Erdos9796Mission

/-! The removable-vertex interface used by the Problem 97 descent. -/

open Erdos9796Mission

namespace Erdos9796Mission

/-- A point of `A` is removable when deleting it preserves the property that
every remaining point has four equidistant witnesses. -/
def IsRemovableVertex (A : Finset Plane) (x : Plane) : Prop :=
  x ∈ A ∧ HasNEquidistantProperty 4 (A.erase x)

end Erdos9796Mission


