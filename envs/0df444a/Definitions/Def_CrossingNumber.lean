-- Prove2me | Definitions.Def_CrossingNumber
-- name    : CrossingNumber
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T18:38:00.504404+00:00
-- url     : https://prove2.me/theorems/07282620-1378-485d-be81-fcc51c01e4c6
-- title:
--   Crossing number of a graph
-- statement:
--   The crossing number of a finite graph is the infimum of the cardinalities of the crossing sets over all ordinary polygonal drawings of that graph.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/CrossingNumber.lean#L1-L10

import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: CrossingNumber]
noncomputable def CrossingNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : ℕ :=
-- BODY
  sInf (Set.range (fun D : OrdinaryPolygonalDrawing G => D.crossingSet.card))


