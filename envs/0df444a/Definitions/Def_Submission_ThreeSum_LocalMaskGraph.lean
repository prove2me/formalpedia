-- Prove2me | Definitions.Def_Submission_ThreeSum_LocalMaskGraph
-- name    : Submission_ThreeSum_LocalMaskGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:32:41.667777+00:00
-- url     : https://prove2.me/theorems/40533d92-14d6-4947-a52d-82bb54ca128a
-- title:
--   Local Mask Graph
-- statement:
--   Definitions and structural lemmas for Local Mask Graph, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalMaskGraph.lean

import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
set_option autoImplicit false
namespace ThreeSum.LocalMaskGraph
open Finset SubsetAddress MaskDecode
open scoped BigOperators
def maskAt (L h i : ℕ) : ℕ := (enumerateLayer L h).getD i 0
def setAt (L h i : ℕ) : Finset (Fin L) := decode L (maskAt L h i)
def vertexCount (L h : ℕ) : ℕ := L.choose h
end ThreeSum.LocalMaskGraph


