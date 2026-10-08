-- Prove2me | Definitions.Def_UnitCircle
-- name    : UnitCircle
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-04T17:07:55.856381+00:00
-- url     : https://prove2.me/theorems/72129b6a-38c3-46fa-9634-e6b2abcbf344
-- title:
--   Unit Circle
-- statement:
--   For a point $p\in\mathbb{R}^2$, $\operatorname{UnitCircle}(p)$ is the unit circle centered at $p$, namely the set of all $x\in\mathbb{R}^2$ satisfying $\operatorname{dist}(x,p)=1$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `UnitCircle`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/UnitCircle.lean#L1-L6

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

-- [TABLET NODE: UnitCircle]
def UnitCircle (p : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
-- BODY
  {x | dist x p = 1}


