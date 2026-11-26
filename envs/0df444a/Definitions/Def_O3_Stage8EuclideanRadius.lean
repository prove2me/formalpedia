-- Prove2me | Definitions.Def_O3_Stage8EuclideanRadius
-- name    : O3_Stage8EuclideanRadius
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:17:09.36186+00:00
-- url     : https://prove2.me/theorems/e20a0396-9026-587f-8530-513e7070308e
-- title:
--   Stage8 Euclidean Radius
-- statement:
--   Definitions and structural lemmas for Stage8 Euclidean Radius, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanRadius.lean

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit true
namespace O3.Stage8EuclideanRadius
open O3
abbrev EuclideanLpSpace (d : ℕ) :=
  PiLp (ENNReal.ofReal (2 : ℝ)) (fun _ : Fin d ↦ ℝ)
end O3.Stage8EuclideanRadius


