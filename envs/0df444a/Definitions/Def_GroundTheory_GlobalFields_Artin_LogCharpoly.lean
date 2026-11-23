-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- name    : GroundTheory_GlobalFields_Artin_LogCharpoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:13.947864+00:00
-- url     : https://prove2.me/theorems/a8ead553-0eac-4652-8e03-526af0e4a3cc
-- title:
--   Log Charpoly
-- statement:
--   Definitions and structural lemmas for Log Charpoly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace GroundTheory.Global
section MatrixJacobi
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
def matrixGeomSeries (M : Matrix n n R) : Matrix n n (PowerSeries R) :=
  Matrix.of fun i j => PowerSeries.mk fun k => (M ^ k) i j
end MatrixJacobi
section LogSeries
variable {k : Type*} [Field k] [CharZero k]
end LogSeries
section Endomorphism
variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
end Endomorphism
end GroundTheory.Global


