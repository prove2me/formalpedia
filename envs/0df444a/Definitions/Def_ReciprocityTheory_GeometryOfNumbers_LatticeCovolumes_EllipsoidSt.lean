-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidSt
-- name    : ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:08.70774+00:00
-- url     : https://prove2.me/theorems/5b12a86e-90b1-42b3-bd1d-359795403dc6
-- title:
--   Ellipsoid St
-- statement:
--   Definitions and structural lemmas for Ellipsoid St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidSt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder
open ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
noncomputable def qC {r : ℕ} (G : Matrix (Fin r) (Fin r) ℂ) (y : Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (y i) * G i j * y j).re
noncomputable def qR {r : ℕ} (G : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * G i j * y j
end ReciprocityTheory.GeometryOfNumbersTheory


