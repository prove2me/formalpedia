-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
-- name    : ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:57.796798+00:00
-- url     : https://prove2.me/theorems/7493e3bd-64ed-4f84-bcdf-f4b0acbd7c17
-- title:
--   Bergman Deriv St
-- statement:
--   Definitions and structural lemmas for Bergman Deriv St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/PluriharmonicAnalysis/BergmanDerivSt.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
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
open scoped ComplexOrder
variable {X : Type*} [MeasurableSpace X]
noncomputable def wPath (w₀ u : X → ℝ) (a t : ℝ) (x : X) : ℝ :=
  w₀ x * Real.exp (-(t * a * u x))
end ReciprocityTheory.GeometryOfNumbersTheory


