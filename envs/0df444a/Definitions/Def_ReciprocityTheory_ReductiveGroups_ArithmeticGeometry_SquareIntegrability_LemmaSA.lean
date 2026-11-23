-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:23.975213+00:00
-- url     : https://prove2.me/theorems/f667b794-d5d4-400a-b90d-4c5d6264e3de
-- title:
--   Lemma SA
-- statement:
--   Definitions and structural lemmas for Lemma SA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/LemmaSA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
def lemSJ : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι :=
  ((-I : ℂ) • (LinearMap.id : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)).restrictScalars ℝ
def lemSG {n : ℕ} (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => (Hf (b i) (b k)).im
end
end ReciprocityTheory.ChartRestriction.G.I2


