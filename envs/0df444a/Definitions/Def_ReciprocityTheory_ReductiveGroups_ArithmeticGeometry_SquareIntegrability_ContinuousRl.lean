-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:48.893863+00:00
-- url     : https://prove2.me/theorems/9fe556ed-293d-4679-b3ed-c2a1381b3cbc
-- title:
--   Continuous Rl
-- statement:
--   Definitions and structural lemmas for Continuous Rl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ContinuousRl.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2.DimB
variable {k : ℕ}
local instance _p2m_local_instance_697ec7c02f_11 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_697ec7c02f_13 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance _p2m_local_instance_697ec7c02f_16 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def rl (t : Fin k → ℝ) : Fin k → ℂ := fun i => (t i : ℂ)
def iz (n : Fin k → ℤ) : Fin k → ℂ := fun i => (n i : ℂ)
def ubox (k : ℕ) : Set (Fin k → ℝ) :=
  {x | ∀ i, x i ∈ Ioc ((0 : Fin k → ℝ) i) ((0 : Fin k → ℝ) i + 1)}
def tproj (t : Fin k → ℝ) : UnitAddTorus (Fin k) := fun i => (t i : UnitAddCircle)
def IPer (Ψ : (Fin k → ℂ) → ℂ) : Prop := ∀ (n : Fin k → ℤ) z, Ψ (z + iz n) = Ψ z
def Av (Ψ : (Fin k → ℂ) → ℂ) (w : Fin k → ℂ) : ℂ := ∫ x in ubox k, Ψ (rl x + w)
def ex (m : Fin k → ℤ) (z : Fin k → ℂ) : ℂ := cexp (-(2 * Real.pi * I * ∑ l, (m l : ℂ) * z l))
def Pm (h : (Fin k → ℂ) → ℂ) (m : Fin k → ℤ) : (Fin k → ℂ) → ℂ := fun z => h z * ex m z
end ReciprocityTheory.ChartRestriction.G.I2.DimB


