-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:31.791501+00:00
-- url     : https://prove2.me/theorems/c8a2ce3d-3896-473f-a4e7-537caf359e74
-- title:
--   Comparison
-- statement:
--   Definitions and structural lemmas for Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def metricDefect (A : HermLine n) (z : Cone n ℂ) : ℝ :=
  Real.log (A.metric z) - ∑ k, (A.deg k : ℝ) * Real.log (l2Norm (z k))
variable (n) in

def unitSpheres : Set (Cone n ℂ) := {z | ∀ k, l2Norm (z k) = 1}
section Blocks
variable {K : Type*} [Field K] [NumberField K]
def blockFin (y : Cone n K) (k : ι) (v : FinitePlace K) : ℝ := Real.log (⨆ i, v (y k i))
def blockSum (y : Cone n K) (k : ι) : ℝ :=
  (∑ᶠ v : FinitePlace K, blockFin y k v) + ∑ σ : K →+* ℂ, Real.log (l2Norm fun i ↦ σ (y k i))
end Blocks
end
end GroundTheory.Heights₂.Heights


