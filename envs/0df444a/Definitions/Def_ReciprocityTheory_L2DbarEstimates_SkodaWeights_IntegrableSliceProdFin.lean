-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
-- name    : ReciprocityTheory_L2DbarEstimates_SkodaWeights_IntegrableSliceProdFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:39:01.112466+00:00
-- url     : https://prove2.me/theorems/3eb84e1a-0440-4bc1-892b-98601fcdbe6c
-- title:
--   Integrable Slice Prod Fin
-- statement:
--   Definitions and structural lemmas for Integrable Slice Prod Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/IntegrableSliceProdFin.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.H.SkodaOperators
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open scoped ENNReal InnerProductSpace
noncomputable section
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
def opG {M : Type*} {p : ℕ} (g : Fin p → M → ℂ) (f : M × Fin p → ℂ) : M → ℂ :=
  fun x => ∑ i, g i x * f (x, i)
def opS {M : Type*} {p : ℕ} (g : Fin p → M → ℂ) (w : M → ℂ) : M × Fin p → ℂ :=
  fun q => w q.1 * (starRingEnd ℂ) (g q.2 q.1) / ((vsq (gv g q.1) : ℝ) : ℂ)
def adjK {M : Type*} {p : ℕ} (g : Fin p → M → ℂ) (φ : M → ℝ) (w : M → ℂ) (f : M × Fin p → ℂ) :
    M × Fin p → ℂ :=
  fun q => (Real.exp (-φ q.1) : ℂ) * ((starRingEnd ℂ) (opS g w q) * f q)
end
end ReciprocityTheory.L2DbarEstimates.H.SkodaOperators


