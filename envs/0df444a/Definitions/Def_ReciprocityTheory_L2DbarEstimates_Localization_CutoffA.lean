-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
-- name    : ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:38.866318+00:00
-- url     : https://prove2.me/theorems/50728462-bb59-4458-b630-9337a39fb9ef
-- title:
--   Cutoff A
-- statement:
--   Definitions and structural lemmas for Cutoff A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
def cutW {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ η : M → ℝ)
    (f : M → V n) (w : M → ℂ) : M → ℂ := fun x =>
  (η x : ℂ) * w x - (Real.exp (w1 ph ψ x - w2 ph ψ x) : ℂ) *
    ∑ j, d n z j (fun y => (η y : ℂ)) x * f x j
def cutS {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (η : M → ℝ)
    (f : M → V n) (σ : M → Fin n → Fin n → ℂ) : M → Fin n → Fin n → ℂ := fun x j k =>
  (η x : ℂ) * σ x j k + wedge (fun i => db n z i (fun y => (η y : ℂ)) x) (fun i => f x i) j k
end
end ReciprocityTheory.L2DbarEstimates.F


