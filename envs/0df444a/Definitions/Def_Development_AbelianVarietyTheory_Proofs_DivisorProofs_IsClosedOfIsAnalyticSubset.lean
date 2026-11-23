-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:38.186734+00:00
-- url     : https://prove2.me/theorems/fe3b03df-aaaa-4662-b38f-5bbb48508da5
-- title:
--   Is Closed Of Is Analytic Subset
-- statement:
--   Definitions and structural lemmas for Is Closed Of Is Analytic Subset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
noncomputable section
variable {d : ℕ} {X : Type} [TopologicalSpace X]
def HasHoloImm (A : FinHolAtlas d X) (T : Set X) (k : ℕ) : Prop :=
  ∃ (U : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → X) (j : Fin A.n),
    IsOpen U ∧ U.Nonempty ∧ Set.MapsTo g U (T ∩ (A.chart j).source) ∧
    AnalyticOnNhd ℂ (A.chart j ∘ g) U ∧
    ∀ z ∈ U, Function.Injective (fderiv ℂ (A.chart j ∘ g) z)
end
end GlobalTheory.LogResInt


