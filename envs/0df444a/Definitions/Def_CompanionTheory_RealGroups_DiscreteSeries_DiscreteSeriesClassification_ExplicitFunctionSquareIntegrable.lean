-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_ExplicitFunctionSquareIntegrable
-- name    : CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_ExplicitFunctionSquareIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:00.136805+00:00
-- url     : https://prove2.me/theorems/b113c510-79cd-4527-a734-99f5ebbfed47
-- title:
--   Explicit Function Square Integrable
-- statement:
--   Definitions and structural lemmas for Explicit Function Square Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/ExplicitFunctionSquareIntegrable.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
namespace CompanionTheory.RgDs
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
def phi (x : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∏ i : Fin n, ((lead ((i : ℕ) + 1) (xᴴ * x)).re ^ 2)⁻¹
def FinVol : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (ν : Measure (UJ ε)), ν.IsHaarMeasure →
    ∫⁻ x : UJ ε, ENNReal.ofReal (phi (toM x)) ∂ν < ⊤
def ExplicitFunctionSquareIntegrable : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    IsHCParam lam → IsMu lam μ → ∀ ν : Measure (UJ ε), ν.IsHaarMeasure →
      MemLp (fun g : UJ ε => PsiM T μ (toM g)) 2 ν
end CompanionTheory.RgDs


