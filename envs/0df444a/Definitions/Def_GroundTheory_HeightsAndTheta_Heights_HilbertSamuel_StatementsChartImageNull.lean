-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChartImageNull
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChartImageNull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:03.567818+00:00
-- url     : https://prove2.me/theorems/4f083648-c949-4cca-bb4b-8150d5e200e4
-- title:
--   Statements Chart Image Null
-- statement:
--   Definitions and structural lemmas for Statements Chart Image Null, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsChartImageNull.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentsMeetNull
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def ChartDimLt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (p : (k : K) → ι k),
    IsMultiHomogIdeal J →
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ ReciprocityTheory.AnForm.R.chartIdeal J p) < (e : WithBot ℕ∞)
def ChartRatioImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < (e : WithBot ℕ∞) →
      volume {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} = 0
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


