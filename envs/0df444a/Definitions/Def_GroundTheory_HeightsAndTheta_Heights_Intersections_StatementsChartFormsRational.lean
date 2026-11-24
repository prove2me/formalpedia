-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:24.130796+00:00
-- url     : https://prove2.me/theorems/8959295c-dd31-452a-a3bc-3fb59f16c219
-- title:
--   Statements Chart Forms Rational
-- statement:
--   Definitions and structural lemmas for Statements Chart Forms Rational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsChartFormsRational.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
def chartFunField {Ω : Type*} [Field Ω] {ι : Type*} (x : ι → Ω) (i : ι) : Subfield Ω :=
  Subfield.closure (Set.range fun j => x j / x i)
def ChartFormsRational.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → ∀ i, x i ≠ 0 →
      ∃ (l₀ : ν) (k₀ k₁ : κ), δ l₀ ≠ 0 ∧ φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1) ≠ 0 ∧
        (∀ l, δ l / δ l₀ ∈ chartFunField x i) ∧
        (∃ c₀ c₁ : κ → Ω, (∀ k, c₀ k ∈ chartFunField x i) ∧ (∀ k, c₁ k ∈ chartFunField x i) ∧
          ∀ k, φ k = c₀ k • φ k₀ + c₁ k • φ k₁) ∧
        (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * δ l₀ / x i ^ 3 ∈ chartFunField x i
end
end GroundTheory.Heights₂.Heights.Inter


