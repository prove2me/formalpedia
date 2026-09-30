-- Prove2me | Definitions.Def_capacityTemporalFlow
-- name    : capacityTemporalFlow
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T23:45:36.112712+00:00
-- url     : https://prove2.me/theorems/1e3613cf-a861-451c-bab6-1d222b18c90f
-- title:
--   Canonical density-flow functionals and component integrability
-- statement:
--   Let $(X_E,\mu_E)$ and $(X_L,\mu_L)$ be arbitrary measure spaces, each equipped with seven real-valued three-label density functions. For $r\in\{E,L\}$, their canonical components are
--
--   $$
--   \begin{aligned}
--   \gamma_{123}^r&=\min(f_1^r,\min(f_2^r,f_3^r)),\\
--   \gamma_{12}^r&=\max(\min(f_1^r,f_2^r)-f_3^r,0),\\
--   \gamma_{23}^r&=\max(\min(f_2^r,f_3^r)-f_1^r,0).
--   \end{aligned}
--   $$
--
--   Let $R:X_E\to X_L$ be any function and let $q_{12},q_{23}:X_L\to\mathbb R$ be any weights. Set $w_{ij}^E=q_{ij}\circ R$ and $w_{ij}^L=q_{ij}$, and write
--
--   $$
--   C_r=\gamma_{123}^r+w_{12}^r\gamma_{12}^r+w_{23}^r\gamma_{23}^r.
--   $$
--
--   The canonical score-gap functional is
--
--   $$
--   G=\int C_E\,d\mu_E-\int C_L\,d\mu_L.
--   $$
--
--   Define the component integrals by
--
--   $$
--   \begin{aligned}
--   T_r&=\int\gamma_{123}^r\,d\mu_r,\\
--   P_{12,r}&=\int w_{12}^r\gamma_{12}^r\,d\mu_r,\\
--   P_{23,r}&=\int w_{23}^r\gamma_{23}^r\,d\mu_r.
--   \end{aligned}
--   $$
--
--   The expanded functional is separately defined as
--
--   $$
--   \begin{aligned}
--   G_{\mathrm{exp}}={}&(T_E-T_L)\\
--   &+(P_{12,E}-P_{12,L})\\
--   &+(P_{23,E}-P_{23,L}).
--   \end{aligned}
--   $$
--
--   For one density system and one pair of weights, the component-integrability predicate requires the three functions $\gamma_{123},w_{12}\gamma_{12},w_{23}\gamma_{23}$ to be real-integrable. This predicate supplies the hypotheses used later to identify $G$ with $G_{\mathrm{exp}}$.
--
--   The bundle defines the two functionals and the integrability predicate; it does not itself assert their equality, an inequality between them, or a temporal coarsening law. Neither the measures' finiteness nor the measurability of $R$ is assumed by these definitions. The letters $E,L$ label two systems, not actual times in a specified process.
--
--   **Formalization Note** The functionals use Lean's total real-valued integral. Integrability is not built into the functions' inputs; it is imposed explicitly in the subsequent theorems.
-- source:
--   Interval-Möbius capacity and temporal block flow, unpublished project note (2026), equation (4.2), represented here by pulled-back density integrals rather than signed pushforward measures. CAPACITY_FLOW_THEOREM.md SHA-256 700d20415a4a673e5b27b1e6d508a89204afb85dfe54daddf8d4d84b1492d15f. Exact formal source: formal_capacity/FormalCapacity/Measure/Temporal.lean, densityCanonicalFlowGap (47–53), CanonicalComponentsIntegrable (84–89), densityCanonicalFlowGapExpanded (91–100). Source-file SHA-256 a3635f1e16db99dcb1c6f75e9f898023ec59225c99e22894e21a77556bf1089b. Ranges are compiler-derived and include source docstrings. This bundle does not assert pushforward transport or process-level coarsening. Local source archive; no public repository URL, commit, externally established authorship, or novelty claim is asserted. Target environment: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Definitions.Def_capacityThreeLabel
import Definitions.Def_capacityMeasureThreeLabel

set_option autoImplicit false

/-!
# The temporal capacity-flow inequality

This file proves the abstract form of equation (4.2).  The first theorem uses
finite block measures and an arbitrary measurable restriction map.  The second
specializes it to the density hypotheses discharged by the integrated
three-label stability theorem.  The final corollary expands the canonical
score into the triple and two weighted pair terms printed in (4.2).
-/

open MeasureTheory

namespace FormalCapacity.Measure

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]



/-- Difference of the early pulled-back and late integrated canonical scores. -/
def densityCanonicalFlowGap
    (early : ThreeLabelDensities α) (late : ThreeLabelDensities β)
    (μEarly : Measure α) (μLate : Measure β) (R : α → β)
    (q12 q23 : β → ℝ) : ℝ :=
  (∫ x, early.canonicalScore (q12 ∘ R) (q23 ∘ R) x ∂μEarly) -
    (∫ y, late.canonicalScore q12 q23 y ∂μLate)



/-- Integrability of the three separate canonical score components. -/
structure CanonicalComponentsIntegrable
    (d : ThreeLabelDensities α) (q12 q23 : α → ℝ) (μ : Measure α) : Prop where
  triple : Integrable d.canonical123 μ
  pair12 : Integrable (fun x ↦ q12 x * d.canonical12 x) μ
  pair23 : Integrable (fun x ↦ q23 x * d.canonical23 x) μ

/-- The displayed, term-by-term version of the left side of (4.2). -/
def densityCanonicalFlowGapExpanded
    (early : ThreeLabelDensities α) (late : ThreeLabelDensities β)
    (μEarly : Measure α) (μLate : Measure β) (R : α → β)
    (q12 q23 : β → ℝ) : ℝ :=
  ((∫ x, early.canonical123 x ∂μEarly) - (∫ y, late.canonical123 y ∂μLate)) +
    ((∫ x, q12 (R x) * early.canonical12 x ∂μEarly) -
      (∫ y, q12 y * late.canonical12 y ∂μLate)) +
    ((∫ x, q23 (R x) * early.canonical23 x ∂μEarly) -
      (∫ y, q23 y * late.canonical23 y ∂μLate))





end
end FormalCapacity.Measure


