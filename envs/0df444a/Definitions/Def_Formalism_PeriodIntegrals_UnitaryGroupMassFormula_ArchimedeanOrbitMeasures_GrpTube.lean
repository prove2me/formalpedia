-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_GrpTube
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:02:29.069996+00:00
-- url     : https://prove2.me/theorems/fcfe42e1-f8a0-4404-a9e4-2b96d7669d17
-- title:
--   Grp Tube
-- statement:
--   Definitions and structural lemmas for Grp Tube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/GrpTube.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_LintegralMulRightOfMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AprimeInfG
open MeasureTheory Topology Filter Metric Set
open scoped ENNReal
section Abstract
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
def tubeS (H : Subgroup G) (V : Set G) (S : Set H) : Set G := {g | ∃ a ∈ V, ∃ h ∈ S, g = a * (h : G)}
end Abstract
section Ratio
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
structure TubeChart (μ : Measure G) (H : Subgroup G) (ν : Measure H) {ι η : Type} [Fintype ι] [Fintype η]
    (κ : EuclideanSpace ℝ ι → G) (χ : EuclideanSpace ℝ η → H) (r0 : ℝ)
    (d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ) (e : EuclideanSpace ℝ η → ℝ) : Prop where
  pos : 0 < r0
  inj : ∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0, (κ a)⁻¹ * κ b ∈ H → a = b
  mS : ∀ s, 0 < s → s ≤ r0 → MeasurableSet (χ '' ball 0 s)
  mT : ∀ ρ s, 0 < ρ → ρ ≤ r0 → 0 < s → s ≤ r0 → MeasurableSet (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s))
  mH : ∀ ρ, 0 < ρ → ρ ≤ r0 → MeasurableSet (tubeS H (κ '' ball 0 ρ) univ)
  densG : ∀ ρ s, 0 < ρ → ρ ≤ r0 → 0 < s → s ≤ r0 →
    μ (tubeS H (κ '' ball 0 ρ) (χ '' ball 0 s)) = ∫⁻ p in ball 0 ρ ×ˢ ball 0 s, ENNReal.ofReal (d p)
  densH : ∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)
end Ratio
end PI.AprimeInfG


