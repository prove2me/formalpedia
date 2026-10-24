-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
-- name    : KLS408915f_FunctionalInequalities_Poincare_Relaxation
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:47:22.512248+00:00
-- url     : https://prove2.me/theorems/93fe6cf9-4dd2-4e1d-ac63-501eadd0b5a9
-- title:
--   Poincaré test family from a finite pre-energy
-- statement:
--   `Poincare.TestFamily.ofPreEnergy` builds a test family from a pre-energy on real L²(μ), assigning each concrete test the variance of its ambient L² realization and its original finite energy. The bundle contains only this family definition; it does not itself state density, quadraticity, or a comparison between the pre-energy and its sequential relaxation. The associated framework permits empty test types and extended optimal constants, including ⊤.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/Relaxation.lean#L30-L34 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.Relaxation`, definition bundle `KLS408915f_FunctionalInequalities_Poincare_Relaxation`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology
namespace FunctionalInequalities
namespace Poincare
namespace TestFamily
universe u
variable {α : Type u} [MeasurableSpace α] (μ : ProbabilityMeasure α)
  (P : Energy.PreEnergy (Lp ℝ 2 (μ : Measure α)))
/-- Concrete tests with the variance of their `L²` realizations and their raw finite energy. -/
def ofPreEnergy : TestFamily where
  Test := P.Test
  variance f := L2.variance μ (P.toAmbient f)
  energy := P.energy
end TestFamily
end Poincare
end FunctionalInequalities


