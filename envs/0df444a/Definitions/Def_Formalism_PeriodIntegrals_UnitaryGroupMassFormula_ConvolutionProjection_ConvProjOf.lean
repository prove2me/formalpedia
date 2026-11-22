-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConvolutionProjection_ConvProjOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:32.729117+00:00
-- url     : https://prove2.me/theorems/fa1e7886-8b33-4974-8b24-94b6fc024055
-- title:
--   Conv Proj Of
-- statement:
--   Definitions and structural lemmas for Conv Proj Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConvolutionProjection/ConvProjOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhConvProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace PI.UnitaryGroupMassFormula.PhConvProj.Defs
open PI.PhConvProj
def SelfAdjStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ
def SandStep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → ∀ a, T.comp ((π a).comp T) = m a • T
end PI.UnitaryGroupMassFormula.PhConvProj.Defs


