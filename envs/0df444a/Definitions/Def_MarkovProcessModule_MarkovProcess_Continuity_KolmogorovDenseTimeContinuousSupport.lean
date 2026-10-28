-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_KolmogorovDenseTimeContinuousSupport
-- name    : MarkovProcessModule_MarkovProcess_Continuity_KolmogorovDenseTimeContinuousSupport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T20:05:55.093159+00:00
-- url     : https://prove2.me/theorems/d802522b-2bff-4c4d-a30e-12a41ec864ec
-- title:
--   MarkovProcess.Continuity.KolmogorovDenseTimeContinuousSupport
-- statement:
--   # Kolmogorov support for dense-time trajectory kernels
--
--   This file applies the global dyadic-floor modification to the coordinate process of a
--   dense-time trajectory kernel.  A parameterwise Kolmogorov moment condition implies that the
--   dense-time law is supported on restrictions of continuous paths.
--
--   No measurability of the totalized modification as a path-valued map, PDE increment estimate,
--   Markov property of the resulting paths, or Hunt-process assertion is made here.
--
--   Complete pinned Lean module MarkovProcess.Continuity.KolmogorovDenseTimeContinuousSupport by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/KolmogorovDenseTimeContinuousSupport.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Polish
import Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_GlobalDyadicFloorModification
import Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousSupport

/-!
# Kolmogorov support for dense-time trajectory kernels

This file applies the global dyadic-floor modification to the coordinate process of a
dense-time trajectory kernel.  A parameterwise Kolmogorov moment condition implies that the
dense-time law is supported on restrictions of continuous paths.

No measurability of the totalized modification as a path-valued map, PDE increment estimate,
Markov property of the resulting paths, or Hunt-process assertion is made here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha]

/-- A parameterwise Kolmogorov moment estimate for the canonical coordinate process implies
almost-sure support of every dense-time trajectory law on restrictions of continuous paths.
The constants and exponents may depend on the kernel parameter. -/
theorem IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (hK : ∀ b, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r) (kappa b) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    IsSupportedOnContinuousPaths kappa := by
  apply IsSupportedOnContinuousPaths.of_continuousModification kappa
  intro b
  obtain ⟨p, q, gamma, M, hcoord, hgamma, hgammaq⟩ := hK b
  let X : DenseTime → (DenseTime → alpha) → alpha := fun r omega ↦ omega r
  refine ⟨fun t omega ↦ continuousGlobalDyadicFloorLimit X omega t, ?_, ?_⟩
  · intro omega
    exact continuous_continuousGlobalDyadicFloorLimit X omega
  · intro r
    simpa only [X, DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply] using
      IsKolmogorovProcess.ae_eq_continuousGlobalDyadicFloorLimit
        hcoord hgamma hgammaq r

section ContinuousPathKernel

/-- Under the coordinate Kolmogorov estimate, transporting to continuous paths and restricting
back to dense time recovers the original trajectory kernel.  The path-space transport uses only
the already established measurable extension map. -/
theorem map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (default : ContinuousPath alpha)
    (hK : ∀ b, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r) (kappa b) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    (toContinuousPathKernel kappa default).map ContinuousPath.denseRestriction = kappa := by
  exact IsSupportedOnContinuousPaths.map_denseRestriction kappa
    (IsSupportedOnContinuousPaths.of_isKolmogorovCoordinate kappa hK) default

end ContinuousPathKernel

end Kernel
end
end MarkovProcess


