-- Prove2me | Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovDenseTimeContinuousSupport_e9ca7f43
-- name    : MarkovProcess_V3H_Continuity_KolmogorovDenseTimeContinuousSupport_e9ca7f43
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:38:23.417983+00:00
-- url     : https://prove2.me/theorems/904f584f-f78b-4c5b-bb77-ef080e1ec542
-- title:
--   MarkovProcess: MarkovProcess_V3H_Continuity_KolmogorovDenseTimeContinuousSupport_e9ca7f43
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousSupport_0a861712
import Definitions.Def_MarkovProcess_V3H_Continuity_GlobalDyadicFloorModification_4a0b7713
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Path_Polish_87f91693
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinite

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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
theorem IsSupportedOnContinuousPaths.p2m_embedded_97b706232ed542b0
    (kappa : Kernel beta (DenseTime → alpha)) [IsMarkovKernel kappa]
    (hK : ∀ b, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r) (kappa b) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p) :
    IsSupportedOnContinuousPaths kappa := by
  apply _root_.MarkovProcess.Kernel.IsSupportedOnContinuousPaths.p2m_embedded_0f21bfb58d615e9f kappa
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
  exact _root_.MarkovProcess.Kernel.IsSupportedOnContinuousPaths.p2m_embedded_0eb019a7602852c8 kappa
    (_root_.MarkovProcess.Kernel.IsSupportedOnContinuousPaths.p2m_embedded_97b706232ed542b0 kappa hK) default

end ContinuousPathKernel

end Kernel
end
end MarkovProcess


