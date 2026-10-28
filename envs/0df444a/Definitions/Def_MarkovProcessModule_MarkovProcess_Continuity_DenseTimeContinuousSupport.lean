-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousSupport
-- name    : MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousSupport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:46:53.231246+00:00
-- url     : https://prove2.me/theorems/a48166d8-1e10-4a9a-9937-c6fe1d15ca71
-- title:
--   MarkovProcess.Continuity.DenseTimeContinuousSupport
-- statement:
--   # Continuous support from a continuous modification
--
--   This file turns a continuous-time modification of the coordinate process of a dense-time law
--   into almost-sure support on restrictions of continuous paths. The only measure-theoretic step is
--   the simultaneous choice of all dense-time modification identities, which is valid because
--   `DenseTime` is countable.
--
--   The continuous modification itself is not constructed here: it is the Kolmogorov--Chentsov
--   argument of `Continuity/GlobalDyadicFloorModification.lean`, applied to dense-time trajectory
--   kernels in `Continuity/KolmogorovDenseTimeContinuousSupport.lean`.
--
--   Complete pinned Lean module MarkovProcess.Continuity.DenseTimeContinuousSupport by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DenseTimeContinuousSupport.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Continuity_DenseTimeContinuousLaw

/-!
# Continuous support from a continuous modification

This file turns a continuous-time modification of the coordinate process of a dense-time law
into almost-sure support on restrictions of continuous paths. The only measure-theoretic step is
the simultaneous choice of all dense-time modification identities, which is valid because
`DenseTime` is countable.

The continuous modification itself is not constructed here: it is the Kolmogorov--Chentsov
argument of `Continuity/GlobalDyadicFloorModification.lean`, applied to dense-time trajectory
kernels in `Continuity/KolmogorovDenseTimeContinuousSupport.lean`.
-/

open MeasureTheory ProbabilityTheory Set

namespace MarkovProcess

noncomputable section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha]

/-- A continuous-time modification of every coordinate law implies that the original dense-time
law is almost surely the restriction of a continuous path. The modification may depend on the
kernel parameter `b`; no measurable choice of modifications in `b` is required for this
pointwise support conclusion. -/
theorem IsSupportedOnContinuousPaths.of_continuousModification
    (kappa : Kernel beta (DenseTime → alpha))
    (hmod : ∀ b, ∃ Y : NNReal → (DenseTime → alpha) → alpha,
      (∀ omega, Continuous (fun t ↦ Y t omega)) ∧
        ∀ q, (fun omega : DenseTime → alpha ↦ omega q) =ᵐ[kappa b]
          Y (DenseTime.castOrderEmbedding q)) :
    IsSupportedOnContinuousPaths kappa := by
  intro b
  obtain ⟨Y, hYcont, hYmod⟩ := hmod b
  have hmod_all : ∀ᵐ omega ∂kappa b, ∀ q,
      omega q = Y (DenseTime.castOrderEmbedding q) omega :=
    ae_all_iff.2 hYmod
  filter_upwards [hmod_all] with omega homega
  let path : ContinuousPath alpha :=
    ⟨fun t ↦ Y t omega, hYcont omega⟩
  refine ⟨path, ?_⟩
  funext q
  exact (homega q).symm

end Kernel
end
end MarkovProcess


