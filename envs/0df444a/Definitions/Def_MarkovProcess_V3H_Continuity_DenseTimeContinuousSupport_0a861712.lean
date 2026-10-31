-- Prove2me | Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousSupport_0a861712
-- name    : MarkovProcess_V3H_Continuity_DenseTimeContinuousSupport_0a861712
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:40.272989+00:00
-- url     : https://prove2.me/theorems/f2f91ab0-0237-44f5-a9d5-e3814988fdca
-- title:
--   MarkovProcess: MarkovProcess_V3H_Continuity_DenseTimeContinuousSupport_0a861712
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousExtension_479df42c
import Definitions.Def_MarkovProcess_V3H_Continuity_DenseTimeContinuousLaw_cc004751
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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
theorem IsSupportedOnContinuousPaths.p2m_embedded_0f21bfb58d615e9f
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


