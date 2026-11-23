-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:40.709805+00:00
-- url     : https://prove2.me/theorems/a7abb05e-fb79-4d05-ad06-2eee3f3f6d48
-- title:
--   Disintegration Density Continuous
-- statement:
--   Definitions and structural lemmas for Disintegration Density Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
namespace GlobalTheory.CompanionTheory.SW.FibreFam
section Top
variable {V : Type} [TopologicalSpace V]
end Top
section Meas
variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
def BumpFamily (U : Set V) (B : Set X) (fib : X → Measure V) : Prop :=
  (∀ b, b ∉ B → fib b = 0) ∧
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∀ b ∈ B, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) B
end Meas
end GlobalTheory.CompanionTheory.SW.FibreFam


