-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T12:25:32.90626+00:00
-- url     : https://prove2.me/theorems/be03981a-7002-4bf3-9ed0-88dd91824b32
-- title:
--   Integral Mem Of Is Closed
-- statement:
--   Definitions and structural lemmas for Integral Mem Of Is Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/IntegralMemOfIsClosed.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
namespace CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
section General
variable {α V : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α}
  [IsFiniteMeasureOnCompacts μ]
end General
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
def mulR (g : Mat n) : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ g).toContinuousLinearMap
def Lx (X : Mat n) (φ : Mat n → ℝ) : Mat n → ℝ := fun g => -(fderiv ℝ φ g (X * g))
def LW (W : List (Mat n)) (φ : Mat n → ℝ) : Mat n → ℝ := W.foldr Lx φ
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
instance : T2Space (MG G hG) := MG.isClosedEmbedding_mat.isEmbedding.t2Space
variable [CompleteSpace H]
def orbSpan (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (w : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w) '' G)
end CompanionTheory.D.Upq.Sm
end


