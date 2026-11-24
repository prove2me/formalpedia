-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:15.182615+00:00
-- url     : https://prove2.me/theorems/6769d0be-534b-429c-921b-9892cf765737
-- title:
--   St Analytic Implicit Chart
-- statement:
--   Definitions and structural lemmas for St Analytic Implicit Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAnalyticImplicitChart.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
def AnalyticImplicitChart.Statement : Prop :=
  ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (h : ι → (σ → ℂ) → ℂ) (a : σ → ℂ) (W : Set (σ → ℂ)),
    (∀ j, AnalyticAt ℂ (h j) a) → (∀ j, h j a = 0) →
    LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) → W ∈ 𝓝 a →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
      (g : (Fin d → ℂ) → σ → ℂ), d + Fintype.card ι = Fintype.card σ ∧ IsOpen O ∧ IsOpen V ∧ a ∈ V ∧
        V ⊆ W ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        {z | z ∈ V ∧ ∀ j, h j z = 0} = g '' O
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


