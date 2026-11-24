-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:27.38678+00:00
-- url     : https://prove2.me/theorems/d4f163ae-147c-4927-b893-3715bd04ad21
-- title:
--   St Sheet Piece Product Analytic
-- statement:
--   Definitions and structural lemmas for St Sheet Piece Product Analytic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetPieceProductAnalytic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LocalParametrisation
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
def SheetPieceProductAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ)
    (U V : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ),
    IsLocalParametrisation X w B A D δ N → IsOpen U → IsOpen V →
    {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V → {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅ →
    ∃ f : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ f (A ⁻¹' D) ∧
      ∀ z, A z ∈ D → δ (A z) ≠ 0 →
        f z = ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = A z}, (ℓ z - ℓ x)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


