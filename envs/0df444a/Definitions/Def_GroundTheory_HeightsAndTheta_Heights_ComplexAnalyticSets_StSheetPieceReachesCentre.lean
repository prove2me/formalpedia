-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceReachesCentre
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceReachesCentre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:18.159376+00:00
-- url     : https://prove2.me/theorems/84136f5b-e91d-436d-8bb0-a806b43a784d
-- title:
--   St Sheet Piece Reaches Centre
-- statement:
--   Definitions and structural lemmas for St Sheet Piece Reaches Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSheetPieceReachesCentre.lean

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
def SheetPieceReachesCentre.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ)
    (U V : Set (σ → ℂ)),
    IsLocalParametrisation X w B A D δ N → IsOpen U → IsOpen V →
    {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V → {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅ →
    ({x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U).Nonempty →
      w ∈ closure ({x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


