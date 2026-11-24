-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreSectionsCovering
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreSectionsCovering
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:53.343802+00:00
-- url     : https://prove2.me/theorems/aee9ea74-c84b-488f-b896-e2053e27145b
-- title:
--   St Fibre Sections Covering
-- statement:
--   Definitions and structural lemmas for St Fibre Sections Covering, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFibreSectionsCovering.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCoverCycles
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
open Filter Topology Matrix
noncomputable section
def FibreSectionsCovering.Statement : Prop :=
  ∀ (n e N : ℕ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (Ω : Set (Fin (e + 1) → ℂ))
    (X : Set (Fin n → ℂ)) (hX : Set.MapsTo (fun x => A *ᵥ x) X Ω),
    (∀ y ∈ Ω, {x | x ∈ X ∧ A *ᵥ x = y}.encard = N) →
    (∀ x ∈ X, ∃ (O : Set (Fin (e + 1) → ℂ)) (V' : Set (Fin n → ℂ)) (g : (Fin (e + 1) → ℂ) → Fin n → ℂ),
      IsOpen O ∧ A *ᵥ x ∈ O ∧ IsOpen V' ∧ x ∈ V' ∧ DifferentiableOn ℂ g O ∧ g (A *ᵥ x) = x ∧
        (∀ y ∈ O, A *ᵥ g y = y) ∧ X ∩ V' = g '' O) →
    IsCoveringMap hX.restrict
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


