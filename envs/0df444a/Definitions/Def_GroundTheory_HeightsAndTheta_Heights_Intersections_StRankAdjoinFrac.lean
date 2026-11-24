-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:21.386795+00:00
-- url     : https://prove2.me/theorems/5214d66a-1169-44d2-b031-1d381695f449
-- title:
--   St Rank Adjoin Frac
-- statement:
--   Definitions and structural lemmas for St Rank Adjoin Frac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StRankAdjoinFrac.lean

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
abbrev adjoinInclAlgebra (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) :
    Algebra (Algebra.adjoin F S) (Algebra.adjoin F T) :=
  (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom.toAlgebra
def RankAdjoinFrac.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (S T : Set Ω) (h : S ⊆ T),
    letI := adjoinInclAlgebra F h
    Module.finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T)
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


