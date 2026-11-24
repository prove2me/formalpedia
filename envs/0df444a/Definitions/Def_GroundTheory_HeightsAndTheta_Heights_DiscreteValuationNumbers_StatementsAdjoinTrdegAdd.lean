-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsAdjoinTrdegAdd
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsAdjoinTrdegAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:59.639157+00:00
-- url     : https://prove2.me/theorems/1dc25286-1b14-4bd8-aaeb-a336f7ea4009
-- title:
--   Statements Adjoin Trdeg Add
-- statement:
--   Definitions and structural lemmas for Statements Adjoin Trdeg Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsAdjoinTrdegAdd.lean

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
def AdjoinTrdegAdd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (L : Type) [CommRing L] [IsDomain L] [Algebra R L],
    Function.Injective (algebraMap R L) →
    ∀ (s t : Set L) (ι : Type) [Fintype ι] (x : ι → L), Set.range x ⊆ t →
      AlgebraicIndependent (Algebra.adjoin R s) x →
      (∀ a ∈ t, IsAlgebraic (Algebra.adjoin R (s ∪ Set.range x)) a) →
      Algebra.trdeg R (Algebra.adjoin R (s ∪ t)) =
        Algebra.trdeg R (Algebra.adjoin R s) + (Fintype.card ι : Cardinal)
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


