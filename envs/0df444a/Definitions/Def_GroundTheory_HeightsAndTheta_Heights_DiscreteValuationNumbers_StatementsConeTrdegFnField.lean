-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:32.20083+00:00
-- url     : https://prove2.me/theorems/05b65705-a783-444d-bff3-ee4b58fa45cf
-- title:
--   Statements Cone Trdeg Fn Field
-- statement:
--   Definitions and structural lemmas for Statements Cone Trdeg Fn Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsConeTrdegFnField.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal fnField)
def ConeTrdegFnField.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (Ω : Type) [Field Ω] [Algebra O Ω],
    Function.Injective (algebraMap O Ω) →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
      (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) =
        Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω)) + Fintype.card K
end GroundTheory.Heights₂.Heights.NumbersDVR


