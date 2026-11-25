-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIsolFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIsolFinite
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:48.665505+00:00
-- url     : https://prove2.me/theorems/9460f379-1f65-48a3-b141-7f80fd70ea92
-- title:
--   Statements Fibre Isol Finite
-- statement:
--   Definitions and structural lemmas for Statements Fibre Isol Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsFibreIsolFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def FibreIsolFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    ∀ u : (Σ k, ι k) → ℂ, ∃ T : Finset ((Σ k', ι' k') → ℂ),
      ∀ z' ∈ mcPts P', SameOrbit (fun p => z' (v p)) u →
        (∃ ε > 0, ∀ z'' ∈ mcPts P', SameOrbit (fun p => z'' (v p)) u → dist z'' z' < ε →
          SameOrbit z'' z') →
        ∃ t ∈ T, SameOrbit z' t
section Inhabitants
open IndefiniteRowSideFullHecke.Inter
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


