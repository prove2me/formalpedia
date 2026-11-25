-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreRest
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreRest
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:54:36.437407+00:00
-- url     : https://prove2.me/theorems/96882d98-c671-5796-934d-2e5764785825
-- title:
--   Imports More Rest
-- statement:
--   Definitions and structural lemmas for Imports More Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsMoreRest.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
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
def ArithmeticIntersectionChartFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    FiniteDimensional G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩))
section Inhabitants
open IndefiniteRowSideFullHecke.Inter
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


