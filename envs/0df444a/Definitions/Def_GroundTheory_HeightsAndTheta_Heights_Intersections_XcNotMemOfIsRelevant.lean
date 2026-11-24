-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:32.618327+00:00
-- url     : https://prove2.me/theorems/99af6d20-e069-4c8d-905e-292880b77745
-- title:
--   Xc Not Mem Of Is Relevant
-- statement:
--   Definitions and structural lemmas for Xc Not Mem Of Is Relevant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/XcNotMemOfIsRelevant.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def RegularityLocalProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (f g : MRing ι) (a : K → ℕ) (x : funField P) (t : Ideal (MRing ι) → MRing ι)
    (yf yg : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog f a → IsMultiHomog g a → f ∉ P → g ∉ P →
    (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) →
    (∀ W ∈ divSupp P f ∪ divSupp P g, IsMultiHomog (t W) a ∧ t W ∉ W ∧
      yf W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) ∧
      yg W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g)) →
    ∑ᶠ W ∈ divSupp P f, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) -
        ∑ᶠ W ∈ divSupp P g, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) =
      ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ x‖
end
end GroundTheory.Heights₂.Heights.Inter


