-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:39.995008+00:00
-- url     : https://prove2.me/theorems/11f6bd6a-93a0-45cc-b5ac-74d296cb9449
-- title:
--   St Semiloc Chart Ratio
-- statement:
--   Definitions and structural lemmas for St Semiloc Chart Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StSemilocChartRatio.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def SemilocChartRatio.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (i' : ∀ k', ι' k'), IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ k', (X ⟨k', i' k'⟩ : MRing ι') ∉ P') →
    ∀ q : Σ k', ι' k', ∃ b b' : semiLocRing P' (fibreOver v P' W),
      (b' : FractionRing (MRing ι' ⧸ P')) ≠ 0 ∧
      (b : FractionRing (MRing ι' ⧸ P')) * algebraMap _ _ (Ideal.Quotient.mk P' (X ⟨q.1, i' q.1⟩)) =
        (b' : FractionRing (MRing ι' ⧸ P')) * algebraMap _ _ (Ideal.Quotient.mk P' (X q))
end GroundTheory.Heights₂.Heights.Inter


