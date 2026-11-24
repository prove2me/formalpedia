-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalSpanTwo
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalSpanTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:23.778813+00:00
-- url     : https://prove2.me/theorems/527b4129-5bdc-4db6-ac47-5febae293fc0
-- title:
--   Not Is Horizontal Span Two
-- statement:
--   Definitions and structural lemmas for Not Is Horizontal Span Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotIsHorizontalSpanTwo.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
def ArithmeticIntersectionVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (a : Fin n → K → ℤ) (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → ¬ IsHorizontal W' →
    (imageZ v W' ∈ divSupp (imageZ v P') s ∧
        ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
          geoNum n W' (fun j => pullDeg κ (a j)) =
            J' (fibreIdeal κ G') 0 Fin.elim0 * geoNum n (imageZ v W') a) ∨
      (imageZ v W' ∉ divSupp (imageZ v P') s ∧ geoNum n W' (fun j => pullDeg κ (a j)) = 0)
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


