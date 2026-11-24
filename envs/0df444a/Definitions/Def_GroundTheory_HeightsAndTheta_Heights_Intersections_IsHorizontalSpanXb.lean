-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:16.38037+00:00
-- url     : https://prove2.me/theorems/22e7fccb-8be7-47f4-a683-b4cd406e9d14
-- title:
--   Is Horizontal Span Xb
-- statement:
--   Definitions and structural lemmas for Is Horizontal Span Xb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalSpanXb.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsPrimeSpanXb
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
def ArithmeticIntersectionHorizontal.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ n : ℕ, GenDegAt I n →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
      (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
      IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → IsHorizontal W' →
      (imageZ v W' ∈ divSupp (imageZ v P') s ∧
          ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
            I K' ι' W' n L' = (J' (fibreIdeal κ G') 0 Fin.elim0 : ℝ) * I K ι (imageZ v W') n L) ∨
        (imageZ v W' ∉ divSupp (imageZ v P') s ∧ I K' ι' W' n L' = 0)
section Inhabitants
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


