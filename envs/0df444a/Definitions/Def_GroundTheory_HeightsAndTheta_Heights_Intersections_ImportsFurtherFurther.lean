-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherFurther
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherFurther
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T13:09:51.090425+00:00
-- url     : https://prove2.me/theorems/b8bda109-1023-5a0f-b3e9-350f870df9a6
-- title:
--   Imports Further Further
-- statement:
--   Definitions and structural lemmas for Imports Further Further, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsFurtherFurther.lean

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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
def PullbackDegreeCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    IsGoodProj (imageZ v P') Ψ →
    ∀ᵐ y : Fin n → ℂ, ∀ w ∈ fibre (imageZ v P') Ψ y,
      (({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ).ncard : ℤ) =
        J (fibreIdeal κ G) 0 Fin.elim0
section Inhabitants
open IndefiniteRowSideFullHecke.Inter
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


