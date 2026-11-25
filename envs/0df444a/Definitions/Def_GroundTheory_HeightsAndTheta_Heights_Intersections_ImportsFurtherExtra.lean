-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherExtra
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherExtra
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:22.796366+00:00
-- url     : https://prove2.me/theorems/f565aa5e-f353-489b-b826-1562f93500d7
-- title:
--   Imports Further Extra
-- statement:
--   Definitions and structural lemmas for Imports Further Extra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsFurtherExtra.lean

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
def pullbackDensity_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsGoodProj (imageZ v P') Ψ →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm A → IsPullHerm κ v A A' →
    IsSectionOn (imageZ v P') A s →
    ∀ᵐ y : Fin n → ℂ, ∀ x ∈ pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ,
      logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => potOf R (L' j)) (pullQ R v Ψ) x =
        sheetDensity (imageZ v P') Ψ (pot L) (logNorm A s) y (pullW R v Ψ x)
section Inhabitants
open IndefiniteRowSideFullHecke.Inter
end Inhabitants
end GroundTheory.Heights₂.Heights.Inter


