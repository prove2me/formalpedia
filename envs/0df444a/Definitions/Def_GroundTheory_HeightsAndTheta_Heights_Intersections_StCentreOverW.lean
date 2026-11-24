-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StCentreOverW
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StCentreOverW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:07.847382+00:00
-- url     : https://prove2.me/theorems/5ab329ea-d2f1-4ef3-a015-4c0beb18ad08
-- title:
--   St Centre Over W
-- statement:
--   Definitions and structural lemmas for St Centre Over W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StCentreOverW.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StValCentreZ
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
def CentreOverW.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)) (_hv : IsBlockMap κ v) (hP' : IsArithVar P' (n + 1)),
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    haveI := hP'.2.1.1
    ∀ R : ValuationSubring (FractionRing (MRing ι' ⧸ P')),
      (∀ a ∈ locRing (imageZ v P') W, fracMapZ v P' a ∈ R) →
      ∀ y : Ideal (MRing ι'), IsValCentre P' R y → y = P' ∨ y ∈ fibreOver v P' W
end GroundTheory.Heights₂.Heights.Inter


