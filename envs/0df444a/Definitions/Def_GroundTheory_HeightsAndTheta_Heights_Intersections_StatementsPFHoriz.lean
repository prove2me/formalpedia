-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:20.765252+00:00
-- url     : https://prove2.me/theorems/51aedf24-69e5-45d4-b692-944ef6591ae0
-- title:
--   Statements PFHoriz
-- statement:
--   Definitions and structural lemmas for Statements PFHoriz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsPFHoriz.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFSecRed
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
section Fibre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
open Classical in

def baseSubst (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') :
    MRing ι' →+* MRingOver G.Φ (fibreIdx ι' κ) :=
  eval₂Hom (algebraMap ℤ _) fun q =>
    if h : q.1 ∈ Set.range κ then
      (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
    else X ⟨⟨q.1, h⟩, q.2⟩
def fibreOf (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P')
    (W : Ideal (MRing ι')) : Ideal (MRingOver G.Φ (fibreIdx ι' κ)) :=
  Ideal.map (baseSubst κ G) W
end Fibre
def PFHoriz.Statement : Prop :=
  ∀ (I : AllFam) (r : ℕ), PFAt I r →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' W : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
      IsBlockMap κ v → IsArithVar W (d + r) → imageZ v W = imageZ v P' → IsArithVar (imageZ v P') d →
      IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      (∀ j, IsSmoothHerm (N j)) →
      I K' ι' W (d + r) (Fin.append L' N) =
        (J (fibreOf κ G W) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L
end
end GroundTheory.Heights₂.Heights.Inter


