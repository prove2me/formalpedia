-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_closedFiberModels_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-22T00:20:05.051961+00:00
-- url     : https://prove2.me/submissions/5b7136eb-2304-497d-9950-31453b829dbc

import Definitions.Def_AlgebraicGeometry_Scheme_ProperAmbientModels
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_noetherian_ambientModels_of_isProper

noncomputable section

section

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    Nonempty (PhilipponProperClosedFiberApproximation.ClosedFiberModels
      (pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) f)) := by
  obtain ⟨M⟩ := AlgebraicGeometry.Scheme.nonempty_noetherian_ambientModels_of_isProper f
  exact ⟨PhilipponProperAmbientModels.closedFiberModels f M⟩

end

end
