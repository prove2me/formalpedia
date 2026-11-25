-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_refinement_kills_etale_system_class
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T08:35:59.379587+00:00
-- url     : https://prove2.me/submissions/ea799277-aaf7-47ec-897e-61b5ca96bf24

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitGlobalSectionDetection
import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitVanishingDetection

noncomputable section

section

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleLimitCohomologyTransport (stageRestriction)
open PhilipponEtaleStageCohomology (transition)
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    (q : ℕ) (F : System (directImages D)) (i : I) (x : (F.obj i).H q)
    (hx : stageRestriction c hc F i q x = 0) :
    ∃ (j : I) (a : j ⟶ i), transition a F q x = 0 := by
  exact
    PhilipponEtaleLimitVanishingDetection.exists_transition_eq_zero c hc
      (fun H k z => PhilipponEtaleLimitSectionDetection.exists_transition_eq_zero c hc k H z)
      (fun η k z w => PhilipponEtaleLimitSectionDetection.exists_transition_mem_image c hc k η z w)
      q F i x hx

end

end
