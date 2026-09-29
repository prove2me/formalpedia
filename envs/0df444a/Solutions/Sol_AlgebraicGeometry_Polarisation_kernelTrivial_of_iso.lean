-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelTrivial_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2686bfee-0cb1-5483-82b3-c8de1f26518d

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace L4G0

noncomputable def dualIso {X : Scheme.{0}} {M M' : X.Modules} (e : M ≅ M') :
    Scheme.Modules.dual M ≅ Scheme.Modules.dual M' :=
  ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ X.Modules)).symm

noncomputable def mumfordBundleIso {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) {M M' : A.Modules} (e : M ≅ M') :
    mumfordBundle f L M ≅ mumfordBundle f L M' :=
  (Scheme.Modules.pullback (addMor f L)).mapIso e ⊗ᵢ
    ((Scheme.Modules.pullback (pullback.fst f f)).mapIso (dualIso e) ⊗ᵢ
      (Scheme.Modules.pullback (pullback.snd f f)).mapIso (dualIso e))

theorem locIsoOnBase_of_iso_left {S' : Type} [CommRing S'] {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of S'))
    {N N' P : X.Modules} (e : N ≅ N') (h : LocIsoOnBase g N' P) : LocIsoOnBase g N P := by
  intro s
  obtain ⟨U, hs, ⟨φ⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ φ⟩⟩

end L4G0

open L4G0 in
theorem solution
    (S : Type) [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (M M' : A.Modules) (e : M ≅ M') (h : KernelTrivial f L M) :
    KernelTrivial f L M' := by
  intro R _ t x hx
  exact h R t x (locIsoOnBase_of_iso_left _ ((Scheme.Modules.pullback (sliceAt f x)).mapIso (mumfordBundleIso f L e)) hx)

end S_AlgebraicGeometry_Polarisation_kernelTrivial_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelTrivial_of_iso (solution)
