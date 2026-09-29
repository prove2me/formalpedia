-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.epi_sheafification_map_of_locallySurjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d01d288f-a4c1-5085-b5f3-1e4dfcf61d28

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.AlgebraicGeometry Opposite TopologicalSpace"

universe v v' u'

namespace PresheafOfModules
p2m_export "PresheafOfModules" "sheafification map toSheafify IsLocallyInjective toPresheaf sheafifyMap obj IsLocallySurjective"
p2m_open "PresheafOfModules"

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem epi_sheafification_map_of_isLocallySurjective {P Q : PresheafOfModules.{v} R₀}
    (ψ : P ⟶ Q) [Presheaf.IsLocallySurjective J ((toPresheaf R₀).map ψ)] :
    Epi ((sheafification.{v} α).map ψ) := by
  apply (SheafOfModules.toSheaf.{v} R).epi_of_epi_map
  change Epi ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ))
  haveI : Sheaf.IsLocallySurjective
      ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ))
    haveI : Presheaf.IsLocallySurjective J
        (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P) ≫
          CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ)) := by
      rw [← CategoryTheory.toSheafify_naturality]
      infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J
      (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P)) _
  infer_instance

end PresheafOfModules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules Opens grothendieckTopology PresheafOfModules"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.solution {P Q : X.PresheafOfModules} (ψ : P ⟶ Q)
    (h : ∀ (U : X.Opens) (s : Q.obj (op U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ Q.map (homOfLE i).op s ∈ Set.range (ψ.app (op V))) :
    Epi ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ψ) := by
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map ψ) :=
    ⟨fun {U} s x hx => by
      obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
      exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩⟩
  exact PresheafOfModules.epi_sheafification_map_of_isLocallySurjective (𝟙 X.ringCatSheaf.obj) ψ

#print axioms solution

end AlgebraicGeometry.Scheme.Modules

end S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective (solution)
