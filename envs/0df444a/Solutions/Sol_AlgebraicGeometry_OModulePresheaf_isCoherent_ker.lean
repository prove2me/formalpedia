-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isCoherent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/a080dfb9-e80c-5598-92ae-7c5d4c58dbbc

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Spec Scheme IsLocallyNoetherian.component_noetherian IsNoetherian OModulePresheaf.ker OModulePresheaf.kerImSES OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsCoherent"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "ker kerImSES Hom IsCoherent obj"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section PModAlg
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)
variable [IsLocallyNoetherian V]

theorem isCoherent_ker (hF : OModulePresheaf.IsCoherent F) :
    OModulePresheaf.IsCoherent (OModulePresheaf.ker φ) := fun U => by
  haveI := hF U
  haveI : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI : _root_.IsNoetherian (Γ(V, U.1)) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective ((OModulePresheaf.kerImSES φ).inc.appSections U.1)
    ((OModulePresheaf.kerImSES φ).injective U.1)

end PModAlg

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsLocallyNoetherian V] {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hF : F.IsCoherent) : (OModulePresheaf.ker φ).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_ker φ hF

end S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_ker (solution)
