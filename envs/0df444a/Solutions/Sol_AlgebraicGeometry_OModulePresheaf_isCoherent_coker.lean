-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isCoherent_coker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b7d3abc4-2977-54cb-998d-03227be612d1

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf.coker OModulePresheaf.imCokerSES OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsCoherent"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "coker imCokerSES Hom IsCoherent"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section PModAlg
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem isCoherent_coker (hG : OModulePresheaf.IsCoherent G) :
    OModulePresheaf.IsCoherent (OModulePresheaf.coker φ) := fun U => by
  haveI := hG U
  exact Module.Finite.of_surjective ((OModulePresheaf.imCokerSES φ).proj.appSections U.1)
    ((OModulePresheaf.imCokerSES φ).surjective U.1)

end PModAlg

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG : G.IsCoherent) : (OModulePresheaf.coker φ).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_coker φ hG

end S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker (solution)
