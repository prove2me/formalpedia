-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isQuasicoherent_coker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7f7956f2-7778-5e3f-8e4b-7a26f36937db

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf.coker OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsQuasicoherent"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "coker Hom IsQuasicoherent res res_smul mk"
namespace G4T
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section PModQC
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem isQuasicoherent_coker (hG : OModulePresheaf.IsQuasicoherent G)
    (hF : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsQuasicoherent (OModulePresheaf.coker φ) := fun U f => by
  refine ⟨fun x => x.inductionOn' fun x₀ => ?_, fun y => y.inductionOn' fun y₀ hy => ?_⟩
  · obtain ⟨n, y, hy⟩ := (hG U f).1 x₀
    exact ⟨n, Submodule.Quotient.mk y, congrArg Submodule.Quotient.mk hy⟩
  ·

    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hy
    obtain ⟨n, w, hw⟩ := (hF U f).1 z
    have h1 : G.res (V.basicOpen_le f) ((f ^ n : Γ(V, U.1)) • y₀ - φ.app U.1 w) = 0 := by
      rw [map_sub, G.res_smul, ← hz, ← φ.app_smul, ← hw]
      exact sub_eq_zero.mpr (show φ.app _ (F.res _ w) = G.res _ (φ.app U.1 w) from
        LinearMap.congr_fun (φ.naturality (V.basicOpen_le f)) w)
    obtain ⟨m, hm⟩ := (hG U f).2 _ h1
    rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
    exact ⟨m + n, (Submodule.Quotient.mk_eq_zero _).mpr
      ⟨(f ^ m : Γ(V, U.1)) • w, (φ.app_smul U.1 _ _).trans hm.symm⟩⟩

end PModQC

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG : G.IsQuasicoherent) (hF : F.IsQuasicoherent) : (OModulePresheaf.coker φ).IsQuasicoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isQuasicoherent_coker φ hG hF

end S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker (solution)
