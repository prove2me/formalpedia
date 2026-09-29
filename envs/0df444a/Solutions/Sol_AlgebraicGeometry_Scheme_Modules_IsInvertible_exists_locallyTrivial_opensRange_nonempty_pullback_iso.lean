-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_locallyTrivial_opensRange_nonempty_pullback_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a0e1941e-524e-5692-a9f1-a0913b371717

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P0PushforwardStart

noncomputable def pullbackPushforwardIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pushforward j).obj M) ≅ M :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app _) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j).app M

noncomputable def pullbackImageIsoUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) (V : U.Opens)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    (Scheme.Modules.pullback (j ''ᵁ V).ι).obj ((Scheme.Modules.pushforward j).obj M) ≅
      SheafOfModules.unit (j ''ᵁ V).toScheme.ringCatSheaf :=
  let φ := j.isoImage V
  have hfact : (j ''ᵁ V).ι = φ.inv ≫ (V.ι ≫ j) := (Scheme.Hom.isoImage_inv_ι j V).symm
  (Scheme.Modules.pullbackCongr hfact).app _ ≪≫
    ((Scheme.Modules.pullbackComp φ.inv (V.ι ≫ j)).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso
      (((Scheme.Modules.pullbackComp V.ι j).app _).symm ≪≫
        (Scheme.Modules.pullback V.ι).mapIso (pullbackPushforwardIso j M) ≪≫ eV) ≪≫
    Scheme.Modules.pullbackUnitIso φ.inv

end P0PushforwardStart

theorem solution
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : U.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ 𝓛 : X.Modules,
      (∀ x ∈ Scheme.Hom.opensRange j, ∃ U : X.Opens, x ∈ U ∧ U ≤ Scheme.Hom.opensRange j ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ M) := by
  refine ⟨(Scheme.Modules.pushforward j).obj M, ?_,
    ⟨P0PushforwardStart.pullbackPushforwardIso j M⟩⟩
  intro x hx
  obtain ⟨u, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx
  obtain ⟨V, huV, ⟨eV⟩⟩ := hM.exists_trivialization u
  exact ⟨j ''ᵁ V, ⟨u, huV, rfl⟩, Scheme.Hom.image_le_opensRange j V,
    ⟨P0PushforwardStart.pullbackImageIsoUnit j M V eV⟩⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso (solution)
