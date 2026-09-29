-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/7c7ad8fd-69a1-553c-8baa-05c8c1cc17cc

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Modules.map_smul Scheme.Opens.opensRange_ι Scheme.Modules.IsFrameOn"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor Modules Opens grothendieckTopology Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules Modules.IsFrameOn"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext toPresheaf pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback restrict map_smul IsFrameOn"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace FrameBridge

open Opposite TopologicalSpace

variable {X : Scheme.{u}}

section restrict

variable (W : X.Opens)

def restrictRingCatSheafHom : (W : Scheme.{u}).ringCatSheaf ⟶
    (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (W : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

def restrictFunctor' : X.Modules ⥤ (W : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom W)

lemma restrictFunctor'_eq : restrictFunctor' W = Modules.restrictFunctor W.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (W.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

def restrictFunctor'IsoPullback : restrictFunctor' W ≅ Modules.pullback W.ι :=
  eqToIso (restrictFunctor'_eq W) ≪≫ Modules.restrictFunctorIsoPullback W.ι

lemma image_le (W' : (W : Scheme.{u}).Opens) : W.ι ''ᵁ W' ≤ W :=
  (W.ι.image_le_opensRange W').trans_eq W.opensRange_ι

variable {W} in
lemma image_preimage_of_le {W₂ : X.Opens} (h : W₂ ≤ W) : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) = W₂ := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

abbrev secX (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) : Γ(X, W.ι ''ᵁ W') := a

end restrict

section smulHom

variable (N : X.Modules) (W : X.Opens) (τ : Γ(N, W))

def smulSectionHom : SheafOfModules.unit ((W : X.Opens) : Scheme.{u}).ringCatSheaf ⟶
    (restrictFunctor' W).obj N :=
  ⟨{ app := fun W' => ModuleCat.ofHom
      { toFun := fun a =>
          (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ : Γ(N, W.ι ''ᵁ W'.unop))
        map_add' := fun a b => add_smul (secX W W'.unop a) (secX W W'.unop b) _
        map_smul' := fun r a => mul_smul (secX W W'.unop r) (secX W W'.unop a) _ }
     naturality := fun {W' W''} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro a
       show secX W W''.unop (X.presheaf.map (W.ι.opensFunctor.map i.unop).op (secX W W'.unop a)) •
           N.presheaf.map (homOfLE (image_le W W''.unop)).op τ =
         N.presheaf.map (W.ι.opensFunctor.map i.unop).op
           (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ)
       rw [Scheme.Modules.map_smul]
       congr 1
       change _ = (N.presheaf.map _ ≫ N.presheaf.map _) τ
       rw [← N.presheaf.map_comp]
       rfl }⟩

lemma smulSectionHom_app_apply (W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ) (a : Γ(W, W'.unop)) :
    (smulSectionHom N W τ).val.app W' a =
      secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ := rfl

variable {N W τ}

lemma isIso_smulSectionHom_of_bijective
    (hb : ∀ W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ, Function.Bijective ((smulSectionHom N W τ).val.app W')) :
    IsIso (smulSectionHom N W τ) := by
  set ψ := smulSectionHom N W τ
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W'
    have : IsIso ((CategoryTheory.forget Ab).map
        (((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)).app W')) :=
      (isIso_iff_bijective _).2 (hb W')
    exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)
  have := (SheafOfModules.fullyFaithfulForget (((W : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ) (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

end smulHom

variable {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}

theorem isIso_smulSectionHom (h : IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    IsIso (smulSectionHom M W (M.presheaf.map (homOfLE hWU).op s)) := by
  apply isIso_smulSectionHom_of_bijective
  intro W'
  have e : M.presheaf.map (homOfLE (image_le W W'.unop)).op (M.presheaf.map (homOfLE hWU).op s) =
      M.presheaf.map (homOfLE ((image_le W W'.unop).trans hWU)).op s := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
    rw [← M.presheaf.map_comp]
    rfl
  have hb := h ((image_le W W'.unop).trans hWU) ((image_le W W'.unop).trans hWV)
  rw [← e] at hb
  exact hb

theorem nonempty_pullback_iso_unit (h : IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :=
  haveI := isIso_smulSectionHom h W hWU hWV
  ⟨((restrictFunctor'IsoPullback W).symm.app M) ≪≫
    (asIso (smulSectionHom M W (M.presheaf.map (homOfLE hWU).op s))).symm⟩

end FrameBridge

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry.Scheme.Modules in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (h : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : AlgebraicGeometry.Scheme.{u}).ringCatSheaf) :=
  FrameBridge.nonempty_pullback_iso_unit h W hWU hWV

end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit (solution)
