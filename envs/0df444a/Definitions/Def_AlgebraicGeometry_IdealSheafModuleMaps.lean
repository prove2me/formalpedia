-- Prove2me | Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
-- name    : AlgebraicGeometry_IdealSheafModuleMaps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/8fc3eb69-c024-5d73-ba99-01c871cc239f
-- title:
--   Base-change comparison maps for ideal sheaf modules
-- statement:
--   Throughout, $f \colon X' \to X$ is a morphism of schemes and $I$ is a quasi-coherent ideal sheaf datum on $X$, with associated closed subscheme $i \colon Z \to X$ (`I.subschemeι`); $I.\mathrm{comap}\,f$ is the inverse-image ideal on $X'$, with closed subscheme $i' \colon Z' \to X'$. Recall that for a morphism $g$ the map `unitToPushforwardUnit` is the unit morphism of sheaves of modules $\mathcal O \to g_*\mathcal O$, and that $I.\mathrm{module}$ is by definition the kernel of $\mathcal O_X \to i_*\mathcal O_Z$.
--
--   Four things are introduced. First, `comapSubschemeHom` is the morphism $Z' \to Z$ obtained from the canonical isomorphism of $Z'$ with the fibre product $X' \times_X Z$ (`I.comapIso f`) followed by the second projection; `comapSubschemeHom_comp` records that the resulting square commutes, i.e. this morphism followed by $i$ equals $i'$ followed by $f$. Secondly, `kernelι_unitToPushforwardUnit_map_eq_zero` asserts that the composite $\ker(\mathcal O_X \to i_*\mathcal O_Z) \to \mathcal O_X \to f_*\mathcal O_{X'}$, followed by the pushforward along $f$ of $\mathcal O_{X'} \to i'_*\mathcal O_{Z'}$, is zero; the proof is a computation on sections over each open set, using the commuting square above. Thirdly, `moduleToPushforwardComapModule` is the morphism
--   $$I.\mathrm{module} \longrightarrow (f_*)\bigl((I.\mathrm{comap}\,f).\mathrm{module}\bigr)$$
--   obtained from that vanishing by lifting through the kernel and transporting along the isomorphism expressing that pushforward of sheaves of modules preserves this kernel. Finally, `pullbackModuleComparison` is its adjoint under the pullback–pushforward adjunction for sheaves of modules, a morphism $f^*\,I.\mathrm{module} \to (I.\mathrm{comap}\,f).\mathrm{module}$. No hypothesis on $f$ or on $I$ is imposed, and the last map is in general not an isomorphism.
--
--   **Relation to Mathlib.** Ideal sheaf data, the closed subscheme of an ideal sheaf, `comap` and `comapIso`, and the pushforward, pullback and adjunction for sheaves of modules are Mathlib's; the module $I.\mathrm{module}$ attached to an ideal sheaf datum, and the comparison maps defined here, belong to the project.
--
--   **Where it is used.** The module attached to an ideal sheaf datum and its dual are what the project uses for the ideal and the line bundle of a relative effective Cartier divisor; `pullbackModuleComparison` is the map which, under invertibility hypotheses proved elsewhere, expresses that $\mathcal O(-D)$ is compatible with base change of such divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IdealSheafModuleMaps.lean

import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (f : X' ⟶ X) (I : X.IdealSheafData)

open Opposite

abbrev comapSubschemeHom : (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι

@[reassoc]
lemma comapSubschemeHom_comp :
    I.comapSubschemeHom f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  simp [comapSubschemeHom]

lemma kernelι_unitToPushforwardUnit_map_eq_zero :
    (kernel.ι I.subschemeι.unitToPushforwardUnit ≫ f.unitToPushforwardUnit) ≫
      (SheafOfModules.pushforward f.toRingCatSheafHom).map
        (I.comap f).subschemeι.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m

  set s : Γ(X, U.unop) := (kernel.ι I.subschemeι.unitToPushforwardUnit).val.app U m with hs_def
  have hs : I.subschemeι.app U.unop s = 0 := by
    have := congrArg (fun φ ↦ φ.val.app U m) (kernel.condition I.subschemeι.unitToPushforwardUnit)
    exact this

  have hs' : (I.subschemeι.app U.unop).hom s = 0 := hs

  have h0 : ((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s = 0 := by
    change ((I.comapSubschemeHom f).app _).hom ((I.subschemeι.app U.unop).hom s) = 0
    rw [hs', map_zero]

  have key := congrArg (fun φ ↦ φ.hom s)
    (Scheme.Hom.congr_app (I.comapSubschemeHom_comp f).symm U.unop)
  change (((I.comap f).subschemeι ≫ f).app U.unop).hom s = 0
  rw [key]
  change ((I.comap f).subscheme.presheaf.map _).hom
    (((I.comapSubschemeHom f ≫ I.subschemeι).app U.unop).hom s) = 0
  rw [h0, map_zero]

def moduleToPushforwardComapModule :
    (I.module : SheafOfModules X.ringCatSheaf) ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (I.comap f).module :=
  kernel.lift _ _ (I.kernelι_unitToPushforwardUnit_map_eq_zero f) ≫
    (PreservesKernel.iso (SheafOfModules.pushforward f.toRingCatSheafHom)
      (I.comap f).subschemeι.unitToPushforwardUnit).inv

def pullbackModuleComparison :
    (Scheme.Modules.pullback f).obj I.module ⟶ (I.comap f).module :=
  ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _).symm
    (I.moduleToPushforwardComapModule f)

end AlgebraicGeometry.Scheme.IdealSheafData

end


