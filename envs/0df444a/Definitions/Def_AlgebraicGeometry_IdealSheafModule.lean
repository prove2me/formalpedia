-- Prove2me | Definitions.Def_AlgebraicGeometry_IdealSheafModule
-- name    : AlgebraicGeometry_IdealSheafModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/2dbe1029-0533-5cfb-9722-3a3661a6c2cf
-- title:
--   Ideal sheaves as modules, and their duals
-- statement:
--   Throughout, $X$ and $Y$ are schemes and `X.Modules` denotes the category of sheaves of modules over the structure sheaf of $X$, viewed as a sheaf of rings, equipped with the symmetric monoidal closed structure obtained by sheafifying the monoidal closed structure on presheaves of modules; its monoidal unit is $\mathcal O_X$ itself.
--
--   For a morphism of schemes $f \colon X \to Y$, `Scheme.Hom.unitToPushforwardUnit` is the canonical map $\mathcal O_Y \to f_*\mathcal O_X$ of sheaves of $\mathcal O_Y$-modules, namely Mathlib's `SheafOfModules.unitToPushforwardObjUnit` for the induced morphism of sheaves of rings.
--
--   Given `I : X.IdealSheafData`, with associated closed subscheme $Z =$ `I.subscheme` and closed immersion $i =$ `I.subschemeι`, the definition `Scheme.IdealSheafData.module` sets $\mathcal I$-as-a-module to be the kernel, formed in the abelian category `X.Modules`, of the map $\mathcal O_X \to i_*\mathcal O_Z$ just described; this is the sheaf usually written $\mathcal O_X(-Z)$, whose sections over an open $U$ are the sections of the ideal. The definition `Scheme.IdealSheafData.moduleι` is the kernel inclusion of this object into the monoidal unit $\mathcal O_X$, and `Scheme.IdealSheafData.invModule` is its dual `Scheme.Modules.dual`, i.e. the internal hom $\underline{\mathrm{Hom}}_{\mathcal O_X}(\mathcal O_X(-Z), \mathcal O_X)$ evaluated at the unit; no local freeness is asserted.
--
--   Finally, for a relative effective Cartier divisor `D : RelEffCartierDiv f r g` — a structure consisting of an ideal sheaf datum `D.I` on $\mathcal C \times_S T$ together with the requirements that the composite of its closed immersion with the projection to $T$ be finite, flat and locally of finite presentation, and have fibrewise rank $r$ at every point of $T$ — the abbreviations `RelEffCartierDiv.idealModule` and `RelEffCartierDiv.lineBundle` name $\mathcal O(-D) =$ `D.I.module` and $\mathcal O(D) =$ `D.I.invModule` respectively. The name `lineBundle` records the intended use: invertibility is not part of the definition.
--
--   **Relation to Mathlib.** Mathlib supplies `Scheme.IdealSheafData`, the associated closed subscheme, and the unit-to-pushforward map `SheafOfModules.unitToPushforwardObjUnit`; the module attached to an ideal sheaf datum, its inclusion into $\mathcal O_X$ and its dual are the project's own, and the dual is taken with respect to the monoidal closed structure on sheaves of modules constructed in this project's `SheafOfModules_Monoidal`.
--
--   **Where it is used.** These definitions are the passage from ideal sheaves, and in particular from relative effective divisors on a curve over a base, to sheaves of modules, so that a divisor can be traded for the line bundle it cuts out; this is the vocabulary in which the relative Picard functor of a curve is handled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IdealSheafModule.lean

import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

namespace Scheme.IdealSheafData

def module (I : X.IdealSheafData) : X.Modules :=
  (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)

def moduleι (I : X.IdealSheafData) : I.module ⟶ 𝟙_ X.Modules :=
  kernel.ι I.subschemeι.unitToPushforwardUnit

def invModule (I : X.IdealSheafData) : X.Modules :=
  Scheme.Modules.dual I.module

end Scheme.IdealSheafData

abbrev RelEffCartierDiv.idealModule {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.module

abbrev RelEffCartierDiv.lineBundle {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.invModule

end AlgebraicGeometry

end


