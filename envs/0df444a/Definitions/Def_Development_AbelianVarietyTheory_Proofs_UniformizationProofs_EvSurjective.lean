-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:43:09.613803+00:00
-- url     : https://prove2.me/theorems/099d0ac3-00ca-4d6a-9c6c-bb3d542271b4
-- title:
--   Ev Surjective
-- statement:
--   Definitions and structural lemmas for Ev Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvSurjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
section Expand
variable {S S' : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {R : CommRingCat.{0}}
end Expand
section Points
variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}
abbrev app {Z V : Scheme.{0}} (r : Z ⟶ V) : Γ(V, ⊤)ˣ →* Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom
def pt (x y u : Z ⟶ splitTorus S X) : Z ⟶ splitTorus S (X × X × X) :=
  ofVal ((valHom x).coprod ((valHom y).coprod (valHom u)))
def dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (x y u : Z ⟶ V) : Γ(Z.left, ⊤)ˣ :=
  app (x * y * u).left g * app x.left g * app y.left g * app u.left g / app (x * y).left g / app (x * u).left g /
    app (y * u).left g
end Points
section Affine
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
abbrev ex : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ →* (AddMonoidAlgebra A X)ˣ :=
  Units.map (ev (X := X) (𝟙 (Spec (CommRingCat.of A)))).toMonoidHom
variable {J : Ideal A}
end Affine
end GlobalTheory.CubeLift


