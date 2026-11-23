-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:42.710526+00:00
-- url     : https://prove2.me/theorems/e6396593-6688-48a7-bf3b-fd222fe6536b
-- title:
--   Fn Of Comp
-- statement:
--   Definitions and structural lemmas for Fn Of Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/FnOfComp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
abbrev A1 : Scheme.{0} := Spec (CommRingCat.of (Polynomial ℤ))
def mOf {X : Scheme.{0}} (ρ : Γ(X, ⊤)) : X ⟶ A1 :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) ρ))
def fnOf {X : Scheme.{0}} (m : X ⟶ A1) : Γ(X, ⊤) :=
  m.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X)
section Desc
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
end Desc
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf


