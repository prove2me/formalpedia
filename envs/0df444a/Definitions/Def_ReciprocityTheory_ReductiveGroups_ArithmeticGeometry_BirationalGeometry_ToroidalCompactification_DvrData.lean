-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:55.637697+00:00
-- url     : https://prove2.me/theorems/8752353b-3e6b-4fc7-8b23-eb579873aa2d
-- title:
--   Dvr Data
-- statement:
--   Definitions and structural lemmas for Dvr Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DvrData.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
structure UnramExt (V : Type) [CommRing V] where
  W : Type
  [ring : CommRing W]
  [dom : IsDomain W]
  [dvr : IsDiscreteValuationRing W]
  [alg : Algebra V W]
  fin : Module.Finite V W
  inj : Function.Injective (algebraMap V W)
  unram : Algebra.FormallyUnramified V W
  complete : IsAdicComplete (maximalIdeal W) W
attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
abbrev ValPt.ξ (P : ValPt Y) (W : UnramExt P.V) : Sp W.W ⟶ Y.X := spMap (algebraMap P.V W.W) ≫ P.yt
def DvrDataOver (P : ValPt Y) (W : UnramExt P.V) (t : SAB H (Sp W.W)) : Prop :=
  ∃ Q : PELUnif (maximalIdeal W.W) t, (∀ y, PsiUnitOn Q.D.toPre y (P.ξ W ⁻¹' abLocus Y.t.G)) ∧ Q.TorsionIso
def SplitOver {V : Type} [CommRing V] (W : UnramExt V) (t : SAB H (Sp W.W)) : Prop :=
  ∃ S : SplitExt (Sp (ResidueField W.W)), S.IsGt ((Over.pullback (spMap (residue W.W))).obj t.G)
def DvrDataAt (P : ValPt Y) : Prop :=
  ∃ (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t ∧ DvrDataOver P W t
def SplitsAt (P : ValPt Y) : Prop :=
  ∃ (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


