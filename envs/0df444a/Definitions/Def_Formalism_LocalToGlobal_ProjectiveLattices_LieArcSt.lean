-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieArcSt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LieArcSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:20.714642+00:00
-- url     : https://prove2.me/theorems/93bd66af-4ae2-4356-b4e8-d5d52d32f239
-- title:
--   Lie Arc St
-- statement:
--   Definitions and structural lemmas for Lie Arc St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieArcSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def GtTan {K₁ : Type} [Field K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    (ν : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) : Prop :=
  ∃ g₀ : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (Over.mk (𝟙 (Sp K₁))), g₀.IsZero ∧
    ReciprocityTheory.ChartRestriction.G.Out.GtPt.IsPull (spMap (TrivSqZeroExt.fstHom K₁ K₁ K₁).toRingHom) ν g₀
def LieArcSt (Y : Model Xo c β) : Prop :=
  ∀ {K₁ : Type} [Field K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (ν : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)), GtTan ν →
    ∃ v : epsR (PowerSeries K₁) ⟶ W.t.G, IsLieImage W ν v
end Formalism.L2.Pj


