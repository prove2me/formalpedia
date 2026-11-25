-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:17:55.433071+00:00
-- url     : https://prove2.me/theorems/975d86a8-c060-5179-b90b-ed4bee3cb237
-- title:
--   Gen Fr Pf V
-- statement:
--   Definitions and structural lemmas for Gen Fr Pf V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfV.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
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
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart Rel viaT liftT scaleD)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
instance gfpActHom (a : 𝓞 E) : IsMonHom (Xo.univ.t.act.act a) := Xo.univ.t.act.hom a
def gfpVec {L : Type} [Field L] (x : Sp L ⟶ Xo.X) {n : ℕ}
    (xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G)
    (cc : Fin n → L) : Sp (DualNumber L) ⟶ Xo.univ.t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x
section V
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
theorem gfpVec_w (cc : Fin n → L) :
    gfpVec x xc cc ≫ Xo.univ.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ x := by
  have hw : (tvec (x := xc) cc).left ≫ pullback.snd Xo.univ.t.G.hom x = spMap (algebraMap L (DualNumber L)) := by
    simpa using Over.w (tvec (x := xc) cc)
  simp only [gfpVec, Category.assoc, pullback.condition, reassoc_of% hw]
variable (xc) in

def gfpW (cc : Fin n → L) : tEps x ⟶ Xo.univ.t.G := Over.homMk (gfpVec x xc cc) (gfpVec_w cc)
end V
end Formalism.L2.Pj


