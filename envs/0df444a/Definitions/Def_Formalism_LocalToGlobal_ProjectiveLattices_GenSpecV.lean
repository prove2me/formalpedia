-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecV
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_GenSpecV
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:20:07.767169+00:00
-- url     : https://prove2.me/theorems/845d534f-21bb-49ee-908a-b77db30c3049
-- title:
--   Gen Spec V
-- statement:
--   Definitions and structural lemmas for Gen Spec V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecV.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecRel
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
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart scaleD)
open Formalism.L2.Pj.GSR (Rel viaT liftT)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
instance gsvActHom (a : 𝓞 E) : IsMonHom (Xo.univ.t.act.act a) := Xo.univ.t.act.hom a
def gsvVec {L : Type} [CommRing L] (x : Sp L ⟶ Xo.X) {n : ℕ}
    (xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G)
    (cc : Fin n → L) : Sp (DualNumber L) ⟶ Xo.univ.t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst Xo.univ.t.G.hom x
section V
variable {L : Type} [CommRing L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
theorem gsvVec_w (cc : Fin n → L) :
    gsvVec x xc cc ≫ Xo.univ.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ x := by
  have h1 := Over.w (tvec (x := xc) cc)
  rw [gsvVec, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) h1
variable (xc) in

def gsvW (cc : Fin n → L) : tEps x ⟶ Xo.univ.t.G := Over.homMk (gsvVec x xc cc) (gsvVec_w cc)
end V
end Formalism.L2.Pj


