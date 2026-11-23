-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:47.880341+00:00
-- url     : https://prove2.me/theorems/b2011654-1c9c-4226-a96b-86d0672887f8
-- title:
--   Eval Standard Points Three
-- statement:
--   Definitions and structural lemmas for Eval Standard Points Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EvalStandardPointsThree.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer.FrameChange
section Val
variable {A : Type} [CommRing A] {X Y : Scheme.{0}}
def evH (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (p.appLE U ⊤ h).hom
open Classical in

def uv (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) : Γ(X, U)ˣ →* Aˣ :=
  if h : ⊤ ≤ p ⁻¹ᵁ U then Units.map (evH p U h : Γ(X, U) →* A) else 1
def hv (L : LB X) (j j' : L.ι) (ψ : Spec (CommRingCat.of A) ⟶ X) : Aˣ := uv ψ _ (L.g j j')
end Val
section Grp
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
def lamφ : Fin 4 → ((G ⊗ G).left ⟶ G.left) :=
  ![(fst G G * snd G G : G ⊗ G ⟶ G).left, (fst G G).left, (snd G G).left, (1 : G ⊗ G ⟶ G).left]
def lamε : Fin 4 → ℤ := ![1, -1, -1, 1]
variable {G}
def lamV {T : Over S} {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) (x y : T ⟶ G) : U :=
  h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left
variable [IsCommMonObj G]
end Grp
section Main
end Main
end GlobalTheory.JetSer.FrameChange


