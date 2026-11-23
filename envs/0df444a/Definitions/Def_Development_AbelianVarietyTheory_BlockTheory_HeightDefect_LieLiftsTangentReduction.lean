-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_LieLiftsTangentReduction
-- name    : Development_AbelianVarietyTheory_BlockTheory_HeightDefect_LieLiftsTangentReduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:23.136936+00:00
-- url     : https://prove2.me/theorems/cd861b4f-56f9-4ac7-8464-5ef862ff7ab4
-- title:
--   Lie Lifts Tangent Reduction
-- statement:
--   Definitions and structural lemmas for Lie Lifts Tangent Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/LieLiftsTangentReduction.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj
abbrev epsRed (R : Type) [CommRing R] : Sp R ⟶ Sp (DualNumber R) :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom
def IsGtTangent {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (ν : GtPt D (epsR R)) : Prop :=
  epsRed R ≫ ν.b.left = eSec D.P.A ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (ν.s χ) (epsRed R)) (LB.oneGen D.P.L)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
def LieLifts {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁}
    {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ) : Prop :=
  ∀ ν : GtPt a.D₀ (epsR K₁), IsGtTangent ν →
    ∃ v : epsR (PowerSeries K₁) ⟶ W.t.G, IsTangent v ∧ IsLieImage W ν v
variable (Xo c) in

def ArcLieLift : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K₁ : Type) [Field K₁] (b : O →+* K₁)
    (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ), LieLifts W
end GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction


