-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:42.750956+00:00
-- url     : https://prove2.me/theorems/513ffa4c-2472-4519-80a6-644a859d5fcd
-- title:
--   Stalk Map Injective Of Flat
-- statement:
--   Definitions and structural lemmas for Stalk Map Injective Of Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/StalkMapInjectiveOfFlat.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
theorem toF_X_ne_zero : toF (R := PowerSeries k) F PowerSeries.X ≠ 0 :=
  (map_ne_zero (algebraMap (FractionRing (PowerSeries k)) F)).2
    ((map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries k) _)).2 PowerSeries.X_ne_zero)
def xUnit (k : Type) [Field k] (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (y : Sp F) :
    ((Sp F).presheaf.stalk y)ˣ := Units.map (toStk y).toMonoidHom (Units.mk0 _ (toF_X_ne_zero (k := k) F))
section Values
variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) = constF k F x)
  {y : Sp F} {J₀ : (Sp F ⟶ a.D₀.P.A.left) → a.D₀.P.L.ι} {J : (Sp F ⟶ P.toPre.P.A.left) → P.toPre.P.L.ι}
  (hJ₀ : Good a.D₀.P.L y J₀) (hJ : Good P.toPre.P.L y J)
include hW hF hJ₀ hJ
end Values
end GlobalTheory.ConstFam


