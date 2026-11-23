-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NonzeroLocusSecPw
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NonzeroLocusSecPw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:35.948026+00:00
-- url     : https://prove2.me/theorems/f21cb669-8d6c-4bd6-b9ef-b6943816bfe3
-- title:
--   Nonzero Locus Sec Pw
-- statement:
--   Definitions and structural lemmas for Nonzero Locus Sec Pw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/NonzeroLocusSecPw.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.ProjAffineLoci
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gs gs_res gs_mul fn_ext)
open TopologicalSpace
variable {X : Scheme.{0}} {R : Type} [CommRing R]
def zeroSec (H : LB X) : LB.Sec H := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩
def secPw {L : LB X} (σ : LB.Sec L) (d : ℕ) : LB.Sec (pw L d) where
  f := fun k => σ.f k ^ d
  compat := fun i j => by
    have h := congrArg (· ^ d) (σ.compat i j)
    simp only [mul_pow, ← map_pow] at h
    refine h.trans (congrArg (· * _) ?_)
    change _ = ((L.g i j ^ (d : ℤ) : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j))
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
end GlobalTheory.ProjAffineLoci


