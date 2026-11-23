-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:00:25.347807+00:00
-- url     : https://prove2.me/theorems/f3067b3d-6315-45ff-947e-af16711cd0b4
-- title:
--   Sign Insert
-- statement:
--   Definitions and structural lemmas for Sign Insert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SignInsert.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KoszulCx
section Alg
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
end Alg
section Geo
variable {R : Type} [CommRing R]
def mulSec {X : Scheme.{0}} (L : LB X) {a b c : ℤ} (h : c = a + b) (s : LB.Sec (pw L a)) (t : LB.Sec (pw L b)) :
    LB.Sec (pw L c) where
  f := fun i => (show Γ(X, L.U i) from s.f i) * (show Γ(X, L.U i) from t.f i)
  compat := fun i j => by
    have hs : rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
      ((L.g i j ^ a : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X inf_le_right (s.f j) := s.compat i j
    have ht : rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.f i) =
      ((L.g i j ^ b : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X inf_le_right (t.f j) := t.compat i j
    change rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (_ * _) =
      ((L.g i j ^ c : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (_ * _)
    rw [map_mul, map_mul]
    erw [hs, ht]
    rw [h, zpow_add, Units.val_mul]
    exact mul_mul_mul_comm _ _ _ _
end Geo
end GlobalTheory.KeyKa.KoszulCx
end


