-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NonzeroLocusConstMul
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NonzeroLocusConstMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:18.839376+00:00
-- url     : https://prove2.me/theorems/8f4f47a6-d3f3-457a-8cd9-f30b214c1589
-- title:
--   Nonzero Locus Const Mul
-- statement:
--   Definitions and structural lemmas for Nonzero Locus Const Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/NonzeroLocusConstMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
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
noncomputable section
namespace GlobalTheory.PowChange
open GlobalTheory.PowLie
variable {R : Type} [CommRing R]
theorem res_constFn {X : Scheme.{0}} (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn q U a) = constFn q V a :=
  congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)
def constMul {X : Scheme.{0}} (q : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f i := constFn q _ a * s.f i
  compat i j := by
    rw [map_mul, map_mul, res_constFn, res_constFn, s.compat, mul_left_comm]
end GlobalTheory.PowChange


