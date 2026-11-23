-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:22.599481+00:00
-- url     : https://prove2.me/theorems/5778114e-e99d-43e3-858e-93273394edb4
-- title:
--   Mem Nonzero Locus Via
-- statement:
--   Definitions and structural lemmas for Mem Nonzero Locus Via, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MemNonzeroLocusVia.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
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
namespace GlobalTheory.KeyKa.EtBaseChange
section Val
variable {T T' : Type} [CommRing T] [CommRing T'] {X Y : Scheme.{0}}
def valH (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) : Γ(X, U) →+* T :=
  (w.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom).hom
end Val
section Dual
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
end Dual
section Via
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}
end Via
end GlobalTheory.KeyKa.EtBaseChange
namespace GlobalTheory.KeyKa
open EtBaseChange
end GlobalTheory.KeyKa
end


