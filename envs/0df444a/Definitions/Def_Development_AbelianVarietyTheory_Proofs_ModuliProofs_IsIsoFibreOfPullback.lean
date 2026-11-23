-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoFibreOfPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:25.025685+00:00
-- url     : https://prove2.me/theorems/13493beb-fdb9-456f-a8c6-bf3e6368ad51
-- title:
--   Is Iso Fibre Of Pullback
-- statement:
--   Definitions and structural lemmas for Is Iso Fibre Of Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoFibreOfPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.NearFibreIso
open GlobalTheory.DenseFibreIso
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)
def Near (Q : MorphismProperty Scheme.{0}) (x : X) : Prop :=
  ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Y) (f' : T' ⟶ T),
    IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f'
variable (K : Type) [Field K] [Algebra R K]
end GlobalTheory.NearFibreIso


