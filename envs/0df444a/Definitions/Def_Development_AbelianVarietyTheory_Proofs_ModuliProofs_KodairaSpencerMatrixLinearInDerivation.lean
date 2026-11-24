-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerMatrixLinearInDerivation
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerMatrixLinearInDerivation
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:26.030418+00:00
-- url     : https://prove2.me/theorems/c7718a57-e568-4b30-ab82-aca29eb12391
-- title:
--   Kodaira Spencer Matrix Linear In Derivation
-- statement:
--   Definitions and structural lemmas for Kodaira Spencer Matrix Linear In Derivation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KodairaSpencerMatrixLinearInDerivation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticKodairaSpencerClassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FderivFnAddLattice
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace GlobalTheory.KS.Lin
section
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} {u : HolUnif A₀ L₀ g} {X : Scheme.{0}}
  {R : Type} [CommRing R] {p : X ⟶ Sp R} {m : A₀.left ⟶ X}
end
end GlobalTheory.KS.Lin


