-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSecOnNonvanishingOfTameQuotient
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:24.679512+00:00
-- url     : https://prove2.me/theorems/6d31006c-35df-4d1a-a529-7000b8e0245f
-- title:
--   Exists Sec On Nonvanishing Of Tame Quotient
-- statement:
--   Definitions and structural lemmas for Exists Sec On Nonvanishing Of Tame Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSecOnNonvanishingOfTameQuotient.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSumSmulSeparatingInertia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory.DescTheta
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
theorem le_pull_chart {L : LB X} (φ : Y ⟶ X) (O : X.Opens) (i : L.ι) :
    φ ⁻¹ᵁ (O ⊓ L.U i) ≤ φ ⁻¹ᵁ O ⊓ (L.pull φ).U (fun _ => i) :=
  le_inf (φ.preimage_mono inf_le_left)
    ((φ.preimage_mono inf_le_right).trans (pull_U φ (fun _ => i)).ge)
noncomputable def evalAt {k : Type} [Field k] (ζ : Sp k ⟶ X) (U : X.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ U) :
    Γ(X, U) →+* k :=
  (ζ.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
end GlobalTheory.DescTheta
namespace GlobalTheory
open DescTheta GlobalTheory.LB
end GlobalTheory


