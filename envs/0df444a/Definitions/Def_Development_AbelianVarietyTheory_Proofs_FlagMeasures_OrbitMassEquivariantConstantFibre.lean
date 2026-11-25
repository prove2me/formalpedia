-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEquivariantConstantFibre
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:55:46.225897+00:00
-- url     : https://prove2.me/theorems/f85b6c2f-3eff-4226-80b8-6dbe7d146081
-- title:
--   Orbit Mass Equivariant Constant Fibre
-- statement:
--   Definitions and structural lemmas for Orbit Mass Equivariant Constant Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitMassEquivariantConstantFibre.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.MassFibre
end GlobalTheory.MassFibre
namespace GlobalTheory.MassFibre
open MulAction
noncomputable def wt {G : Type} [Group G] (Γ : Subgroup G) {Y : Type} [MulAction G Y] (y : Y) : ℝ≥0∞ :=
  ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹
end GlobalTheory.MassFibre
namespace GlobalTheory.MassFibre
end GlobalTheory.MassFibre


