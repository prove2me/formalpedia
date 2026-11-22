-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:38.22782+00:00
-- url     : https://prove2.me/theorems/8dc81fd0-1af6-4ffc-9685-fd2f9a2e95a9
-- title:
--   Length Quot Smul Range Free
-- statement:
--   Definitions and structural lemmas for Length Quot Smul Range Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/LengthQuotSmulRangeFree.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
namespace Formalism.NG
namespace QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
abbrev smulRange (M : Type*) [AddCommGroup M] [Module O M] (l : O) : Submodule O M :=
  LinearMap.range (l • (LinearMap.id : M →ₗ[O] M))
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
def img (E : Set (Module.End (FractionRing O) V)) (N : Submodule O V) : Submodule O V :=
  Submodule.span O {v | ∃ f ∈ E, ∃ n ∈ N, f n = v}
def Dsub (E : Set (Module.End (FractionRing O) V)) (N : Submodule O V)
    (U : Submodule (FractionRing O) V) : Submodule O N :=
  (img E N ⊔ (U.restrictScalars O ⊓ N)).comap N.subtype
section Eig
variable {X : Type*} {T : Subalgebra O (X → O)} {act : T →+* Module.End (FractionRing O) V}
end Eig
end QuotientPowerLengths
open QuotientPowerLengths
end Formalism.NG


