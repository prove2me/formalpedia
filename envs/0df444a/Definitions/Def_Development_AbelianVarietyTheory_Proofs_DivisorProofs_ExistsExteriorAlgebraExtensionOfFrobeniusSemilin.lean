-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsExteriorAlgebraExtensionOfFrobeniusSemilin
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsExteriorAlgebraExtensionOfFrobeniusSemilin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:20.559132+00:00
-- url     : https://prove2.me/theorems/c7f3cea6-7114-4620-a0e0-b1706d8b7355
-- title:
--   Exists Exterior Algebra Extension Of Frobenius Semilin
-- statement:
--   Definitions and structural lemmas for Exists Exterior Algebra Extension Of Frobenius Semilin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsExteriorAlgebraExtensionOfFrobeniusSemilin.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI.FrobeniusTwistSmul
def FrobTw (K : Type) (p : ℕ) (W : Type) : Type := W
section
variable (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (W : Type) [AddCommGroup W] [Module K W]
instance : AddCommGroup (FrobTw K p W) := inferInstanceAs (AddCommGroup W)
instance : Module K (FrobTw K p W) := @Module.compHom K K W _ _ _ _ (frobenius K p)
end
end GlobalTheory.DI.FrobeniusTwistSmul


