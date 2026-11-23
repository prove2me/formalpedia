-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:37.834651+00:00
-- url     : https://prove2.me/theorems/fc556dfc-56cd-4142-9813-da14c070dae3
-- title:
--   Val Iota Le Of Mem
-- statement:
--   Definitions and structural lemmas for Val Iota Le Of Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValIotaLeOfMem.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
def iota (a : OF E) : Af E := algebraMap E (Af E) (algebraMap (OF E) E a)
def LocIn (n : ℕ) (v : HeightOneSpectrum (OF E)) (z : Af E) : Prop :=
  ∃ a : OF E, ∀ P, Over P v → Valued.v (z P - iota a P) ≤ WithZero.exp (-(n : ℤ))
end GlobalTheory.CMVal.Euler


