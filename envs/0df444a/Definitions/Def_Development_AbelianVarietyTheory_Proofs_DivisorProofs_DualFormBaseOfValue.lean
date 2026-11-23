-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormBaseOfValue
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormBaseOfValue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:01.452814+00:00
-- url     : https://prove2.me/theorems/57a9ba7c-4636-4d8e-9339-0ff8f702b7a6
-- title:
--   Dual Form Base Of Value
-- statement:
--   Definitions and structural lemmas for Dual Form Base Of Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormBaseOfValue.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
namespace GlobalTheory.DualBase
example (ε : ℤˣ) (η : ℤˣ) (hε : ε = 1) (hη : η = -1) : (((ε * η : ℤˣ) : ℤ) : ℂ) = -1 := by
  subst hε hη; simp
end GlobalTheory.DualBase


