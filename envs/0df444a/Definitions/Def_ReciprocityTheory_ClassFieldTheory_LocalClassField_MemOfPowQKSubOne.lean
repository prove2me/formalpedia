-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:30.781811+00:00
-- url     : https://prove2.me/theorems/82b97a25-ab95-4d7f-8be7-6f091b62c6ac
-- title:
--   Mem Of Pow QKSub One
-- statement:
--   Definitions and structural lemmas for Mem Of Pow QKSub One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/MemOfPowQKSubOne.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime]
noncomputable def red (x : PadicAlgCl p) : kbar p :=
  open Classical in if h : ‖x‖ ≤ 1 then res ⟨x, mem_Obar_iff.2 h⟩ else 0
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions


