-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvariantSubspaceMobiusInverseOneProdIco
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:37.831599+00:00
-- url     : https://prove2.me/theorems/5bcc1b70-85a8-4557-aeed-a9311c260329
-- title:
--   Invariant Subspace Mobius Inverse One Prod Ico
-- statement:
--   Definitions and structural lemmas for Invariant Subspace Mobius Inverse One Prod Ico, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumGaussianMulProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
noncomputable def oneValue (q a : ℕ) : ℂ :=
  if a = 0 then 0 else ∏ i ∈ Finset.Ico 1 a, (1 - (q : ℂ) ^ i)
end GlobalTheory.CuspGL


