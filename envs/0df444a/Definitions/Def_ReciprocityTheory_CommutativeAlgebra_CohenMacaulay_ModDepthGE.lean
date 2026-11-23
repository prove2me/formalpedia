-- Prove2me | Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
-- name    : ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:17.185751+00:00
-- url     : https://prove2.me/theorems/e09b944d-21b0-420d-b6c7-b6d588aa828d
-- title:
--   Mod Depth GE
-- statement:
--   Definitions and structural lemmas for Mod Depth GE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/ModDepthGE.lean

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.CA
variable (R : Type*) [CommRing R] [IsLocalRing R] (M : Type*) [AddCommGroup M] [Module R M]
def ModDepthGE (n : ℕ) : Prop :=
  ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
    RingTheory.Sequence.IsRegular M rs
def IsCMMod : Prop :=
  IsNoetherianRing R ∧ Module.Finite R M ∧
    ∃ n : ℕ, Module.supportDim R M = n ∧ ModDepthGE R M n
end ReciprocityTheory.CA


