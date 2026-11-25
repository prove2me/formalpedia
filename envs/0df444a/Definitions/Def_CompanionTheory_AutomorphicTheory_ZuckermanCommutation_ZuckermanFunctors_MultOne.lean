-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
-- name    : CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:46:18.98348+00:00
-- url     : https://prove2.me/theorems/6e9dbabe-012c-4b64-8074-f752dad3f1ed
-- title:
--   Mult One
-- statement:
--   Definitions and structural lemmas for Mult One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
namespace CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
def cM (n : ℕ) : Matrix Unit (Fin n × Fin n) ℂ := fun _ p => if p.1 = p.2 then 1 else 0
def uM (ι : Type) [DecidableEq ι] : Matrix (Unit × ι) ι ℂ := fun p d => if p.2 = d then 1 else 0
end CompanionTheory.Zuck
end


