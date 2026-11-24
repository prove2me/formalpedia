-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.095146+00:00
-- url     : https://prove2.me/theorems/b0e0afb4-c579-429a-835e-b352f21a6cb4
-- title:
--   Lower Tri Of Interlaced
-- statement:
--   Definitions and structural lemmas for Lower Tri Of Interlaced, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LowerTriOfInterlaced.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace GlobalTheory.FockHighestWeight
variable {r n : ℕ}
def diagExp (r : ℕ) (ν : Fin n → ℕ) : Fin r × Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v.1.val = v.2.val then ν v.2 else 0
end GlobalTheory.FockHighestWeight


