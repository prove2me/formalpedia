-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:45.035846+00:00
-- url     : https://prove2.me/theorems/330deeea-47f6-44f2-abbf-abcd7165dcba
-- title:
--   Alt Push
-- statement:
--   Definitions and structural lemmas for Alt Push, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/AltPush.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Finset
noncomputable section
namespace KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def permTerm (e : ι → ℕ) (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ∏ i, X (π i) ^ e i
def sgnP (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ((Equiv.Perm.sign π : ℤ) : MvPolynomial ι ℚ)
variable {r s : ℕ}
end KAlt
end
end GroundTheory.Heights₂.Heights


