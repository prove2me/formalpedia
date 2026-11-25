-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
-- name    : GroundTheory_AutomorphicForms_CuspidalSplittingSums
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:53.316922+00:00
-- url     : https://prove2.me/theorems/5b7b041b-1b63-4f5f-aee8-685e3e977b9b
-- title:
--   Cuspidal Splitting Sums
-- statement:
--   Definitions and structural lemmas for Cuspidal Splitting Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Function
open scoped Pointwise
section Sums
variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]
def quotSum (Φ : G → M) : M :=
  ∑ᶠ q : G ⧸ H, Φ q.out
variable {H}
variable [TopologicalSpace G] [IsTopologicalGroup G]
end Sums
section CompactModCenter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
end CompactModCenter
end Parabolic
end GroundTheory.Automorphic


