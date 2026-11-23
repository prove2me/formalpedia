-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:00.5928+00:00
-- url     : https://prove2.me/theorems/61a1e039-ac0f-445b-ab5b-6c631aa296d0
-- title:
--   Bridge Level Gen A
-- statement:
--   Definitions and structural lemmas for Bridge Level Gen A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLevelGenA
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
def coprS (g : R) : Submonoid R where
  carrier := {s | IsCoprime s g ∧ s ≠ 0}
  one_mem' := ⟨isCoprime_one_left, one_ne_zero⟩
  mul_mem' := fun {_ _} ha hb => ⟨IsCoprime.mul_left ha.1 hb.1, mul_ne_zero ha.2 hb.2⟩
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
end Formalism.MainNotions.BridgeLevelGenA
end


