-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:55.51354+00:00
-- url     : https://prove2.me/theorems/4fac1618-5cec-4c0c-906f-34ce8cf6db93
-- title:
--   Root Eq Of Sub Mem
-- statement:
--   Definitions and structural lemmas for Root Eq Of Sub Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
section Cyc
variable (N : ℕ) [NeZero N]
def zO : 𝓞 (Cond.Cyc N) := (Cond.z_spec N).toInteger
variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]
end Cyc
variable {φ : Frame} (H : HostRaw φ)
end Formalism.HC.Der
end


