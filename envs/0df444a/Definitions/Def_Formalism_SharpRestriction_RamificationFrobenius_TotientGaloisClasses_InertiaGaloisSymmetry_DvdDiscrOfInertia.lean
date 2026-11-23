-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:28.168106+00:00
-- url     : https://prove2.me/theorems/7fe8a943-0281-4559-ad24-1ca463276444
-- title:
--   Dvd Discr Of Inertia
-- statement:
--   Definitions and structural lemmas for Dvd Discr Of Inertia, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/DvdDiscrOfInertia.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
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
open Formalism.FrobeniusOrbits
namespace Rd
variable {φ : Frame} (H : HostRaw φ)
instance neZeroN : NeZero H.condN :=
  ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩
theorem two_dvd : 2 ^ (φ.e + 2) ∣ H.condN := (H.tower_dvd.mul_right _).mul_right _
end Rd
open Rd
variable {φ : Frame} (H : HostRaw φ)
end Formalism.HC.Der
end


