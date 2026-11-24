-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T19:39:09.441442+00:00
-- url     : https://prove2.me/theorems/e6f6e188-6acf-476d-aae5-e4f590a0770b
-- title:
--   Cyc Basic
-- statement:
--   Definitions and structural lemmas for Cyc Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb

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
section Generic
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
end Generic
section Cyc
variable (N : ℕ) [NeZero N]
def tauN : (ZMod N)ˣ ≃* (Cond.Cyc N ≃ₐ[ℚ] Cond.Cyc N) :=
  (IsCyclotomicExtension.Rat.galEquivZMod N (Cond.Cyc N)).symm
end Cyc
variable {φ : Frame} (H : HostRaw φ)
instance neZero_condN : NeZero H.condN :=
  ⟨by have := H.QS_pos; have := H.hyp.1.pos; have := H.hyp.2.1.pos; positivity⟩
def emb : H.E →ₐ[ℚ] Cond.Cyc H.condN := H.cycEmb
end Formalism.HC.Der
end


