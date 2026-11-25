-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_MuDefs
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:37.872165+00:00
-- url     : https://prove2.me/theorems/4c97f089-1ab7-4773-a47e-19ad6ac86009
-- title:
--   Mu Defs
-- statement:
--   Definitions and structural lemmas for Mu Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/MuDefs.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Theorems.Thm_Formalism_HC_HostRaw_exists_primitiveRoot_w
import Theorems.Thm_Formalism_HC_HostRaw_w_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
def muO (l : ℕ) : ℕ := Module.finrank H.E (CyclotomicField l H.E)
instance muW_neZero : NeZero H.w := ⟨H.w_pos.ne'⟩
def muGen : H.E := H.exists_primitiveRoot_w.choose
theorem muGen_prim : IsPrimitiveRoot H.muGen H.w := H.exists_primitiveRoot_w.choose_spec
def muExp : φ.GG →* (ZMod H.w)ˣ := (H.muGen_prim.autToPow ℚ).comp H.gal.symm.toMonoidHom
def psiAut (τ : φ.Psi) : H.E →+* H.E := (H.gal.symm (τ : φ.GG) : H.E →+* H.E)
def CondMU [Fintype φ.Psi] (a : φ.Psi → ℤ) : Prop := UpperTheory.MU H.psiAut a
abbrev IsRt (x : H.E) : Prop := H.IsMu x
abbrev muW : ℕ := H.w
end UpperTheory.HF.Formalism.HC.HostRaw
end


