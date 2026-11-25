-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_RecH
-- name    : Development_AutomorphicArithmetic_PrimitiveCosets_RecH
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:33:17.346494+00:00
-- url     : https://prove2.me/theorems/47205ff8-439e-4772-8d29-59c7811d562c
-- title:
--   Rec H
-- statement:
--   Definitions and structural lemmas for Rec H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/RecH.lean

import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace UpperTheory.Comparison₂
open Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost
def toE (φ : Frame) : φ.GG →* Multiplicative (E0 × φ.A) where
  toFun g := Multiplicative.ofAdd ((Multiplicative.toAdd (sgn2 g.1.2), Multiplicative.toAdd (sgn2 g.1.1)), φ.iotaInv g.2)
  map_one' := by
    simp only [Prod.snd_one, Prod.fst_one, map_one]
    rfl
  map_mul' g h := by
    simp only [Prod.snd_mul, Prod.fst_mul, map_mul]
    rfl
variable {φ : Frame}
def recH (H : HostRaw φ) : (ZMod H.condN)ˣ →* Multiplicative (E0 × φ.A) := (toE φ).comp H.art
def arith (H : HostRaw φ) : ArithData φ.A := cftData H.q H.d (recH H)
end UpperTheory.Comparison₂
end


