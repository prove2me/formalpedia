-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbedding
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinitePadicIntDomainEmbedding
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:51.676393+00:00
-- url     : https://prove2.me/theorems/5b5ecfd8-770c-4d6b-90d3-98cb2abc23b1
-- title:
--   Exists Finite Padic Int Domain Embedding
-- statement:
--   Definitions and structural lemmas for Exists Finite Padic Int Domain Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinitePadicIntDomainEmbedding.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteOfFiniteQuotMapOfIsPrecomplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.CompletionEmbed
variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsLocalRing C]
noncomputable def levelMap (hpm : (p : C) ∈ maximalIdeal C) (n : ℕ) :
    ℤ_[p] →+* C ⧸ maximalIdeal C ^ n :=
  have h : ((p ^ n : ℕ) : C ⧸ maximalIdeal C ^ n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal C ^ n)), Ideal.Quotient.eq_zero_iff_mem,
      Nat.cast_pow]
    exact Ideal.pow_mem_pow hpm n
  (ZMod.castHom (ringChar.dvd h) (C ⧸ maximalIdeal C ^ n)).comp (PadicInt.toZModPow n)
theorem levelMap_compat (hpm : (p : C) ∈ maximalIdeal C) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (levelMap p C hpm n) =
      levelMap p C hpm m := by
  unfold levelMap
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _
noncomputable def toCompletion (hpm : (p : C) ∈ maximalIdeal C) :
    ℤ_[p] →+* AdicCompletion (maximalIdeal C) C :=
  AdicCompletion.liftRingHom (maximalIdeal C) (levelMap p C hpm)
    (fun hle => levelMap_compat p C hpm hle)
end GlobalTheory.CompletionEmbed


