-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HtDualExists
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_HtDualExists
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:34:57.035163+00:00
-- url     : https://prove2.me/theorems/bdd0be96-8fe7-580b-b00d-f3bfbd714dad
-- title:
--   Ht Dual Exists
-- statement:
--   Definitions and structural lemmas for Ht Dual Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/HtDualExists.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvHtStatement
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_DualLattices_DualPairInh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
def htDualRing {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S) (ψ : LHom Λ S) :
    DualNum.DN Λ →+* (Dq.D : Type) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Dq.σ.1.comp ψ.1 : (Λ : Type) →ₐ[R₀] (Dq.D : Type)) :
      (Λ : Type) →+* (Dq.D : Type)) Dq.η) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sq, Dq.η_sq, mul_zero])
end GlobalTheory


