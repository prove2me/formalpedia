-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPairLat
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemPairLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:52.597067+00:00
-- url     : https://prove2.me/theorems/9b1f6e3a-6072-4dcc-b53b-943ab71dd1db
-- title:
--   Mem Pair Lat
-- statement:
--   Definitions and structural lemmas for Mem Pair Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemPairLat.lean

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
open NumberField
open scoped nonZeroDivisors
namespace GlobalTheory.SkewLat
variable {E : Type} [Field E] [NumberField E]
def scLat {n : ℕ} (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ}
  zero_mem' := fun c _ => by rw [smul_zero]; exact Λ.zero_mem
  add_mem' := fun hx hy c hc => by rw [smul_add]; exact Λ.add_mem (hx c hc) (hy c hc)
  smul_mem' := fun r y hy c hc => by rw [smul_comm]; exact Λ.smul_mem r (hy c hc)
def blkA {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin a → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inl)
def blkB {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) : (Fin d → E) →ₗ[𝓞 E] (Fin b → E) :=
  LinearMap.funLeft (𝓞 E) E (e ∘ Sum.inr)
def pairLat {a b d : ℕ} (ΛA : Submodule (𝓞 E) (Fin a → E)) (ΛB : Submodule (𝓞 E) (Fin b → E))
    (e : Fin a ⊕ Fin b ≃ Fin d) : Submodule (𝓞 E) (Fin d → E) :=
  ΛA.comap (blkA e) ⊓ ΛB.comap (blkB e)
end GlobalTheory.SkewLat
end


