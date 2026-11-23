-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInfEmbUnique
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInfEmbUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:50.117499+00:00
-- url     : https://prove2.me/theorems/e1bb3081-a997-448e-9f42-bc2342ef16d1
-- title:
--   Is Inf Emb Unique
-- statement:
--   Definitions and structural lemmas for Is Inf Emb Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsInfEmbUnique.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh26.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F
noncomputable def UpperTheory.Reformulated.B.Qh26.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qh26.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))


