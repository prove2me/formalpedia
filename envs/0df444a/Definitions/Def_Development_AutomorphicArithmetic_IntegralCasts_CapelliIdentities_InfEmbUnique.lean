-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfEmbUnique
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfEmbUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:25.803+00:00
-- url     : https://prove2.me/theorems/a8c5be1f-414b-446a-a878-cacd46092e00
-- title:
--   Inf Emb Unique
-- statement:
--   Definitions and structural lemmas for Inf Emb Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfEmbUnique.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf27.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F
noncomputable def UpperTheory.Reformulated.B.Qf27.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qf27.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qf27.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qf27.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))


