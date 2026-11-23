-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SesquilinearFlipConj
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SesquilinearFlipConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:32.931927+00:00
-- url     : https://prove2.me/theorems/e2c277e1-7975-4e12-8402-0b0558efda7d
-- title:
--   Sesquilinear Flip Conj
-- statement:
--   Definitions and structural lemmas for Sesquilinear Flip Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SesquilinearFlipConj.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SesquilinearFlipConj.HasSesq :
    {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Prop :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (π : Representation ℂ G V) ↦
      ∃ (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
        B ≠ (0 : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) ∧
          ∀ (g : G) (v w : V),
            ((B : V → V →ₗ⋆[ℂ] ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) v) : V → ℂ) (((π : G → V →ₗ[ℂ] V) g : V → V) w) =
              ((B : V → V →ₗ⋆[ℂ] ℂ) v : V → ℂ) w
namespace UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers
noncomputable def flipConj {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (by intro v₁ v₂ w; simp [map_add])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])
    (by intro v w₁ w₂; simp [map_add])
    (by intro c v w; simp [map_smulₛₗ, smul_eq_mul])
end UpperTheory.Reformulated.B.SesquilinearFlipConj.Helpers


