-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T09:29:13.167748+00:00
-- url     : https://prove2.me/theorems/7b6fdcd3-8c0e-45ea-957a-7a90ab62905b
-- title:
--   Form Right Mem
-- statement:
--   Definitions and structural lemmas for Form Right Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
def cnt (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (n : 𝓞 F)
    (Ω : Set V) : ℕ :=
  Nat.card {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω}
def fixS (x : V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g x = x}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a (b x) = x
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    change a.symm x = x
    rw [LinearEquiv.symm_apply_eq]
    exact ha.symm
def tube (D : Subgroup (V ≃ₗ[K] V)) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    Set V :=
  {y | ∃ g ∈ D, y - g x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V)}
end Formalism.HermitianLattices.Ext.L3.LIOrb


