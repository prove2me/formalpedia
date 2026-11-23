-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ModuliPointsState
-- name    : ReciprocityTheory_DualLattices_ModuliPointsState
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:25.845623+00:00
-- url     : https://prove2.me/theorems/b5b3943b-5264-47ed-b1e6-dc5748c5c9a5
-- title:
--   Moduli Points State
-- statement:
--   Definitions and structural lemmas for Moduli Points State, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ModuliPointsState.lean

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
structure DualPair (R : LAlg R₀) where
  D : LAlg R₀
  π : LHom D R
  σ : LHom R D
  η : (D : Type u)
  sect : ∀ r, π.1 (σ.1 r) = r
  η_sq : η * η = 0
  ker_eq : RingHom.ker π.1 = Ideal.span {η}
  free : ∀ r, σ.1 r * η = 0 → r = 0
namespace DualPair
variable {R : LAlg R₀} (Dp : DualPair R)
lemma η_mem : Dp.η ∈ Dp.π.ker := by
  show Dp.η ∈ RingHom.ker Dp.π.1
  rw [Dp.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)
lemma sqZero : Dp.π.SqZero := by
  refine ⟨fun r => ⟨Dp.σ.1 r, Dp.sect r⟩, ?_⟩
  rw [Dp.ker_eq, Ideal.span_singleton_pow, pow_two, Dp.η_sq, Ideal.span_singleton_eq_bot]
def ηk : Dp.π.ker := ⟨Dp.η, Dp.η_mem⟩
end DualPair
namespace BX
variable (B : BX R₀)
def IsHeight {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] R) : Prop :=
  ∀ v : B.gg, ∃ z : (Dp.D : Type u)ˣ,
    B.IsPairing N (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y) z ∧ (z : Dp.D) = 1 + Dp.σ.1 (h v) * Dp.η
end BX
def HighestWeightVectorUniformBounds (B : BX R₀) : Prop :=
  ∀ (R : LAlg R₀) (Dp : DualPair R) (N : ℕ), (N : (R : Type u)) = 0 →
    (∀ (y : B.G R) (v : B.gg) (u : B.P Dp.D (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y)),
      HEq (B.pmap Dp.π u) (B.zero1 y) →
      HEq (B.nsmul1 u N) (B.zero1 (B.map Dp.σ y))) ∧
    (∀ y : B.G R, N • y = 0 → ∃! h : B.gg →ₗ[R₀] R, B.IsHeight Dp N y h) ∧
    (∀ (y y' : B.G R) (h h' : B.gg →ₗ[R₀] R), B.IsHeight Dp N y h → B.IsHeight Dp N y' h' →
      B.IsHeight Dp N (y + y') (h + h'))
end ReciprocityTheory.PGsh


