-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_ClopenCondOnto
-- name    : Development_AutomorphicSpectrum_Definitions_MetricPeriods_ClopenCondOnto
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:00.342832+00:00
-- url     : https://prove2.me/theorems/33eaabf4-adff-4d39-993e-bf9a1ae38065
-- title:
--   Clopen Cond Onto
-- statement:
--   Definitions and structural lemmas for Clopen Cond Onto, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/ClopenCondOnto.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat
open Matrix Metric GroundTheory.Heights₂.Heights.Regular
structure LogPeriods (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] where
  a_le : a ≤ n
  free : Module.Free ℤ Λ
  fin : Module.Finite ℤ Λ
  rank : Module.finrank ℤ Λ = 2 * g

  E : LinearMap.BilinForm ℤ Λ
  alt : ∀ x, E x x = 0
  unimod : Function.Bijective E

  P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))
  hol : ∀ x, DifferentiableOn ℂ (fun w => P w x) (logCover a_le)

  H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  herm : ∀ w ∈ logCover a_le, (H (expCover a w)).IsHermitian
  pos : ∀ w ∈ logCover a_le, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H (expCover a w) *ᵥ star z).re
  im : ∀ w ∈ logCover a_le, ∀ x y, (P w x ⬝ᵥ H (expCover a w) *ᵥ star (P w y)).im = E x y

  T : Fin a → (Λ →ₗ[ℤ] Λ)
  mono : ∀ i, ∀ w ∈ logCover a_le, ∀ x,
    P (w + Pi.single (Fin.castLE a_le i) (2 * Real.pi * Complex.I)) x = P w (T i x)

  W : Submodule ℤ Λ
  coiso : ∀ x, (∀ y ∈ W, E x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W

  s : W → (Fin n → ℂ) → (Fin g → ℂ)
  s_hol : ∀ x, DifferentiableOn ℂ (s x) (ball 0 1)
  s_eq : ∀ x, ∀ w ∈ logCover a_le, s x (expCover a w) = P w x
  span : Submodule.span ℂ (Set.range fun x => s x 0) = ⊤
end GlobalTheory.CompanionTheory.Ar.Flat


