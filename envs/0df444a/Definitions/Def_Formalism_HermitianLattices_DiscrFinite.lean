-- Prove2me | Definitions.Def_Formalism_HermitianLattices_DiscrFinite
-- name    : Formalism_HermitianLattices_DiscrFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:03.791462+00:00
-- url     : https://prove2.me/theorems/8d3c770b-02f4-4935-8b27-7ad128a24485
-- title:
--   Discr Finite
-- statement:
--   Definitions and structural lemmas for Discr Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/DiscrFinite.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_ThetaLEuclid
import Definitions.Def_Formalism_AlphaUniqueness_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Formalism.K
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Defs
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V]
abbrev discr (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : Type _ :=
  (tdualSub h L) ⧸ (L.comap (tdualSub h L).subtype)
def drep (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (δ : discr h L) : V :=
  ((Submodule.mkQ_surjective (L.comap (tdualSub h L).subtype) δ).choose : tdualSub h L)
def qDiscr (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (δ : discr h L) : ℂ :=
  Complex.exp (Real.pi * Complex.I *
    ((Algebra.trace ℚ K (h (drep h L δ) (drep h L δ)) : ℚ) : ℂ))
variable [IsScalarTower (NumberField.RingOfIntegers K) K V]
def thetaVec (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (τ : ℂ)
    (δ : discr h L) : ℂ :=
  thetaL h L (drep h L δ) τ
end Defs
def ThetaWeil : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    L ≤ tdualSub h L → (∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h x x) = 2 * n) →
    ∀ [Fintype (discr h L)],
      IsUQuad (qDiscr h L) ∧ Nondeg (qDiscr h L) ∧
      (∀ τ : ℂ, thetaVec h L (τ + 1) = weilT (qDiscr h L) (thetaVec h L τ)) ∧
      ∀ τ : ℂ, 0 < τ.im →
        thetaVec h L (-τ⁻¹) = fun δ =>
          (-Complex.I * τ) ^ (((Module.finrank ℚ K * Module.finrank K V : ℕ) : ℂ) / 2) *
            weilS (qDiscr h L) (thetaVec h L τ) δ
def DiscrFinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    L ≤ tdualSub h L → Finite (discr h L)
end Formalism.HermitianLatticesTheory


