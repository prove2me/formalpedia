-- Prove2me | Definitions.Def_Formalism_HermitianLattices_ThetaLEuclid
-- name    : Formalism_HermitianLattices_ThetaLEuclid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:57.157892+00:00
-- url     : https://prove2.me/theorems/98d8b62a-ab1d-4b34-b45d-5fc9628a4059
-- title:
--   Theta LEuclid
-- statement:
--   Definitions and structural lemmas for Theta LEuclid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/ThetaLEuclid.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.HermitianLatticesTheory
def ThetaLEuclid : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
    (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V) (τ : ℂ),
      thetaL h L γ τ = thetaE (zmap ι L) (ι γ) τ
def ThetaLSLaw : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V),
      ∀ [DiscreteTopology (zmap ι L)] [IsZLattice ℝ (zmap ι L)],
    ∀ (γ : V) (τ : ℂ), 0 < τ.im →
      thetaL h L γ (-τ⁻¹) =
        (-Complex.I * τ) ^ ((N : ℂ) / 2) / (ZLattice.covolume (zmap ι L) : ℂ) *
          ∑' μ : tdualSub h L,
            Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ K (h γ μ) : ℚ) : ℂ)) *
            Complex.exp (Real.pi * Complex.I * τ * ((Algebra.trace ℚ K (h μ μ) : ℚ) : ℂ))
end Formalism.HermitianLatticesTheory


