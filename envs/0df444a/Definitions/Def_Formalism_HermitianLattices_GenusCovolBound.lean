-- Prove2me | Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
-- name    : Formalism_HermitianLattices_GenusCovolBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:29.473632+00:00
-- url     : https://prove2.me/theorems/11a87a17-4295-4b5f-88ac-5f9402bfafae
-- title:
--   Genus Covol Bound
-- statement:
--   Definitions and structural lemmas for Genus Covol Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/GenusCovolBound.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
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
def tdualSub {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (M : Submodule (NumberField.RingOfIntegers K) V) :
    Submodule (NumberField.RingOfIntegers K) V :=
  Submodule.span (NumberField.RingOfIntegers K)
    {y | ∀ x ∈ M, ∃ z : ℤ, Algebra.trace ℚ K (h x y) = z}
def GenusCovolBound : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∃ C : ℝ, ∀ M ∈ genus h L, ∀ [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) ≤ C
def AutFinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
      Set.Finite {g : V ≃ₗ[K] V | g ∈ isom h ∧ gmap g L = L}
end Formalism.HermitianLatticesTheory


