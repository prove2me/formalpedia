-- Prove2me | Definitions.Def_Formalism_HermitianLattices_DefsCS
-- name    : Formalism_HermitianLattices_DefsCS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:33.272841+00:00
-- url     : https://prove2.me/theorems/e3f6692d-e686-45b3-8f77-84428b443da6
-- title:
--   Defs CS
-- statement:
--   Definitions and structural lemmas for Defs CS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/DefsCS.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
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
def zmap {V W : Type*} [AddCommGroup V] [AddCommGroup W] {R : Type*} [Ring R] [Module R V]
    (ι : V →+ W) (M : Submodule R V) : Submodule ℤ W :=
  (M.toAddSubgroup.map ι).toIntSubmodule
def TraceReal : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∃ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) ∧
      (∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖) ∧
      (∀ M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K M →
        ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))
def GenusCovol : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ L M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L → M ∈ genus h L →
    ∀ [DiscreteTopology (zmap ι L)] [IsZLattice ℝ (zmap ι L)]
      [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) = ZLattice.covolume (zmap ι L)
def ShortVectors : Prop :=
  ∀ (N : ℕ) (c C : ℝ), 0 < c → ∃ B : ℝ, ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    (∀ v ∈ Λ, v ≠ 0 → c ≤ ‖v‖) → ZLattice.covolume Λ ≤ C →
    ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ i, v i ∈ Λ) ∧ LinearIndependent ℝ v ∧
      ∀ i, ‖v i‖ ≤ B
def GenusScale : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∃ d : ℕ, 0 < d ∧ ∀ M ∈ genus h L, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)
def FinIntermediate : Prop :=
  ∀ (W : Type) [AddCommGroup W] (P Q : AddSubgroup W), P ≤ Q → Finite (Q ⧸ P.addSubgroupOf Q) →
    Set.Finite {M : AddSubgroup W | P ≤ M ∧ M ≤ Q}
def IsomOfTrace : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V),
    (∀ x y : V, Algebra.trace ℚ K (h (g x) (g y)) = Algebra.trace ℚ K (h x y)) → g ∈ isom h
end Formalism.HermitianLatticesTheory


