-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_DividedPowerIntegrals_GenDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:22.632262+00:00
-- url     : https://prove2.me/theorems/d9ee6ae5-53ff-40bb-8a04-ce2dc5329658
-- title:
--   Gen Defs
-- statement:
--   Definitions and structural lemmas for Gen Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/DividedPowerIntegrals/GenDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace PI.DivPowInteg.Gen
section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]
noncomputable def gdelta (κ : I → J → K) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)
noncomputable def dL (κ : I → J → K) (i : I) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ j, κ i j • (pderiv (Sum.inr j)).toLinearMap
noncomputable def dR (κ : I → J → K) (j : J) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, κ i j • (pderiv (Sum.inl i)).toLinearMap
end
def PowXL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (gdelta κ ^ (n + 1)) (X (Sum.inl i) * R) =
      X (Sum.inl i) * (gdelta κ ^ (n + 1)) R + (n + 1) • dL κ i ((gdelta κ ^ n) R)
def PowXR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (j : J)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (gdelta κ ^ (n + 1)) (X (Sum.inr j) * R) =
      X (Sum.inr j) * (gdelta κ ^ (n + 1)) R + (n + 1) • dR κ j ((gdelta κ ^ n) R)
def CommL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ), (gdelta κ ^ n) (dL κ i R) = dL κ i ((gdelta κ ^ n) R)
def CommR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (j : J)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ), (gdelta κ ^ n) (dR κ j R) = dR κ j ((gdelta κ ^ n) R)
def VanL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (∀ m ∈ R.support, ∑ i, m (Sum.inl i) < n) → (gdelta κ ^ n) R = 0
def VanR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (∀ m ∈ R.support, ∑ j, m (Sum.inr j) < n) → (gdelta κ ^ n) R = 0
end PI.DivPowInteg.Gen


