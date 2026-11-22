-- Prove2me | Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
-- name    : Formalism_ResultantValuation_ResultantConjugate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:09:41.464421+00:00
-- url     : https://prove2.me/theorems/6d37c14a-edf6-4aaf-bd93-c80fc6bb2368
-- title:
--   Resultant Conjugate
-- statement:
--   Definitions and structural lemmas for Resultant Conjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantConjugate.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.ResultantValuation
def PermDetOnePlus : Prop :=
  ∀ (m : ℕ) (σ : Equiv.Perm (Fin m)),
    ((1 : Matrix (Fin m) (Fin m) ℚ) + σ.permMatrix ℚ).det ≠ 0 ↔ ∀ k ∈ σ.cycleType, Odd k
def ResultantConjugate : Prop :=
  ∀ (K : Type) [Field K] (c : K →+* K) (a b : ℕ) (α : Fin a → K) (β : Fin b → K)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)),
    (∀ i, α i ≠ 0) → (∀ j, β j ≠ 0) →
    (∀ i, c (α i) = (α (σ i))⁻¹) → (∀ j, c (β j) = (β (τ j))⁻¹) →
    (∏ i, ∏ j, (α i - β j)) =
      (-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a * c (∏ i, ∏ j, (α i - β j))
def CayleyDifference : Prop :=
  ∀ (K : Type) [Field K] (ε g₁ g₂ : K), (2 : K) ≠ 0 → ε ≠ 0 → g₁ + 1 ≠ 0 → g₂ + 1 ≠ 0 →
    g₁ = (ε + ε * (g₁ - 1) * (g₁ + 1)⁻¹) * (ε - ε * (g₁ - 1) * (g₁ + 1)⁻¹)⁻¹ ∧
    ε * (g₁ - 1) * (g₁ + 1)⁻¹ - ε * (g₂ - 1) * (g₂ + 1)⁻¹ =
      2 * ε * (g₁ - g₂) / ((g₁ + 1) * (g₂ + 1))
def LaplaceRows : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (M : Matrix (Fin (a + b)) (Fin (a + b)) R),
    M.det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a},
      (-1 : R) ^ (a * (a - 1) / 2 + ∑ j ∈ J.1, (j : ℕ)) *
        (M.submatrix (Fin.castAdd b) (J.1.orderEmbOfFin J.2)).det *
        (M.submatrix (Fin.natAdd a)
          ((J.1ᶜ).orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin, J.2]; omega))).det
def VandermondeSplit : Prop :=
  ∀ (R : Type) [CommRing R] (a b : ℕ) (z : Fin (a + b) → R),
    (Matrix.vandermonde z).det =
      (Matrix.vandermonde (z ∘ Fin.castAdd b)).det * (Matrix.vandermonde (z ∘ Fin.natAdd a)).det *
        ∏ i : Fin a, ∏ j : Fin b, (z (Fin.natAdd a j) - z (Fin.castAdd b i))
end Formalism.ResultantValuation


