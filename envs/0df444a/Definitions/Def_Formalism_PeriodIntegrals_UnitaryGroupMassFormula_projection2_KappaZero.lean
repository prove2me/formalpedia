-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:02.804868+00:00
-- url     : https://prove2.me/theorems/57f69bc8-2760-4f4b-a382-302f70ce0b4f
-- title:
--   Kappa Zero
-- statement:
--   Definitions and structural lemmas for Kappa Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/KappaZero.lean

import Definitions.Def_Formalism_PeriodIntegrals_OneCosetSharp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OneCosetSharp.W
open Loc LocE
def Nums (k₀ m t j n' c n : ℕ) : Prop :=
  1 ≤ k₀ ∧ Even m ∧ 4 ≤ m ∧ 1 ≤ j ∧ j ≤ m - 2 ∧ c = m - 1 - j ∧
    n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = k₀ + m - 1 + j * t
def Claim1 : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    Nums k₀ m t j n' c n →
    ∀ h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
        (∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
          E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) →
        ∃ ρ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ h = ρ * κ
def Claim2 : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    Nums k₀ m t j n' c n →
    ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
      E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (PhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0
def PatClosed : Prop :=
  ∀ (k : Type) [Field k] (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ κ₁ κ₂ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), InJS k₀ m t c n κ₁ → InJS k₀ m t c n κ₂ →
      InJS k₀ m t c n (κ₁ * κ₂) ∧ InJS k₀ m t c n κ₁⁻¹
def KappaZero : Prop :=
  ∀ (k : Type) [Field k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k), PhiS ψ₀ χ k₀ m t j n' c n y ≠ 0 →
      ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), InJS k₀ m t c n κ ∧
        ∀ p < n' + (c + 1), κ (eN k (n + c) (fIdx k₀ c n p)) = y (eN k (n' + (c + 1)) (fIdx k₀ (c + 1) n' p))
def NElem : Prop :=
  ∀ (k : Type) [Field k] (n' c n : ℕ) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k),
    ∃ ν ∈ R1 k n c, (∀ v, ν (inX k n c v) = inX k n c v) ∧
      ∀ i < c, ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i))
def GaStep : Prop :=
  ∀ (k : Type) [Field k] (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
      (∀ i < c, g (eN k (n + c) (n + i)) = eN k (n + c) (n + i)) →
      (∀ p < n' + (c + 1), (p < k₀ ∨ k₀ + c < p) → ∃ v, g (eN k (n + c) (fIdx k₀ c n p)) = inX k n c v) →
      ∃ γ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ g = γ * κ
end PI.OneCosetSharp.W


