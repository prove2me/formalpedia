-- Prove2me | Definitions.Def_Formalism_TowerValuationBounds_TowerValuationBoundIndexed
-- name    : Formalism_TowerValuationBounds_TowerValuationBoundIndexed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:34.611452+00:00
-- url     : https://prove2.me/theorems/24d4aa62-b507-42b3-8cc0-dec7b331b827
-- title:
--   Tower Valuation Bound Indexed
-- statement:
--   Definitions and structural lemmas for Tower Valuation Bound Indexed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TowerValuationBounds/TowerValuationBoundIndexed.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ValuationGridEstimates
open Finset
def TowerValuationBoundIndexed : Prop :=
  ∀ (G : Type) [CommGroup G] (v : G → ℝ), (∀ x y, v (x * y) = v x + v y) →
    ∀ (a a' d h p q e : ℕ), a + a' = d → a = a' + 2 * e → d = 2 * h →
    2 * (p + q) + 1 < e → 2 * (p + q) + 1 < a' →
    ∀ (T Td Tdp ρ E : ℤ → G) (N0 : ℤ → ℝ) (ε δ σ : ℝ),
    (∀ s : ℤ, 1 ≤ s → s ≤ h →
      0 ≤ N0 s ∧ ρ s = Tdp s / T s ∧ -N0 s ≤ v (Tdp s) ∧ v (Tdp s) ≤ v (Td s) + ε) →
    (∀ s : ℤ, 1 - ((e : ℤ) + q - p) ≤ s → s ≤ 0 → ρ s = E s * ρ (1 - s) ∧ v (E s) = 0) →
    ∀ (c0 c00 A A0 A0' : G), v c0 ≤ v A + 3 * δ → -v c00 ≤ v A0' + 3 * δ →
    A / A0 = ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), ρ s →
    ∀ (ub ua : ℕ → G), (∀ j, j < q → v (ub j) ≤ σ) → (∀ i, i < p → v (ua i) ≤ σ) →
    ∀ r : G, r = ((∏ j ∈ range q, ub j) * ∏ i ∈ range p, ua i) * (c0 / c00) *
        (∏ k ∈ Icc 1 p, ρ ((e : ℤ) + q - k + 1)) * (∏ k ∈ Icc 1 q, ρ ((e : ℤ) + k))⁻¹ →
    v r ≤ v A0 + v A0' + 3 * (∑ s ∈ Icc (1 : ℤ) h, |v (T s)|) + 2 * (∑ s ∈ Icc (1 : ℤ) h, |v (Td s)|) +
      ((a : ℝ) - p) * ε + 5 * (∑ s ∈ Icc (1 : ℤ) h, N0 s) + 6 * δ + (p + q : ℕ) * σ
def GridValuationBoundIndexed : Prop :=
  ∀ (W X S : Type) (m N : ℕ) (lam δ : W → ℝ) (ell : W → ℕ) (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
    (vr : W → Fin m × Fin m → ℝ) (vx : W → X → ℝ) (XX : Fin m × Fin m → Bool → Finset X)
    (ch : W → Bool) (dd hh yy : Fin m × Fin m → ℕ) (S0 : Finset S) (cc ee qq : S → ℕ)
    (vq : W → S → ℝ) (H : X → ℝ) (BN Bδ : ℝ) (W0 : Finset W),
    (∀ w, 0 ≤ lam w) → (∀ w, 0 ≤ δ w) → (∀ ij s l, 0 ≤ N0 ij s l) → (∀ w s, 0 ≤ vq w s) →
    (∀ w, (ell w).Prime) →
    (∀ (l : ℕ) (F : Finset W), (∀ w ∈ F, ell w = l) → ∑ w ∈ F, lam w ≤ Real.log l) →
    (∀ ij, dd ij = 2 * hh ij) → (∀ ij, dd ij ≤ 2 * N) → (∀ ij, yy ij ≤ m) →
    (∀ s ∈ S0, cc s ≤ ee s) →
    (∀ w ∈ W0, ∀ ij, vr w ij ≤ (∑ x ∈ XX ij (ch w), |vx w x|) +
      5 * (∑ s ∈ Icc (1 : ℤ) (hh ij), N0 ij s (ell w)) + dd ij * ((ell w : ℝ) ^ 2)⁻¹ + 6 * δ w +
      2 * yy ij * (∑ s ∈ S0, (cc s : ℝ) * vq w s)) →
    (∀ (x : X) (F : Finset W), ∑ w ∈ F, lam w * |vx w x| ≤ H x) →
    (∀ ij (s : ℤ) (P : Finset ℕ), (∀ l ∈ P, l.Prime) → ∑ l ∈ P, N0 ij s l * Real.log l ≤ BN) →
    (∀ F : Finset W, ∑ w ∈ F, lam w * δ w ≤ Bδ) →
    (∀ s ∈ S0, ∀ F : Finset W, ∑ w ∈ F, lam w * vq w s ≤ Real.log (qq s)) →
    ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) +
      (m : ℝ) ^ 2 * (10 * N * BN + 2 * N + 6 * Bδ + 4 * m * ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s))
end Formalism.ValuationGridEstimates


