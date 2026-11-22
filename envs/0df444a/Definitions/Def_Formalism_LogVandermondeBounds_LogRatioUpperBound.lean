-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_LogRatioUpperBound
-- name    : Formalism_LogVandermondeBounds_LogRatioUpperBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:13.359648+00:00
-- url     : https://prove2.me/theorems/1127a214-a2c8-484e-8eb7-0aeeb5820ac4
-- title:
--   Log Ratio Upper Bound
-- statement:
--   Definitions and structural lemmas for Log Ratio Upper Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogRatioUpperBound.lean

import Definitions.Def_Formalism_LogVandermondeBounds_LogRatioLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset
def plusSign (k i : ℕ) : Bool := decide (i < k - 1 ∨ (i - (k - 1)) % 2 = 0)
def nBetween (k a b : ℕ) : ℕ := ((Ioo a b).filter (fun c => plusSign k c ≠ plusSign k a)).card
noncomputable def dTau (k m : ℕ) (lam : ℕ → ℝ) : ℝ :=
  (∏ a ∈ range (k - 1 + m), ∏ b ∈ (Ico (a + 1) (k - 1 + m)).filter (fun b => plusSign k b = plusSign k a),
      (lam a - lam b + nBetween k a b)) /
    ((∏ i ∈ range (k - 1 + m / 2), ((i.factorial : ℕ) : ℝ)) * ∏ i ∈ range (m / 2), ((i.factorial : ℕ) : ℝ))
def LogRatioUpperBound : Prop :=
  ∀ (ε C₀ C₃ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → 1 ≤ C₃ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (f m k : ℕ) (vE Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ)
      (Dstar dstar massk massr Isig Ipi : ℝ) (Lval dsig : ℕ → ℝ),
    1 ≤ f → 2 ≤ m → Even m → 2 ≤ k → (m : ℝ) ^ 2 * L ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ vE → Real.log vE ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    Real.log g₁ ≤ C₀ * L → Real.log g₂ ≤ C₀ * L →
    (∀ ρ, ρ < f → PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ) ∧
      (∀ i j, i < j → j < k → 1 ≤ u ρ i - u ρ j)) →
    0 < massk → 0 < massr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Lval M ∧ |Real.log (Lval M)| ≤ f * Real.log (zetaR M)) →
    (hmass : massr = massk * ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) →
    (hidx : Isig / Ipi ≤ (2 : ℝ) ^ (2 * f) * (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2)) →
    (hD : Dstar = massr * Isig * ∏ ρ ∈ range f, dsig ρ) →
    (h3 : ∀ ρ, ρ < f → 0 < dsig ρ ∧ dsig ρ ≤ 4 * dTau k m (rowPar k (v ρ) (b ρ)) *
      (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) *
        (v ρ 0 + b ρ (m - 1))) ^ ((k - 1 + m / 2) * (m / 2))) →
    (hd : dstar = massk * Ipi * ∏ ρ ∈ range f, dimVN (u ρ) k) →
    (1 / ((f : ℝ) * k)) * Real.log (Dstar / dstar) ≤ C * m * L
end Formalism.LogVandermondeBounds.StandardLattice


