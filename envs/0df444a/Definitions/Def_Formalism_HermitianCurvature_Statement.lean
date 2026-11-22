-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_Statement
-- name    : Formalism_HermitianCurvature_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:07:59.021816+00:00
-- url     : https://prove2.me/theorems/544df748-35fd-430c-bfc6-3427277c33e6
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt
open Finset Real NumberField
def RecursionSharp : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ),
    0 ≤ a → a ≤ 1/2 → 0 ≤ ε → ((r : ℝ) + 1) * (ε + a) ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * (ε + a)) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2
def RecursionText : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (a ε : ℝ) (e σ : ℕ → ℝ),
    0 ≤ a → a ≤ 1/2 → 0 ≤ ε → ε ≤ a → (r : ℝ) * a ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + ε) * √(1 + e i) * σ (i - 1) + ∑ t ∈ Icc 2 i, a ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * a) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2
def BoxSumOne : Prop :=
  ∀ Kx : ℝ, 2 < Kx → ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), b ≠ 0 →
    ∀ x : InfinitePlace E → ℝ, (∀ w, 0 < x w) →
      ∏ w, x w ≤ √(FractionalIdeal.absNorm b : ℝ) →
      ∀ S : Finset E, (∀ l ∈ S, l ∈ b ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx) ≤ C ^ Fintype.card (InfinitePlace E)
def DualSizeIdentity : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℝ) (g rd : ℝ) (r i : ℕ), 0 < g → 0 < rd →
    (∏ v, c v * (2 * π / g) ^ ((2 * i : ℤ) - 3 - 2 * r)) /
        (g * rd ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(Fintype.card ι : ℤ)) =
      (∏ v, c v) * (2 * π / rd) ^ (((2 * i : ℤ) - 3 - 2 * r) * Fintype.card ι) *
        g ^ (((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) * Fintype.card ι)
def MainConstant : Prop :=
  ∀ (P : Type) [Fintype P] (glk uk nn gg : P → ℝ) (ρ₀ ρ₀' dimπ dimπ' V₀ deg : ℝ),
    (∀ p, 0 < glk p) → (∀ p, 0 < uk p) → (∀ p, 0 < nn p) → (∀ p, 0 < gg p) →
    0 < V₀ → 0 < deg →
    (∏ p, (glk p / uk p) * (glk p * nn p) / gg p) * (ρ₀ * dimπ) * (ρ₀' * dimπ') / (V₀ * deg) =
      ((∏ p, glk p / uk p) * ρ₀ * dimπ) * ((∏ p, glk p / uk p) * ρ₀' * dimπ') /
        ((∏ p, gg p / (nn p * uk p)) * V₀ * deg)
def LeadingMinorsCount : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r : ℕ),
    Nat.card {C : Matrix (Fin r) (Fin r) K //
        ∀ (j : ℕ) (hj : j ≤ r), (C.submatrix (Fin.castLE hj) (Fin.castLE hj)).det ≠ 0} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r
def OmNorm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ip : V → V → ℂ),
    (∀ x y w, ip (x + y) w = ip x w + ip y w) → (∀ (s : ℂ) x y, ip (s • x) y = s * ip x y) →
    (∀ x y, ip y x = starRingEnd ℂ (ip x y)) →
    ∀ (z x : V) (T T' : ℝ) (Dr : ℂ), 0 < T → ip z z = -(T : ℂ) → ip x x = -(T' : ℂ) →
      ip (Dr • (x + (ip x z / (T : ℂ)) • z)) z = 0 ∧
      ip (Dr • (x + (ip x z / (T : ℂ)) • z)) (Dr • (x + (ip x z / (T : ℂ)) • z)) =
        (((Complex.normSq (Dr * ip x z) - T * T' * Complex.normSq Dr) / T : ℝ) : ℂ)
end Formalism.FourierDecayAlt


