-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
-- name    : Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:41.879661+00:00
-- url     : https://prove2.me/theorems/50ef5bb0-98ee-4577-ba11-84c7b89e48c0
-- title:
--   Quotient Upper Bounds Of Power Bounds
-- statement:
--   Definitions and structural lemmas for Quotient Upper Bounds Of Power Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/QuotientUpperBoundsOfPowerBounds.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
open Finset Polynomial
def progr (t₀ d : ℤ) (j : ℕ) : ℤ := t₀ + d * (j : ℤ)
def WindowCountAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (ζ : K) (t₀ d : ℤ) (Y₀ h : ℕ), IsCoprime d (p : ℤ) →
    ∑ j ∈ range Y₀, vmin p h ((progr t₀ d j : K) - ζ) ≤ ∑ i ∈ Icc 1 h, ((Y₀ : ℝ) / (p : ℝ) ^ i + 1)
open Classical in
def DiscsDisjointAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (t₀ d : ℤ) (Y₀ h : ℕ), IsCoprime d (p : ℤ) → Y₀ ≤ p ^ h →
    ∑ j ∈ range Y₀, (roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card ≤
      roots.card
open Classical in
def WindowMeanAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (roots : Multiset K) (lam La₀ E : ℝ) (n₀ del₀ : ℕ) (t₀ d : ℤ) (Y₀ h : ℕ) (β : ℤ → ℕ),
    IsCoprime d (p : ℤ) → 0 < Y₀ → Y₀ ≤ p ^ h → 0 < E →
    roots.card ≤ del₀ * n₀ →
    lam + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * La₀ →
    (∀ j ∈ range Y₀,
      (β (progr t₀ d j) : ℝ) * E ≤ (lam + (roots.map (fun ζ => vmin p h ((progr t₀ d j : K) - ζ))).sum) +
        E * ((roots.filter (fun ζ => ‖(progr t₀ d j : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)))).card : ℝ)) →
    (∑ j ∈ range Y₀, (β (progr t₀ d j) : ℝ)) / (Y₀ : ℝ) ≤
      (n₀ : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)
open Classical in

def WindowFullAP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (n del₀ h : ℕ) (E : ℝ) (c : Fin n → Fin n → ℕ → K) (lead : K) (roots : Multiset K) (t₀ d : ℤ) (Y₀ : ℕ)
    (La₀ : ℝ) (U V : ℤ → Matrix (Fin n) (Fin n) K) (dg : ℤ → Fin n → K),
    IsCoprime d (p : ℤ) → 0 < Y₀ → Y₀ ≤ p ^ h → del₀ ≤ p ^ h → 0 < E → lead ≠ 0 → (∀ i j k, ‖c i j k‖ ≤ 1) →
    (binMatK K del₀ c).det = Polynomial.C lead * (roots.map (fun ζ => X - Polynomial.C ζ)).prod →
    (∀ j ∈ range Y₀, (∀ a b, ‖U (progr t₀ d j) a b‖ ≤ 1) ∧ (∀ a b, ‖V (progr t₀ d j) a b‖ ≤ 1) ∧
      ‖(U (progr t₀ d j)).det‖ = 1 ∧ ‖(V (progr t₀ d j)).det‖ = 1 ∧
      (binMatK K del₀ c).map (Polynomial.eval ((progr t₀ d j : ℤ) : K)) =
        U (progr t₀ d j) * Matrix.diagonal (dg (progr t₀ d j)) * V (progr t₀ d j)) →
    -Real.logb p ‖lead‖ + (roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La₀ →
    (∑ j ∈ range Y₀, ((univ.filter (fun i => ‖dg (progr t₀ d j) i‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) / (Y₀ : ℝ) ≤
      (n : ℝ) * ((del₀ : ℝ) / Y₀ + (La₀ + (del₀ : ℝ) * h / Y₀) / E)
def QuotientUpperBoundsOfPowerBounds : Prop :=
  ∀ (p a Y k Ns Qn be : ℝ) (D₁ L₁ Rj Rn : ℤ),
    1 < p → 0 < a → 0 < Y → 0 < k → 0 < Ns → 0 < Qn →
    be ≤ 4 * a * p ^ (-D₁ - L₁ - Rj) →
    a / (8 * Y * k ^ 2 * Ns * p ^ D₁ * Qn) < p ^ (Rn + 1) →
    128 * k ^ 2 * Ns * Y ^ 2 ≤ p ^ (L₁ - 1) →
    be / (Qn * p ^ (Rn - Rj)) ≤ 32 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ∧
      32 * p * Y * k ^ 2 * Ns * p ^ (-L₁) ≤ 1 / (4 * Y)
noncomputable def lgV2 (p a r : ℕ) : ℝ := Real.logb p (8 * a + r) + 1
end Formalism.GM


