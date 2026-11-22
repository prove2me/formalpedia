-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_StatementB
-- name    : Formalism_ThetaSupremumBounds_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:29.873723+00:00
-- url     : https://prove2.me/theorems/b56bec81-d8ad-4e6a-aa25-24f8b91f4ebd
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/StatementB.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory
open scoped Real Nat
noncomputable section
namespace Formalism.DimensionVariation
def DominanceMono : Prop :=
  ∀ (r : ℕ) (s μ ν : Fin r → ℝ), Antitone s → (∀ i, 0 ≤ s i) → (∀ i, 0 ≤ μ i) → (∀ i, 0 ≤ ν i) →
    (∀ k : ℕ, (∑ i ∈ univ.filter (fun i : Fin r => (i : ℕ) < k), μ i) ≤
      ∑ i ∈ univ.filter (fun i : Fin r => (i : ℕ) < k), ν i) →
    (∑ i, μ i) = ∑ i, ν i →
    (∏ i, s i ^ μ i) ≤ ∏ i, s i ^ ν i
def ClassSchur : Prop :=
  ∀ (Cl Cl' : Type) [Fintype Cl] [Fintype Cl'] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ) (T : Cl → Cl' → A →L[ℂ] B) (tmax : ℝ)
    (fn : Cl → A),
    (∀ L, 0 < γ L ∧ γ L ≤ 1) → (∀ L', 0 < γ' L' ∧ γ' L' ≤ 1) → (∀ L L', ‖ε L L'‖ = 1) →
    (∀ L L', ‖T L L'‖ ^ 2 ≤ tmax) →
    (∑ L', γ' L' * ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2) ≤
      ((Fintype.card Cl : ℝ) * (Fintype.card Cl' : ℝ)) * tmax * ∑ L, γ L * ‖fn L‖ ^ 2
def HminAMGM : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (β : Pl → ℝ) (v : ℝ), 0 < v → (∀ τ, 0 ≤ β τ) →
    ((2 * v) ^ Fintype.card Pl)⁻¹ ≤ ∏ τ, β τ →
    (Fintype.card Pl : ℝ) / v ≤ 2 * ∑ τ, β τ
def SupTailIntegral : Prop :=
  ∀ (g : ℕ) (h : ℝ), 1 ≤ g → 0 < h →
    (∫ u in Set.Ioi (0 : ℝ), (1 + 4 * u / h) ^ g * (π * Real.exp (-(π * u)))) ≤
      2 ^ (g - 1) * (1 + (4 / h) ^ g * (g ! : ℝ) / π ^ g)
def SupNumeric : Prop :=
  ∀ (g : ℕ) (h : ℝ), 1 ≤ g → 0 < h →
    (2 : ℝ) ^ g * (2 ^ g * (2 ^ (g - 1) * (1 + (4 / h) ^ g * (g ! : ℝ) / π ^ g))) ≤
      4 ^ g * (2 + 8 * (g : ℝ) / h) ^ g
def OriginColumn : Prop :=
  ∀ u e n0 n1 t i a : ℝ, n1 = n0 + t + 1 →
    (u - (n0 + 1 - 2 * i) / 2) + (e - n1 / 2) = (u + e) - (n0 + n1 + 1 - 2 * i) / 2 ∧
    (u - (n1 + 1 - 2 * i) / 2) + (e - n0 / 2) = (u + e) - (n0 + n1 + 1 - 2 * i) / 2 ∧
    (e - n0 / 2) - (e - n1 / 2) = (t + 1) / 2 ∧
    ((-e + (t + 2 - 2 * a) / 2) - (n1 + 1 - 2 * (n0 + a)) / 2) + (e - n0 / 2) = 0
def OriginBlock : Prop :=
  ∀ k t j j' a e e' : ℝ,
    ((-e' + (t + 2 - 2 * a) / 2) + e) -
      ((k + (j - 1) * (t + 1)) + (k + j * (t + 1)) + 1 - 2 * (k + (j' - 1) * (t + 1) + a)) / 2 =
      (e - e') - (j - j') * (t + 1)
def SignatureCount : Prop :=
  ∀ k m j : ℝ, 1 ≤ j → j ≤ m →
    -k + (k + j - 1) - (m - j) = 2 * j - 1 - m ∧ |((k + j - 1) - (m - j)) - k| ≤ m
def RowsOffTop : Prop :=
  ∀ (k : ℕ) (c : Fin k → ℝ) (w blk Cc N S m tt η C0 : ℝ),
    (∀ i, |c i| ≤ Cc * (N + S)) → 0 ≤ blk → blk ≤ m * (tt + 1) * η →
    0 ≤ w → 0 ≤ N → 0 ≤ S → 1 ≤ C0 → Cc ≤ C0 →
    ∃ δ : ℝ, (∑ i, (w + c i)) + blk = (k : ℝ) * w + δ ∧
      |δ| ≤ C0 * (w + (k : ℝ) * (N + S) + m * (tt + 1) * η)
def RowsTop : Prop :=
  ∀ (k2 : ℕ) (c : Fin (k2 + 1) → ℝ) (a w rk blk Cc N S m tt η b' x C0 : ℝ),
    (∀ i, |c i| ≤ Cc * (N + S)) → 0 ≤ blk → blk ≤ m * (tt + 1) * η →
    0 ≤ rk → rk ≤ 2 * b' / x → 1 ≤ x →
    0 ≤ w → 0 ≤ N → 0 ≤ S → 1 ≤ C0 → Cc ≤ C0 →
    ∃ δ : ℝ, a + (∑ i, (w + c i)) + rk + blk = a + ((k2 + 2 : ℕ) : ℝ) * w + δ ∧
      |δ| ≤ C0 * (w + ((k2 + 2 : ℕ) : ℝ) * (N + S) + m * (tt + 1) * η + ((k2 + 2 : ℕ) : ℝ) * b')
end Formalism.DimensionVariation


