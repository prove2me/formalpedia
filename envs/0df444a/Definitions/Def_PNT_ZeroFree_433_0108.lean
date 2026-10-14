-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0108
-- name    : PNT_ZeroFree_433_0108
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:02:30.236208+00:00
-- url     : https://prove2.me/theorems/aee65805-8cd7-49ef-80e1-1fbf86dc9d2a
-- title:
--   Zero-free region foundations: QuadraticSieve.MiddleWindows [0108]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/MiddleWindows.lean#L98-L620

import Definitions.Def_PNT_ZeroFree_433_0107

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/MiddleWindows.lean#L98-L620
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.MiddleWindows
section
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.original_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    originalMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B)
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.original_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply original_middle_rectangle_upper M B (Ideal.absNorm (rows i)) D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM (by linarith) (hrows i).2.1 hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) = fun _ => 0 :=
      funext (fun h => originalMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.dual_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U *
        (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    dualMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M F P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B)))
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.dual_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W F hF hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM hF (by linarith) (hrows i).2.1 (by linarith) hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) = fun _ => 0 :=
      funext (fun h => dualMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M F P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FourierBridge

theorem large_principal_scale_shape (X N Q D V : ℝ) (hD : 0 < D)
    (hcut : X * N ≤ V * D) :
    (X / D) * (N + Q * D) ≤ V + X * Q := by
  have hh : X * N / D ≤ V := (div_le_iff₀ hD).mpr hcut
  calc
    _ = X * N / D + X * Q := by field_simp
    _ ≤ _ := add_le_add hh le_rfl

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalCorrectionAt (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
  (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
  (a : n → ℂ) (b : p → ℂ)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hleft hright

theorem principalCorrectionAt_bound :
    principalCorrectionAt S T rows left right a b M ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hh := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT
    rows left right hr hl hri (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) hleft hright a b
    (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add, logPhase_zero, mul_one] at hh
  have heq : (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖) =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ := by
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E.val i j k‖)]
    apply Finset.sum_congr rfl
    intro D hD
    exact Finset.sum_coe_sort T (fun E => ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)
  have hp := principal_middle_prefactor_sum S T rows
    (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖)
    (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
    (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
  change principalCorrectionAt S T rows left right a b M ≤ _ at hp
  rw [heq] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hh (by positivity))

theorem HasSieveExponent.large_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (V : ℝ)
    (hcut : Real.sqrt (M / B) * N ≤ V * (D₁ * D₂)) :
    principalCorrectionAt S T rows left right a b M ≤
      2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (V + Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hb := principalCorrectionAt_bound ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a b
  have hf := divisorEnergyFactor_nonneg ε hε N a b
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        (divisorEnergyFactor ε hε N a b *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        ((Real.sqrt (M / B) / (D₁ * D₂)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        (V + Real.sqrt (M / B) * B ^ α) := mul_le_mul_of_nonneg_left
      (large_principal_scale_shape _ _ _ _ _ (by positivity) hcut) (by positivity)
    _ = _ := by rw [sqrt_div_mul_rpow M B α hM.le (by linarith)]

end

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem sum_two_subtype_pools {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (f : Ideal O → Ideal O → A) :
    (∑ D : S, ∑ E : T, f D.val E.val) = ∑ D ∈ S, ∑ E ∈ T, f D E := by
  rw [Finset.sum_coe_sort S (fun D => ∑ E : T, f D E.val)]
  apply Finset.sum_congr rfl
  intro D hD
  exact Finset.sum_coe_sort T (f D)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold originalMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M P h := by
  classical
  simp_rw [originalMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.original_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.original_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply originalMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply originalMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact originalMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold dualMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) / (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M F P h := by
  classical
  simp_rw [dualMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.dual_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M F P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.dual_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W F hF P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply dualMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply dualMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact dualMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M F P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_double_sum_real_factor {n p : Type*} [Fintype n] [Fintype p]
    (u : n → p → ℂ) (z : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z)‖ = c * ‖∑ j, ∑ k, u j k * z‖ := by
  simp only [← Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (M : ℝ) (h : O)
    (d : Ideal O) (i : m) : ℂ :=
  ((Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) *
      ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def originalProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ left j * right k then
      originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalProductDivisorMiddleAt W K rows left right a b M P h := by
  classical
  unfold originalProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    originalProductDivisorMiddleAt W K rows left right a b M P h ≤
      originalMiddleWindowAt W S T rows left right a b M (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i _ _ => originalPrincipalKernel W rows M h d i)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [originalMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold originalPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.original_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hs := hexp.original_middle_pool deltaLoss hδ ε hε S T B N M U hB hN hM hU
    (columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2))
    (columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2))
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := originalProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => originalProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end CanonicalQuadraticSieve

end

end OAI

end


