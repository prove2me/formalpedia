-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0106
-- name    : PNT_ZeroFree_433_0106
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:51:26.448764+00:00
-- url     : https://prove2.me/theorems/77d6dad9-3691-4a47-a65d-ffb881602da7
-- title:
--   Zero-free region foundations: Poisson.LatticeEnvelopes [0106]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/LatticeEnvelopes.lean#L79-L700

import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0104

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/LatticeEnvelopes.lean#L79-L700
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Poisson.LatticeEnvelopes
section
namespace OAI

noncomputable section

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

open scoped BigOperators Classical SchwartzMap

namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

def nonzeroLatticeEnvelopeConstant : ℝ :=
  4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass

theorem nonzeroLatticeEnvelopeConstant_nonneg :
    0 ≤ nonzeroLatticeEnvelopeConstant := by
  have := eisensteinCauchyMass_nonneg
  unfold nonzeroLatticeEnvelopeConstant
  positivity

theorem scaled_cauchy_nonzero_mass (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) ≤
        nonzeroLatticeEnvelopeConstant := by
  let F : ℝ → ℂ := fun x => (((1 + x) ^ 2)⁻¹ : ℝ)
  have hF (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 2 * ‖F x‖ ≤ 1 := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_inv_cancel₀ (by positivity : (1 + x) ^ 2 ≠ 0)]
  have hh := lattice_profile_nonzero_scaled_bound F 1 (by norm_num) hF t ht
  change t * (∑' h : {h : O // h ≠ 0}, ‖F (t * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
    nonzeroLatticeEnvelopeConstant * 1 at hh
  simpa only [F, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ((1 + t * ‖eisEmbedding _‖ ^ 2) ^ 2)⁻¹ by positivity),
    mul_one] using hh

theorem nonzero_lattice_envelope_sum
    (t C : ℝ) (ht : 0 < t) (hC : 0 ≤ C)
    (f : {h : O // h ≠ 0} → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hbound : ∀ h, (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * f h ≤ C) :
    Summable f ∧ t * (∑' h, f h) ≤ nonzeroLatticeEnvelopeConstant * C := by
  have hp (h : {h : O // h ≠ 0}) :
      f h ≤ C * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hbound h
  have hs := (scaled_eisenstein_cauchy_summable t ht).subtype (fun h : O => h ≠ 0)
  have hfs : Summable f := Summable.of_nonneg_of_le hf hp (hs.mul_left C)
  refine ⟨hfs, ?_⟩
  have hh := hfs.tsum_le_tsum hp (hs.mul_left C)
  rw [tsum_mul_left] at hh
  calc
    _ ≤ t * (C * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hh ht.le
    _ = C * (t * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
    _ ≤ C * nonzeroLatticeEnvelopeConstant :=
      mul_le_mul_of_nonneg_left (scaled_cauchy_nonzero_mass t ht) hC
    _ = _ := mul_comm _ _

end EisensteinSchwartzPoisson

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def originalMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose

def dualMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose

theorem originalMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ originalMiddleDecayConstant W :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem dualMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ dualMiddleDecayConstant W :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem divisorBlockCost_mono_coefficients
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (D₁ D₂ B N : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (a a₀ : n → ℂ) (b b₀ : p → ℂ)
    (ha : ∀ j, ‖a j‖ ≤ ‖a₀ j‖) (hb : ∀ k, ‖b k‖ ≤ ‖b₀ k‖) :
    divisorBlockCost ε hε D₁ D₂ B N a b ≤ divisorBlockCost ε hε D₁ D₂ B N a₀ b₀ := by
  have hA := sieveNorm_nonneg B (N / D₁)
  have hB := sieveNorm_nonneg B (N / D₂)
  unfold divisorBlockCost
  gcongr
  · exact ha _
  · exact hb _

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

def dualMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) :
    0 ≤ originalMiddleAt W S T rows left right a b M h := by
  unfold originalMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) :
    0 ≤ dualMiddleAt W S T rows left right a b M F h := by
  unfold dualMiddleAt
  positivity

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows ha hb

theorem actual_original_middle_all_frequencies
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
        2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := Real.sqrt (M / B) / (D₁ * D₂)
  have ht : 0 < t := by dsimp only [t]; positivity
  let C := originalMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (originalMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ 2 * t * C := by
    have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M
      hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ originalMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (originalMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h.val‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : Real.sqrt (M / B) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt (M / B) / (D₁ * D₂) = 2 * t := by dsimp only [t]; ring
    rw [hpre] at hp
    change originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * (2 * t * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = 2 * t * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ 2 * t * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t (2 * t * C) ht (by positivity)
    _ (fun h => originalMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * (2 * t * C) := hv
    _ = _ := by dsimp only [C]; ring

end

theorem dual_middle_scale_identity (M F B N : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N) :
    Real.sqrt ((M / F) / B) = (M / (F * N)) * (N * Real.sqrt (F / (M * B))) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ (M / F) / B by positivity),
    Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem actual_dual_middle_all_frequencies
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
        (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N)) *
          Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀) := by
  let t := (N * Real.sqrt (F / (M * B))) / (D₁ * D₂)
  let r := M / (F * N)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hr0 : 0 < r := by dsimp only [r]; positivity
  let C := dualMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (dualMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 *
        dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ (2 * t * r) * C := by
    have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M F
      hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ dualMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (dualMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T rows
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h.val‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF) (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).2.1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖eisEmbedding h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) = 2 * t * r := by
      rw [dual_middle_scale_identity M F B N hM hF (by linarith) (by linarith)]
      dsimp only [t, r]
      ring
    rw [hpre] at hp
    change dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * ((2 * t * r) * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = (2 * t * r) * ((1 + t * ‖eisEmbedding h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ (2 * t * r) * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t ((2 * t * r) * C) ht (by positivity)
    _ (fun h => dualMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M F h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * ((2 * t * r) * C) := hv
    _ = _ := by dsimp only [C, r]; ring

end

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def divisorExponentConstant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) : ℝ :=
  (h.divisor_pair deltaLoss hδ).choose

theorem divisorExponentConstant_pos {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    0 < divisorExponentConstant h deltaLoss hδ := (h.divisor_pair deltaLoss hδ).choose_spec.1

theorem divisor_cost_with_constant {α : ℝ} (h : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (B N D₁ D₂ : ℝ)
    (hB : 1 ≤ B) (hN : 1 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) ≤
      divisorEnergyFactor ε hε N a b *
        (divisorExponentConstant h deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂))) := by
  rw [divisorBlockCost_sqrt ε hε D₁ D₂ B N (by linarith) (by linarith) a b]
  exact mul_le_mul_of_nonneg_left
    ((h.divisor_pair deltaLoss hδ).choose_spec.2 B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

theorem sqrt_div_mul_rpow (M B α : ℝ) (hM : 0 ≤ M) (hB : 0 < B) :
    Real.sqrt (M / B) * B ^ α = Real.sqrt M * B ^ (α - 1 / 2) := by
  rw [Real.rpow_sub hB, ← Real.sqrt_eq_rpow, Real.sqrt_div hM]
  ring

theorem original_middle_scale_shape (M B N D T α : ℝ)
    (hM : 0 ≤ M) (hB : 0 < B) (hD : D ≤ T * Real.sqrt (M / B)) :
    N + B ^ α * D ≤ N + T * Real.sqrt M * B ^ (α - 1 / 2) := by
  calc
    _ ≤ N + B ^ α * (T * Real.sqrt (M / B)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hB.le α))
    _ = _ := by rw [mul_left_comm (B ^ α) T, mul_comm (B ^ α), sqrt_div_mul_rpow M B α hM hB]; ring

theorem dual_middle_scale_shape (M F B N D T α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N)
    (hD : D ≤ T * (N * Real.sqrt (F / (M * B)))) :
    (M / (F * N)) * (N + B ^ α * D) ≤
      M / F + T * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hratio : 0 ≤ M / (F * N) := by positivity
  calc
    _ ≤ (M / (F * N)) * (N + B ^ α * (T * (N * Real.sqrt (F / (M * B))))) := by gcongr
    _ = M / F + T * (Real.sqrt ((M / F) / B) * B ^ α) := by
      rw [dual_middle_scale_identity M F B N hM hF hB hN]
      field_simp

    _ = _ := by rw [sqrt_div_mul_rpow (M / F) B α (by positivity) hB]; ring

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

theorem HasSieveExponent.original_middle_block
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * Real.sqrt (M / B)) :
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + U * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (originalMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc hk)
    _ = ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          (N + B ^ α * (D₁ * D₂)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (original_middle_scale_shape M B N (D₁ * D₂) U α hM.le (by linarith) hcut) (by positivity)

theorem HasSieveExponent.dual_middle_block
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * (N * Real.sqrt (F / (M * B)))) :
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + U * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N a₀ b₀
  have hs := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (dualMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N))) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          ((M / (F * N)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁ * D₂) U α hM hF (by linarith) (by linarith) hcut) (by positivity)

end CanonicalQuadraticSieve

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology Matrix MatrixGroups

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def integralComplexMatrix : SL(2,O) →* SL(2,ℂ) := Matrix.SpecialLinearGroup.map eisEmbedding

@[simp] lemma integralComplexMatrix_apply (M : SL(2,O)) (i j : Fin 2) :
    integralComplexMatrix M i j = eisEmbedding (M i j) := rfl

lemma integralComplexMatrix_levelThree (M : levelThree) :
    integralComplexMatrix (M : SL(2,O)) = complexMatrix M := rfl

lemma row_wedge_gram (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) +
      Complex.normSq (u 0*star (v 0)+u 1*star (v 1)) = rowEnergy u * rowEnergy v := by
  simp only [rowEnergy,← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma row_wedge_le_energy (u v : Fin 2 → ℂ) :
    Complex.normSq (u 0*v 1-u 1*v 0) ≤ rowEnergy u * rowEnergy v := by
  rw [← row_wedge_gram u v]
  exact le_add_of_nonneg_right (Complex.normSq_nonneg _)

lemma bottom_row_wedge_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) 0 * complexBottomRow h 1 -
      complexBottomRow (g*h) 1 * complexBottomRow h 0 = g 1 0 := by
  have hd : h 0 0*h 1 1-h 0 1*h 1 0=1 := by
    simpa only [Matrix.det_fin_two] using h.property
  simp only [complexBottomRow,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination g 1 0 * hd

theorem hyperbolicHeight_mul_bound (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    hyperbolicHeight (g • w) * hyperbolicHeight w * Complex.normSq (g 1 0) ≤ 1 := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) ≤ 1
    have hw := row_wedge_le_energy (complexBottomRow (g*h)) (complexBottomRow h)
    rw [bottom_row_wedge_mul] at hw
    have hp : 0 < rowEnergy (complexBottomRow (g*h)) * rowEnergy (complexBottomRow h) :=
      mul_pos (rowEnergy_pos _ (complexBottomRow_ne_zero _))
        (rowEnergy_pos _ (complexBottomRow_ne_zero _))
    have he : liftedHeight (g*h) * liftedHeight h * Complex.normSq (g 1 0) =
        Complex.normSq (g 1 0) /
          (rowEnergy (complexBottomRow (g*h))*rowEnergy (complexBottomRow h)) := by
      simp only [liftedHeight,div_eq_mul_inv,mul_inv]
      ring
    rw [he]
    exact (div_le_one hp).mpr hw

lemma one_le_normSq_embedding (c : O) (hc : c≠0) : 1 ≤ Complex.normSq (eisEmbedding c) := by
  rw [Complex.normSq_eq_norm_sq,eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))

theorem integral_hyperbolicHeight_mul_le_one (M : SL(2,O)) (hc : M 1 0≠0) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix M • w) * hyperbolicHeight w ≤ 1 := by
  have hb := hyperbolicHeight_mul_bound (integralComplexMatrix M) w
  have hc1 := one_le_normSq_embedding (M 1 0) hc
  have hp := mul_pos (hyperbolicHeight_pos (integralComplexMatrix M • w)) (hyperbolicHeight_pos w)
  change _ * _ * Complex.normSq (eisEmbedding (M 1 0)) ≤ 1 at hb
  nlinarith

def cuspHoroball (σ : SL(2,O)) (Y : ℝ) : Set HyperbolicSpace :=
  {w | Y < hyperbolicHeight (integralComplexMatrix σ⁻¹ • w)}

theorem cuspHoroball_disjoint (σ τ : SL(2,O)) (Y Z : ℝ)
    (hY : 1≤Y) (hZ : 1≤Z) (hc : (σ⁻¹*τ) 1 0≠0) :
    Disjoint (cuspHoroball σ Y) (cuspHoroball τ Z) := by
  apply Set.disjoint_left.mpr
  intro w hwσ hwτ
  have hprod := integral_hyperbolicHeight_mul_le_one (σ⁻¹*τ) hc
    (integralComplexMatrix τ⁻¹ • w)
  simp only [map_mul,map_inv,mul_smul,smul_inv_smul] at hprod
  have hσ : 1 < hyperbolicHeight (integralComplexMatrix σ⁻¹ • w) := lt_of_le_of_lt hY hwσ
  have hτ : 1 < hyperbolicHeight (integralComplexMatrix τ⁻¹ • w) := lt_of_le_of_lt hZ hwτ
  simp only [map_inv] at hσ hτ
  nlinarith [mul_pos (sub_pos.mpr hσ) (sub_pos.mpr hτ)]

def InequivalentCusps (σ τ : SL(2,O)) : Prop :=
  ∀ M : levelThree, (σ⁻¹*(M : SL(2,O))*τ) 1 0≠0

def cuspNeighborhood (σ : SL(2,O)) (Y : ℝ) : Set HyperbolicSpace :=
  {w | ∃ M : levelThree, w ∈ cuspHoroball ((M : SL(2,O))*σ) Y}

lemma cuspNeighborhood_invariant (σ : SL(2,O)) (Y : ℝ) (M : levelThree) (w : HyperbolicSpace) :
    complexMatrix M • w ∈ cuspNeighborhood σ Y ↔ w ∈ cuspNeighborhood σ Y := by
  constructor
  · rintro ⟨N,hN⟩
    refine ⟨M⁻¹*N,?_⟩
    change Y < hyperbolicHeight (integralComplexMatrix (((M⁻¹*N : levelThree) : SL(2,O))*σ)⁻¹ • w)
    change Y < hyperbolicHeight (integralComplexMatrix ((N : SL(2,O))*σ)⁻¹ • (complexMatrix M • w)) at hN
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,inv_inv,map_mul,map_inv,mul_smul,
      integralComplexMatrix_levelThree] using hN
  · rintro ⟨N,hN⟩
    refine ⟨M*N,?_⟩
    change Y < hyperbolicHeight (integralComplexMatrix (((M*N : levelThree) : SL(2,O))*σ)⁻¹ • (complexMatrix M • w))
    change Y < hyperbolicHeight (integralComplexMatrix ((N : SL(2,O))*σ)⁻¹ • w) at hN
    simpa only [Subgroup.coe_mul,mul_inv_rev,map_mul,map_inv,mul_smul,
      integralComplexMatrix_levelThree,inv_smul_smul] using hN

theorem cuspNeighborhood_disjoint (σ τ : SL(2,O)) (hστ : InequivalentCusps σ τ)
    (Y Z : ℝ) (hY : 1≤Y) (hZ : 1≤Z) :
    Disjoint (cuspNeighborhood σ Y) (cuspNeighborhood τ Z) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨M,hM⟩ ⟨N,hN⟩
  apply Set.disjoint_left.mp (cuspHoroball_disjoint ((M : SL(2,O))*σ) ((N : SL(2,O))*τ) Y Z hY hZ ?_) hM hN
  have hc := hστ (M⁻¹*N)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_rev,mul_assoc] using hc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

lemma cosetHeight_pos (x : CuspCosets) (w : HyperbolicSpace) : 0<cosetHeight x w := by
  induction x using Quotient.inductionOn with
  | _ M => exact (cosetHeight_cosetOf M w).symm ▸ hyperbolicHeight_pos _

lemma cosetHeight_rightEquiv (M : levelThree) (x : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight (rightEquiv M x) w = cosetHeight x (complexMatrix M • w) := by
  induction x using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf (N*M)) w = cosetHeight (cosetOf N) (complexMatrix M • w)
    rw [cosetHeight_cosetOf,cosetHeight_cosetOf,map_mul,mul_smul]

lemma high_coset_unique (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace)
    (x y : CuspCosets) (hx : Y<cosetHeight x w) (hy : Y<cosetHeight y w) : x=y := by
  induction x using Quotient.inductionOn with | _ M =>
    induction y using Quotient.inductionOn with | _ N =>
      by_contra hne
      have hc : ((M*N⁻¹ : levelThree) : SL(2,O)) 1 0≠0 := by
        intro hc
        have hT : M*N⁻¹ ∈ cuspStabilizer := (mem_cuspStabilizer_iff _).mpr hc
        exact hne ((cosetOf_eq_iff M N).mpr ⟨M*N⁻¹,hT,by group⟩)
      have hp := integral_hyperbolicHeight_mul_le_one
        ((M*N⁻¹ : levelThree) : SL(2,O)) hc (complexMatrix N • w)
      rw [integralComplexMatrix_levelThree,map_mul,map_inv,mul_smul,inv_smul_smul] at hp
      change Y<cosetHeight (cosetOf M) w at hx
      change Y<cosetHeight (cosetOf N) w at hy
      rw [cosetHeight_cosetOf] at hx hy
      have hm := lt_of_le_of_lt hY hx
      have hn := lt_of_le_of_lt hY hy
      nlinarith [mul_pos (sub_pos.mpr hm) (sub_pos.mpr hn)]

lemma high_cosets_finite (Y : ℝ) (hY : 1≤Y) (w : HyperbolicSpace) :
    Set.Finite {x : CuspCosets | Y<cosetHeight x w} := by
  have h : Set.Subsingleton {x : CuspCosets | Y<cosetHeight x w} :=
    fun x hx y hy => high_coset_unique Y hY w x y hx hy
  exact h.finite

def cuspCutoffTerm (Y : ℝ) (F : ℝ → ℂ) (x : CuspCosets) (w : HyperbolicSpace) : ℂ :=
  if Y<cosetHeight x w then (cosetCharacter x)⁻¹ * F (cosetHeight x w) else 0

lemma cuspCutoffTerm_finiteSupport (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Function.HasFiniteSupport (fun x => cuspCutoffTerm Y F x w) := by
  apply (high_cosets_finite Y hY w).subset
  intro x hx
  by_contra hn
  simp only [Function.mem_support] at hx
  change ¬Y<cosetHeight x w at hn
  exact hx (by simp [cuspCutoffTerm,hn])

lemma cuspCutoffTerm_summable (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    Summable (fun x => cuspCutoffTerm Y F x w) :=
  summable_of_hasFiniteSupport (cuspCutoffTerm_finiteSupport Y hY F w)

def cuspCutoffCorrection (Y : ℝ) (F : ℝ → ℂ) (w : HyperbolicSpace) : ℂ :=
  ∑'x,cuspCutoffTerm Y F x w

lemma cuspCutoffTerm_automorphy (Y : ℝ) (F : ℝ → ℂ) (M : levelThree)
    (x : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm Y F x (complexMatrix M • w) =
      complexCharacter M * cuspCutoffTerm Y F (rightEquiv M x) w := by
  have hM : complexCharacter M≠0 := by
    intro h
    have hn := norm_complexCharacter M
    rw [h,norm_zero] at hn
    exact zero_ne_one hn
  simp only [cuspCutoffTerm,cosetHeight_rightEquiv,cosetCharacter_rightEquiv]
  split_ifs <;> simp [mul_inv_rev,hM,mul_assoc,mul_left_comm,mul_comm]

theorem cuspCutoffCorrection_automorphy (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (M : levelThree) (w : HyperbolicSpace) :
    cuspCutoffCorrection Y F (complexMatrix M • w) = complexCharacter M*cuspCutoffCorrection Y F w := by
  have hsum := cuspCutoffTerm_summable Y hY F w
  have hreindex := (rightEquiv M).hasSum_iff.mpr hsum.hasSum
  have hscale := hreindex.mul_left (complexCharacter M)
  exact (cuspCutoffTerm_summable Y hY F (complexMatrix M • w)).hasSum.unique
    (hscale.congr_fun (fun x => cuspCutoffTerm_automorphy Y F M x w))

lemma cuspCutoffCorrection_eq (Y : ℝ) (hY : 1≤Y) (F : ℝ → ℂ)
    (w : HyperbolicSpace) (x : CuspCosets) (hx : Y<cosetHeight x w) :
    cuspCutoffCorrection Y F w = (cosetCharacter x)⁻¹*F (cosetHeight x w) := by
  unfold cuspCutoffCorrection
  rw [tsum_eq_single x]
  · simp [cuspCutoffTerm,hx]
  · intro y hy
    have hn : ¬Y<cosetHeight y w := fun hh => hy (high_coset_unique Y hY w y x hh hx)
    simp [cuspCutoffTerm,hn]

lemma hyperbolicHeight_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (upperPoint z v hv)=v := by
  have h := hyperbolicHeight_action_upperPoint 1 z v hv
  simpa [Matrix.one_apply] using h

def infinityConstantMode (s : ℂ) (v : ℝ) : ℂ :=
  if hv : 0<v then eisensteinFourierCoefficient v hv s 0 else 0

def truncatedAtInfinity (Y : ℝ) (s : ℂ) (w : HyperbolicSpace) : ℂ :=
  hyperbolicEisenstein s w-cuspCutoffCorrection Y (infinityConstantMode s) w

theorem truncatedAtInfinity_automorphy (Y : ℝ) (hY : 1≤Y) (s : ℂ) (hs : 2<s.re)
    (M : levelThree) (w : HyperbolicSpace) :
    truncatedAtInfinity Y s (complexMatrix M • w) = complexCharacter M*truncatedAtInfinity Y s w := by
  rw [truncatedAtInfinity,hyperbolicEisenstein_automorphy M s hs,
    cuspCutoffCorrection_automorphy Y hY]
  unfold truncatedAtInfinity
  ring

theorem truncatedAtInfinity_upperPoint (Y : ℝ) (hY : 1≤Y) (s : ℂ)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hYv : Y<v) :
    truncatedAtInfinity Y s (upperPoint z v hv) =
      upperEisenstein z v hv s-eisensteinFourierCoefficient v hv s 0 := by
  have hh : cosetHeight (cosetOf 1) (upperPoint z v hv)=v := by
    rw [cosetHeight_cosetOf,map_one,one_smul,hyperbolicHeight_upperPoint]
  rw [truncatedAtInfinity,cuspCutoffCorrection_eq Y hY _ _ (cosetOf 1) (hh.symm ▸ hYv),
    hh,cosetCharacter_cosetOf,map_one,inv_one,one_mul,hyperbolicEisenstein_upperPoint]
  rw [infinityConstantMode,dif_pos hv]

end CubicEisenstein

end

end OAI

end


