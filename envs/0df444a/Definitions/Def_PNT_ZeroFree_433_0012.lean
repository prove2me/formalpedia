-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0012
-- name    : PNT_ZeroFree_433_0012
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:12:06.810986+00:00
-- url     : https://prove2.me/theorems/b21549f3-f08e-4dce-a2e1-0e56cd961055
-- title:
--   Zero-free region foundations: GaussSum.LocalProductAssembly [0012]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L24-L613

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0011

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L24-L613
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
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

namespace ActualEisensteinCubic

open ConcreteTraceCRT
open scoped ComplexConjugate

theorem canonicalSextic_inverse_eq_conj_on_units (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) (u : (O ⧸ P)ˣ) :
    (canonicalSextic P hgood (u : O ⧸ P))⁻¹ =
      star (canonicalSextic P hgood (u : O ⧸ P)) := by
  let χ := canonicalSextic P hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hval : χ (u : O ⧸ P) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe 6 u, hχ6, MulChar.one_apply_coe]
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hval (by decide))

theorem breveLocalG_eq_conjugate (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    breveLocalG P hgood p hP hp =
      star (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O))) *
        breveGamma3 P hgood p hP hp := by
  have htwo : (2 : O ⧸ P) ≠ 0 := Ring.two_ne_zero hchar
  have hfour : (4 : O ⧸ P) ≠ 0 := by
    convert! pow_ne_zero 2 htwo using 1 ; norm_num
  have hunit : IsUnit (4 : O ⧸ P) := isUnit_iff_ne_zero.mpr hfour
  let u : (O ⧸ P)ˣ := hunit.unit
  have hu : (u : O ⧸ P) = Ideal.Quotient.mk P (4 : O) := hunit.unit_spec
  unfold breveLocalG
  rw [← hu, canonicalSextic_inverse_eq_conj_on_units P hgood u]

end ActualEisensteinCubic

namespace FourierBridge
open scoped ContDiff FourierTransform SchwartzMap

theorem coupled_double_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ V₁ V₂ : ℝ → ℂ)
    (R₁ R₂ : ℝ) (a₁ a₂ y : ι → ℝ)
    (hV₁c : HasCompactSupport V₁) (hV₁s : ContDiff ℝ ∞ V₁)
    (hF₁s : ContDiff ℝ ∞ F₁)
    (hV₂c : HasCompactSupport V₂) (hV₂s : ContDiff ℝ ∞ V₂)
    (hF₂s : ContDiff ℝ ∞ F₂)
    (hactive₁ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₁ (∑ j : ι, a₁ j * y j) = 1)
    (hactive₂ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₂ (∑ j : ι, a₂ j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
      F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
      ∫ t₁ : ℝ,
        (∫ t₂ : ℝ,
          (∏ j : ι,
            W j (y j) * logPhase t₁ (a₁ j * y j) *
              logPhase t₂ (a₂ j * y j)) *
            (𝓕 (logProfile V₂ F₂ R₂ 1 hV₂c hV₂s hF₂s)) t₂) *
          (𝓕 (logProfile V₁ F₁ R₁ 1 hV₁c hV₁s hF₁s)) t₁ := by
  classical
  let P : ℂ := ∏ j : ι, W j (y j)
  let Z₁ : ℂ := F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j))
  let Z₂ : ℂ := F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j))
  let b₁ := 𝓕 (logProfile V₁ F₁ R₁ 1 hV₁c hV₁s hF₁s)
  let b₂ := 𝓕 (logProfile V₂ F₂ R₂ 1 hV₂c hV₂s hF₂s)
  let Q (t₁ : ℝ) : ℂ :=
    ∏ j : ι, W j (y j) * logPhase t₁ (a₁ j * y j)
  let T (t₁ t₂ : ℝ) : ℂ :=
    ∏ j : ι,
      W j (y j) * logPhase t₁ (a₁ j * y j) *
        logPhase t₂ (a₂ j * y j)
  have hsep₁ : P * Z₁ = ∫ t₁ : ℝ, Q t₁ * b₁ t₁ := by
    simpa [P, Z₁, Q, b₁] using
      coupled_log_separation W F₁ V₁ R₁ a₁ y
        hV₁c hV₁s hF₁s hactive₁
  have hsep₂ (t₁ : ℝ) :
      Q t₁ * Z₂ = ∫ t₂ : ℝ, T t₁ t₂ * b₂ t₂ := by
    let W' : ι → ℝ → ℂ :=
      fun j z => W j z * logPhase t₁ (a₁ j * z)
    have hP : (∏ j : ι, W' j (y j)) = Q t₁ := rfl
    have hactive₂' : (∏ j : ι, W' j (y j)) ≠ 0 →
        V₂ (∑ j : ι, a₂ j * y j) = 1 := by
      intro hW'
      have hprod : (∏ j : ι, W j (y j)) ≠ 0 := by
        intro hz
        have hz' : (∏ j : ι, W' j (y j)) = 0 := by
          rw [show (∏ j : ι, W' j (y j)) =
            (∏ j : ι, W j (y j)) *
              (∏ j : ι, logPhase t₁ (a₁ j * y j)) by
                simp [W', Finset.prod_mul_distrib]]
          simp [hz]
        exact hW' hz'
      exact hactive₂ hprod
    simpa [W', Q, T, Z₂, b₂] using
      coupled_log_separation W' F₂ V₂ R₂ a₂ y
        hV₂c hV₂s hF₂s hactive₂'
  calc
    P * Z₁ * Z₂ = (∫ t₁ : ℝ, Q t₁ * b₁ t₁) * Z₂ := by rw [hsep₁]
    _ = ∫ t₁ : ℝ, (Q t₁ * b₁ t₁) * Z₂ := by rw [integral_mul_const]
    _ = ∫ t₁ : ℝ, (Q t₁ * Z₂) * b₁ t₁ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      ring
    _ = ∫ t₁ : ℝ,
          (∫ t₂ : ℝ, T t₁ t₂ * b₂ t₂) * b₁ t₁ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      rw [hsep₂ t₁]

end FourierBridge

namespace AnalyticBridge

theorem double_weighted_fourier_minkowski
    {Ω : Type*} (S : Finset Ω)
    (b₁ b₂ : ℝ → ℂ) (φ : Ω → ℝ → ℝ → ℂ)
    (J₁ J₂ : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hinner : ∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ => b₂ t₂ * φ ω t₁ t₂) volume)
    (houter : ∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)) volume)
    (hweight₁ : Integrable
      (fun t₁ : ℝ => (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) volume)
    (hweight₂ : Integrable
      (fun t₂ : ℝ => (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) volume)
    (hφ : ∀ t₁ t₂ : ℝ,
      ‖∑ ω ∈ S, φ ω t₁ t₂‖ ≤
        H * (1 + ‖t₁‖) ^ J₁ * (1 + ‖t₂‖) ^ J₂) :
    ‖∑ ω ∈ S,
        ∫ t₁ : ℝ,
          b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)‖ ≤
      H *
        (∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
        (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) := by
  let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖
  have hI₂ : 0 ≤ I₂ :=
    integral_nonneg (fun t₂ => by positivity)
  have hinnerbound (t₁ : ℝ) :
      ‖∑ ω ∈ S, ∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂‖ ≤
        (H * (1 + ‖t₁‖) ^ J₁) * I₂ := by
    apply weighted_fourier_minkowski S b₂ (fun ω t₂ => φ ω t₁ t₂)
      J₂ (H * (1 + ‖t₁‖) ^ J₁) (by positivity)
      (hinner t₁) hweight₂
    intro t₂
    convert! hφ t₁ t₂ using 1
  have houterbound :
      ‖∑ ω ∈ S,
          ∫ t₁ : ℝ,
            b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)‖ ≤
        (H * I₂) *
          (∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) := by
    apply weighted_fourier_minkowski S b₁
      (fun ω t₁ => ∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)
      J₁ (H * I₂) (mul_nonneg hH hI₂)
      houter hweight₁
    intro t₁
    convert! hinnerbound t₁ using 1 ; ring
  simpa [I₂, mul_assoc, mul_comm, mul_left_comm] using houterbound

end AnalyticBridge

namespace FourierBridge
open scoped FourierTransform SchwartzMap

theorem logPhase_norm (t y : ℝ) : ‖logPhase t y‖ = 1 := by
  simpa [logPhase] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * y)

theorem logPhase_continuous_left (y : ℝ) :
    Continuous (fun t : ℝ => logPhase t y) := by
  unfold logPhase
  fun_prop

end FourierBridge

namespace AnalyticBridge
open scoped FourierTransform SchwartzMap

theorem bounded_separated_double_integrable
    {Ω : Type*} (S : Finset Ω)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (u v : Ω → ℝ → ℂ)
    (humeas : ∀ ω ∈ S, AEStronglyMeasurable (u ω) volume)
    (hvmeas : ∀ ω ∈ S, AEStronglyMeasurable (v ω) volume)
    (hubdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖u ω t‖ ≤ M)
    (hvbdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖v ω t‖ ≤ M) :
    (∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ =>
        (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) volume) ∧
    (∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        (𝓕 g₁) t₁ *
          (∫ t₂ : ℝ,
            (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂))) volume) := by
  have hb₁ : Integrable (fun t : ℝ => (𝓕 g₁) t) volume :=
    (𝓕 g₁).integrable
  have hb₂ : Integrable (fun t : ℝ => (𝓕 g₂) t) volume :=
    (𝓕 g₂).integrable
  have hvint (ω : Ω) (hω : ω ∈ S) :
      Integrable (fun t₂ : ℝ => (𝓕 g₂) t₂ * v ω t₂) volume := by
    obtain ⟨Mv, hMv⟩ := hvbdd ω hω
    exact hb₂.mul_bdd (hvmeas ω hω)
      (Filter.Eventually.of_forall hMv)
  constructor
  · intro t₁ ω hω
    have hmeas : AEStronglyMeasurable
        (fun t₂ : ℝ => u ω t₁ * v ω t₂) volume :=
      (hvmeas ω hω).const_mul (u ω t₁)
    obtain ⟨Mv, hMv⟩ := hvbdd ω hω
    have hbound : ∀ t₂ : ℝ,
        ‖u ω t₁ * v ω t₂‖ ≤ ‖u ω t₁‖ * Mv := by
      intro t₂
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMv t₂) (norm_nonneg _)
    exact hb₂.mul_bdd hmeas (Filter.Eventually.of_forall hbound)
  · intro ω hω
    let Cv : ℂ := ∫ t₂ : ℝ, (𝓕 g₂) t₂ * v ω t₂
    have hfactor (t₁ : ℝ) :
        (∫ t₂ : ℝ,
          (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) = u ω t₁ * Cv := by
      calc
        (∫ t₂ : ℝ,
          (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) =
            ∫ t₂ : ℝ, u ω t₁ * ((𝓕 g₂) t₂ * v ω t₂) := by
          apply integral_congr_ae
          filter_upwards [] with t₂
          ring
        _ = u ω t₁ * Cv := by rw [integral_const_mul]
    obtain ⟨Mu, hMu⟩ := hubdd ω hω
    have hmeas : AEStronglyMeasurable
        (fun t₁ : ℝ => u ω t₁ * Cv) volume :=
      (humeas ω hω).mul_const Cv
    have hbound : ∀ t₁ : ℝ,
        ‖u ω t₁ * Cv‖ ≤ Mu * ‖Cv‖ := by
      intro t₁
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hMu t₁) (norm_nonneg _)
    have hInt : Integrable
        (fun t₁ : ℝ => (𝓕 g₁) t₁ * (u ω t₁ * Cv)) volume :=
      hb₁.mul_bdd hmeas (Filter.Eventually.of_forall hbound)
    convert! hInt using 1
    funext t₁
    rw [hfactor t₁]

end AnalyticBridge

namespace PowerExtraction

theorem from_finite_sixth_power_rows
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * D ^ ((23 / 24 : ℝ) + ε) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hextract := ShortDraft.complex_row_extraction rows primes row A untwisted
    (D ^ (49 / 60 : ℝ)) (D ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinj happrox hmean
  have herror : (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ (49 / 30 : ℝ) := by
    calc
      (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ ((49 / 60 : ℝ) * 2) :=
        (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = D ^ (49 / 30 : ℝ) := by congr 1; norm_num
  rw [herror] at hextract
  exact from_mean_square_and_prime_rows D ε (primes.card : ℝ)
    ‖A untwisted‖ hD hε (norm_nonneg _) hcount hextract

end PowerExtraction

namespace ActualEisensteinCubic

section

open AddChar MulChar

private noncomputable def localA5Kernel (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x h : O ⧸ P) : ℂ :=
  let χ := canonicalSextic P hgood
  let q : ℂ := Nat.card (O ⧸ P)
  if h = 0 then (if j = 0 then 1 - q⁻¹ else 0)
  else q⁻¹ *
    (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
    (((χ⁻¹) ^ 2) ((σ : O ⧸ P) * h)) *
    ψ ((ε * x) * h⁻¹)

private theorem localA5Kernel_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    localA5Kernel P hgood ψ j σ ε x 0 =
      if j = 0 then 1 - (Nat.card (O ⧸ P) : ℂ)⁻¹ else 0 := by
  simp [localA5Kernel]

private theorem localA5Kernel_active_eq_raw (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    (∑ u : (O ⧸ P)ˣ, localA5Kernel P hgood ψ j σ ε x u) =
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ u : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P,
          (canonicalSextic P hgood ^ j) t * ψ (-(u * t))) *
        (((canonicalSextic P hgood)⁻¹) ^ 2) (σ * u) *
        ψ ((ε * x) * ((u⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hu : (u : O ⧸ P) ≠ 0 := Units.ne_zero u
  simp only [localA5Kernel, if_neg hu,
    Units.val_inv_eq_inv_val]
  ring

private noncomputable def localA5Output (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) : ℂ :=
  let χ := canonicalSextic P hgood
  let q : ℂ := Nat.card (O ⧸ P)
  if j = 0 then
    -(((χ⁻¹) ^ 2) σ) *
      (q⁻¹ * ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x))
  else if j = 4 then
    (((χ⁻¹) ^ 2) σ) *
      (q⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1))
  else
    ((χ⁻¹) ^ 2) σ *
      (q⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x

private theorem localA5Kernel_active_eq_output (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (j : ℕ) (hj6 : j < 6)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    (∑ u : (O ⧸ P)ˣ, localA5Kernel P hgood ψ j σ ε x u) =
      localA5Output P hgood ψ j σ ε x := by
  rw [localA5Kernel_active_eq_raw]
  by_cases hj0 : j = 0
  · subst j
    simpa only [localA5Output, ite_true] using
      canonical_A5_jzero_active P hgood hchar ψ hψ σ ε x
  by_cases hj4 : j = 4
  · subst j
    simpa [localA5Output] using
      canonical_A5_jfour P hgood hchar ψ hψ σ ε x
  simpa only [localA5Output, if_neg hj0, if_neg hj4] using
    canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x

theorem actual_local_product_assembly
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    (∑ h : ∀ i, O ⧸ Ideal.span {p i},
      ∏ i, localA5Kernel (Ideal.span {p i}) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (h i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (Ideal.span {p i}) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (Ideal.span {p i}) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let f : ∀ i, (O ⧸ Ideal.span {p i}) → ℂ := fun i h =>
    localA5Kernel (Ideal.span {p i}) (hgood i)
      (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
      (j i) (σ i) (ε i) (x i) h
  let D : ι → ℂ := fun i => localA5Output (Ideal.span {p i}) (hgood i)
    (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
    (j i) (σ i) (ε i) (x i)
  have hzero : ∀ i, j i ≠ 0 → f i 0 = 0 := by
    intro i hj
    simp only [f, localA5Kernel_zero, if_neg hj]
  have hactive : ∀ i, (∑ u : (O ⧸ Ideal.span {p i})ˣ,
      f i (u : O ⧸ Ideal.span {p i})) = 1 * D i := by
    intro i
    simp only [one_mul, f, D]
    exact localA5Kernel_active_eq_output (Ideal.span {p i})
      (hgood i) (hchar i)
      (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
      (PrimitiveTrace.eisTraceModChar_breveE_ne_one
        (Ideal.span {p i}) (p i) rfl (hp i))
      (j i) (hj6 i) (σ i) (ε i) (x i)
  have h := FixedRayActiveSet.assemble_local_A5
    (fun i => O ⧸ Ideal.span {p i}) j f (fun _ => 1) D hzero hactive
  simpa only [f, D, one_mul] using h

theorem actual_crt_product_assembly
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    [Fintype (O ⧸ ⨅ i, Ideal.span {p i})]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i}))
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
      Ideal.quotientInfRingEquivPiQuotient P (by
        intro i k hik
        exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik))
    (∑ z : O ⧸ ⨅ i, P i,
      ∏ i, localA5Kernel (P i) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (P i) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  have hcop : Pairwise (fun i k => IsCoprime (P i) (P k)) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
    Ideal.quotientInfRingEquivPiQuotient P hcop
  have hsum :
      (∑ z : O ⧸ ⨅ i, P i,
        ∏ i, localA5Kernel (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ h : ∀ i, O ⧸ P i,
        ∏ i, localA5Kernel (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i) (h i) := by
    apply Fintype.sum_equiv e.toEquiv
    intro z
    rfl
  dsimp only
  rw [hsum]
  exact actual_local_product_assembly p hp hgood hchar j hj6 σ ε x

@[instance_reducible] noncomputable def crtIntersectionFintype
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i})) :
    Fintype (O ⧸ ⨅ i, Ideal.span {p i}) := by
  classical
  letI (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hcop : Pairwise
      (fun i k => IsCoprime (Ideal.span {p i}) (Ideal.span {p k})) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e := Ideal.quotientInfRingEquivPiQuotient
    (fun i => Ideal.span {p i}) hcop
  exact Fintype.ofEquiv (∀ i, O ⧸ Ideal.span {p i}) e.symm.toEquiv

theorem actual_crt_product_assembly_finite
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i}))
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    letI : Fintype (O ⧸ ⨅ i, Ideal.span {p i}) :=
      crtIntersectionFintype p hdistinct
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
      Ideal.quotientInfRingEquivPiQuotient P (by
        intro i k hik
        exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik))
    (∑ z : O ⧸ ⨅ i, P i,
      ∏ i, localA5Kernel (P i) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (P i) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let : Fintype (O ⧸ ⨅ i, Ideal.span {p i}) :=
    crtIntersectionFintype p hdistinct
  exact actual_crt_product_assembly p hdistinct hp hgood hchar j hj6 σ ε x

end

theorem canonicalSextic_sixth_power_mask (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (a ^ 6)) =
      if a ∈ P then 0 else 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [map_pow, ShortDraftSextic.sextic_power_is_unit_mask
    (canonicalSextic P hgood) (canonicalSextic_pow_six P hgood)]
  by_cases ha : a ∈ P
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]

end ActualEisensteinCubic

namespace PoissonFirstLocal

private def localA (ε : Bool) (p : ℕ) : ℕ := if ε then p else 1
private def localC (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 1 else p
private def localCorrectionE (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if parityBit then localA ε₁ p * localA ε₂ p else 1
private def localS (parityBit : Bool) (p : ℕ) : ℕ := if parityBit then p else 1
private def localJ2 (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if !parityBit && ε₁ && ε₂ then p else 1

theorem first_poisson_local_scale_identity
    (parityBit ε₁ ε₂ : Bool) (p : ℕ) :
    localC parityBit ε₁ ε₂ p * localCorrectionE parityBit ε₁ ε₂ p *
        (localJ2 parityBit ε₁ ε₂ p) ^ 2 =
      localA ε₁ p * localA ε₂ p * localS parityBit p := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    simp [localC, localCorrectionE, localJ2, localS, localA,
      localE, bit,
      show (1 : ZMod 6) ≠ 0 by decide,

      show (3 : ZMod 6) ≠ 0 by decide,
      ] <;> ring_nf <;>
      (intro h; exfalso; revert h; decide)

theorem first_poisson_global_scale_identity
    (P : Finset ℕ) (parityBit ε₁ ε₂ : ℕ → Bool) :
    (∏ p ∈ P, localC (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localJ2 (parityBit p) (ε₁ p) (ε₂ p) p) ^ 2 =
    (∏ p ∈ P, localA (ε₁ p) p) *
      (∏ p ∈ P, localA (ε₂ p) p) *
      (∏ p ∈ P, localS (parityBit p) p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    simp only [Finset.prod_insert hp]
    calc
      (localC (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localC (parityBit q) (ε₁ q) (ε₂ q) q) *
        (localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localCorrectionE (parityBit q) (ε₁ q) (ε₂ q) q) *
        (localJ2 (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localJ2 (parityBit q) (ε₁ q) (ε₂ q) q) ^ 2 =
        (localC (parityBit p) (ε₁ p) (ε₂ p) p *
          localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p *
          localJ2 (parityBit p) (ε₁ p) (ε₂ p) p ^ 2) *
        ((∏ q ∈ P, localC (parityBit q) (ε₁ q) (ε₂ q) q) *
          (∏ q ∈ P, localCorrectionE (parityBit q) (ε₁ q) (ε₂ q) q) *
          (∏ q ∈ P, localJ2 (parityBit q) (ε₁ q) (ε₂ q) q) ^ 2) := by ring
      _ = (localA (ε₁ p) p * localA (ε₂ p) p * localS (parityBit p) p) *
        ((∏ q ∈ P, localA (ε₁ q) q) *
          (∏ q ∈ P, localA (ε₂ q) q) *
          (∏ q ∈ P, localS (parityBit q) q)) := by
        rw [first_poisson_local_scale_identity, ih]
      _ = (localA (ε₁ p) p * ∏ q ∈ P, localA (ε₁ q) q) *
          (localA (ε₂ p) p * ∏ q ∈ P, localA (ε₂ q) q) *
          (localS (parityBit p) p * ∏ q ∈ P, localS (parityBit q) q) := by ring

end PoissonFirstLocal

end

end OAI

end


