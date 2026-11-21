-- Prove2me | Definitions.Def_SourceProof_e2ad760de48bf7e2c4b556ed
-- name    : SourceProof_e2ad760de48bf7e2c4b556ed
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:08:06.469019+00:00
-- url     : https://prove2.me/theorems/2fbe49d9-9a3c-482d-b68e-b5b7d4daf23f
-- title:
--   LevyStochCalc source module: SourceProof_e2ad760de48bf7e2c4b556ed
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_cross` comes from the `LevyStochCalc.Driver.JointChaosProfileExpansion` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfileExpansion_F000
import Definitions.Def_SourceProof_9f5b9ce81c93f22e13f9f9ab

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos expansion of the exponential vector of a step at a mark profile

For a Lévy driver, a coordinate `j`, a step `(a, b]` with `τ = b − a`, a finite pairwise disjoint
family `A` of mark sets of finite intensity, a Brownian frequency `α` and a complex profile `c`
constant on each mark set, the block of total degree `e` of the step is

  `C_e(α, c; A) = ∑_(r + s = e) ((i α) ^ r / r!) H_r(ΔWʲ; τ) (D_s(c) / s!)`,

a combination of the complex joint chaos elements of the bidegrees `(r, s)` with `r + s = e`.
Through the bidegree Gram across families and the binomial identity
`∑_(r + s = e) x ^ r y ^ s / (r! s!) = (x + y) ^ e / e!`, blocks of different total degree are
orthogonal whatever the two families, and

  `E[C_e(α, c; A) C_e(α', c'; A')] = (τ (⟨c, c'⟩ − α α')) ^ e / e!`,
  `E‖C_e(α, c; A)‖ ^ 2 = (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k))) ^ e / e!`,

with `⟨c, c'⟩ = ∑_(k, l) c_k c'_l ν(A k ∩ A' l)`. The blocks are the Cauchy product of the Wiener
chaos series of the increment, absolutely summable everywhere, and the chaos series of the strips,
absolutely summable almost everywhere, so they sum almost everywhere, and by the summability of
their `L²` norms in `L²(P; ℂ)`, to the joint exponential vector `V_W(α) V_N(c; A)`, the product of
the exponential vector of the increment and that of the strips; its second moment is
`exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`. At `c_k = e^{i u h_k} − 1` for a simple mark profile `h`
the joint exponential vector is almost surely `V_W(α) 𝓔_u(h)`, with `𝓔_u(h)` the exponential vector
of the step at `h`, and the constants of the block moments are
`∫ ‖e^{i u h} − 1‖ ^ 2 dν` and `∫ (e^{i u h} − 1) ^ 2 dν`. The product `V_W(α) 𝓔_u(h)` depends
continuously on `h ∈ L²(ν)`, as the first factor is bounded.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC` — the block of total degree `e`.
* `LevyStochCalc.Driver.LevyDriver.jointProfileExpVector` — the joint exponential vector.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_cross`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_conj_cross` — the block Gram
  across two mark families.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileBlockC`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_sq` — the two second moments.
* `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_zero`,
  `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_one` — the blocks of total degree zero and
  one, `1` and `i α ΔWʲ + ∑_k c_k Ñ((a, b] ×ˢ A k)`.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileBlockC_simpleProfile`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_sq_simpleProfile` — the second
  moments at `c_k = e^{i u h_k} − 1` through `∫ ‖e^{i u h} − 1‖ ^ 2 dν` and
  `∫ (e^{i u h} − 1) ^ 2 dν`.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointProfileBlockC_mul_conj` — the pairing
  of blocks against a coefficient measurable at the node preceding the step.
* `LevyStochCalc.Driver.LevyDriver.hasSum_jointProfileBlockC` — the blocks sum almost everywhere
  to the joint exponential vector.
* `LevyStochCalc.Driver.LevyDriver.hasSum_toLp_jointProfileBlockC` — the same in `L²(P; ℂ)`.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileExpVector` —
  `E‖V_W(α) V_N(c; A)‖ ^ 2 = exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`.
* `LevyStochCalc.Driver.LevyDriver.jointProfileExpVector_ae_eq` — at `c_k = e^{i u h_k} − 1` the
  joint exponential vector is `V_W(α) 𝓔_u(h)`.
* `LevyStochCalc.Driver.LevyDriver.hasSum_toLp_jointProfileBlockC_simpleProfile` — the blocks
  sum in `L²(P; ℂ)` to `V_W(α) 𝓔_u(h)`.
* `LevyStochCalc.Driver.LevyDriver.tendsto_eLpNorm_wienerExpVector_mul_profileExpVector_sub` —
  `V_W(α) 𝓔_u(h)` is continuous in `h` from `L²(ν)` to `L²(P; ℂ)`.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
  Filter
open scoped NNReal ENNReal Topology

universe u v w

section Expansion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Blocks of a total degree -/


theorem _root_.Prove2MeSourceProof.h_e2ad760de48bf7e2c4b556ed (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (α α' : ℝ) (c : Fin p → ℂ) (c' : Fin q → ℂ) (e e' : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b A α c e ω * D.jointProfileBlockC j a b A' α' c' e' ω ∂P
      = if e = e' then ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A' l)).toReal : ℂ) - (α : ℂ) * α')) ^ e
          / (e.factorial : ℂ) else 0 := by
  classical
  set τ : ℂ := (((b : ℝ) - (a : ℝ) : ℝ) : ℂ) with hτ
  set L : ℂ := ∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A' l)).toReal : ℂ) with hL
  set κ : ℝ → ℕ × ℕ → ℂ := fun β rs => (Complex.I * β) ^ rs.1
    / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ)) with hκ
  set F : ℕ × ℕ → ℕ × ℕ → Ω → ℂ := fun rs rs' ω => (κ α rs * κ α' rs')
    * (D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω
      * D.jointChaosStepProfileC j rs'.1 rs'.2 a b A' c' ω) with hF
  have hint : ∀ rs rs', Integrable (F rs rs') P := fun rs rs' =>
    (((_root_.Prove2MeSourceProof.h_ebefc144eb70c8d3856a45a9 D) j hab hA hAν hd rs.1 rs.2 c).integrable_mul
      ((_root_.Prove2MeSourceProof.h_ebefc144eb70c8d3856a45a9 D) j hab hA' hAν' hd' rs'.1 rs'.2 c')).const_mul _
  have hexp : (fun ω => D.jointProfileBlockC j a b A α c e ω
      * D.jointProfileBlockC j a b A' α' c' e' ω)
      = fun ω => ∑ rs ∈ antidiagonal e, ∑ rs' ∈ antidiagonal e', F rs rs' ω := by
    funext ω
    rw [LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_eq_sum, LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun rs _ => Finset.sum_congr rfl fun rs' _ => ?_
    simp only [hF, hκ]
    ring
  have hterm : ∀ rs rs', ∫ ω, F rs rs' ω ∂P = (κ α rs * κ α' rs')
      * ((((if rs.1 = rs'.1 then (rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1 else 0 : ℝ))
          : ℂ) * (if rs.2 = rs'.2 then (rs.2.factorial : ℂ) * (τ * L) ^ rs.2 else 0)) := by
    intro rs rs'
    rw [hF, integral_const_mul, (_root_.Prove2MeSourceProof.h_4d042d322bf3234fc77542c9 D) j hab hA hAν hd
      hA' hAν' hd']
  rw [hexp, integral_finsetSum _ fun rs _ => integrable_finsetSum _ fun rs' _ => hint rs rs']
  simp_rw [integral_finsetSum _ fun rs' _ => hint _ rs', hterm]
  have hkill : ∀ rs rs' : ℕ × ℕ, rs ≠ rs' →
      (((if rs.1 = rs'.1 then (rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1 else 0 : ℝ))
        : ℂ) * (if rs.2 = rs'.2 then (rs.2.factorial : ℂ) * (τ * L) ^ rs.2 else 0) = 0 := by
    intro rs rs' hne
    by_cases h1 : rs.1 = rs'.1
    · have h2 : rs.2 ≠ rs'.2 := fun h => hne (Prod.ext h1 h)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, Complex.ofReal_zero, zero_mul]
  split_ifs with hee
  · subst hee
    have hdiag : ∀ rs ∈ antidiagonal e, (∑ rs' ∈ antidiagonal e, κ α rs * κ α' rs'
        * ((((if rs.1 = rs'.1 then (rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1
            else 0 : ℝ)) : ℂ)
          * (if rs.2 = rs'.2 then (rs.2.factorial : ℂ) * (τ * L) ^ rs.2 else 0)))
        = (τ * (-((α : ℂ) * α'))) ^ rs.1 * (τ * L) ^ rs.2
          / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ)) := by
      intro rs hrs
      rw [Finset.sum_eq_single_of_mem rs hrs fun rs' _ hne => by
        rw [hkill rs rs' (Ne.symm hne), mul_zero]]
      rw [if_pos rfl, if_pos rfl]
      simp only [hκ]
      have hB : ((((rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1 : ℝ)) : ℂ)
          = (rs.1.factorial : ℂ) * τ ^ rs.1 := by
        rw [hτ]; push_cast; ring
      rw [div_mul_div_comm, ← mul_pow, show Complex.I * (α : ℂ) * (Complex.I * (α' : ℂ))
        = -((α : ℂ) * α') by ring_nf; rw [Complex.I_sq]; ring, hB, mul_pow τ]
      generalize -((α : ℂ) * α') = X
      generalize τ * L = Y
      field_simp
      ring
    rw [Finset.sum_congr rfl hdiag, _root_.Prove2MeSourceProof.h_9f5b9ce81c93f22e13f9f9ab]
    congr 1
    ring
  · refine Finset.sum_eq_zero fun rs hrs => Finset.sum_eq_zero fun rs' hrs' => ?_
    have hne : rs ≠ rs' := by
      rintro rfl
      exact hee ((mem_antidiagonal.1 hrs).symm.trans (mem_antidiagonal.1 hrs'))
    rw [hkill rs rs' hne, mul_zero]
/-! ### The joint exponential vector -/

end Expansion

/-! ### The pairing of blocks at the node preceding the step -/

section Node

variable {Ω : Type u} {M : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

end Node

end LevyStochCalc.Driver.LevyDriver


