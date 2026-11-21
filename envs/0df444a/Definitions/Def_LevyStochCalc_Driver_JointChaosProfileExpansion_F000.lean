-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosProfileExpansion_F000
-- name    : LevyStochCalc_Driver_JointChaosProfileExpansion_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:05:37.000322+00:00
-- url     : https://prove2.me/theorems/0bc81ad6-332a-4f75-9d7b-6d43ef4e9337
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosProfileExpansion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosProfileExpansion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfileComplex_F001
import Definitions.Def_LevyStochCalc_Poisson_ProfileChaosExpansion_F001
import Definitions.Def_LevyStochCalc_Poisson_ProfileExpVectorCont_F000
import Definitions.Def_LevyStochCalc_Probability_WienerChaosExpansion_F000
import Definitions.Def_SourceProof_0747e5a8579d432eeee00d7b
import Definitions.Def_SourceProof_ebefc144eb70c8d3856a45a9

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

/-- The block of total degree `e` of the step `(a, b]` at the Brownian frequency `α` and the
complex profile `c` on the family `A`: `∑_(r + s = e) ((i α) ^ r / r!) H_r (D_s(c) / s!)`. -/
noncomputable def jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) (ω : Ω) : ℂ :=
  ∑ rs ∈ antidiagonal e,
    wienerChaosStepC rs.1 (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
      * (markedChaosDegreeC D.N rs.2 (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
        / (rs.2.factorial : ℂ))
/-- A block as a combination of the bidegree elements. -/
theorem jointProfileBlockC_eq_sum (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) (ω : Ω) :
    D.jointProfileBlockC j a b A α c e ω
      = ∑ rs ∈ antidiagonal e, (Complex.I * α) ^ rs.1
          / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
          * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω := by
  refine Finset.sum_congr rfl fun rs _ => ?_
  rw [wienerChaosStepC, jointChaosStepProfileC]
  field_simp
/-- The conjugate of a block is the block at the opposite frequency and the conjugate profile. -/
theorem conj_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) (ω : Ω) :
    (starRingEnd ℂ) (D.jointProfileBlockC j a b A α c e ω)
      = D.jointProfileBlockC j a b A (-α) (fun k => (starRingEnd ℂ) (c k)) e ω := by
  rw [jointProfileBlockC_eq_sum, jointProfileBlockC_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun rs _ => ?_
  rw [map_mul, map_div₀, map_pow, map_mul, Complex.conj_I, Complex.conj_ofReal, map_mul,
    Complex.conj_natCast, Complex.conj_natCast, conj_jointChaosStepProfileC]
  push_cast
  ring
/-- The block of total degree zero is `1`. -/
@[simp] theorem jointProfileBlockC_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (ω : Ω) :
    D.jointProfileBlockC j a b A α c 0 ω = 1 := by
  simp [jointProfileBlockC, wienerChaosStepC]
/-- The block of total degree one is `i α ΔWʲ + ∑_k c_k Ñ((a, b] ×ˢ A k)`. -/
theorem jointProfileBlockC_one (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (ω : Ω) :
    D.jointProfileBlockC j a b A α c 1 ω
      = Complex.I * α * (((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω : ℝ) : ℂ)
        + ∑ k, c k * (D.N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) ω : ℂ) := by
  rw [jointProfileBlockC, Finset.Nat.antidiagonal_succ]
  simp [wienerChaosStepC, wienerChaosStep, _root_.Prove2MeSourceProof.h_0747e5a8579d432eeee00d7b]
  ring
/-- A block of a step at a profile on a finite pairwise disjoint family of mark sets of finite
intensity lies in `L²`. -/
theorem memLp_two_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) (e : ℕ) :
    MemLp (D.jointProfileBlockC j a b A α c e) 2 P := by
  have h := memLp_finsetSum (μ := P) (p := 2) (antidiagonal e)
    (f := fun rs (ω : Ω) => (Complex.I * α) ^ rs.1
      / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
      * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω)
    fun rs _ => ((_root_.Prove2MeSourceProof.h_ebefc144eb70c8d3856a45a9 D) j hab hA hAν hd rs.1 rs.2 c).const_mul _
  rw [show D.jointProfileBlockC j a b A α c e = fun ω => ∑ rs ∈ antidiagonal e,
      (Complex.I * α) ^ rs.1 / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
        * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω from
    funext (D.jointProfileBlockC_eq_sum j a b A α c e)]
  exact h
/-! ### The joint exponential vector -/

end Expansion

/-! ### The pairing of blocks at the node preceding the step -/

section Node

variable {Ω : Type u} {M : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

end Node

end LevyStochCalc.Driver.LevyDriver


