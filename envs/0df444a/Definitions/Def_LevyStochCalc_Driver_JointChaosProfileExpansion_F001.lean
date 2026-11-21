-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosProfileExpansion_F001
-- name    : LevyStochCalc_Driver_JointChaosProfileExpansion_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:11:23.942908+00:00
-- url     : https://prove2.me/theorems/5f3d7369-270e-41a1-980e-5dc9cfd42bce
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosProfileExpansion
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosProfileExpansion. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfileExpansion_F000
import Definitions.Def_SourceProof_1300fa9daba157208895db31
import Definitions.Def_SourceProof_503b26636876cd9e74391072
import Definitions.Def_SourceProof_6585134b289c2b12a9b076df
import Definitions.Def_SourceProof_e2ad760de48bf7e2c4b556ed

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

/-- **The Hermitian block Gram across two mark families.** Blocks of different total degree are
orthogonal, and
`E[C_e(α, c; A) conj C_e(α', c'; A')] = (τ (∑_(k, l) c_k conj c'_l ν(A k ∩ A' l) + α α')) ^ e / e!`.
-/
theorem integral_jointProfileBlockC_mul_conj_cross (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (α α' : ℝ) (c : Fin p → ℂ) (c' : Fin q → ℂ) (e e' : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b A α c e ω
        * (starRingEnd ℂ) (D.jointProfileBlockC j a b A' α' c' e' ω) ∂P
      = if e = e' then ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)
            + (α : ℂ) * α')) ^ e / (e.factorial : ℂ) else 0 := by
  simp_rw [conj_jointProfileBlockC]
  rw [(_root_.Prove2MeSourceProof.h_e2ad760de48bf7e2c4b556ed D) j hab hA hAν hd hA' hAν' hd']
  push_cast
  ring_nf
/-- The second moment of the modulus of a block,
`E‖C_e(α, c; A)‖ ^ 2 = (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k))) ^ e / e!`. -/
theorem integral_norm_sq_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) (e : ℕ) :
    ∫ ω, ‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 ∂P
      = (((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal)) ^ e
          / (e.factorial : ℝ) := by
  have h := D.integral_jointProfileBlockC_mul_conj_cross j hab hA hAν hd hA hAν hd α α c c e e
  rw [if_pos rfl, sum_sum_mul_measure_inter_self hd] at h
  have hpt : ∀ ω, ((‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 : ℝ) : ℂ)
      = D.jointProfileBlockC j a b A α c e ω
        * (starRingEnd ℂ) (D.jointProfileBlockC j a b A α c e ω) := by
    intro ω
    rw [Complex.mul_conj']
    push_cast
    ring
  have hs : ∑ k, c k * (starRingEnd ℂ) (c k) * ((ν (A k)).toReal : ℂ)
      = ((∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj']
  refine Complex.ofReal_injective ?_
  rw [← integral_complex_ofReal, integral_congr_ae (Eventually.of_forall hpt), h, hs]
  push_cast
  ring
/-- The bilinear second moment of a block,
`E[C_e(α, c; A) ^ 2] = (τ (∑_k c_k ^ 2 ν(A k) − α ^ 2)) ^ e / e!`. -/
theorem integral_jointProfileBlockC_sq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) (e : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b A α c e ω ^ 2 ∂P
      = ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∑ k, c k ^ 2 * ((ν (A k)).toReal : ℂ) - (α : ℂ) ^ 2)) ^ e / (e.factorial : ℂ) := by
  have h := (_root_.Prove2MeSourceProof.h_e2ad760de48bf7e2c4b556ed D) j hab hA hAν hd hA hAν hd α α c c e e
  rw [if_pos rfl, sum_sum_mul_measure_inter_self hd] at h
  simp_rw [sq]
  rw [h]
/-- A block of a step at a profile on a family of mark sets whose strips are members of the
family `C` is measurable for the σ-algebra of the step over `C`. -/
theorem measurable_jointProfileBlockC_stepSigma (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {m p : ℕ} (C : Fin m → Set (ℝ × E)) {A : Fin p → Set E}
    (hAC : ∀ k, ∃ i, C i = Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) :
    Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (D.jointProfileBlockC j a b A α c e) := by
  rw [show D.jointProfileBlockC j a b A α c e = fun ω => ∑ rs ∈ antidiagonal e,
      (Complex.I * α) ^ rs.1 / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
        * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω from
    funext (D.jointProfileBlockC_eq_sum j a b A α c e)]
  exact Finset.measurable_sum _ fun rs _ =>
    (D.measurable_jointChaosStepProfileC_stepSigma j rs.1 rs.2 a b C hAC c).const_mul _
/-! ### The joint exponential vector -/

/-- The joint exponential vector of the step `(a, b]` at the Brownian frequency `α` and the
complex profile `c` on the family `A`: the exponential vector of the increment of the coordinate
`j` times the exponential vector of the strips `(a, b] ×ˢ A k`. -/
noncomputable def jointProfileExpVector (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (ω : Ω) : ℂ :=
  wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * markedExpVector D.N (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
/-- **The blocks sum to the joint exponential vector.** The blocks of a step at a profile on a
finite pairwise disjoint family of mark sets of finite intensity sum almost everywhere to the
joint exponential vector. -/
theorem hasSum_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (α : ℝ) (c : Fin p → ℂ) :
    ∀ᵐ ω ∂P, HasSum (fun e : ℕ => D.jointProfileBlockC j a b A α c e ω)
      (D.jointProfileExpVector j a b A α c ω) := by
  filter_upwards [_root_.Prove2MeSourceProof.h_1ace97fa8da1f451121369a1 D.N (fun k => measurableSet_Ioc.prod (hA k))
    (fun k => referenceIntensity_strip_ne_top a.coe_nonneg (hAν k)) c] with ω hω
  set x : ℝ := (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω with hx
  set f : ℕ → ℂ := fun r => wienerChaosStepC r (b - a) α x with hf
  set g : ℕ → ℂ := fun s => markedChaosDegreeC D.N s
    (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω / (s.factorial : ℂ) with hg
  have hfn : Summable fun r => ‖f r‖ := by
    refine (_root_.Prove2MeSourceProof.h_503b26636876cd9e74391072 ((b - a : ℝ≥0) : ℝ) x (Complex.I * α)).congr
      fun r => ?_
    simp only [hf, wienerChaosStepC, wienerChaosStep]
  have hfs : HasSum f (wienerExpVector (b - a) α x) := hasSum_wienerChaosStepC (b - a) α x
  have hprod : Summable fun e : ℕ => ∑ rs ∈ antidiagonal e, f rs.1 * g rs.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hω.1).of_norm
  have hval : (∑' e : ℕ, ∑ rs ∈ antidiagonal e, f rs.1 * g rs.2)
      = D.jointProfileExpVector j a b A α c ω := by
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hω.1, hfs.tsum_eq,
      hω.2.tsum_eq]
    rfl
  have hsum := hprod.hasSum
  rw [hval] at hsum
  exact hsum
/-- The `L²` norms of the blocks are summable. -/
theorem summable_sqrt_integral_norm_sq_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ) (c : Fin p → ℂ) :
    Summable fun e : ℕ => Real.sqrt (∫ ω, ‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 ∂P) := by
  have hτ : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.2 (by exact_mod_cast hab)
  refine (_root_.Prove2MeSourceProof.h_b750ef8bbdd7c269127a06e5
    (x := ((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal))
    (by positivity)).congr fun e => ?_
  rw [D.integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c e]
/-- The joint exponential vector of a step lies in `L²`. -/
theorem memLp_two_jointProfileExpVector (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) :
    MemLp (D.jointProfileExpVector j a b A α c) 2 P :=
  memLp_two_of_hasSum_ae (fun e => D.memLp_two_jointProfileBlockC j hab hA hAν hd α c e)
    (D.summable_sqrt_integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c)
    (D.hasSum_jointProfileBlockC j hA hAν α c)
/-- **The joint chaos expansion in `L²`.** The blocks of a step at a profile on a finite pairwise
disjoint family of mark sets of finite intensity sum in `L²(P; ℂ)` to the joint exponential
vector. -/
theorem hasSum_toLp_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) :
    HasSum (fun e : ℕ => (D.memLp_two_jointProfileBlockC j hab hA hAν hd α c e).toLp
        (D.jointProfileBlockC j a b A α c e))
      ((D.memLp_two_jointProfileExpVector j hab hA hAν hd α c).toLp
        (D.jointProfileExpVector j a b A α c)) :=
  hasSum_toLp_of_summable_norm _ _
    (D.summable_sqrt_integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c)
    (D.hasSum_jointProfileBlockC j hA hAν α c)
/-- The second moment of the modulus of the joint exponential vector,
`E‖V_W(α) V_N(c; A)‖ ^ 2 = exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`. -/
theorem integral_norm_sq_jointProfileExpVector (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) :
    ∫ ω, ‖D.jointProfileExpVector j a b A α c ω‖ ^ 2 ∂P
      = Real.exp (((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal)) := by
  have h1 := hasSum_integral_norm_sq_of_hasSum_toLp _ _ (fun e e' hee => ?_)
    (D.hasSum_toLp_jointProfileBlockC j hab hA hAν hd α c)
  · have h2 : HasSum (fun e : ℕ => ∫ ω, ‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 ∂P)
        (Real.exp (((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal))) := by
      rw [Real.exp_eq_exp_ℝ]
      refine (NormedSpace.expSeries_div_hasSum_exp _).congr_fun fun e => ?_
      rw [D.integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c e]
    exact h1.unique h2
  · have h := D.integral_jointProfileBlockC_mul_conj_cross j hab hA hAν hd hA hAν hd α α c c e' e
    rw [if_neg (Ne.symm hee)] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    ring
/-- **The joint exponential vector at a simple profile.** At the profile `c_k = e^{i u h_k} − 1`
of the values of a simple mark profile `h`, the joint exponential vector of the strips of its mark
sets is almost surely the exponential vector of the increment times the exponential vector
`𝓔_u(h)` of the step at `h`. -/
theorem jointProfileExpVector_ae_eq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) :
    D.jointProfileExpVector j a b G.B α
        (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1)
      =ᵐ[P] fun ω => wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
        * profileExpVector D.N G.toFun (a : ℝ) (b : ℝ) u ω := by
  filter_upwards [_root_.Prove2MeSourceProof.h_6585134b289c2b12a9b076df D.N G a.coe_nonneg
    (by exact_mod_cast hab) u] with ω hω
  exact congrArg (fun z => wienerExpVector (b - a) α
    ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) * z) hω.symm
/-- **The block moments at a simple profile, modulus.** At the profile `c_k = e^{i u h_k} − 1` of
the values of a simple mark profile `h`,
`E‖C_e(α, c; A)‖ ^ 2 = (τ (α ^ 2 + ∫ ‖e^{i u h} − 1‖ ^ 2 dν)) ^ e / e!`. -/
theorem integral_norm_sq_jointProfileBlockC_simpleProfile (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) (e : ℕ) :
    ∫ ω, ‖D.jointProfileBlockC j a b G.B α
        (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e ω‖ ^ 2 ∂P
      = (((b : ℝ) - (a : ℝ)) * (α ^ 2
          + ∫ x, ‖Complex.exp (Complex.I * ((u * G.toFun x : ℝ) : ℂ)) - 1‖ ^ 2 ∂ν)) ^ e
          / (e.factorial : ℝ) := by
  rw [D.integral_norm_sq_jointProfileBlockC j hab G.B_measurable G.B_finite G.B_disjoint,
    SimpleProfile.integral_comp_toFun G
      (fun x => ‖Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1‖ ^ 2) (by simp)]
  simp_rw [smul_eq_mul, mul_comm ((ν (G.B _)).toReal)]
/-- **The block moments at a simple profile, bilinear.** At the profile `c_k = e^{i u h_k} − 1`
of the values of a simple mark profile `h`,
`E[C_e(α, c; A) ^ 2] = (τ (∫ (e^{i u h} − 1) ^ 2 dν − α ^ 2)) ^ e / e!`. -/
theorem integral_jointProfileBlockC_sq_simpleProfile (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) (e : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b G.B α
        (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e ω ^ 2 ∂P
      = ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∫ x, (Complex.exp (Complex.I * ((u * G.toFun x : ℝ) : ℂ)) - 1) ^ 2 ∂ν
            - (α : ℂ) ^ 2)) ^ e / (e.factorial : ℂ) := by
  rw [D.integral_jointProfileBlockC_sq j hab G.B_measurable G.B_finite G.B_disjoint,
    SimpleProfile.integral_comp_toFun G
      (fun x => (Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1) ^ 2) (by simp)]
  simp_rw [Complex.real_smul, mul_comm ((ν (G.B _)).toReal : ℂ)]
/-- The exponential vector of the increment times the exponential vector of the step at a simple
profile lies in `L²`. -/
theorem memLp_two_wienerExpVector_mul_profileExpVector (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) :
    MemLp (fun ω => wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
      * profileExpVector D.N G.toFun (a : ℝ) (b : ℝ) u ω) 2 P :=
  (D.memLp_two_jointProfileExpVector j hab G.B_measurable G.B_finite G.B_disjoint α _).ae_eq
    (D.jointProfileExpVector_ae_eq j hab G α u)
/-- **The joint chaos expansion at a simple profile.** At the profile `c_k = e^{i u h_k} − 1` of
the values of a simple mark profile `h`, the blocks sum in `L²(P; ℂ)` to the exponential vector
of the increment times the exponential vector `𝓔_u(h)` of the step at `h`. -/
theorem hasSum_toLp_jointProfileBlockC_simpleProfile (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) :
    HasSum (fun e : ℕ => (D.memLp_two_jointProfileBlockC j hab G.B_measurable G.B_finite
        G.B_disjoint α (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e).toLp
        (D.jointProfileBlockC j a b G.B α
          (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e))
      ((D.memLp_two_wienerExpVector_mul_profileExpVector j hab G α u).toLp
        (fun ω => wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * profileExpVector D.N G.toFun (a : ℝ) (b : ℝ) u ω)) := by
  rw [← MemLp.toLp_congr _ _ (D.jointProfileExpVector_ae_eq j hab G α u)]
  exact D.hasSum_toLp_jointProfileBlockC j hab G.B_measurable G.B_finite G.B_disjoint α _
/-- **Continuity of the joint exponential vector in the profile.** If square-integrable mark
profiles `h_n` converge to `h` in `L²(ν)`, then `V_W(α) 𝓔_u(h_n) → V_W(α) 𝓔_u(h)` in
`L²(P; ℂ)`. -/
theorem tendsto_eLpNorm_wienerExpVector_mul_profileExpVector_sub
    (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {h : ℕ → E → ℝ}
    {f : E → ℝ} (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) (α u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω =>
      wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * profileExpVector D.N (h n) (a : ℝ) (b : ℝ) u ω
        - wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * profileExpVector D.N f (a : ℝ) (b : ℝ) u ω) 2 P) atTop (𝓝 0) :=
  Probability.tendsto_eLpNorm_mul_sub_mul (C := Real.exp (α ^ 2 * ((b - a : ℝ≥0) : ℝ) / 2))
    (fun ω => (norm_wienerExpVector _ _ _).le)
    (_root_.Prove2MeSourceProof.h_1300fa9daba157208895db31 D.N hh hf a.coe_nonneg (by exact_mod_cast hab) u hc)
end Expansion

/-! ### The pairing of blocks at the node preceding the step -/

section Node

variable {Ω : Type u} {M : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

/-- **The pairing of blocks at the node across two mark families.** Against a complex
coefficient `Q` measurable for a σ-algebra `M` independent of the σ-algebra of the step over
`(a, b]` and every finite family of measurable regions inside `(a, b] ×ˢ E` (such as the joint
filtration at `a`), the Hermitian pairing of two blocks of the step over two families of mark sets
is the mean of `Q` times their pairing. -/
theorem integral_coeff_mul_jointProfileBlockC_mul_conj (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hA' : ∀ l, MeasurableSet (A' l)) (hM : M ≤ mΩ)
    (hind : ∀ {m : ℕ} (C : Fin m → Set (ℝ × E)), (∀ k, MeasurableSet (C k)) →
      (∀ k, C k ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ) →
        Indep (D.stepSigma C (a : ℝ) (b : ℝ)) M P)
    {Q : Ω → ℂ} (hQ : StronglyMeasurable[M] Q) (α α' : ℝ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) (e e' : ℕ) :
    ∫ ω, Q ω * (D.jointProfileBlockC j a b A α c e ω
        * (starRingEnd ℂ) (D.jointProfileBlockC j a b A' α' c' e' ω)) ∂P
      = (∫ ω, Q ω ∂P) * ∫ ω, D.jointProfileBlockC j a b A α c e ω
          * (starRingEnd ℂ) (D.jointProfileBlockC j a b A' α' c' e' ω) ∂P := by
  have hCm := measurableSet_append_strip a b hA hA'
  refine D.integral_mul_eq_mul_integral_of_indep_stepSigma _ hCm _ _ hM
    (hind _ hCm (append_strip_subset a b A A')) hQ ?_
  simp_rw [conj_jointProfileBlockC]
  exact (D.measurable_jointProfileBlockC_stepSigma j a b _
      (fun k => ⟨Fin.castAdd q k, Fin.append_left _ _ k⟩) α c e).mul
    (D.measurable_jointProfileBlockC_stepSigma j a b _
      (fun l => ⟨Fin.natAdd p l, Fin.append_right _ _ l⟩) _ _ e')
end Node

end LevyStochCalc.Driver.LevyDriver


