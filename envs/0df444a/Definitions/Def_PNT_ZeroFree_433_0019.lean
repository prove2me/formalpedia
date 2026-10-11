-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0019
-- name    : PNT_ZeroFree_433_0019
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:33:50.476493+00:00
-- url     : https://prove2.me/theorems/64970410-b3bc-47d9-926d-866a20c97115
-- title:
--   Zero-free region foundations: GaussSum.GaussianFiberMass [0019]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.GaussianFiberMass
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/GaussianFiberMass.lean#L23-L614

import Definitions.Def_PNT_ZeroFree_433_0018

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/GaussianFiberMass.lean#L23-L614
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.GaussianFiberMass
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

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_real_trace_div (r : ℝ) (u v : ℤ) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (r : ℂ)) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ))))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / (r : ℂ)) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ) by simp]
  rw [← add_div, hL]
  congr 1
  ring

theorem breveE_real_trace_of_O (r : ℝ) (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((ActualEisensteinCoordinates.coords z).2 : ℂ) / (r : ℂ)) := by
  rw [← ActualEisensteinCoordinates.eval_coords z]
  rw [eisEmbedding_eval]
  simp only [ShortDraftLatticeCount.coords_eval]
  exact breveE_real_trace_div r _ _

end ActualEisensteinCubic
namespace SqrtBranch
open Complex

private theorem arg_ne_pi_of_re_pos {a : ℂ} (ha : 0 < a.re) : a.arg ≠ Real.pi := by
  intro h
  have := (Complex.arg_eq_pi_iff.mp h).1
  linarith

theorem cpow_half_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    a ^ (1 / 2 : ℂ) * (((r : ℂ) / a) ^ (1 / 2 : ℂ)) =
      (r : ℂ) ^ (1 / 2 : ℂ) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have harg := arg_ne_pi_of_re_pos ha
  have hlog : Complex.log ((r : ℂ) / a) = (Real.log r : ℂ) - Complex.log a := by
    rw [div_eq_mul_inv, Complex.log_ofReal_mul hr (inv_ne_zero ha0),
      Complex.log_inv a harg]
    ring
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdiv : (r : ℂ) / a ≠ 0 := div_ne_zero hr0 ha0
  rw [Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hdiv,
    Complex.cpow_def_of_ne_zero hr0, hlog, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_log hr.le]
  ring

theorem prefactor_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    (1 / a ^ (1 / 2 : ℂ)) * (1 / (((r : ℂ) / a) ^ (1 / 2 : ℂ))) =
      1 / ((r : ℂ) ^ (1 / 2 : ℂ)) := by
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
    congrArg (fun z : ℂ => z⁻¹) (cpow_half_product ha hr)

end SqrtBranch

namespace PowerExtraction

theorem from_mean_square_and_prime_rows_with_loss
    (D ε J A C M : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ M * J)
    (hmean : J * A ^ 2 ≤
      2 * M * D ^ ((21 / 10 : ℝ) + ε) +
        2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * (M + C) * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hMJpos : 0 < M * J :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hcount
  have hJpos : 0 < J := by
    nlinarith
  have hbase : D ^ ((21 / 10 : ℝ) + ε) ≤
      (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              rw [← Real.rpow_add hDpos]
              congr 1
              ring
      _ ≤ (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
  have hpow : M * D ^ ((21 / 10 : ℝ) + ε) ≤
      M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      M * D ^ ((21 / 10 : ℝ) + ε) ≤
          M * ((M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
            mul_le_mul_of_nonneg_left hbase hMpos.le
      _ = M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hcoeff : 2 * M ^ 2 + 2 * C ^ 2 ≤ 4 * (M + C) ^ 2 := by
    nlinarith [mul_nonneg hMpos.le hCpos.le]
  have hT : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hmain : J * A ^ 2 ≤
      4 * (M + C) ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      J * A ^ 2 ≤
          2 * M * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
      _ ≤ 2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              have hleft :
                  2 * M * D ^ ((21 / 10 : ℝ) + ε) ≤
                    2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by
                nlinarith [hpow]
              have hright :
                  2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) ≤
                    2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
                exact mul_le_mul_of_nonneg_left herr (by positivity)
              linarith
      _ = (2 * M ^ 2 + 2 * C ^ 2) *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by ring
      _ ≤ 4 * (M + C) ^ 2 *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
              mul_le_mul_of_nonneg_right hcoeff hT
      _ = 4 * (M + C) ^ 2 * J *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have hsq : A ^ 2 ≤
      4 * (M + C) ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htarget : 0 ≤ 2 * (M + C) * D ^ E := by positivity
  apply (sq_le_sq₀ hA htarget).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

end PowerExtraction

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fiber_gaussian_eq_shifted
    (a b x y m n : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) (η : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding
        (ActualEisensteinCoordinates.eval x y +
          ActualEisensteinCoordinates.eval a b *
            ActualEisensteinCoordinates.eval m n)‖ ^ 2 : ℂ)) =
      RankTwoEisShift.shifted
        (η * ((a*a-a*b+b*b : ℤ) : ℝ))
        (EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    ne_of_gt (coordinate_norm_pos_of_nonzero a b hc)
  have hqR : EisensteinFiberShift.q (a : ℝ) (b : ℝ) ≠ 0 := by
    dsimp [EisensteinFiberShift.q, EisensteinFiberShift.Q]
    exact_mod_cast hqZ
  have hshift := EisensteinFiberShift.exact_shift
    (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ) (m : ℝ) (n : ℝ) hqR
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      (((a*a-a*b+b*b)*(m*m-m*n+n*n) +
        ((2*a-b)*x+(2*b-a)*y)*m +
        (-(a+b)*x+(2*a-b)*y)*n +
        (x*x-x*y+y*y) : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_fiber_norm_sq a b x y m n
  rw [hnormC]
  dsimp [RankTwoEisShift.shifted, RankTwoEisShift.Q]
  congr 1
  dsimp [EisensteinFiberShift.Q, EisensteinFiberShift.q] at hshift
  have hshiftC := congrArg (fun v : ℝ => (v : ℂ)) hshift
  push_cast at hshiftC ⊢
  linear_combination -(Real.pi : ℂ) * (η : ℂ) * hshiftC

end ActualEisensteinCubic

namespace EisensteinAbelFiber

open scoped Topology
open Filter

theorem shifted_gaussian_mass (x y : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z))
      (𝓝[>] (0 : ℝ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z) =
        ((2 / Real.sqrt 3 : ℝ) : ℂ) *
          (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by
    rw [RankTwoEisShift.shifted_eisenstein_gaussian_poisson ht x y]
    have hpre := EisensteinGaussianPrefactor.complex_eta_times_prefactor
      t 1 ht (by norm_num)
    simp only [mul_one] at hpre
    change (t : ℂ) *
        ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) = _
    calc
      (t : ℂ) * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) =
        (((t : ℂ) * (1 / (t : ℂ) ^ (1 / 2 : ℂ))) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ)))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by ring
      _ = _ := by rw [hpre]
  have hlim := (RankTwoLimit.dual_sum_tendsto_one_small_t x y).const_mul
    (((2 / Real.sqrt 3 : ℝ) : ℂ))
  have heq : (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((2 / Real.sqrt 3 : ℝ) : ℂ) *
        (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpoint t ht
  simpa using hlim.congr' heq.symm

theorem scaled_shifted_gaussian_mass (q : ℝ) (hq : 0 < q)
    (x y : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted (η*q) x y z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 * q) : ℝ) : ℂ))) := by
  have hscale : Tendsto (fun η : ℝ => η*q)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun η : ℝ => η)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using hid.mul_const q
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hη hq
  have hlim := (shifted_gaussian_mass x y).comp hscale
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hlim' := hlim.const_mul (1 / (q : ℂ))
  convert! hlim' using 1
  · funext η
    dsimp
    push_cast
    field_simp [hqC]
  · push_cast
    field_simp [hqC]

end EisensteinAbelFiber

namespace ActualEisensteinCubic

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fiber_gaussian_mass (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ,
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding
            (ActualEisensteinCoordinates.eval x y +
              ActualEisensteinCoordinates.eval a b *
                ActualEisensteinCoordinates.eval z.1 z.2)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  have hq : 0 < (((a*a-a*b+b*b : ℤ) : ℝ)) := by
    exact_mod_cast coordinate_norm_pos_of_nonzero a b hc
  let u := EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  let v := EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  have h := EisensteinAbelFiber.scaled_shifted_gaussian_mass
    (((a*a-a*b+b*b : ℤ) : ℝ)) hq u v
  convert! h using 1
  funext η
  congr 1
  apply tsum_congr
  intro z
  exact actual_fiber_gaussian_eq_shifted a b x y z.1 z.2 hc η

end

section

open EisensteinEmbedding ConcreteTraceCRT Complex

def latticeCoordEquiv : O ≃ ℤ × ℤ where
  toFun := ActualEisensteinCoordinates.coords
  invFun z := ActualEisensteinCoordinates.eval z.1 z.2
  left_inv := ActualEisensteinCoordinates.eval_coords
  right_inv z := ShortDraftLatticeCount.coords_eval z.1 z.2

theorem eis_gaussian_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  have hbase := RankTwoPoisson.eis_gauss_summable hη
  have hcomp : Summable (fun z : O =>
      RankTwoPoisson.eisGauss η (latticeCoordEquiv z)) :=
    (latticeCoordEquiv.summable_iff).2 hbase
  convert! hcomp using 1
  funext z
  let p := ActualEisensteinCoordinates.coords z
  have hz : z = ActualEisensteinCoordinates.eval p.1 p.2 :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval p.1 p.2)‖ : ℂ)^2) =
      ((p.1*p.1-p.1*p.2+p.2*p.2 : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq p.1 p.2
  rw [hnormC]
  change _ = RankTwoPoisson.eisGauss η
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval p.1 p.2))
  rw [ShortDraftLatticeCount.coords_eval]
  dsimp [RankTwoPoisson.eisGauss, RankTwoPoisson.eisQ]
  congr 1
  push_cast
  ring

theorem actual_oscillatory_kernel_summable (c : O) (hc : c ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  have hbase := (eis_gaussian_summable hη).norm
  apply hbase.of_norm_bounded
  intro z
  simp only [norm_mul]
  rw [AddChar.norm_apply]
  simp

end

theorem finite_actual_prime_extraction_dyadic_ball_with_loss
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε M : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hM : 1 ≤ M)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
      M * (selected.card : ℝ))
    (hmean :
      (∑ u ∈ ShortDraftLatticeCount.rowNormBall H,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * (M + 192) * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let rows := ShortDraftLatticeCount.rowNormBall H
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hrows : selected.image (fun i => p i ^ 6) ⊆ rows :=
    sixth_power_rows_in_rowNormBall selected p D H hD hnormupper hH
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤
        192 * (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (PowerExtraction.dyadic_prime_error_bound D
        (Ideal.absNorm (Ideal.span {p i})) hD (hnormlower i hi))
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hextract := ShortDraft.complex_row_extraction rows selected
    (fun i => p i ^ 6) A 1
    (192 * (D : ℝ) ^ (49 / 60 : ℝ))
    (M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinjRows happrox hmean'
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hpow : ((D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
      (D : ℝ) ^ (49 / 30 : ℝ) := by
    calc
      ((D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
          (D : ℝ) ^ ((49 / 60 : ℝ) * 2) :=
            (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = (D : ℝ) ^ (49 / 30 : ℝ) := by congr 1; norm_num
  have herror : (192 * (D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
      192 ^ 2 * (D : ℝ) ^ (49 / 30 : ℝ) := by
    rw [mul_pow, hpow]
  rw [herror] at hextract
  have hbound := PowerExtraction.from_mean_square_and_prime_rows_with_loss
    (D : ℝ) ε (selected.card : ℝ) ‖A 1‖ 192 M hDreal hε
    (norm_nonneg _) (by norm_num) hM hcount
    (by simpa only [mul_assoc] using hextract)
  simpa only [hone] using hbound

end ActualEisensteinCubic
namespace GaussianPhasePointwise

theorem exp_imag_diff_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ)) =
      (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (v : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

theorem exp_imag_denominator_error (θ A η : ℝ) (hA : 0 ≤ A) :
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
      |θ| * (A * η ^ 2) := by
  let r : ℝ := 1 + A * η ^ 2
  have hAη : 0 ≤ A * η ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiff : |θ / r - θ| = |θ| * ((r - 1) / r) := by
    have heq : θ / r - θ = -θ * ((r - 1) / r) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le)]
  have hfrac : (r - 1) / r ≤ r - 1 := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr)]
  have hbound := exp_imag_diff_le (θ / r) θ
  dsimp [r] at hbound ⊢
  calc
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
        |θ / (1 + A * η ^ 2) - θ| := hbound
    _ = |θ| * (((1 + A * η ^ 2) - 1) / (1 + A * η ^ 2)) := hdiff
    _ ≤ |θ| * (A * η ^ 2) := by
      have hfrac' := hfrac
      dsimp [r] at hfrac'
      nlinarith [mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr hfrac')]

end GaussianPhasePointwise

namespace ActualEisensteinCubic

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_O_fiber_gaussian_mass (c r : O) (hc : c ≠ 0) :
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' w : O, Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  dsimp only
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let x := (ActualEisensteinCoordinates.coords r).1
  let y := (ActualEisensteinCoordinates.coords r).2
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hreq : r = ActualEisensteinCoordinates.eval x y :=
    (ActualEisensteinCoordinates.eval_coords r).symm
  have hcE : ActualEisensteinCoordinates.eval a b ≠ 0 := by
    rw [← hceq]
    exact hc
  have hmass := actual_fiber_gaussian_mass a b x y hcE
  convert! hmass using 1
  funext η
  congr 1
  let W : O → ℂ := fun w => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))
  have hsum := (latticeCoordEquiv.symm.tsum_eq W).symm
  have happly (z : ℤ × ℤ) : latticeCoordEquiv.symm z =
      ActualEisensteinCoordinates.eval z.1 z.2 := rfl
  simpa only [W, hceq, hreq, happly] using hsum

theorem original_abel_gauss_limit (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    let K : ℂ := ((2 / (Real.sqrt 3 *
      (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc) (r ^ 2))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let K : ℂ := ((2 / (Real.sqrt 3 *
    (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let W (η : ℝ) (z : O) := Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding z‖ ^ 2 : ℂ))
  have hfiber (r : O ⧸ Ideal.span {c}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    simpa only [K, a, b, W] using
      actual_O_fiber_gaussian_mass c
        (GaussianShiftedPartition.representative c r) hc
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul (ψ (r ^ 2))
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' z : O, ψ
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))) := by
    have hpart := GaussianShiftedPartition.actual_quadratic_shifted_partition
      c hc (W η) (actual_oscillatory_kernel_summable c hc hη)
    change (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w) at hpart
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  simpa only [K, ψ, W, Finset.mul_sum, mul_comm] using hlim

end ActualEisensteinCubic

end

end OAI

end


