-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0018
-- name    : PNT_ZeroFree_433_0018
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:32:03.073725+00:00
-- url     : https://prove2.me/theorems/46ca4944-2c89-4bc4-9a3d-e28beeb01baf
-- title:
--   Zero-free region foundations: GaussSum.GaussianDualLimit [0018]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L20-L573

import Definitions.Def_PNT_ZeroFree_433_0017

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/GaussianDualLimit.lean#L20-L573
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit
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

theorem principal_absNorm_pow (p : O) (k : ℕ) :
    Ideal.absNorm (Ideal.span {p ^ k}) =
      (Ideal.absNorm (Ideal.span {p})) ^ k := by
  rw [← Ideal.span_singleton_pow]
  exact map_pow Ideal.absNorm (Ideal.span {p}) k

theorem sixth_power_rows_within_norm_cutoff
    {β : Type*} (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hcover : ∀ u : O,
      (Ideal.absNorm (Ideal.span {u}) : ℝ) ≤
        (D : ℝ) ^ (11 / 10 : ℝ) → u ∈ rows) :
    selected.image (fun i => p i ^ 6) ⊆ rows := by
  classical
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
  apply hcover
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  calc
    (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
        (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
          exact_mod_cast principal_absNorm_pow (p i) 6
    _ ≤ ((D : ℝ) ^ (11 / 60 : ℝ)) ^ 6 := by
          gcongr
          exact hupper i hi
    _ = (D : ℝ) ^ (11 / 10 : ℝ) := by
          rw [← Real.rpow_mul_natCast hDpos.le (11 / 60 : ℝ) 6]
          congr 1
          norm_num

end ActualEisensteinCubic
namespace OscillatoryDeterminant

open Complex

private def q (a b : ℂ) : ℂ := a*a-a*b+b*b

private noncomputable def A (t a b : ℂ) : ℂ := t + 2*Complex.I*b/q a b
private noncomputable def B (t a b : ℂ) : ℂ := -t/2-2*Complex.I*a/q a b
private noncomputable def D (t a b : ℂ) : ℂ := t + 2*Complex.I*(a-b)/q a b

theorem determinant (t a b : ℂ) (hq : q a b ≠ 0) :
    A t a b * D t a b - (B t a b)^2 =
      4/q a b + 3*t^2/4 := by
  dsimp [A, B, D]
  field_simp [hq]
  dsimp [q]
  ring_nf
  simp [Complex.I_sq]
  ring

end OscillatoryDeterminant

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_bilinear_coordinates (u v m n : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (ActualEisensteinCoordinates.eval u v) *
        eisEmbedding (ActualEisensteinCoordinates.eval m n) / eisLam) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((u*n+v*m-v*n : ℤ) : ℂ)) := by
  rw [← map_mul, ActualEisensteinCoordinates.eval_mul]
  rw [eisEmbedding_eval]
  simpa using
    breveE_int_trace_div 1 (u*m-v*n) (u*n+v*m-v*n) (by norm_num)

theorem breveE_standard_dual_frequency (k l m n : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k) *
        eisEmbedding (ActualEisensteinCoordinates.eval m n) / eisLam) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((k*m+l*n : ℤ) : ℂ)) := by
  rw [breveE_bilinear_coordinates]
  congr 1
  push_cast
  ring

end ActualEisensteinCubic
namespace EisensteinFiberShift

def Q (x y : ℝ) : ℝ := x*x-x*y+y*y
def q (a b : ℝ) : ℝ := Q a b
noncomputable def shiftX (a b x y : ℝ) : ℝ := ((a-b)*x+b*y)/q a b
noncomputable def shiftY (a b x y : ℝ) : ℝ := (-b*x+a*y)/q a b

theorem exact_shift (a b x y m n : ℝ) (hq : q a b ≠ 0) :
    Q (x+a*m-b*n) (y+b*m+(a-b)*n) =
      q a b * Q (m+shiftX a b x y) (n+shiftY a b x y) := by
  dsimp [shiftX, shiftY, Q]
  field_simp [hq]
  dsimp [q, Q]
  ring

end EisensteinFiberShift

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

noncomputable def rowNormBall (H : ℕ) : Finset O := by
  classical
  let I : Finset ℤ := Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
  exact (I.product I).image (fun v => eval v.1 v.2)

theorem mem_rowNormBall_of_qNat_le (H : ℕ) (u : O)
    (h : qNat u ≤ H) : u ∈ rowNormBall H := by
  classical
  have hq : q (coords u) ≤ (H : ℤ) := by
    change (q (coords u)).toNat ≤ H at h
    have hnonneg := qO_nonneg u
    omega
  let a := (coords u).1
  let b := (coords u).2
  have hab : a ^ 2 - a * b + b ^ 2 ≤ (H : ℤ) := hq
  obtain ⟨ha2, hb2⟩ := coordinate_squares a b (H : ℤ)
    (by positivity) hab
  have hH : (0 : ℤ) ≤ H := by positivity
  have haL : -((H : ℤ) + 1) ≤ a := by nlinarith [sq_nonneg (H : ℤ)]
  have haU : a ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  have hbL : -((H : ℤ) + 1) ≤ b := by nlinarith [sq_nonneg (H : ℤ)]
  have hbU : b ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  unfold rowNormBall
  apply Finset.mem_image.mpr
  refine ⟨coords u, ?_, eval_coords u⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨haL, haU⟩,
     Finset.mem_Icc.mpr ⟨hbL, hbU⟩⟩

theorem mem_rowNormBall_of_absNorm_le (H : ℕ) (u : O)
    (h : Ideal.absNorm (Ideal.span {u}) ≤ H) :
    u ∈ rowNormBall H := by
  apply mem_rowNormBall_of_qNat_le
  simpa only [ActualEisensteinCubic.qNat_eq_absNorm_span] using h

end ShortDraftLatticeCount
namespace EisensteinGaussianPrefactor

theorem sqrt_product (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t * Real.sqrt (3*t/4) =
      Real.sqrt 3 * t / 2 := by
  have h3 : Real.sqrt (3/4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have harg : 3*t/4 = (3/4:ℝ)*t := by ring
  rw [harg, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/4), h3]
  calc
    Real.sqrt t * (Real.sqrt 3 / 2 * Real.sqrt t) =
        Real.sqrt 3 / 2 * (Real.sqrt t)^2 := by ring
    _ = Real.sqrt 3 * t / 2 := by rw [Real.sq_sqrt ht]; ring

theorem eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    η * (1 / Real.sqrt (η*q)) *
      (1 / Real.sqrt (3*(η*q)/4)) =
      2 / (Real.sqrt 3 * q) := by
  have ht : 0 < η*q := mul_pos hη hq
  have hsqrt : Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4) =
      Real.sqrt 3 * (η*q) / 2 := sqrt_product (η*q) ht.le
  have hne1 : Real.sqrt (η*q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hne2 : Real.sqrt (3*(η*q)/4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hne3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  calc
    η * (1 / Real.sqrt (η*q)) *
        (1 / Real.sqrt (3*(η*q)/4)) =
        η / (Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4)) := by ring
    _ = η / (Real.sqrt 3 * (η*q) / 2) := by rw [hsqrt]
    _ = 2 / (Real.sqrt 3 * q) := by
      field_simp

end EisensteinGaussianPrefactor

namespace ActualEisensteinCubic

theorem sixth_power_rows_in_rowNormBall
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ)) :
    selected.image (fun i => p i ^ 6) ⊆
      ShortDraftLatticeCount.rowNormBall H := by
  apply sixth_power_rows_within_norm_cutoff selected p
    (ShortDraftLatticeCount.rowNormBall H) D hD hupper
  intro u hu
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H
  exact_mod_cast hu.trans hH

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_gaussian_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * ((m*m-m*n+n*n : ℤ) : ℂ) -
          2 * Complex.I *
            (((-b*m*m+2*a*m*n+(b-a)*n*n : ℤ) : ℂ) /
              ((a*a-a*b+b*b : ℤ) : ℂ)))) := by
  dsimp only
  rw [quadraticTraceModChar_coordinate a b m n hc]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      ((m*m-m*n+n*n : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq m n
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end ActualEisensteinCubic

namespace EisensteinGaussianPrefactor

theorem complex_eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    (η : ℂ) *
      (1 / ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ)) *
      (1 / (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ))) =
      ((2 / (Real.sqrt 3 * q) : ℝ) : ℂ) := by
  have ht : 0 ≤ η*q := (mul_pos hη hq).le
  have hs : 0 ≤ 3*(η*q)/4 := by positivity
  have hpow1 : ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
      (Real.sqrt (η*q) : ℂ) := by
    calc
      ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
          ((η*q : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ)) := by norm_num
      _ = (((η*q) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow ht (1/2 : ℝ)).symm
      _ = (Real.sqrt (η*q) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  have hpow2 : (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
      (Real.sqrt (3*(η*q)/4) : ℂ) := by
    calc
      (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
          (((3*(η*q)/4 : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ))) := by norm_num
      _ = (((3*(η*q)/4) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow hs (1/2 : ℝ)).symm
      _ = (Real.sqrt (3*(η*q)/4) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  rw [hpow1, hpow2]
  exact_mod_cast eta_times_prefactor η q hη hq

end EisensteinGaussianPrefactor

namespace ActualEisensteinCubic

theorem finite_actual_prime_extraction_dyadic_ball
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
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
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ ShortDraftLatticeCount.rowNormBall H,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  apply finite_actual_prime_extraction_dyadic P hgood columns support weight
    selected p (ShortDraftLatticeCount.rowNormBall H) D ε hD hε hp hprime
    hinj ?_ hsupport hcolnorm hweight hnormlower hcount hmean
  exact sixth_power_rows_in_rowNormBall selected p D H hD hnormupper hH

end ActualEisensteinCubic
namespace OscillatoryDeterminant

open Complex

noncomputable def r (t a b : ℂ) : ℂ := 1 + 3 * q a b * t^2 / 16

theorem inverse_quadratic (t a b k l : ℂ)
    (hq : q a b ≠ 0) (hr : r t a b ≠ 0) :
    (D t a b * k^2 - 2 * B t a b * k*l + A t a b * l^2) /
      (A t a b * D t a b - (B t a b)^2) =
      (t * q a b / (4 * r t a b)) * (k^2+k*l+l^2) +
        Complex.I / (2 * r t a b) *
          ((a-b)*k^2+2*a*k*l+b*l^2) := by
  rw [determinant t a b hq]
  have hden : 4/q a b + 3*t^2/4 = 4*r t a b/q a b := by
    dsimp [r]
    field_simp [hq]
    ring
  rw [hden]
  dsimp [A, B, D]
  field_simp [hq, hr]
  dsimp [q] at *
  ring_nf
  try simp [Complex.I_sq]

end OscillatoryDeterminant
open Filter Real Asymptotics

private theorem cheby_small_log :
    ∀ᶠ Y : ℝ in atTop, Real.log (Y + 2) ≤ (Real.log 2 / 80) * (Y + 2) := by
  have hsmall : (fun x : ℝ => Real.log x) =o[atTop] id := by
    simpa only [pow_one] using (Real.isLittleO_pow_log_id_atTop (n := 1))
  have hbound := hsmall.bound (by positivity : 0 < Real.log (2 : ℝ) / 80)
  have hshift : Tendsto (fun Y : ℝ => Y + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  filter_upwards [hshift.eventually hbound,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  simpa only [Function.comp_def, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ Y + 2)),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y + 2)] using hY

theorem rational_prime_three_interval_real_count :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((Real.log 2) / 20) * (Y / Real.log Y) ≤
        (Nat.primeCounting ⌊Y⌋₊ : ℝ) -
          (Nat.primeCounting ⌊Y / 3⌋₊ : ℝ) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hε : 0 < Real.log (2 : ℝ) / 4 := by positivity
  obtain ⟨X₀, hX₀⟩ := (eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le hε))
  obtain ⟨X₁, hX₁⟩ := (eventually_atTop.1 cheby_small_log)
  refine ⟨max 729 (max (3 * X₀) X₁), ?_⟩
  intro Y hY
  have hY729 : (729 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hYX₀ : X₀ ≤ Y / 3 := by
    linarith [le_max_left (3 * X₀) X₁, le_max_right (729 : ℝ) (max (3 * X₀) X₁)]
  have hYX₁ : X₁ ≤ Y := by
    linarith [le_max_right (3 * X₀) X₁, le_max_right (729 : ℝ) (max (3 * X₀) X₁)]
  have hYpos : (0 : ℝ) < Y := by linarith
  have hY3pos : (0 : ℝ) < Y / 3 := by positivity
  have hlogYpos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogY3pos : 0 < Real.log (Y / 3) := Real.log_pos (by linarith)
  have hlog3 : 6 * Real.log (3 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 729) hY729
    calc
      6 * Real.log (3 : ℝ) = Real.log ((3 : ℝ) ^ 6) := by rw [Real.log_pow]; ring
      _ = Real.log 729 := by norm_num
      _ ≤ Real.log Y := h
  have hlogY3 : 5 / 6 * Real.log Y ≤ Real.log (Y / 3) := by
    rw [Real.log_div (ne_of_gt hYpos) (by norm_num : (3 : ℝ) ≠ 0)]
    linarith
  have hlogerror : Real.log (Y + 2) ≤ (Real.log 2 / 40) * Y := by
    have hbound := hX₁ Y hYX₁
    have hprod : 0 ≤ Real.log 2 * (Y - 2) :=
      mul_nonneg hlog2pos.le (by linarith)
    nlinarith
  have hconsterror : Real.log (2 : ℝ) ≤ (Real.log 2 / 40) * Y := by
    have hprod : 0 ≤ Real.log 2 * (Y - 40) :=
      mul_nonneg hlog2pos.le (by linarith)
    nlinarith
  have hnumlo : (19 / 20 : ℝ) * Real.log 2 * Y ≤
      (Y - 1) * Real.log 2 - Real.log (Y + 2) := by
    nlinarith [hlogerror, hconsterror]
  have hPlo : (19 / 20 : ℝ) * Real.log 2 * (Y / Real.log Y) ≤
      (Nat.primeCounting ⌊Y⌋₊ : ℝ) := by
    calc
      _ = ((19 / 20 : ℝ) * Real.log 2 * Y) / Real.log Y := by ring
      _ ≤ ((Y - 1) * Real.log 2 - Real.log (Y + 2)) / Real.log Y :=
        (div_le_div_of_nonneg_right hnumlo hlogYpos.le)
      _ ≤ _ := Chebyshev.pi_ge' (by linarith)
  have hfrac : (Y / 3) / Real.log (Y / 3) ≤ (2 / 5 : ℝ) * (Y / Real.log Y) := by
    have hprod : 0 ≤ Y * (Real.log (Y / 3) - 5 / 6 * Real.log Y) :=
      mul_nonneg hYpos.le (sub_nonneg.mpr hlogY3)
    have hq : (Y / 3) / Real.log (Y / 3) ≤
        ((2 / 5 : ℝ) * Y) / Real.log Y := by
      apply (div_le_div_iff₀ hlogY3pos hlogYpos).mpr
      nlinarith
    convert! hq using 1 ; ring
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; ring
  have hcoeff : 0 ≤ Real.log 4 + Real.log 2 / 4 := by positivity
  have hPup : (Nat.primeCounting ⌊Y / 3⌋₊ : ℝ) ≤
      (9 / 10 : ℝ) * Real.log 2 * (Y / Real.log Y) := by
    calc
      _ ≤ (Real.log 4 + Real.log 2 / 4) * ((Y / 3) / Real.log (Y / 3)) :=
        by simpa only [mul_div_assoc] using hX₀ (Y / 3) hYX₀
      _ ≤ (Real.log 4 + Real.log 2 / 4) * ((2 / 5 : ℝ) * (Y / Real.log Y)) :=
        mul_le_mul_of_nonneg_left hfrac hcoeff
      _ = (9 / 10 : ℝ) * Real.log 2 * (Y / Real.log Y) := by rw [hlog4]; ring
  have htarget : (Real.log 2 / 20) * (Y / Real.log Y) =
      ((19 / 20 : ℝ) - 9 / 10) * Real.log 2 * (Y / Real.log Y) := by ring
  rw [htarget]
  linarith

theorem rational_prime_three_interval_count :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((Real.log 2) / 20) * (Y / Real.log Y) ≤
        (((Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime).card : ℝ) := by
  obtain ⟨Y₀, hY₀⟩ := rational_prime_three_interval_real_count
  refine ⟨max 729 Y₀, ?_⟩
  intro Y hY
  have hY729 : (729 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hfloor : ⌊Y / 3⌋₊ ≤ ⌊Y⌋₊ :=
    Nat.floor_mono (by linarith : Y / 3 ≤ Y)
  have hsubset : Nat.primesLE ⌊Y / 3⌋₊ ⊆ Nat.primesLE ⌊Y⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans hfloor, (Nat.mem_primesLE.mp hp).2⟩
  have hset : (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime =
      Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊Y / 3⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨hhi, hp⟩, fun hh => (not_le_of_gt hlo) hh.1⟩
    · rintro ⟨⟨hhi, hp⟩, hnot⟩
      exact ⟨⟨lt_of_not_ge (fun hle => hnot ⟨hle, hp⟩), hhi⟩, hp⟩
  have hcard : ((Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime).card =
      Nat.primeCounting ⌊Y⌋₊ - Nat.primeCounting ⌊Y / 3⌋₊ := by
    rw [hset, Finset.card_sdiff_of_subset hsubset,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hpile : Nat.primeCounting ⌊Y / 3⌋₊ ≤ Nat.primeCounting ⌊Y⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting,
      ← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card hsubset
  rw [hcard, Nat.cast_sub hpile]
  exact hY₀ Y (le_trans (le_max_right _ _) hY)

namespace RankTwoLimit

section

open scoped Topology

open RankTwoPoisson RankTwoEisShift Filter

private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem eisQ_pos {z : ℤ × ℤ} (hz : z ≠ (0,0)) :
    0 < RankTwoPoisson.eisQ z := by
  by_cases hm : z.1 = 0
  · have hn : z.2 ≠ 0 := by
      intro h0
      exact hz (Prod.ext hm h0)
    have hnR : (z.2 : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hnR]
  · have hmR : (z.1 : ℝ) ≠ 0 := by exact_mod_cast hm
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hmR, sq_nonneg (z.2 : ℝ)]

private theorem eisGauss_norm (T : ℝ) (z : ℤ × ℤ) :
    ‖RankTwoPoisson.eisGauss T z‖ =
      Real.exp (-Real.pi * T * RankTwoPoisson.eisQ z) := by
  simp [RankTwoPoisson.eisGauss, Complex.norm_exp]

noncomputable def dualTerm (T : ℝ) (x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  RankTwoPoisson.eisGauss T (z.1,-z.2) * RankTwoEisShift.dualPhase z.1 z.2 x y

noncomputable def limitTerm (z : ℤ × ℤ) : ℂ :=
  if z = (0,0) then 1 else 0

private theorem dualTerm_tendsto (x y : ℝ) (z : ℤ × ℤ) :
    Tendsto (fun T : ℝ => dualTerm T x y z) atTop (𝓝 (limitTerm z)) := by
  by_cases hz : z = (0,0)
  · subst z
    simp [dualTerm, limitTerm, RankTwoPoisson.eisGauss,
      RankTwoPoisson.eisQ, RankTwoEisShift.dualPhase]
  · have hz' : (z.1,-z.2) ≠ ((0,0) : ℤ × ℤ) := by
      intro h
      apply hz
      have h1 : z.1 = 0 := by simpa using congrArg Prod.fst h
      have h2 : z.2 = 0 := by simpa using congrArg Prod.snd h
      exact Prod.ext h1 h2
    have hq := eisQ_pos hz'
    have hneg : -Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) < 0 := by
      nlinarith [mul_pos Real.pi_pos hq]
    have harg : Tendsto
        (fun T : ℝ => -Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2))
        atTop atBot := by
      convert! tendsto_id.const_mul_atTop_of_neg hneg using 1
      ext T
      simp [mul_assoc, mul_comm]
    have hexp : Tendsto
        (fun T : ℝ => Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
    have hc : Tendsto (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2))
        atTop (𝓝 (0 : ℂ)) := by
      have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp hexp
      have heq : (fun T : ℝ =>
          ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ)) =
          (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2)) := by
        funext T
        simp [RankTwoPoisson.eisGauss, Complex.ofReal_exp]
      change Tendsto (fun T : ℝ =>
        ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) at hh
      rw [heq] at hh
      exact hh
    simpa [dualTerm, limitTerm, hz] using
      hc.mul_const (RankTwoEisShift.dualPhase z.1 z.2 x y)

theorem dual_sum_tendsto_one (x y : ℝ) :
    Tendsto (fun T : ℝ => ∑' z : ℤ × ℤ, dualTerm T x y z)
      atTop (𝓝 (1 : ℂ)) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss 1 (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable (by norm_num))
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ z : ℤ × ℤ,
      ‖dualTerm T x y z‖ ≤ ‖RankTwoPoisson.eisGauss 1 (z.1,-z.2)‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT z
    rw [dualTerm, norm_mul, RankTwoEisShift.dualPhase_norm, mul_one,
      eisGauss_norm, eisGauss_norm]
    have hq := eisQ_nonneg (z.1,-z.2)
    have hpq : 0 ≤ Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) :=
      mul_nonneg Real.pi_pos.le hq
    have hm := mul_le_mul_of_nonneg_right hT hpq
    apply Real.exp_le_exp.mpr
    nlinarith [hm]
  have h := tendsto_tsum_of_dominated_convergence hE.norm
    (dualTerm_tendsto x y) hbound
  simpa [limitTerm] using h

end

open scoped Topology
open Filter

theorem dual_sum_tendsto_one_small_t (x y : ℝ) :
    Tendsto (fun t : ℝ => ∑' z : ℤ × ℤ, dualTerm (4 / (3 * t)) x y z)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hT : Tendsto (fun t : ℝ => (4 / 3 : ℝ) * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).2
      tendsto_inv_nhdsGT_zero
  have h := (dual_sum_tendsto_one x y).comp hT
  simpa [Function.comp_def, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end RankTwoLimit

end

end OAI

end


