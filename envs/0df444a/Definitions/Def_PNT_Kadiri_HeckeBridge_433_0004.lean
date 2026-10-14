-- Prove2me | Definitions.Def_PNT_Kadiri_HeckeBridge_433_0004
-- name    : PNT_Kadiri_HeckeBridge_433_0004
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-12T12:30:58.492475+00:00
-- url     : https://prove2.me/theorems/1db88dfe-00f7-458e-92e5-21b41780459a
-- title:
--   Complete Hecke-to-zeta bridge, part 0004
-- statement:
--   Complete proved arithmetic and analytic lemmas connecting the Eisenstein Hecke L-function to ordinary Dirichlet L-functions and the Riemann zeta function. The final bridge transfers Hecke nonvanishing in Re(s) > 7/8 to zeta nonvanishing. Original hypotheses and proof bodies are retained; no unproved theorem is imported. Source modules: OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights, OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace, OAI.NumberTheory.DirichletL.Hecke.Theta, OAI.NumberTheory.DirichletL.LatticeSummability, OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer, OAI.NumberTheory.DirichletL.CubicSieve.RowMajorants
-- source:
--   OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0; ported to Lean 4.33.1 and pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_HeckeSevenEighths
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0003

/- Complete Hecke-to-Dirichlet and zeta bridge lemmas.
Source: OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace OAI.EisensteinSchwartzPoisson
@[simp] theorem scaledBasisEquiv_apply (w : ℂ) (hw : w.im ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    scaledBasisEquiv w hw c hc z = c * ((z.re : ℂ) + w * (z.im : ℂ)) := rfl
end OAI.EisensteinSchwartzPoisson

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights
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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT


section
open ActualEisensteinCubic ConcreteTraceCRT UniqueFactorizationMonoid CompletedGauss


lemma norm_ideal_moebius_le_one (I : Ideal O) : ‖(moebius I:ℂ)‖≤1 := by
  by_cases hI : Squarefree I
  · simp [hI.moebius_eq]
  · simp [moebius_of_not_squarefree hI]


end


end CubicEisenstein


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace
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

section

open ActualEisensteinCoordinates ShortDraftLatticeCount

theorem omega_sq_for_norm : omega ^ 2 = -omega - 1 := by
  simpa [omega] using
    IsCyclotomicExtension.Rat.Three.eta_sq
      (IsCyclotomicExtension.zeta_spec 3 ℚ K)

theorem conjO_eval_coordinates (a b : ℤ) :
    conjO (eval a b) = eval (a - b) (-b) := by
  have hω : ActualEisensteinCoordinates.omega = omega := rfl
  simp only [eval, map_add, map_mul, map_intCast, hω, conjO_omega]
  rw [omega_sq_for_norm]
  push_cast
  ring

theorem coordinate_norm_eq_mul_conjO (p : O) :
    ((q (coords p) : ℤ) : O) = p * conjO p := by
  let a := (coords p).1
  let b := (coords p).2
  have hp : p = eval a b := (eval_coords p).symm
  symm
  calc
    p * conjO p = eval a b * eval (a - b) (-b) := by
      rw [hp, conjO_eval_coordinates]
    _ = ((q (coords p) : ℤ) : O) := by
      rw [eval_mul]
      simp only [eval, q]
      dsimp [a, b]
      push_cast
      ring

theorem algebraNorm_eq_coordinate_norm (p : O) :
    Algebra.norm ℤ p = q (coords p) := by
  have h := (norm_int_eq_mul_conjO p).trans
    (coordinate_norm_eq_mul_conjO p).symm
  exact_mod_cast h

theorem qNat_eq_absNorm_span (p : O) :
    qNat p = Ideal.absNorm (Ideal.span {p}) := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_coordinate_norm]
  unfold qNat
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (qO_nonneg p),
    Int.natAbs_of_nonneg (qO_nonneg p)]

end

section


open EisensteinEmbedding ConcreteTraceCRT


theorem eisEmbedding_eval (a b : ℤ) :
    eisEmbedding (ActualEisensteinCoordinates.eval a b) =
      (a : ℂ) + (b : ℂ) * omega3 := by
  have hgen : ActualEisensteinCoordinates.omega =
      EisensteinEmbedding.pb.gen := by
    rw [← ActualEisensteinCoordinates.pb_gen]
    rfl
  rw [ActualEisensteinCoordinates.eval, hgen]
  change EisensteinEmbedding.embedding omega3 omega3_sq
    (a + b * EisensteinEmbedding.pb.gen : O) = _
  exact EisensteinEmbedding.embedding_apply_ab omega3 omega3_sq a b


end


end ActualEisensteinCubic

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Hecke.Theta
section
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta


def regroup (N : ℕ) : ((ℤ × Fin N) × (ℤ × Fin N)) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) where
  toFun p := ((p.1.2, p.2.2), (p.1.1, p.2.1))
  invFun p := ((p.2.1, p.1.1), (p.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def residueEquiv (N : ℕ) [NeZero N] : (ℤ × ℤ) ≃ ((Fin N × Fin N) × (ℤ × ℤ)) :=
  (Equiv.prodCongr (Int.divModEquiv N) (Int.divModEquiv N)).trans (regroup N)

def periodicCoeff {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (n : ℤ × ℤ) : ℂ :=
  w (residueEquiv N n).1


theorem theta_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n *
      (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ)) ((pair w).f t) := by
  let hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  let F : (Fin N × Fin N) × (ℤ × ℤ) → ℂ := fun p => w p.1 *
    (Real.exp (-Real.pi * normForm (p.1.1 + (N : ℝ) * p.2.1)
      (p.1.2 + (N : ℝ) * p.2.2) * t) : ℂ)
  have hinner (a : Fin N × Fin N) : HasSum (fun n : ℤ × ℤ => F (a,n))
      (w a * ∑ e : Fin 2, (parityPair a.1 a.2 N hN e).f t) :=
    (cosetTheta_hasSum a.1 a.2 N hN ht).mul_left (w a)
  have hFnorm : Summable (fun p => ‖F p‖) :=
    (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun a => (hinner a).summable.norm, (hasSum_fintype _).summable⟩
  have hF : Summable F := hFnorm.of_norm
  have hid (p : (Fin N × Fin N) × (ℤ × ℤ)) :
      periodicCoeff w ((residueEquiv N).symm p) *
        (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
          (((residueEquiv N).symm p).2) * t) : ℂ) = F p := by
    simp only [periodicCoeff, Equiv.apply_symm_apply]
    change w p.1 * (Real.exp (-Real.pi * normForm
      ((p.2.1 * (N : ℤ) + p.1.1 : ℤ) : ℝ)
      ((p.2.2 * (N : ℤ) + p.1.2 : ℤ) : ℝ) * t) : ℂ) = F p
    simp only [F, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    congr 4 ; ring_nf
  apply (residueEquiv N).symm.hasSum_iff.mp
  change HasSum (fun p => periodicCoeff w ((residueEquiv N).symm p) *
    (Real.exp (-Real.pi * normForm (((residueEquiv N).symm p).1)
      (((residueEquiv N).symm p).2) * t) : ℂ)) _
  simp_rw [hid]
  convert! hF.hasSum using 1
  rw [hF.tsum_prod, tsum_fintype]
  simp_rw [(hinner _).tsum_eq]
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, Finset.mul_sum]


theorem pair_f₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).f₀ = w (0, 0) := by
  have hconst (a : Fin N × Fin N) :
      cosetConstant a.1 a.2 N (Nat.cast_pos.mpr (NeZero.pos N)) =
        if a = (0, 0) then 1 else 0 := by
    rw [cosetConstant_eq _ _ _ _ (by positivity) (by exact_mod_cast a.1.isLt)
      (by positivity) (by exact_mod_cast a.2.isLt)]
    have hz : (a.1 : ℝ) = 0 ∧ (a.2 : ℝ) = 0 ↔ a = (0, 0) := by
      simp only [Prod.ext_iff, Fin.ext_iff, Fin.val_zero, Nat.cast_eq_zero]
    simp only [hz]
  change (∑ p : (Fin N × Fin N) × Fin 2,
    w p.1 * (parityPair p.1.1 p.1.2 N _ p.2).f₀) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  change (∑ a : Fin N × Fin N, w a * cosetConstant a.1 a.2 N _) = _
  simp_rw [hconst]
  simp

def dualScalar (N : ℕ) : ℂ :=
  ((((N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (((3 * (N : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

theorem pair_g₀ {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).g₀ = 2 * dualScalar N * ∑ a, w a := by
  simp only [pair, finitePair, parityPair, ThetaProduct.rectangularPair,
    ThetaProduct.product, ThetaProduct.scaledEvenPair, ThetaProduct.rescale,
    HurwitzZeta.hurwitzEvenFEPair, one_mul, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp_rw [← two_mul]
  rw [← Finset.mul_sum]
  simp only [← Finset.sum_mul, dualScalar]
  ring

theorem pair_g₀_eq_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (hw : ∑ a, w a = 0) : (pair w).g₀ = 0 := by rw [pair_g₀, hw, mul_zero]


@[simp] theorem pair_k {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).k = 1 := rfl

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem pair_hasMellin {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t => (pair w).f t - (pair w).f₀) s (completed w s) :=
  (pair w).hasMellin (by simpa using hs)


theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ


end SevenEighths.HeckeTheta

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.LatticeSummability
section
namespace OAI

noncomputable section
namespace SevenEighths.LatticeSummability
open EisensteinTheta

theorem normForm_nonneg (x y : ℝ) : 0 ≤ normForm x y := by
  unfold normForm
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

theorem normForm_eq_zero_iff (x y : ℝ) : normForm x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    unfold normForm at h
    have hx : x ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    exact ⟨sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp [normForm]

theorem normForm_ge_half_norm_sq (n : ℤ × ℤ) :
    (1 / 2 : ℝ) * ‖n‖ ^ 2 ≤ normForm n.1 n.2 := by
  rw [Prod.norm_def, ← Int.norm_cast_real, ← Int.norm_cast_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  unfold normForm
  rcases le_total |(n.1 : ℝ)| |(n.2 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.1 : ℝ)]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.2 : ℝ)]

theorem summable_pair_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable (fun n : ℤ × ℤ => ‖n‖ ^ (-k)) := by
  have h := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (EisensteinSeries.summable_one_div_norm_rpow hk)
  have hn (n : ℤ) : (n.natAbs : ℝ) = ‖n‖ := by
    exact congrArg (fun x : NNReal => (x : ℝ)) (NNReal.natCast_natAbs n)
  simpa only [finTwoArrowEquiv_symm_apply, Function.comp_def,
    EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.norm_def, Nat.cast_max, hn] using h

theorem summable_normForm_neg_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => normForm n.1 n.2 ^ (-σ)) := by
  have hmajor := (summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left
    ((1 / 2 : ℝ) ^ (-σ))
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (normForm_nonneg _ _) _) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp [normForm, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
    calc
      normForm n.1 n.2 ^ (-σ) ≤ ((1 / 2 : ℝ) * ‖n‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (normForm_ge_half_norm_sq n)
          (by linarith)
      _ = (1 / 2 : ℝ) ^ (-σ) * ‖n‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring

theorem summable_one_div_normForm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => 1 / normForm n.1 n.2 ^ σ) := by
  simpa only [Real.rpow_neg (normForm_nonneg _ _), one_div] using
    summable_normForm_neg_rpow hσ

theorem summable_weighted_normForm {w : ℤ × ℤ → ℂ} {C σ : ℝ}
    (hw : ∀ n, ‖w n‖ ≤ C) (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => ‖w n‖ / normForm n.1 n.2 ^ σ) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (normForm_nonneg _ _) _)) _
    ((summable_one_div_normForm_rpow hσ).mul_left C)
  intro n
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right (hw n) (Real.rpow_nonneg (normForm_nonneg _ _) _)

end SevenEighths.LatticeSummability

end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff


namespace CubicEisenstein

section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)


abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ

def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2


def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))

def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)

def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap

lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous

abbrev EuclideanH1 := euclideanH1Submodule

instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe


end CubicEisenstein

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic
open CompletedGauss ShortDraftHeckeBridge

def normCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : O→*ℂ where
  toFun a := χ (Ideal.absNorm (Ideal.span {a}))
  map_one' := by simp
  map_mul' a b := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp


end InitialMeanSquare


end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.RowMajorants
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
open ActualEisensteinCubic ShortDraftLatticeCount
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


open MeasureTheory Set Module
open scoped BigOperators Classical ENNReal

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def periodBasis : Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.map (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv
lemma periodBasis_zero : periodBasis 0=3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]
lemma periodBasis_one : periodBasis 1=3*omega3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]

def periodLattice : Submodule ℤ ℂ := Submodule.span ℤ (Set.range periodBasis)


instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0004_1 : Countable periodLattice := by unfold periodLattice; infer_instance
instance p2mAnonymous_PNT_Kadiri_HeckeBridge_433_0004_2 : VAddInvariantMeasure periodLattice ℂ volume :=
  inferInstanceAs (VAddInvariantMeasure periodLattice.toAddSubgroup ℂ volume)


lemma three_embedding_mem (n : O) : 3*eisEmbedding n ∈ periodLattice := by
  have hzero : periodBasis 0 ∈ periodLattice := Submodule.subset_span ⟨0,rfl⟩
  have hone : periodBasis 1 ∈ periodLattice := Submodule.subset_span ⟨1,rfl⟩
  have h := periodLattice.add_mem
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).1 hzero)
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).2 hone)
  rw [periodBasis_zero,periodBasis_one] at h
  convert! h using 1
  conv_lhs => rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  simp only [zsmul_eq_mul,]
  ring

def periodPoint (n : O) : periodLattice := ⟨3*eisEmbedding n,three_embedding_mem n⟩

lemma periodPoint_bijective : Function.Bijective periodPoint := by
  constructor
  · intro n m h
    apply eisEmbedding_injective
    exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) (congrArg Subtype.val h)
  · intro p
    have h := (periodBasis.mem_span_iff_repr_mem ℤ p.1).mp p.2
    obtain ⟨a,ha⟩ := h 0
    obtain ⟨b,hb⟩ := h 1
    change (a:ℝ)=_ at ha
    change (b:ℝ)=_ at hb
    refine ⟨ActualEisensteinCoordinates.eval a b, ?_⟩
    apply Subtype.ext
    change 3*eisEmbedding (ActualEisensteinCoordinates.eval a b)=p.1
    rw [← periodBasis.sum_repr p.1,Fin.sum_univ_two,← ha,← hb,
      periodBasis_zero,periodBasis_one,eisEmbedding_eval]
    simp only [Complex.real_smul,Complex.ofReal_intCast]
    ring

def periodEquiv : O ≃ periodLattice := Equiv.ofBijective _ periodPoint_bijective


end CubicEisenstein

end

end OAI

end


