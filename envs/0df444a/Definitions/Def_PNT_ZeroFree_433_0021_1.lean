-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0021_1
-- name    : PNT_ZeroFree_433_0021_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:56:04.593226+00:00
-- url     : https://prove2.me/theorems/b5f80792-e965-46cc-b0f6-8f20ea2ea020
-- title:
--   Zero-free region foundations: Poisson.OscillatoryGaussian [0021_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.OscillatoryGaussian
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean#L22-L302

import Definitions.Def_PNT_ZeroFree_433_0020

/- Oscillatory Gaussian estimates, split at Lean command boundaries.
Two uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/OscillatoryGaussian.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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

namespace OscSpecial

theorem oscillatory_gaussian_poisson {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian (A η a b) (B η a b) (D η a b) z) =
      (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ,
          RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have ha : 0 < (A η a b).re := by
    rw [(coefficient_re η a b hq0).1]
    exact hη
  have hR : 0 < R η a b := by
    unfold R
    positivity
  exact binary_gaussian_poisson_real_det ha hR
    (oscillatory_determinant η a b hq0)
    (real_positive_definite hη hq0)

noncomputable def r (η a b : ℝ) : ℝ := 1 + 3 * q a b * η ^ 2 / 16

theorem r_pos {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    0 < r η a b := by
  unfold r
  positivity

 theorem inverseForm_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    inverseForm (A η a b) (B η a b) (D η a b) (R η a b) z =
      ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
        ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
      Complex.I / (2 * (r η a b : ℂ)) *
        (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
          2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
          (b : ℂ) * (z.2 : ℂ) ^ 2) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hr0 : r η a b ≠ 0 := (r_pos hη hq).ne'
  have hrc : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hR : 0 < R η a b := by unfold R; positivity
  have hRc : (R η a b : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRexpr : (R η a b : ℂ) = 4 * (r η a b : ℂ) / (q a b : ℂ) := by
    simp [R, r]
    field_simp [hqc]
    ring
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hrexpr : (r η a b : ℂ) = 1 + 3 * (q a b : ℂ) * (η : ℂ) ^ 2 / 16 := by
    simp [r]
  dsimp [inverseForm, A, B, D]
  rw [hRexpr]
  field_simp [hqc, hrc]
  push_cast
  ring

theorem dualGaussian_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      Complex.exp (-(Real.pi : ℂ) *
        (((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
          ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
         Complex.I / (2 * (r η a b : ℂ)) *
          (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
            2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
            (b : ℂ) * (z.2 : ℂ) ^ 2))) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hA0 : A η a b ≠ 0 := by
    intro h
    have hAr : (A η a b).re = η := (coefficient_re η a b hq0).1
    simp [h] at hAr
    linarith
  have hR : 0 < R η a b := by unfold R; positivity
  rw [dualGaussian_inverseForm hA0 hR.ne'
    (oscillatory_determinant η a b hq0) z,
    inverseForm_explicit hη hq z]

end OscSpecial

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem dual_quadratic_trace_coeff (a b k l : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)).2 =
      (a-b)*k^2+2*a*k*l+b*l^2 := by
  rw [pow_two, ActualEisensteinCoordinates.eval_mul (k+l) k (k+l) k]
  rw [ActualEisensteinCoordinates.eval_mul]
  rw [ShortDraftLatticeCount.coords_eval]
  ring

 theorem coords_neg_second (z : O) :
    (ActualEisensteinCoordinates.coords (-z)).2 =
      -(ActualEisensteinCoordinates.coords z).2 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hneg : -ActualEisensteinCoordinates.eval a b =
      ActualEisensteinCoordinates.eval (-a) (-b) := by
    simp only [ActualEisensteinCoordinates.eval]
    push_cast
    ring
  rw [hneg, ShortDraftLatticeCount.coords_eval,
    ShortDraftLatticeCount.coords_eval]

theorem breveE_dual_quadratic_real_scale
    (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  rw [breveE_real_trace_of_O]
  have hneg : (ActualEisensteinCoordinates.coords
      (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2))).2 =
      -((a-b)*k^2+2*a*k*l+b*l^2) := by
    have hp := dual_quadratic_trace_coeff a b k l
    rw [coords_neg_second]
    simpa using congrArg Neg.neg hp
  rw [hneg]
  congr 1
  push_cast
  ring_nf

end

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem original_abel_gamma_limit (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((2 / (Real.sqrt 3 * ‖eisEmbedding c‖) : ℝ) : ℂ) *
        quadraticGammaO c hc))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let S : ℂ := ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2)
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hq : (((a*a-a*b+b*b : ℤ) : ℝ)) = ‖eisEmbedding c‖ ^ 2 := by
    calc
      (((a*a-a*b+b*b : ℤ) : ℝ)) =
          ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ ^ 2 :=
        (eisEmbedding_eval_norm_sq a b).symm
      _ = ‖eisEmbedding c‖ ^ 2 := by rw [← hceq]
  have hn : ‖eisEmbedding c‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hc))
  have hnC : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsqrtC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  have hgamma : quadraticGammaO c hc = S / (‖eisEmbedding c‖ : ℂ) := rfl
  have h := original_abel_gauss_limit c hc
  convert! h using 1
  rw [hgamma, hq]
  push_cast
  field_simp [hnC, hsqrtC]
  dsimp only [S]

end

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_binary_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    (coordinate_norm_pos_of_nonzero a b hc).ne'
  have hqC : (((a*a-a*b+b*b : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hqZ
  dsimp only
  rw [actual_oscillatory_gaussian_coordinate a b m n hc η]
  unfold RankTwoComplex.binaryGaussian OscSpecial.A OscSpecial.B
    OscSpecial.D OscSpecial.q
  congr 1
  push_cast
  field_simp [hqC]
  ring

theorem actual_oscillatory_sum_eq_binary
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p := by
  let W : O → ℂ := fun z =>
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates
        (ActualEisensteinCoordinates.eval a b) hc)
      (Ideal.Quotient.mk (Ideal.span {ActualEisensteinCoordinates.eval a b}) z ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))
  have h := (latticeCoordEquiv.symm.tsum_eq W).symm
  simpa only [W, latticeCoordEquiv] using
    (show (∑' z : O, W z) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p from by
      calc
        (∑' z : O, W z) = ∑' p : ℤ × ℤ, W (latticeCoordEquiv.symm p) := h
        _ = _ := by
          apply tsum_congr
          intro p
          have hp : latticeCoordEquiv.symm p =
              ActualEisensteinCoordinates.eval p.1 p.2 := rfl
          rw [hp]
          exact actual_oscillatory_binary_coordinate a b p.1 p.2 hc η)

def dualFrequencyEquiv : (ℤ × ℤ) ≃ O where
  toFun p := ActualEisensteinCoordinates.eval (p.1 + p.2) p.1
  invFun y := ((ActualEisensteinCoordinates.coords y).2,
    (ActualEisensteinCoordinates.coords y).1 -
      (ActualEisensteinCoordinates.coords y).2)
  left_inv p := by
    rcases p with ⟨k,l⟩
    simp only [  ShortDraftLatticeCount.coords_eval]
    ext <;> ring
  right_inv y := by
    change ActualEisensteinCoordinates.eval
      ((ActualEisensteinCoordinates.coords y).2 +
        ((ActualEisensteinCoordinates.coords y).1 -
          (ActualEisensteinCoordinates.coords y).2))
      (ActualEisensteinCoordinates.coords y).2 = y
    convert! ActualEisensteinCoordinates.eval_coords y using 1 ; ring_nf

theorem dualFrequencyEquiv_norm_sq (k l : ℤ) :
    ‖eisEmbedding (dualFrequencyEquiv (k,l))‖ ^ 2 =
      (((k^2+k*l+l^2 : ℤ) : ℝ)) := by
  change ‖eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k)‖ ^ 2 = _
  rw [eisEmbedding_eval_norm_sq]
  ring_nf

theorem dualFrequencyEquiv_trace_phase (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (dualFrequencyEquiv (k,l))^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  exact breveE_dual_quadratic_real_scale r a b k l

end ActualEisensteinCubic

namespace GaussianMoment

open scoped Topology
open Filter


end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex


end ActualEisensteinCubic

namespace OscSpecial


open scoped Topology
open Filter


end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter


end GaussianMoment

end

end OAI

end


