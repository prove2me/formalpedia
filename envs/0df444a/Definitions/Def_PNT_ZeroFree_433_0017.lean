-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0017
-- name    : PNT_ZeroFree_433_0017
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:26:32.336873+00:00
-- url     : https://prove2.me/theorems/3a9f64b0-2ccb-4bc0-9a1b-bfa16e49559a
-- title:
--   Zero-free region foundations: Poisson.BinaryGaussian [0017]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L22-L744

import Definitions.Def_PNT_ZeroFree_433_0016

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/BinaryGaussian.lean#L22-L744
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Poisson.BinaryGaussian
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

namespace RankTwoComplex

open Real

theorem lattice_gaussian_summable_of_re_bound (F : ℤ × ℤ → ℂ)
    {eps : ℝ} (heps : 0 < eps)
    (hbound : ∀ z : ℤ × ℤ,
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (F z).re) :
    Summable (fun z : ℤ × ℤ => Complex.exp (-(Real.pi : ℂ) * F z)) := by
  have h1 := RankTwoPoisson.real_gauss_summable heps
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * eps * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * eps * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine hmaj.of_norm_bounded ?_
  intro z
  have hb := hbound z
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hm := mul_le_mul_of_nonneg_left hb hpi
  have hexp : (-(Real.pi : ℂ) * F z).re ≤
      -Real.pi * eps * (z.1 : ℝ) ^ 2 +
      -Real.pi * eps * (z.2 : ℝ) ^ 2 := by
    simp [Complex.mul_re] at *
    nlinarith [hm]
  simpa only [Complex.norm_exp, Real.exp_add] using
    (Real.exp_le_exp.mpr hexp)

noncomputable def schur (a b d : ℂ) : ℂ := d - b ^ 2 / a

noncomputable def binaryGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2))

noncomputable def firstGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * (Complex.I * b / a * (z.1 : ℂ)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * (z.1 : ℂ) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) - b / a * (z.1 : ℂ)) ^ 2)

private theorem binary_split (a b d : ℂ) (m n : ℤ) :
    binaryGaussian a b d (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (-(b * (n : ℂ))) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (Complex.I * b / a * (k : ℂ)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      firstGaussian a b d (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2)
  let B : ℂ := -(b * (n : ℂ))
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d (k,l) := by
  have hδ0 : schur a b d ≠ 0 := by
    intro h
    simp [h] at hδ
  let A : ℂ := schur a b d
  let B : ℂ := Complex.I * b / a * (k : ℂ)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  have hterm (l : ℤ) : C * H l = dualGaussian a b d (k,l) := by
    have hb : Complex.I * B = -(b / a * (k : ℂ)) := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualGaussian, C, A]
    rw [hb]
    ring_nf
  calc
    (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm

theorem binary_gaussian_poisson {a b d : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d))
    (hM : Summable (firstGaussian a b d))
    (hD : Summable (dualGaussian a b d)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d z := by
      rw [hD.tsum_prod]

end RankTwoComplex

namespace GaussianShiftedPartition

open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE

noncomputable def representative (c : O) (r : O ⧸ Ideal.span {c}) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)

theorem representative_spec (c : O) (r : O ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (representative c r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

theorem actual_quadratic_shifted_partition (c : O) (hc : c ≠ 0)
    (W : O → ℂ)
    (hsum : Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z)) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
        ((Ideal.Quotient.mk (Ideal.span {c}) z) ^ 2) * W z) =
      ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc)
          (r ^ 2) *
          ∑' w : O, W (representative c r + c*w) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.actual_quadratic_gaussian_partition c hc W hsum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact GaussianFiberEquiv.fiber_tsum c hc r
    (representative c r) (representative_spec c r) W

end GaussianShiftedPartition

namespace RankTwoAffine

open RankTwoComplex

noncomputable def binaryGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2) +
    2 * (Real.pi : ℂ) * (u * (z.1 : ℂ) + v * (z.2 : ℂ)))

noncomputable def firstGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * schur a b d * (z.2 : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u)) * (z.2 : ℂ))

noncomputable def dualGaussian (a b d u v : ℂ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) / a * ((z.1 : ℂ) + Complex.I * u) ^ 2) *
    Complex.exp (-(Real.pi : ℂ) / (schur a b d) *
      ((z.2 : ℂ) + Complex.I *
        (v + Complex.I * b / a * ((z.1 : ℂ) + Complex.I * u))) ^ 2)

private theorem binary_split (a b d u v : ℂ) (m n : ℤ) :
    binaryGaussian a b d u v (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (u - b * (n : ℂ)) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring

private theorem first_exponent_identity {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * v * (n : ℂ)) +
      (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) *
            (v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]

private theorem first_transform_term {a b d u v : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * v * (n : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (u - b * (n : ℂ))) ^ 2) =
      firstGaussian a b d u v (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl

private theorem first_poisson_slice {a b d u v : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2 +
    2 * (Real.pi : ℂ) * v * (n : ℂ))
  let B : ℂ := u - b * (n : ℂ)
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d u v m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d u v (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n

private theorem second_poisson_slice {a b d u v : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
  let A : ℂ := schur a b d
  let B : ℂ := v + Complex.I * b / a * ((k : ℂ) + Complex.I * u)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * u) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  calc
    (∑' n : ℤ, firstGaussian a b d u v (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d u v (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d u v (k,l)
      congr 1
      rw [← tsum_mul_left]
      rfl

theorem affine_gaussian_poisson {a b d u v : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d u v))
    (hM : Summable (firstGaussian a b d u v))
    (hD : Summable (dualGaussian a b d u v)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d u v (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d u v (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d u v z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d u v (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d u v (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d u v (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d u v (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d u v (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d u v (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d u v z := by
      rw [hD.tsum_prod]

end RankTwoAffine

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem eisEmbedding_eval_norm_sq (x y : ℤ) :
    ‖eisEmbedding (ActualEisensteinCoordinates.eval x y)‖ ^ 2 =
      (x*x-x*y+y*y : ℤ) := by
  rw [eisEmbedding_eval, ← Complex.normSq_eq_norm_sq]
  have hre : ((x : ℂ) + (y : ℂ) * omega3).re =
      (x : ℝ) - (y : ℝ) / 2 := by
    simp [omega3, Complex.add_re, Complex.mul_re]
    ring
  have him : ((x : ℂ) + (y : ℂ) * omega3).im =
      (y : ℝ) * Real.sqrt 3 / 2 := by
    simp [omega3, Complex.add_im, Complex.mul_im]
    ring
  rw [Complex.normSq_apply, hre, him]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  push_cast
  nlinarith

theorem fiber_coordinates (a b x y m n : ℤ) :
    ActualEisensteinCoordinates.eval x y +
      ActualEisensteinCoordinates.eval a b *
        ActualEisensteinCoordinates.eval m n =
    ActualEisensteinCoordinates.eval (x + a*m-b*n)
      (y+b*m+(a-b)*n) := by
  rw [ActualEisensteinCoordinates.eval_mul]
  simp only [ActualEisensteinCoordinates.eval]
  push_cast
  ring

theorem fiber_quadratic_expansion (a b x y m n : ℤ) :
    let q := a*a-a*b+b*b
    let X := x+a*m-b*n
    let Y := y+b*m+(a-b)*n
    X*X-X*Y+Y*Y =
      q*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) := by
  dsimp
  ring

theorem eisEmbedding_fiber_norm_sq (a b x y m n : ℤ) :
    ‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ ^ 2 =
      ((a*a-a*b+b*b)*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) : ℤ) := by
  rw [fiber_coordinates, eisEmbedding_eval_norm_sq]
  exact_mod_cast fiber_quadratic_expansion a b x y m n

theorem coordinate_norm_pos_of_nonzero (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    0 < a*a-a*b+b*b := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval a b) ≠ 0 :=
    ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hn : 0 < ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ :=
    norm_pos_iff.mpr he
  have heq := eisEmbedding_eval_norm_sq a b
  exact_mod_cast (show (0:ℝ) < (a*a-a*b+b*b : ℤ) by
    rw [← heq]
    positivity)

end ActualEisensteinCubic

namespace RankTwoEisShift

noncomputable def Q (x y : ℝ) : ℝ := x ^ 2 - x * y + y ^ 2

noncomputable def shifted (t x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) : ℝ) : ℂ))

noncomputable def A (t : ℝ) : ℂ := (t : ℂ)
noncomputable def B (t : ℝ) : ℂ := ((-t / 2 : ℝ) : ℂ)
noncomputable def D (t : ℝ) : ℂ := (t : ℂ)
noncomputable def U (t x y : ℝ) : ℂ := ((-t * (x - y / 2) : ℝ) : ℂ)
noncomputable def V (t x y : ℝ) : ℂ := ((-t * (y - x / 2) : ℝ) : ℂ)
noncomputable def C (t x y : ℝ) : ℂ :=
  Complex.exp (((-Real.pi * t * Q x y : ℝ) : ℂ))

private theorem shifted_eq_affine (t x y : ℝ) (m n : ℤ) :
    shifted t x y (m,n) =
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) (m,n) := by
  dsimp [shifted, C, Q, RankTwoAffine.binaryGaussian, A, B, D, U, V]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem schur_eis {t : ℝ} (ht : 0 < t) :
    RankTwoComplex.schur (A t) (B t) (D t) = (((3 * t) / 4 : ℝ) : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [RankTwoComplex.schur, A, B, D]
  push_cast
  field_simp [ht0]
  ring

private theorem schur_eis_pos {t : ℝ} (ht : 0 < t) :
    0 < (RankTwoComplex.schur (A t) (B t) (D t)).re := by
  rw [schur_eis ht]
  have h : 0 < 3 * t / 4 := by positivity
  simpa using h

noncomputable def dualPhase (k l : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((k : ℝ) * x + (l : ℝ) * y) : ℝ) : ℂ)) * Complex.I)

private theorem shifted_dual_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k l : ℤ) :
    C t x y *
      RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,l) =
      RankTwoPoisson.eisGauss (4 / (3 * t)) (k,-l) * dualPhase k l x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.dualGaussian, RankTwoPoisson.eisGauss,
    RankTwoPoisson.eisQ, dualPhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem shifted_real_gauss_summable {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * ((n : ℝ) + y) ^ 2)) := by
  have ht2 : 0 < t / 2 := by positivity
  have hbase := RankTwoPoisson.real_gauss_summable ht2
  have hmaj : Summable (fun n : ℤ =>
      Real.exp (Real.pi * t * y ^ 2) *
        Real.exp (-Real.pi * (t / 2) * (n : ℝ) ^ 2)) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro n
  have hs : (n : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((n : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) + 2 * y)]
  have hm := mul_le_mul_of_nonneg_left hs (mul_pos Real.pi_pos ht).le
  have he : -Real.pi * t * ((n : ℝ) + y) ^ 2 ≤
      Real.pi * t * y ^ 2 + -Real.pi * (t / 2) * (n : ℝ) ^ 2 := by
    nlinarith [hm]
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add] using
    (Real.exp_le_exp.mpr he)

noncomputable def middlePhase (k n : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (k : ℝ) * (x - ((n : ℝ) + y) / 2) : ℝ) : ℂ)) * Complex.I)

private theorem middlePhase_norm (k n : ℤ) (x y : ℝ) :
    ‖middlePhase k n x y‖ = 1 := by
  simp [middlePhase, Complex.norm_exp, Complex.mul_re]

private theorem shifted_middle_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n) =
      RankTwoPoisson.cg ((t⁻¹ : ℝ) : ℂ) k *
        Complex.exp (((-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2 : ℝ) : ℂ)) *
        middlePhase k n x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.firstGaussian, RankTwoPoisson.cg,
    middlePhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem middle_norm {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    ‖C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n)‖ =
      Real.exp (-Real.pi * t⁻¹ * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2) := by
  rw [shifted_middle_term ht]
  simp [ middlePhase_norm, RankTwoPoisson.cg, Complex.norm_exp,
    ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc]

private theorem affine_middle_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable htinv
  have h2 := shifted_real_gauss_summable ht3 y
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * t⁻¹ * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((z.2 : ℝ) + y) ^ 2)) :=
    h1.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hCmid : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hmaj.of_norm_bounded ?_
    intro z
    rw [middle_norm ht]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCmid.mul_left (C t x y)⁻¹
  convert! h using 1
  ext z
  simp [hC]

theorem dualPhase_norm (k l : ℤ) (x y : ℝ) :
    ‖dualPhase k l x y‖ = 1 := by
  simp [dualPhase, Complex.norm_exp, Complex.mul_re]

private theorem affine_dual_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable htd)
  have hCdual : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hE.norm.of_norm_bounded ?_
    intro z
    rw [shifted_dual_term ht]
    simp [ dualPhase_norm]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCdual.mul_left (C t x y)⁻¹
  convert! h using 1
  ext z
  simp [hC]

private theorem shifted_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (shifted t x y) := by
  have ht4 : 0 < t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable ht4
  have hbase : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (Real.pi * t * (x ^ 2 + y ^ 2) / 2) *
        (Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
         Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2))) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq : (((z.1 : ℝ) + x) ^ 2 + ((z.2 : ℝ) + y) ^ 2) / 2 ≤
      Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    dsimp [Q]
    nlinarith [sq_nonneg (((z.1 : ℝ) + x) - ((z.2 : ℝ) + y))]
  have hm : (z.1 : ℝ) ^ 2 / 2 - x ^ 2 ≤ ((z.1 : ℝ) + x) ^ 2 := by
    nlinarith [sq_nonneg ((z.1 : ℝ) + 2 * x)]
  have hn : (z.2 : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((z.2 : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((z.2 : ℝ) + 2 * y)]
  have hl : ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 4 -
      (x ^ 2 + y ^ 2) / 2 ≤ Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    nlinarith [hq, hm, hn]
  have hpt : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hl hpt
  have he : -Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) ≤
      Real.pi * t * (x ^ 2 + y ^ 2) / 2 +
        (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2 +
         -Real.pi * (t / 4) * (z.2 : ℝ) ^ 2) := by
    nlinarith [hmul]
  simpa [shifted, Complex.norm_exp, Real.exp_add, mul_assoc] using
    (Real.exp_le_exp.mpr he)

private theorem affine_original_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have hS := shifted_summable ht x y
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have hCA : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) :=
    hS.congr (fun z => shifted_eq_affine t x y z.1 z.2)
  have h := hCA.mul_left (C t x y)⁻¹
  convert! h using 1
  ext z
  simp [hC]

theorem shifted_eisenstein_gaussian_poisson {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    (∑' z : ℤ × ℤ, shifted t x y z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y := by
  have ha : 0 < (A t).re := by simpa [A] using ht
  have hδ := schur_eis_pos ht
  have hO := affine_original_summable ht x y
  have hM := affine_middle_summable ht x y
  have hD := affine_dual_summable ht x y
  let pref : ℂ :=
    (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
  have haff :
      (∑' z : ℤ × ℤ,
        RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) =
      pref * (∑' z : ℤ × ℤ,
        RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    have h := RankTwoAffine.affine_gaussian_poisson ha hδ hO hM hD
    rw [schur_eis ht] at h
    exact h
  calc
    (∑' z : ℤ × ℤ, shifted t x y z) =
        C t x y * (∑' z : ℤ × ℤ,
          RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      exact shifted_eq_affine t x y z.1 z.2
    _ = C t x y * (pref * (∑' z : ℤ × ℤ,
          RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z)) := by
      rw [haff]
    _ = pref * (∑' z : ℤ × ℤ,
          C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t)
            (U t x y) (V t x y) z) := by
      rw [tsum_mul_left]
      ring
    _ = pref * (∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y) := by
      congr 1
      apply tsum_congr
      intro z
      exact shifted_dual_term ht x y z.1 z.2

end RankTwoEisShift

end

end OAI

end


