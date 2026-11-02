-- Prove2me | Definitions.Def_OAIQ098D001
-- name    : OAIQ098D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:22:55.091697+00:00
-- url     : https://prove2.me/theorems/acf7f252-b07d-444c-a0f6-e82f2b011f62
-- title:
--   Definitions bundle OAIQ098D001 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 261 declarations of OpenAI's Lean: 95 definitions, 2 inductive types or structures and 164 theorems. The definitions and types are `OAI.SharpPlanar.CardinalData`, `OAI.SharpPlanar.D`, `OAI.SharpPlanar.HasLatticePoisson`, `OAI.SharpPlanar.HeadNodeIndex`, `OAI.SharpPlanar.IntegerBasis.basisAlpha`, `OAI.SharpPlanar.IntegerBasis.basisBeta`, `OAI.SharpPlanar.IntegerBasis.basisFunction`, `OAI.SharpPlanar.IntegerBasis.densityDen`, `OAI.SharpPlanar.IntegerBasis.phase12`, `OAI.SharpPlanar.IntegerBasis.spectralCoefficient`, `OAI.SharpPlanar.IntegerBasis.waveAmplitude`, `OAI.SharpPlanar.IntegerGrid.quadraturePoint`, `OAI.SharpPlanar.IntegerIntervals.expHorner`, `OAI.SharpPlanar.IntegerIntervals.pointLambda`, `OAI.SharpPlanar.IntegerIntervals.pointZ`, `OAI.SharpPlanar.IntegerIntervals.precision`, `OAI.SharpPlanar.L1Finite`, `OAI.SharpPlanar.Node`, `OAI.SharpPlanar.Numerical.FiniteIndex`, `OAI.SharpPlanar.Numerical.IE`, `OAI.SharpPlanar.Numerical.IF`, `OAI.SharpPlanar.Numerical.IJ`, `OAI.SharpPlanar.Numerical.RE`, `OAI.SharpPlanar.Numerical.RF`, `OAI.SharpPlanar.Numerical.RJ`, `OAI.SharpPlanar.Numerical.U100.node`, `OAI.SharpPlanar.Numerical.Wminus`, `OAI.SharpPlanar.Numerical.WminusInt`, `OAI.SharpPlanar.Numerical.Wplus`, `OAI.SharpPlanar.Numerical.WplusInt`, `OAI.SharpPlanar.Numerical.centralIndex`, `OAI.SharpPlanar.Numerical.eNode`, `OAI.SharpPlanar.Numerical.exteriorIndex`, `OAI.SharpPlanar.Numerical.finiteIndex`, `OAI.SharpPlanar.Numerical.jDeriv`, `OAI.SharpPlanar.Numerical.jNode`, `OAI.SharpPlanar.Numerical.node1`, `OAI.SharpPlanar.Numerical.node12`, `OAI.SharpPlanar.Numerical.node3`, `OAI.SharpPlanar.Numerical.node4` and 57 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_BasisIntervals`, `PlanarPacking_CanonicalRows`, `PlanarPacking_Cardinal`, `PlanarPacking_Certificate_TableData`, `PlanarPacking_Certificate_WCertificates`, `PlanarPacking_Certificate_WUCert100`, `PlanarPacking_Entire`, `PlanarPacking_Entries`, `PlanarPacking_Fejer`, `PlanarPacking_FiniteCoordinates`, `PlanarPacking_FiniteProjection`, `PlanarPacking_FiniteSplit`, `PlanarPacking_FiniteTail`, `PlanarPacking_Grid`, `PlanarPacking_HexLattice`, `PlanarPacking_Indices`, `PlanarPacking_Intervals`, `PlanarPacking_LatticeGaussian`, `PlanarPacking_LatticePoisson`, `PlanarPacking_MatrixInverse`, `PlanarPacking_MatrixL1`, `PlanarPacking_Nodes`, `PlanarPacking_Quadrature`, `PlanarPacking_TableDensityBase`, `PlanarPacking_TailHead`.
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D004` and `OAIQ098D005`; the statements `OAI.SharpPlanar.atomBase_contains`, `OAI.SharpPlanar.basis_piece_integrable`, `OAI_SharpPlanar_cardinal_jets`, `OAI.SharpPlanar.complexDirectFactor_disk_bound`, `OAI.SharpPlanar.decay_atomBase`, `OAI.SharpPlanar.directDensity_split`, `OAI.SharpPlanar.directDensity_tsum`, `OAI.SharpPlanar.directIntegrand_analytic`, `OAI.SharpPlanar.directIntegrand_disk_bound`, `OAI.SharpPlanar.directMoment_piece_average_error`, `OAI.SharpPlanar.directMoment_piece_error`, `OAI.SharpPlanar.directMoment_rule_error`, `OAI.SharpPlanar.direct_basis_integral_bound`, `OAI.SharpPlanar.direct_basis_integral_summable`, `OAI.SharpPlanar.direct_basis_pair`, `OAI.SharpPlanar.direct_piece_integrable`, `OAI.SharpPlanar.tableRaw_offnode` and `OAI_SharpPlanar_tail_barrier_node`; the proofs of `OAI.SharpPlanar.basis_piece_integrable`, `OAI.SharpPlanar.complexDirectFactor_disk_bound`, `OAI.SharpPlanar.directDensity_split`, `OAI.SharpPlanar.directDensity_tsum`, `OAI.SharpPlanar.directIntegrand_analytic`, `OAI.SharpPlanar.directIntegrand_disk_bound`, `OAI.SharpPlanar.directMoment_piece_average_error`, `OAI.SharpPlanar.directMoment_piece_error`, `OAI.SharpPlanar.directMoment_rule_error`, `OAI.SharpPlanar.direct_basis_integral_bound`, `OAI.SharpPlanar.direct_basis_integral_summable`, `OAI.SharpPlanar.direct_basis_pair`, `OAI.SharpPlanar.direct_piece_integrable` and `OAI.SharpPlanar.tableRaw_offnode`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_PlanarPacking

section
-- module Solutions.OAIQ098_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def b : ℝ := Real.sqrt 3 / 2
noncomputable def h : ℝ := 2 / 5

def residues : Finset ℕ := {0, 1, 3, 4, 7, 9}


abbrev Node := {n : ℕ // 0 < n ∧ n % 12 ∈ residues}


abbrev X := lp (fun _ : Node × Bool => ℝ) 1

noncomputable def P (s : ℝ) : ℝ :=
  ∏ a ∈ residues, (2 * Real.sin (Real.pi * (s - a) / 12)) ^ 2

noncomputable def Pcoeff : ℕ → ℂ
  | 0 => 5
  | 1 => -1 + 2 * Complex.I * b
  | 2 => 1 + 2 * Complex.I * b
  | 3 => -2
  | 4 => -(1 / 2) + Complex.I * b
  | 5 => -1 - 2 * Complex.I * b
  | 6 => 1
  | _ => 0

noncomputable def Q (n : ℕ) : ℝ :=
  (Real.pi / 6) ^ 2 * ∏ a ∈ residues.erase (n % 12),
    (2 * Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12)) ^ 2

noncomputable def D (n : ℕ) : ℝ :=
  (Real.pi / 6) * ∑ a ∈ residues.erase (n % 12),
    (Real.cos (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12) /
      Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12))

noncomputable def lambda (t : ℝ) : ℂ :=
  Complex.I / ((b : ℂ) * ((t : ℂ) + Complex.I * (h : ℂ)))


noncomputable def u (n j : ℕ) (t : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) ^ 2 * Complex.exp (-Complex.I * Real.pi * t * n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      ((l : ℂ) / 6 - t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)

noncomputable def v (n j : ℕ) (t : ℝ) : ℂ :=
  2 * Complex.I * Real.pi * Complex.exp (-Complex.I * Real.pi * t * n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)

structure CardinalData where
  C : ℝ
  c₀ : ℝ
  d₀ : ℝ
  x : X

noncomputable def density (p : CardinalData) (j : ℕ) (t : ℝ) : ℂ :=
  (p.c₀ : ℂ) * u 0 j t + (p.d₀ : ℂ) * v 0 j t +
    ∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)


noncomputable def positiveData (x : X) : CardinalData := ⟨0, 0, 0, x⟩


theorem b_pos : 0 < b := by unfold b; positivity

theorem b_sq : b ^ 2 = 3 / 4 := by
  unfold b
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num



theorem X_summable (x : X) : Summable (fun ni : Node × Bool => |x ni|) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

theorem X_summable_coord (x : X) (i : Bool) : Summable (fun n : Node => |x (n, i)|) := by
  exact (X_summable x).comp_injective (fun _ _ hh => congrArg Prod.fst hh)


theorem X_norm (x : X) : ‖x‖ = ∑' n : Node, (|x (n, false)| + |x (n, true)|) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, Real.norm_eq_abs]
  rw [(X_summable x).tsum_prod]
  simp only [tsum_bool]

theorem X_summable_pairs (x : X) :
    Summable (fun n : Node => |x (n, false)| + |x (n, true)|) := by
  exact (X_summable_coord x false).add (X_summable_coord x true)


theorem h_pos : 0 < h := by norm_num [h]

theorem imaginary_gaussian_denominator (t : ℝ) :
    h ≤ ‖(t : ℂ) + Complex.I * (h : ℂ)‖ := by
  have hh := Complex.abs_im_le_norm ((t : ℂ) + Complex.I * (h : ℂ))
  simpa [abs_of_pos h_pos] using hh

theorem lambda_bound (t : ℝ) : ‖lambda t‖ ≤ 1 / (b * h) := by
  rw [lambda, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos b_pos]
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos b_pos h_pos)
  exact mul_le_mul_of_nonneg_left (imaginary_gaussian_denominator t) b_pos.le

noncomputable def kappa : ℝ := 26 * Real.pi / 435

theorem kappa_pos : 0 < kappa := by unfold kappa; positivity


def coeffMass : ℕ → ℝ
  | 0 => 5
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | _ => 0

theorem Pcoeff_norm (j : ℕ) : ‖Pcoeff j‖ = coeffMass j := by
  have hb := b_sq
  rcases lt_or_ge j 7 with hj | hj
  · interval_cases j <;>
      apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num [coeffMass])).mp
    all_goals
      rw [← Complex.normSq_eq_norm_sq]
      norm_num [Pcoeff, coeffMass, Complex.normSq]
    all_goals nlinarith [hb]
  · have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    have hj4 : j ≠ 4 := by omega
    have hj5 : j ≠ 5 := by omega
    have hj6 : j ≠ 6 := by omega
    simp [Pcoeff, coeffMass]


lemma positive_coeff_mass : ∑ l ∈ Finset.Icc 1 6, ‖Pcoeff l‖ = 10 := by
  simp only [Pcoeff_norm]
  norm_num [Finset.sum_Icc_succ_top, coeffMass]

lemma positive_coeff_mass_le (j : ℕ) : ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ ≤ 10 := by
  rw [← positive_coeff_mass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    simp only [Finset.mem_Icc] at hl ⊢
    omega
  · intro l _ _; exact norm_nonneg _

lemma phase_norm (n : ℕ) (t : ℝ) :
    ‖Complex.exp (-Complex.I * Real.pi * t * n)‖ = 1 := by
  simp [Complex.norm_exp]

lemma atom_phase_norm (n l : ℕ) :
    ‖Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)‖ = 1 := by
  simp [Complex.norm_exp]

lemma frequency_distance_le {l : ℕ} (hl : l ≤ 6) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(l : ℂ)/6 - (t : ℂ)‖ ≤ 1 := by
  have he : (l : ℂ)/6 - (t : ℂ) = (((l : ℝ)/6 - t : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hln : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlu : (l : ℝ) ≤ 6 := by exact_mod_cast hl
  constructor <;> linarith [ht.1, ht.2]


lemma u_bound (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖u n j t‖ ≤ 20 * Real.pi^2 := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      ((l : ℂ)/6-t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖((l : ℂ)/6-t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by
        apply Finset.sum_le_sum
        intro l hl
        rw [norm_mul, norm_mul, atom_phase_norm, mul_one]
        exact (mul_le_mul_of_nonneg_right (frequency_distance_le (Finset.mem_Icc.mp hl).2 ht)
          (norm_nonneg _)).trans_eq (one_mul _)
      _ ≤ 10 := positive_coeff_mass_le j
  unfold u
  rw [norm_mul, norm_mul, norm_mul, norm_pow, phase_norm]
  simp only [norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  nlinarith [sq_nonneg Real.pi]

lemma v_bound (n j : ℕ) {t : ℝ} (_ : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ 20 * Real.pi := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ)/6*n)‖ := norm_sum_le _ _
      _ = ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by simp only [norm_mul, atom_phase_norm, mul_one]
      _ ≤ 10 := positive_coeff_mass_le j
  unfold v
  rw [norm_mul, norm_mul, norm_mul, norm_mul, phase_norm]
  simp only [Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]
  nlinarith [Real.pi_pos]

noncomputable def densityBound : ℝ := 20 * Real.pi^2

lemma densityBound_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity

lemma v_bound' (n j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v n j t‖ ≤ densityBound := by
  apply (v_bound n j ht).trans
  unfold densityBound
  nlinarith [Real.pi_gt_three]

lemma summand_bound (x : X) (n : Node) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t‖ ≤
      densityBound * (|x (n, false)| + |x (n, true)|) := by
  calc
    _ ≤ ‖(x (n, false) : ℂ) * u n.val j t‖ + ‖(x (n, true) : ℂ) * v n.val j t‖ := norm_add_le _ _
    _ = |x (n, false)| * ‖u n.val j t‖ + |x (n, true)| * ‖v n.val j t‖ := by
      simp [Complex.norm_real]
    _ ≤ |x (n, false)| * densityBound + |x (n, true)| * densityBound := by
      gcongr
      exacts [u_bound _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring

lemma density_summable (x : X) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun n : Node => (x (n, false) : ℂ) * u n.val j t +
      (x (n, true) : ℂ) * v n.val j t) := by
  exact ((X_summable_pairs x).mul_left densityBound).of_norm_bounded
    (fun n => summand_bound x n j ht)

lemma density_bound (p : CardinalData) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖density p j t‖ ≤ densityBound * (|p.c₀| + |p.d₀| + ‖p.x‖) := by
  have hnorm : Summable (fun n : Node => ‖(p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => summand_bound p.x n j ht)
    exact (X_summable_pairs p.x).mul_left densityBound
  have hsum : ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)‖ ≤ densityBound * ‖p.x‖ := by
    calc
      _ ≤ ∑' n : Node, ‖(p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : Node, densityBound * (|p.x (n, false)| + |p.x (n, true)|) :=
        hnorm.tsum_le_tsum (fun n => summand_bound p.x n j ht)
          ((X_summable_pairs p.x).mul_left densityBound)
      _ = densityBound * ‖p.x‖ := by rw [tsum_mul_left, ← X_norm]
  unfold density
  calc
    _ ≤ ‖(p.c₀ : ℂ) * u 0 j t‖ + ‖(p.d₀ : ℂ) * v 0 j t‖ +
      ‖∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
        (p.x (n, true) : ℂ) * v n.val j t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |p.c₀| * densityBound + |p.d₀| * densityBound + densityBound * ‖p.x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      exacts [u_bound _ _ ht, v_bound' _ _ ht]
    _ = _ := by ring


lemma piece_interval {j : ℕ} (hj : j < 6) {t : ℝ}
    (ht : t ∈ Set.uIcc ((j : ℝ)/6) (((j : ℝ)+1)/6)) : t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.uIcc_of_le (by linarith : (j : ℝ)/6 ≤ ((j : ℝ)+1)/6)] at ht
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj5 : (j : ℝ) ≤ 5 := by exact_mod_cast (show j ≤ 5 by omega)
  constructor <;> linarith [ht.1, ht.2]


lemma continuous_u (n j : ℕ) : Continuous (u n j) := by
  unfold u
  fun_prop

lemma continuous_v (n j : ℕ) : Continuous (v n j) := by
  unfold v
  fun_prop

lemma continuousOn_density (p : CardinalData) (j : ℕ) :
    ContinuousOn (density p j) (Set.Icc (0 : ℝ) 1) := by
  unfold density
  refine ((continuous_const.mul (continuous_u 0 j)).add
    (continuous_const.mul (continuous_v 0 j))).continuousOn.add ?_
  apply continuousOn_tsum (u := fun n : Node =>
    densityBound * (|p.x (n, false)| + |p.x (n, true)|))
  · intro n
    exact ((continuous_const.mul (continuous_u n.val j)).add
      (continuous_const.mul (continuous_v n.val j))).continuousOn
  · exact (X_summable_pairs p.x).mul_left densityBound
  · intro n t ht
    exact summand_bound p.x n j ht

lemma denominator_ne (t : ℝ) : (t : ℂ) + Complex.I * h ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at hh
  exact (ne_of_gt h_pos) hh

lemma continuous_lambda : Continuous lambda := by
  unfold lambda
  fun_prop (disch := intro t; exact mul_ne_zero (by exact_mod_cast b_pos.ne') (denominator_ne t))

lemma density_positive_add (x y : X) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    density (positiveData (x+y)) j t = density (positiveData x) j t +
      density (positiveData y) j t := by
  simp only [density, positiveData, Complex.ofReal_zero, zero_mul, zero_add,
    lp.coeFn_add, Pi.add_apply, Complex.ofReal_add]
  simp_rw [add_mul]
  simp_rw [show ∀ n : Node,
    (x (n, false) : ℂ) * u n.val j t + (y (n, false) : ℂ) * u n.val j t +
    ((x (n, true) : ℂ) * v n.val j t + (y (n, true) : ℂ) * v n.val j t) =
    ((x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t) +
    ((y (n, false) : ℂ) * u n.val j t + (y (n, true) : ℂ) * v n.val j t) from fun n => by ring]
  exact (density_summable x j ht).tsum_add (density_summable y j ht)

lemma density_positive_smul (r : ℝ) (x : X) (j : ℕ) (t : ℝ) :
    density (positiveData (r • x)) j t = (r : ℂ) * density (positiveData x) j t := by
  simp only [density, positiveData, Complex.ofReal_zero, zero_mul, zero_add,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  simp_rw [mul_assoc, ← mul_add, tsum_mul_left]


lemma residue_lt {a : ℕ} (ha : a ∈ residues) : a < 12 := by
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at ha
  omega

lemma Q_pos (n : ℕ) : 0 < Q n := by
  unfold Q
  apply mul_pos (sq_pos_of_pos (by positivity))
  apply Finset.prod_pos
  intro a ha
  have hane : a ≠ n % 12 := (Finset.mem_erase.mp ha).1
  have hal : a < 12 := residue_lt (Finset.mem_erase.mp ha).2
  have hnl : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  have hh1 : (-12 : ℝ) < ((n % 12 : ℕ) : ℝ) - a := by
    have ha' : (a : ℝ) < 12 := by exact_mod_cast hal
    have hn' : (0 : ℝ) ≤ ((n % 12 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hh2 : (((n % 12 : ℕ) : ℝ) - a) < 12 := by
    have hn' : ((n % 12 : ℕ) : ℝ) < 12 := by exact_mod_cast hnl
    have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  have hs : Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - a) / 12) ≠ 0 := by
    rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < ((n%12 : ℕ):ℝ)-a+12)])
      (by nlinarith [Real.pi_pos, mul_pos Real.pi_pos (by linarith : (0 : ℝ) < 12-(((n%12 : ℕ):ℝ)-a))])]
    apply div_ne_zero
    · apply mul_ne_zero Real.pi_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hane)
    · norm_num
  exact sq_pos_of_ne_zero (mul_ne_zero (by norm_num) hs)

lemma Q_mod (n : ℕ) : Q (n % 12) = Q n := by simp [Q]
lemma D_mod (n : ℕ) : D (n % 12) = D n := by simp [D]

noncomputable def nodeWeight (n : ℕ) : ℝ := (1 + |D n|) / Q n
noncomputable def allNodeWeight : ℝ := ∑ a ∈ residues, nodeWeight a

lemma nodeWeight_pos (n : ℕ) : 0 < nodeWeight n := by
  unfold nodeWeight
  exact div_pos (by positivity) (Q_pos n)

lemma nodeWeight_le (n : Node) : nodeWeight n.val ≤ allNodeWeight := by
  have he : nodeWeight n.val = nodeWeight (n.val % 12) := by rw [nodeWeight, nodeWeight, Q_mod, D_mod]
  rw [he]
  exact Finset.single_le_sum (fun a _ => (nodeWeight_pos a).le) n.property.2


lemma exp_nat_summable : Summable (fun n : ℕ => Real.exp (-kappa * n)) := by
  have he : Real.exp (-kappa) < 1 := by rw [Real.exp_lt_one_iff]; linarith [kappa_pos]
  have hh := summable_geometric_of_lt_one (Real.exp_pos (-kappa)).le he
  simpa only [← Real.exp_nat_mul, mul_comm] using hh

end SharpPlanar

namespace SharpPlanar
open Complex

noncomputable def complexLambda (t : ℂ) : ℂ :=
  Complex.I / ((b:ℂ) * (t+Complex.I*(h:ℂ)))


lemma reciprocal_disk_identity (a ζ : ℂ) (r : ℝ)
    (hΔ : Complex.normSq a-r^2 ≠ 0) :
    Complex.normSq (1-a*ζ)-r^2*Complex.normSq ζ =
      (Complex.normSq a-r^2)*Complex.normSq
        (ζ-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a) -
          r^2/(Complex.normSq a-r^2) := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,
    Complex.mul_im,Complex.one_re,Complex.one_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,zero_mul] at *
  simp only [← sq] at hΔ
  field_simp [hΔ]
  ring

lemma reciprocal_disk_bound {a u : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hΔ : 0 < Complex.normSq a-r^2) (hu : ‖u-a‖ ≤ r) (hu0 : u ≠ 0) :
    ‖u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a‖ ≤ r/(Complex.normSq a-r^2) := by
  let Δ := Complex.normSq a-r^2
  have hid := reciprocal_disk_identity a u⁻¹ r (ne_of_gt hΔ)
  have he : (1:ℂ)-a*u⁻¹ = (u-a)*u⁻¹ := by field_simp
  rw [he,Complex.normSq_mul,Complex.normSq_eq_norm_sq (u-a)] at hid
  have hnon : 0 ≤ Complex.normSq u⁻¹ := Complex.normSq_nonneg _
  have hsmall : Complex.normSq a-r^2 > 0 := hΔ
  have hprod : (‖u-a‖^2-r^2)*Complex.normSq u⁻¹ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (u-a)]) hnon
  rw [Complex.normSq_eq_norm_sq (u⁻¹-(((Complex.normSq a-r^2)⁻¹:ℝ):ℂ)*conj a)] at hid
  have hdpos : 0 < Δ := hΔ
  have hdne : Δ ≠ 0 := ne_of_gt hdpos
  have hratio : 0 ≤ r/Δ := div_nonneg hr hdpos.le
  have hn := norm_nonneg (u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a)
  have hsq : ‖u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a‖^2 ≤ (r/Δ)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hdpos)).mp
    have heq : Δ^2*(r/Δ)^2 = r^2 := by field_simp
    rw [heq]
    have hprod' : Δ*‖u⁻¹-((Δ⁻¹:ℝ):ℂ)*conj a‖^2 ≤ r^2/Δ := by
      dsimp [Δ]
      nlinarith only [hid,hprod]
    have hh := mul_le_mul_of_nonneg_left hprod' hdpos.le
    have heq' : Δ*(r^2/Δ) = r^2 := by field_simp
    rw [heq'] at hh
    nlinarith only [hh]
  dsimp [Δ] at *
  nlinarith only [hsq, hn, hratio]


noncomputable def diskCenter (j : ℕ) : ℝ := (2*(j:ℝ)+1)/12

lemma disk_coordinate_bounds {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖t‖ ≤ 13/12 ∧ -(1/6:ℝ) ≤ t.im ∧ t.im ≤ 1/6 := by
  have hc0 : 0 ≤ diskCenter j := by unfold diskCenter; positivity
  have hc1 : diskCenter j ≤ 11/12 := by
    unfold diskCenter
    have : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
    linarith
  have hi := (Complex.abs_im_le_norm (t-(diskCenter j:ℂ))).trans ht
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,abs_le] at hi
  refine ⟨?_, hi⟩
  have hn := norm_add_le (t-(diskCenter j:ℂ)) (diskCenter j:ℂ)
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0] at hn
  linarith

lemma disk_denominator_lower {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    7/30 ≤ ‖t+Complex.I*(h:ℂ)‖ := by
  have hi := (disk_coordinate_bounds hj ht).2.1
  have hn := (le_abs_self (t+Complex.I*(h:ℂ)).im).trans (Complex.abs_im_le_norm _)
  simp only [Complex.add_im,Complex.I_mul_im,Complex.ofReal_re] at hn
  norm_num [h] at hn ⊢
  linarith

lemma disk_denominator_ne {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : t+Complex.I*(h:ℂ) ≠ 0 := by
  have hb := disk_denominator_lower hj ht
  intro he
  rw [he,norm_zero] at hb
  norm_num at hb

lemma b_lower_simple : 43/50 < b := by
  have hh := b_sq
  have hp := b_pos
  nlinarith

lemma disk_lambda_bound {j : ℕ} (hj : j < 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖complexLambda t‖ < 5 := by
  have hd := disk_denominator_lower hj ht
  have hb := b_lower_simple
  rw [complexLambda,norm_div,norm_mul,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos b_pos]
  apply (div_lt_iff₀ (mul_pos b_pos (by linarith))).mpr
  nlinarith

lemma disk_delta_bounds {j : ℕ} (hj : j < 6) :
    167/1200 ≤ Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ∧
    Complex.normSq ((diskCenter j:ℂ)+Complex.I*(h:ℂ))-(1/6:ℝ)^2 ≤ 389/400 := by
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  have hj5 : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_mul_re,Complex.I_mul_im,
    neg_zero,add_zero,zero_add]
  unfold diskCenter h
  constructor <;> nlinarith [sq_nonneg (j:ℝ)]

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set


noncomputable def complexU (n j : ℕ) (t : ℂ) : ℂ :=
  -2 * (Real.pi:ℂ)^2 * Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      ((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)
noncomputable def complexV (n j : ℕ) (t : ℂ) : ℂ :=
  2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)

lemma disk_frequency_distance {j : ℕ} (hj : j < 6) {l : ℕ}
    (hl : l ∈ Finset.Icc (j+1) 6) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) : ‖(l:ℂ)/6-t‖ ≤ 13/12 := by
  have hjr : (j:ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)
  have hl0 : (0:ℝ) ≤ l := Nat.cast_nonneg l
  have hl1 : (l:ℝ) ≤ 6 := by exact_mod_cast (Finset.mem_Icc.mp hl).2
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hh : ‖(l:ℂ)/6-(diskCenter j:ℂ)‖ ≤ 11/12 := by
    rw [show (l:ℂ)/6-(diskCenter j:ℂ) = (((l:ℝ)/6-diskCenter j:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_le]
    unfold diskCenter
    constructor <;> linarith
  have hn := norm_sub_le ((l:ℂ)/6-(diskCenter j:ℂ)) (t-(diskCenter j:ℂ))
  rw [sub_sub_sub_cancel_right] at hn
  linarith

lemma disk_phase_bound {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖Complex.exp (-Complex.I*Real.pi*t*n)‖ ≤ Real.exp (100*Real.pi/6) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have ht' := (disk_coordinate_bounds hj ht).2.2
  have hn' : (n:ℝ) ≤ 100 := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,zero_mul,
    mul_zero,sub_zero,neg_zero,Complex.mul_im,zero_add]
  nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le hn0,
    mul_nonneg Real.pi_pos.le (show 0 ≤ 100-(n:ℝ) by linarith)]

lemma complexU_disk_bound {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖complexU n j t‖ ≤ 250*Real.exp (100*Real.pi/6) := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      ((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ ≤ (13/12)*10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6,
        ‖((l:ℂ)/6-t)*Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ := norm_sum_le _ _
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, (13/12)*‖Pcoeff l‖ := by
        apply Finset.sum_le_sum
        intro l hl
        rw [norm_mul,norm_mul,atom_phase_norm,mul_one]
        exact mul_le_mul_of_nonneg_right (disk_frequency_distance hj hl ht) (norm_nonneg _)
      _ ≤ (13/12)*10 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (positive_coeff_mass_le j) (by norm_num)
  unfold complexU
  simp only [norm_mul,norm_pow,norm_neg,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ 2*Real.pi^2 * Real.exp (100*Real.pi/6) * ((13/12)*10) := by
      gcongr
      exact disk_phase_bound hj hn ht
    _ ≤ _ := by
      have hp := Real.pi_lt_d2
      have hp0 := Real.pi_pos
      have hp2 : Real.pi^2 < 10 := by nlinarith
      have he := Real.exp_pos (100*Real.pi/6)
      nlinarith

lemma complexV_disk_bound {j n : ℕ} (hj : j < 6) (hn : n ≤ 100) {t : ℂ}
    (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖complexV n j t‖ ≤ 250*Real.exp (100*Real.pi/6) := by
  have hs : ‖∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ ≤ 10 := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)‖ := norm_sum_le _ _
      _ = ∑ l ∈ Finset.Icc (j+1) 6, ‖Pcoeff l‖ := by simp only [norm_mul,atom_phase_norm,mul_one]
      _ ≤ 10 := positive_coeff_mass_le j
  unfold complexV
  simp only [norm_mul,Complex.norm_I,Complex.norm_ofNat,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  calc
    _ ≤ 2*Real.pi*Real.exp (100*Real.pi/6)*10 := by
      gcongr
      exact disk_phase_bound hj hn ht
    _ ≤ _ := by
      have := Real.pi_lt_d2
      have := Real.exp_pos (100*Real.pi/6)
      nlinarith

noncomputable def finiteDensity (c d : ℕ → ℝ) (j : ℕ) (t : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 101, ((c n:ℂ)*complexU n j t + (d n:ℂ)*complexV n j t)

lemma finiteDensity_disk_bound (c d : ℕ → ℝ)
    (hw : ∑ n ∈ Finset.range 101, (|c n|+|d n|) ≤ 3)
    {j : ℕ} (hj : j < 6) {t : ℂ} (ht : ‖t-(diskCenter j:ℂ)‖ ≤ 1/6) :
    ‖finiteDensity c d j t‖ ≤ 1000*Real.exp (100*Real.pi/6) := by
  unfold finiteDensity
  calc
    _ ≤ ∑ n ∈ Finset.range 101, ‖(c n:ℂ)*complexU n j t + (d n:ℂ)*complexV n j t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range 101, (|c n|+|d n|)*(250*Real.exp (100*Real.pi/6)) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ ‖(c n:ℂ)*complexU n j t‖ + ‖(d n:ℂ)*complexV n j t‖ := norm_add_le _ _
        _ ≤ |c n| *(250*Real.exp (100*Real.pi/6)) + |d n| *(250*Real.exp (100*Real.pi/6)) := by
          simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
          gcongr
          · exact complexU_disk_bound hj (by have := Finset.mem_range.mp hn; omega) ht
          · exact complexV_disk_bound hj (by have := Finset.mem_range.mp hn; omega) ht
        _ = _ := by ring
    _ ≤ 3*(250*Real.exp (100*Real.pi/6)) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ _ := by have := Real.exp_pos (100*Real.pi/6); linarith

end SharpPlanar

namespace SharpPlanar
open Complex

lemma divided_power_norm (w : ℂ) (ell : ℕ) :
    ‖w^ell / (ell.factorial:ℂ)‖ ≤ Real.exp ‖w‖ := by
  simpa only [norm_div,norm_pow,Complex.norm_natCast] using
    Real.pow_div_factorial_le_exp ‖w‖ (norm_nonneg w) ell

lemma phase_exp_norm_bound {w : ℂ} {m L : ℝ} (hm : 0 ≤ m) (hw : -L ≤ w.im) :
    ‖Complex.exp (Complex.I*Real.pi*w*m)‖ ≤ Real.exp (Real.pi*m*L) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,
    zero_sub,sub_zero,zero_add]
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hm) (show 0 ≤ w.im+L by linarith)]

lemma numerical_moment_bound : (5000:ℝ)*Real.exp 111 < (10:ℝ)^53 := by
  have he : Real.exp 1 < 11/4 := by linarith [Real.exp_one_lt_d9]
  have hex : Real.exp 111 = (Real.exp 1)^111 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hex]
  have hp : (Real.exp 1)^111 ≤ (11/4:ℝ)^111 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 111
  calc
    _ ≤ 5000*(11/4:ℝ)^111 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ < _ := by norm_num

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

def precision : ℤ := 10^30
lemma precision_pos : (0:ℝ) < precision := by norm_num [precision]

lemma between_mul {a b y x L U : ℝ} (hy : a ≤ y ∧ y ≤ b)
    (ha : L ≤ x*a ∧ x*a ≤ U) (hb : L ≤ x*b ∧ x*b ≤ U) :
    L ≤ x*y ∧ x*y ≤ U := by
  rcases le_total 0 x with hx | hx
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hy.1 hx),
      (mul_le_mul_of_nonneg_left hy.2 hx).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_left hy.2 hx),
      (mul_le_mul_of_nonpos_left hy.1 hx).trans ha.2⟩
lemma real_mul_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  apply between_mul hy
  · rw [mul_comm x c]
    apply between_mul hx <;> constructor <;> simp only [mul_comm c, le_max_iff, min_le_iff, le_refl] <;> tauto
  · rw [mul_comm x d]
    apply between_mul hx <;> constructor <;> simp only [mul_comm d, le_max_iff, min_le_iff, le_refl] <;> tauto

noncomputable def expHorner (z : ℂ) (k : ℕ) : ℕ → ℂ
  | 0 => (k.factorial:ℂ)⁻¹
  | n+1 => (k.factorial:ℂ)⁻¹ + z*expHorner z (k+1) n

lemma expHorner_eq (z : ℂ) (k n : ℕ) :
    expHorner z k n = ∑ i ∈ Finset.range (n+1), z^i/((k+i).factorial:ℂ) := by
  induction n generalizing k with
  | zero => simp [expHorner]
  | succ n ih =>
    rw [expHorner,ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero,Nat.add_zero,one_div]
    rw [add_comm,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']
    simp only [Nat.add_assoc,Nat.add_comm 1 i,mul_div_assoc]

lemma exp_small_error {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (precision:ℝ)*‖Complex.exp z-expHorner z 0 32‖ ≤ 1 := by
  rw [expHorner_eq]
  simp only [Nat.zero_add]
  have hh := Complex.exp_bound hz (n:=33) (by norm_num)
  have hp : ‖z‖^33 ≤ (1:ℝ) := pow_le_one₀ (norm_nonneg _) hz
  have hc : (34:ℝ)*((33).factorial*33:ℝ)⁻¹ ≤ 1/10^30 := by norm_num
  have hb : ‖Complex.exp z-∑ n ∈ Finset.range 33, z^n/(n.factorial:ℂ)‖ ≤ 1/10^30 :=
    hh.trans ((mul_le_of_le_one_left (by positivity) hp).trans hc)
  dsimp [precision]
  norm_num
  nlinarith only [hb]

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

lemma floor_mul_le (x : ℤ) {n : ℤ} (hn : 0 < n) : x/n*n ≤ x :=
  Int.ediv_mul_le x (ne_of_gt hn)
lemma le_ceil_mul (x : ℤ) {n : ℤ} (hn : 0 < n) : x ≤ -((-x)/n)*n := by
  have hh := floor_mul_le (-x) hn
  nlinarith only [hh]

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

-- These are exactly lambda,z from fourier:frequencies, restricted to real t.
noncomputable def pointLambda (t : ℝ) : ℂ :=
  Complex.I / (((Real.sqrt 3/2:ℝ):ℂ) * ((t:ℂ)+Complex.I*(2/5:ℂ)))
noncomputable def pointZ (t : ℝ) : ℂ :=
  -(4/3:ℂ) / ((t:ℂ)+Complex.I*(2/5:ℂ)) - Complex.I*(2/5:ℂ)

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Fejer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fejér quadrature enclosures

Certified nodes and weights for the 256-node cosine quadrature rule.
-/

namespace SharpPlanar
noncomputable def fejerAngle (v : ℕ) : ℝ := Real.pi*((v:ℝ)+1/2)/256
noncomputable def fejerNode (v : ℕ) : ℝ := Real.cos (fejerAngle v)
noncomputable def fejerWeight (v : ℕ) : ℝ :=
  (1-2*∑ a ∈ Finset.Icc (1:ℕ) 127,
    Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1))/256


end SharpPlanar

namespace SharpPlanar
open IntegerIntervals

noncomputable def fejerPartial (v N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    Real.cos (2*((k+1:ℕ):ℝ)*fejerAngle v)/(4*((k+1:ℕ):ℝ)^2-1)

lemma fejerPartial_zero (v : ℕ) : fejerPartial v 0 = 0 := by simp [fejerPartial]

lemma fejerPartial_succ (v N : ℕ) : fejerPartial v (N+1) = fejerPartial v N +
    Real.cos (2*((N+1:ℕ):ℝ)*fejerAngle v)/(4*((N+1:ℕ):ℝ)^2-1) := by
  simp only [fejerPartial,Finset.sum_range_succ]

lemma fejer_partial_eq (v : ℕ) : fejerPartial v 127 =
    ∑ a ∈ Finset.Icc (1:ℕ) 127, Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1) := by
  unfold fejerPartial
  apply Finset.sum_bij (fun k _ => k+1)
  · intro k hk
    simp only [Finset.mem_Icc]
    have := Finset.mem_range.mp hk
    omega
  · intro k hk l hl hkl
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact ⟨k-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro k hk
    rfl

lemma fejerWeight_reverse (v : ℕ) (hv : v < 256) : fejerWeight (255-v) = fejerWeight v := by
  have hv' : v ≤ 255 := by omega
  have ha : fejerAngle (255-v) = Real.pi-fejerAngle v := by
    unfold fejerAngle
    rw [Nat.cast_sub hv']
    push_cast
    ring
  unfold fejerWeight
  rw [ha]
  congr 3
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [show 2*(a:ℝ)*(Real.pi-fejerAngle v)=(a:ℝ)*(2*Real.pi)-2*(a:ℝ)*fejerAngle v by ring]
  exact Real.cos_nat_mul_two_pi_sub _ a

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma cheb_primitive_deriv (n : ℤ) (hn₁ : n+1 ≠ 0) (hn₂ : n-1 ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (T ℝ (n+1)).eval x/(2*(n+1:ℤ))-
      (T ℝ (n-1)).eval x/(2*(n-1:ℤ))) ((T ℝ n).eval x) x := by
  have h := ((T ℝ (n+1)).hasDerivAt x).div_const (2*(n+1:ℤ) : ℝ)
  have h' := ((T ℝ (n-1)).hasDerivAt x).div_const (2*(n-1:ℤ) : ℝ)
  convert h.sub h' using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  rw [T_derivative_eq_U, T_derivative_eq_U]
  simp only [eval_mul, eval_intCast]
  have hu := congrArg (fun p : ℝ[X] => p.eval x) (two_mul_T_eq_U_sub_U ℝ (n-2))
  simp only [sub_add_cancel, eval_mul, eval_sub, eval_ofNat] at hu
  have hn₁' : (n+1:ℝ) ≠ 0 := by exact_mod_cast hn₁
  have hn₂' : (n-1:ℝ) ≠ 0 := by exact_mod_cast hn₂
  push_cast
  simp only [show n+1-1=n by omega, show n-1-1=n-2 by omega]
  field_simp
  nlinarith [hu]

lemma cheb_integral (n : ℕ) :
    (∫ x in (-1:ℝ)..1, (T ℝ n).eval x) =
    (1+(-1:ℝ)^n)/(1-(n:ℝ)^2) := by
  by_cases hn : n=1
  · subst n
    norm_num [integral_id]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => cheb_primitive_deriv (n:ℤ) (by omega) (by omega) x)
    ((T ℝ (n:ℤ)).continuous.intervalIntegrable (-1) 1)
  rw [h, T_eval_one, T_eval_one, T_eval_neg_one, T_eval_neg_one]
  have hp : ((n:ℤ)+1).negOnePow = -(n:ℤ).negOnePow := by simp [Int.negOnePow_add]
  have hm : ((n:ℤ)-1).negOnePow = -(n:ℤ).negOnePow := by simp [Int.negOnePow_sub]
  rw [hp, hm]
  simp only [Units.val_neg, Int.cast_neg]
  have hnat : (((n:ℤ).negOnePow : ℤ) : ℝ) = (-1:ℝ)^n := by
    rw [Int.cast_negOnePow]
    simp
  rw [hnat]
  push_cast
  have hn₁ : (n:ℝ)+1 ≠ 0 := by positivity
  have hn₂ : (n:ℝ)-1 ≠ 0 := by exact_mod_cast (by omega : (n:ℤ)-1 ≠ 0)
  have hn₃ : 1-(n:ℝ)^2 ≠ 0 := by
    intro hzero
    have : (n:ℝ)=1 := by have := Nat.cast_nonneg (α:=ℝ) n; nlinarith
    exact hn (by exact_mod_cast this)
  field_simp
  ring

lemma fejer_recip_telescope (a : ℕ) (ha : 1 ≤ a) :
    (2:ℝ)/(4*(a:ℝ)^2-1) = 1/(2*(a:ℝ)-1)-1/(2*(a:ℝ)+1) := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have h₁ : 2*(a:ℝ)-1 ≠ 0 := by linarith
  have h₂ : 2*(a:ℝ)+1 ≠ 0 := by linarith
  have h₃ : 4*(a:ℝ)^2-1 ≠ 0 := by nlinarith
  field_simp
  ring

lemma fejer_recip_sum (m : ℕ) :
    (∑ a ∈ Finset.Icc 1 m, (2:ℝ)/(4*(a:ℝ)^2-1)) = 1-1/(2*(m:ℝ)+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih,
      fejer_recip_telescope (m+1) (by omega)]
    push_cast
    have he : 2*((m:ℝ)+1)-1=2*(m:ℝ)+1 := by ring
    rw [he]
    ring

lemma fejerWeight_pos (v : ℕ) : 1/(256*255:ℝ) ≤ fejerWeight v := by
  have hsum : (2:ℝ)*∑ a ∈ Finset.Icc (1:ℕ) 127,
      Real.cos (2*(a:ℝ)*fejerAngle v)/(4*(a:ℝ)^2-1) ≤ 254/255 := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ a ∈ Finset.Icc (1:ℕ) 127, (2:ℝ)/(4*(a:ℝ)^2-1) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
        have hd : 0 < 4*(a:ℝ)^2-1 := by nlinarith
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by nlinarith [Real.cos_le_one (2*(a:ℝ)*fejerAngle v)]) hd.le
      _ = 254/255 := by rw [fejer_recip_sum]; norm_num
  unfold fejerWeight
  linarith


noncomputable def fejerPolynomial :=
  1-∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1)) • T ℝ (2*a)

lemma fejerPolynomial_eval (v : ℕ) :
    fejerPolynomial.eval (fejerNode v) = 256*fejerWeight v := by
  unfold fejerPolynomial
  rw [eval_sub, eval_one, eval_finsetSum]
  simp only [eval_smul, smul_eq_mul, fejerNode, T_real_cos]
  unfold fejerWeight
  simp only [Finset.mul_sum]
  push_cast
  rw [show ∀ x : ℝ, 256*(x/256)=x from fun x => by ring]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma fejerPolynomial_degree : fejerPolynomial.degree ≤ 254 := by
  apply (degree_sub_le _ _).trans
  apply max_le
  · norm_num
  · apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro a ha
    apply (degree_smul_le _ _).trans
    rw [degree_T]
    have ha' := (Finset.mem_Icc.mp ha).2
    norm_cast
    omega

lemma fejer_weighted_orthogonal (n : ℕ) :
    (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
      (∫ x, (T ℝ n).eval x ∂measureT) -
      ∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
        (∫ x, (T ℝ (2*a)).eval x*(T ℝ n).eval x ∂measureT) := by
  unfold fejerPolynomial
  simp only [eval_sub, eval_one, eval_finsetSum, eval_smul, smul_eq_mul,
    sub_mul, one_mul, Finset.sum_mul, mul_assoc]
  rw [MeasureTheory.integral_sub (integrable_measureT (by fun_prop))
    (integrable_measureT (by fun_prop)), MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_const_mul]
  · intro a ha
    exact integrable_measureT (by fun_prop)

lemma fejer_integral_zero :
    (∫ x, fejerPolynomial.eval x*(T ℝ 0).eval x ∂measureT) = Real.pi := by
  change (∫ x, fejerPolynomial.eval x*(T ℝ (0:ℕ)).eval x ∂measureT) = _
  rw [fejer_weighted_orthogonal 0]
  norm_num only [Nat.cast_zero] at *
  rw [integral_eval_T_real_measureT_zero]
  simp only [sub_eq_self]
  apply Finset.sum_eq_zero
  intro a ha
  have hne : 2*a ≠ (0:ℕ) := by have := (Finset.mem_Icc.mp ha).1; omega
  have h := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne
  push_cast at h
  rw [h, mul_zero]

lemma fejer_integral_even (k : ℕ) (hk : k ∈ Finset.Icc 1 127) :
    (∫ x, fejerPolynomial.eval x*(T ℝ (2*k)).eval x ∂measureT) =
      Real.pi/(1-(2*(k:ℝ))^2) := by
  have hk₀ : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  have hcast : (2*(k:ℤ)) ≠ 0 := by omega
  have he := fejer_weighted_orthogonal (2*k)
  push_cast at he
  rw [he]
  rw [integral_eval_T_real_measureT_of_ne_zero hcast]
  rw [Finset.sum_eq_single_of_mem k hk]
  · have hh := integral_T_real_mul_self_measureT_of_ne_zero (by omega : 2*k ≠ 0)
    push_cast at hh
    rw [hh]
    rw [show 1-(2*(k:ℝ))^2 = -(4*(k:ℝ)^2-1) by ring]
    simp only [div_neg]
    ring
  · intro a ha hne
    have hne' : 2*a ≠ 2*k := by omega
    have hh := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne'
    push_cast at hh
    rw [hh, mul_zero]

lemma fejer_integral_odd (k : ℕ) :
    (∫ x, fejerPolynomial.eval x*(T ℝ (2*k+1)).eval x ∂measureT) = 0 := by
  have hh := fejer_weighted_orthogonal (2*k+1)
  push_cast at hh
  rw [hh, integral_eval_T_real_measureT_of_ne_zero (by omega : (2*(k:ℤ)+1) ≠ 0)]
  have he : (∑ a ∈ Finset.Icc (1:ℕ) 127, (2/(4*(a:ℝ)^2-1))*
      (∫ x, (T ℝ (2*a)).eval x*(T ℝ (2*k+1)).eval x ∂measureT)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hne : 2*a ≠ 2*k+1 := by omega
    have h := integral_eval_T_real_mul_eval_T_real_measureT_of_ne hne
    push_cast at h
    rw [h, mul_zero]
  rw [he, sub_self]

lemma fejer_cheb_integral (n : ℕ) (hn : n < 256) :
    (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
      (Real.pi/2)*(∫ x in (-1:ℝ)..1, (T ℝ n).eval x) := by
  rw [cheb_integral]
  rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
  · have he : n=2*k := by omega
    rw [he] at hn ⊢
    by_cases hk₀ : k=0
    · subst k
      simpa only [Nat.mul_zero, Nat.cast_zero, pow_zero, add_self_div_two,
        zero_pow (by norm_num : 2 ≠ 0), sub_zero, div_one, one_add_one_eq_two,
        div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using fejer_integral_zero
    · rw [show ((2*k:ℕ):ℤ)=2*(k:ℤ) by push_cast; rfl,
        fejer_integral_even k (by simp only [Finset.mem_Icc]; omega)]
      simp only [pow_mul, neg_one_sq, one_pow, Nat.cast_mul, Nat.cast_ofNat]
      ring
  · subst n
    rw [show ((2*k+1:ℕ):ℤ)=2*(k:ℤ)+1 by push_cast; rfl, fejer_integral_odd]
    simp [pow_add, pow_mul]

lemma fejer_polynomial_integral (P : ℝ[X]) (hP : P.degree < 256) :
    (∫ x, fejerPolynomial.eval x * P.eval x ∂measureT) =
      (Real.pi/2)*(∫ x in (-1:ℝ)..1, P.eval x) := by
  have hmem : P ∈ degreeLT ℝ 256 := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio 256 = Finset.range 256 by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum, intervalIntegral.integral_finsetSum]
  · simp_rw [mul_left_comm (fejerPolynomial.eval _) (c _),
      MeasureTheory.integral_const_mul, intervalIntegral.integral_const_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [show (chebyshevTsequence ℝ n) = T ℝ n by rfl,
      fejer_cheb_integral n (Finset.mem_range.mp hn)]
    ring
  · intro n hn
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro n hn
    exact integrable_measureT (by fun_prop)

lemma fejer_exact (P : ℝ[X]) (hP : P.degree < 256) :
    ∑ v ∈ Finset.range 256, fejerWeight v * P.eval (fejerNode v) =
      (1/2:ℝ)*(∫ x in (-1:ℝ)..1, P.eval x) := by
  by_cases hp : P=0
  · simp [hp]
  have hdP : P.natDegree ≤ 255 := by
    have : P.natDegree < (256:ℕ) := (natDegree_lt_iff_degree_lt hp).mpr hP
    omega
  have hdF : fejerPolynomial.natDegree ≤ 254 :=
    natDegree_le_iff_degree_le.mpr fejerPolynomial_degree
  have hd : (fejerPolynomial*P).degree < 2*256 := by
    apply lt_of_le_of_lt (degree_le_natDegree)
    have hnat : (fejerPolynomial*P).natDegree ≤ 509 :=
      (natDegree_mul_le).trans (by omega)
    exact_mod_cast (by omega : (fejerPolynomial*P).natDegree < 2*256)
  have h := integral_eq_sumZeroes (P:=fejerPolynomial*P) (by norm_num : 256 ≠ 0) hd
  simp only [eval_mul] at h
  rw [fejer_polynomial_integral P hP] at h
  unfold sumZeroes at h
  have he : ∀ v : ℕ, Real.cos (((2*(v:ℝ)+1)/512)*Real.pi) = fejerNode v := by
    intro v
    unfold fejerNode fejerAngle
    congr 1
    ring
  norm_num only [Nat.cast_ofNat] at h
  simp only [he, eval_mul, fejerPolynomial_eval] at h
  simp only [mul_assoc, ← Finset.mul_sum] at h
  have halg (A B : ℝ) (hab : Real.pi/2*A = Real.pi/256*(256*B)) :
      B=(1/2:ℝ)*A := by nlinarith only [hab, Real.pi_pos]
  exact halg _ _ h

lemma fejer_mass : ∑ v ∈ Finset.range 256, fejerWeight v = 1 := by
  have h := fejer_exact 1 (by norm_num)
  norm_num at h ⊢
  exact h

lemma fejerNode_mem (v : ℕ) : fejerNode v ∈ Set.Icc (-1:ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

lemma fejer_exact_monomial (k : ℕ) (hk : k < 256) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*(fejerNode v : ℂ)^k) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, (x:ℂ)^k) := by
  have h := fejer_exact (Polynomial.X^k) (by simpa using hk)
  simp only [eval_pow,eval_X] at h
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  simpa only [← Complex.ofReal_pow,intervalIntegral.integral_ofReal] using hc

lemma fejer_exact_complex (c : ℕ → ℂ) :
    (∑ v ∈ Finset.range 256, (fejerWeight v : ℂ)*
      (∑ k ∈ Finset.range 256, c k*(fejerNode v : ℂ)^k)) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, ∑ k ∈ Finset.range 256, c k*(x:ℂ)^k) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = c k * ∑ v ∈ Finset.range 256,
          (fejerWeight v : ℂ)*(fejerNode v : ℂ)^k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = _ := by rw [fejer_exact_monomial k (Finset.mem_range.mp hk)]; ring
  · intro k hk
    exact Continuous.intervalIntegrable (by fun_prop) _ _

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators

namespace SharpPlanar

lemma geometric_tail_error {a : ℕ → ℂ} {v : ℂ} {M r : ℝ}
    (ha : HasSum a v) (hr0 : 0 ≤ r) (hr : r < 1)
    (hb : ∀ n, ‖a n‖ ≤ M*r^n) (N : ℕ) :
    ‖v-∑ n ∈ Finset.range N, a n‖ ≤ M*r^N/(1-r) := by
  have hsum := ha.summable.sum_add_tsum_nat_add N
  rw [ha.tsum_eq] at hsum
  have he : v-∑ n ∈ Finset.range N, a n = ∑' n, a (n+N) := by
    rw [← hsum]
    abel
  rw [he]
  have hg : HasSum (fun n : ℕ => M*r^N*r^n) (M*r^N/(1-r)) :=
    (hasSum_geometric_of_lt_one hr0 hr).mul_left (M*r^N)
  apply tsum_of_norm_bounded hg
  intro n
  calc
    ‖a (n+N)‖ ≤ M*r^(n+N) := hb _
    _ = M*r^N*r^n := by rw [pow_add]; ring

noncomputable def taylorPolynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹*iteratedDeriv n f c*(z-c)^n

lemma analytic_taylor_error {f : ℂ → ℂ} {c z : ℂ} {R M r : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr : r < 1)
    (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hbound : ∀ w ∈ Metric.sphere c R, ‖f w‖ ≤ M)
    (hz : ‖z-c‖ ≤ r*R) (N : ℕ) :
    ‖f z-taylorPolynomial f c N z‖ ≤ M*r^N/(1-r) := by
  have hz' : z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hz.trans_lt (by nlinarith)
  have hsum := Complex.hasSum_taylorSeries_on_ball hf.differentiableOn hz'
  have hs : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹*
      iteratedDeriv n f c*(z-c)^n) (f z) := by
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (funext n; simp only [smul_eq_mul]; ring)
  apply geometric_tail_error hs hr0 hr _ N
  intro n
  have hn : (0 : ℝ) < n.factorial := by positivity
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf hbound
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  calc
    (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f c‖ * ‖z-c‖^n ≤
      (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ)*M/R^n) * (r*R)^n := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity))
        (pow_le_pow_left₀ (norm_nonneg _) hz n) (by positivity) (by positivity)
    _ = M*r^n := by rw [mul_pow]; field_simp


lemma positive_quadrature_error {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (w t : ι → ℝ) (f p : ℝ → ℂ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, t i ∈ Icc a b)
    (hmass : ∑ i, w i = b-a)
    (hf : ContinuousOn f (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (herr : ∀ x ∈ Icc a b, ‖f x-p x‖ ≤ ε)
    (hexact : (∫ x in a..b, p x) = ∑ i, (w i : ℂ)*p (t i)) :
    ‖(∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i)‖ ≤ 2*(b-a)*ε := by
  have hi₁ : IntervalIntegrable f volume a b :=
    (hf.intervalIntegrable_of_Icc hab)
  have hi₂ : IntervalIntegrable p volume a b :=
    (hp.intervalIntegrable_of_Icc hab)
  have he : (∫ x in a..b, f x)-∑ i, (w i : ℂ)*f (t i) =
      (∫ x in a..b, f x-p x) - ∑ i, (w i : ℂ)*(f (t i)-p (t i)) := by
    rw [intervalIntegral.integral_sub hi₁ hi₂, hexact]
    simp only [mul_sub, Finset.sum_sub_distrib]
    abel
  rw [he]
  have hInt : ‖∫ x in a..b, f x-p x‖ ≤ (b-a)*ε := by
    calc
      _ ≤ ∫ x in a..b, ‖f x-p x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, ε := intervalIntegral.integral_mono_on hab
        (hi₁.sub hi₂).norm (intervalIntegrable_const) (fun x hx => herr x hx)
      _ = (b-a)*ε := by simp
  have hFin : ‖∑ i, (w i : ℂ)*(f (t i)-p (t i))‖ ≤ (b-a)*ε := by
    calc
      _ ≤ ∑ i, ‖(w i : ℂ)*(f (t i)-p (t i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, w i*ε := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (herr _ (ht i)) (hw i)
      _ = (b-a)*ε := by rw [← Finset.sum_mul, hmass]
  exact (norm_sub_le _ _).trans (by nlinarith)

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

lemma taylorPolynomial_zero (f : ℂ → ℂ) (N : ℕ) :
    taylorPolynomial f 0 N = fun z =>
      ∑ k ∈ Finset.range N, ((k.factorial:ℂ)⁻¹*iteratedDeriv k f 0)*z^k := by
  funext z
  simp only [taylorPolynomial,sub_zero]

lemma fejer_analytic_average_error (f : ℂ → ℂ)
    (hf : DiffContOnCl ℂ f (Metric.ball 0 2))
    (hbound : ∀ z ∈ Metric.sphere 0 2, ‖f z‖ ≤ (10:ℝ)^53) :
    ‖(1/2:ℂ)*(∫ x in (-1:ℝ)..1, f x) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*f (fejerNode v.val)‖ < 1/10^22 := by
  let p : ℝ → ℂ := fun x => taylorPolynomial f 0 256 x
  let ε : ℝ := (10:ℝ)^53*(1/2:ℝ)^256/(1-(1/2:ℝ))
  have hb (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
      ‖f x-p x‖ ≤ ε := by
    apply analytic_taylor_error (by norm_num : (0:ℝ)<2) (by positivity)
      (by norm_num : (0:ℝ)≤1/2) (by norm_num) hf hbound _ 256
    simp only [sub_zero,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hp : Continuous p := by
    unfold p
    simp only [taylorPolynomial_zero]
    fun_prop
  have hc : ContinuousOn (fun x : ℝ => f x) (Icc (-1:ℝ) 1) := by
    apply hf.continuousOn.comp (Complex.continuous_ofReal.continuousOn)
    intro x hx
    apply subset_closure
    rw [Metric.mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs]
    have := abs_le.mpr hx
    linarith
  have hw (v : Fin 256) : 0 ≤ 2*fejerWeight v.val := by
    have := fejerWeight_pos v.val
    positivity
  have hmass : (∑ v : Fin 256, 2*fejerWeight v.val) = (1:ℝ)-(-1) := by
    rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range,fejer_mass]
    norm_num
  have hexact : (∫ x in (-1:ℝ)..1, p x) =
      ∑ v : Fin 256, ((2*fejerWeight v.val:ℝ):ℂ)*p (fejerNode v.val) := by
    have hh : (∑ v ∈ Finset.range 256, (fejerWeight v:ℂ)*p (fejerNode v)) =
        (1/2:ℂ)*(∫ x in (-1:ℝ)..1, p x) := by
      simpa only [p,taylorPolynomial,sub_zero] using
        fejer_exact_complex (fun k => (k.factorial:ℂ)⁻¹*iteratedDeriv k f 0)
    rw [Fin.sum_univ_eq_sum_range (fun v : ℕ => ((2*fejerWeight v:ℝ):ℂ)*p (fejerNode v)) 256]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,mul_assoc,← Finset.mul_sum]
    rw [hh]
    ring
  have he := positive_quadrature_error (-1) 1 (by norm_num)
    (fun v : Fin 256 => 2*fejerWeight v.val) (fun v : Fin 256 => fejerNode v.val)
    (fun x : ℝ => f x) p ε hw (fun v => fejerNode_mem v.val) hmass hc hp.continuousOn hb hexact
  have heq : (1/2:ℂ)*((∫ x in (-1:ℝ)..1, f x)-
      ∑ v : Fin 256, ((2*fejerWeight v.val:ℝ):ℂ)*f (fejerNode v.val)) =
      (1/2:ℂ)*(∫ x in (-1:ℝ)..1, f x)-
        ∑ v : Fin 256, (fejerWeight v.val:ℂ)*f (fejerNode v.val) := by
    simp only [mul_sub,Complex.ofReal_mul,Complex.ofReal_ofNat,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [← heq,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖ = (1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(2*(1-(-1))*ε) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ < 1/10^22 := by norm_num [ε]

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

noncomputable def diskAffine (j : ℕ) (w : ℂ) : ℂ := (diskCenter j:ℂ)+w/12
lemma diskAffine_mem {j : ℕ} {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖diskAffine j w-(diskCenter j:ℂ)‖ ≤ 1/6 := by
  simp only [diskAffine,add_sub_cancel_left,norm_div,Complex.norm_ofNat]
  linarith

lemma finiteDensity_differentiable (c d : ℕ → ℝ) (j : ℕ) :
    Differentiable ℂ (finiteDensity c d j) := by
  unfold finiteDensity complexU complexV
  fun_prop
lemma complexLambda_differentiableAt {t : ℂ} (ht : t+Complex.I*(h:ℂ) ≠ 0) :
    DifferentiableAt ℂ complexLambda t := by
  unfold complexLambda
  fun_prop (disch := exact mul_ne_zero (Complex.ofReal_ne_zero.mpr b_pos.ne') ht)

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def pieceIntegral (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, F t
noncomputable def pieceRule (F : ℂ → ℂ) (j : ℕ) : ℂ :=
  (1/6:ℂ) * ∑ v : Fin 256, (fejerWeight v.val:ℂ) *
    F (diskAffine j (fejerNode v.val))

lemma pieceIntegral_affine (F : ℂ → ℂ) (j : ℕ) :
    pieceIntegral F j = (1/12:ℂ) * ∫ x in (-1:ℝ)..1,
      F (diskAffine j x) := by
  have he := intervalIntegral.smul_integral_comp_add_mul (fun x : ℝ => F x)
    (a := -1) (b := 1) (1/12) (diskCenter j)
  have ha : diskCenter j + (1/12:ℝ)*(-1) = (j:ℝ)/6 := by
    unfold diskCenter; ring
  have hb : diskCenter j + (1/12:ℝ)*1 = ((j:ℝ)+1)/6 := by
    unfold diskCenter; ring
  rw [ha,hb] at he
  have hint : (fun x : ℝ => F (diskAffine j x)) =
      (fun x : ℝ => F ((diskCenter j + (1/12:ℝ)*x : ℝ):ℂ)) := by
    funext x
    congr 1
    simp only [diskAffine,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
    ring
  rw [pieceIntegral,hint,← he]
  simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_ofNat]

lemma piece_rule_error_scaling (F : ℂ → ℂ) (j : ℕ) {ε : ℝ}
    (he : ‖(1/2:ℂ) * (∫ x in (-1:ℝ)..1, F (diskAffine j x)) -
      ∑ v : Fin 256, (fejerWeight v.val:ℂ)*
        F (diskAffine j (fejerNode v.val))‖ < ε) :
    ‖pieceIntegral F j-pieceRule F j‖ < ε/6 := by
  rw [pieceIntegral_affine,pieceRule]
  have hid (a b : ℂ) : (1/12:ℂ)*a-(1/6:ℂ)*b =
      (1/6:ℂ)*((1/2:ℂ)*a-b) := by ring
  rw [hid,norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] at *
  linarith

lemma six_piece_error {F G : Fin 6 → ℂ} {ε : ℝ}
    (he : ∀ j, ‖F j-G j‖ < ε/6) : ‖(∑ j, F j)-(∑ j, G j)‖ < ε := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans_lt ?_
  have hs : ∑ j : Fin 6, ‖F j-G j‖ < ∑ j : Fin 6, ε/6 :=
    Finset.sum_lt_sum (by intro j _; exact (he j).le)
      ⟨0,Finset.mem_univ _,he 0⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  linarith

end SharpPlanar

namespace SharpPlanar
open MeasureTheory

noncomputable def singleCoefficient (n : ℕ) (k : ℕ) : ℝ := if k=n then 1 else 0
lemma singleCoefficient_mass {n : ℕ} (hn : n ≤ 100) :
    ∑ k ∈ Finset.range 101, |singleCoefficient n k| = 1 := by
  simp [singleCoefficient, apply_ite, show n < 101 by omega]
lemma singleDensity_u {n : ℕ} (hn : n ≤ 100) (j : ℕ) (t : ℂ) :
    finiteDensity (singleCoefficient n) (fun _ => 0) j t = complexU n j t := by
  simp [finiteDensity,singleCoefficient,apply_ite,ite_mul,show n < 101 by omega]
lemma singleDensity_v {n : ℕ} (hn : n ≤ 100) (j : ℕ) (t : ℂ) :
    finiteDensity (fun _ => 0) (singleCoefficient n) j t = complexV n j t := by
  simp [finiteDensity,singleCoefficient,apply_ite,ite_mul,show n < 101 by omega]

noncomputable def complexBasis (d : Bool) (n j : ℕ) (t : ℂ) : ℂ :=
  if d then complexV n j t else complexU n j t

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def phase12 (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/6))
lemma phase12_eq_pow (n : ℕ) : phase12 n = phase12 1^n := by
  rw [phase12,phase12,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma phase12_periodic (n : ℕ) : phase12 (n+12) = phase12 n := by
  unfold phase12
  have he : Complex.I*Real.pi*(((n+12:ℕ):ℂ)/6) =
      Complex.I*Real.pi*((n:ℂ)/6)+2*Real.pi*Complex.I := by push_cast; ring
  rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic).map_mod_nat n

noncomputable def spectralCoefficient (n l : ℕ) : ℂ :=
  Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def basisAlpha (n j : ℕ) : ℂ := ∑ l ∈ Finset.Icc (j+1) 6, spectralCoefficient n l
noncomputable def basisBeta (n j : ℕ) : ℂ :=
  ∑ l ∈ Finset.Icc (j+1) 6, ((l:ℂ)/6)*spectralCoefficient n l

lemma sum_seven_Icc (f : ℕ → ℂ) (j : ℕ) :
    (∑ l ∈ Finset.range 7, if j<l then f l else 0) = ∑ l ∈ Finset.Icc (j+1) 6, f l := by
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
  omega

lemma u_factored (n j : ℕ) (t : ℝ) : u n j t =
    -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) := by
  unfold u basisBeta basisAlpha spectralCoefficient
  congr 1
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring
lemma v_factored (n j : ℕ) (t : ℝ) : v n j t =
    2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j := by
  unfold v basisAlpha spectralCoefficient
  rfl

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma spectralCoefficient_eq_phase (n l : ℕ) :
    spectralCoefficient n l = Pcoeff l*phase12 (l*n) := by
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring
lemma spectralCoefficient_mod (n l : ℕ) :
    spectralCoefficient (n%12) l = spectralCoefficient n l := by
  simp only [spectralCoefficient_eq_phase]
  rw [← phase12_mod (l*(n%12)),← phase12_mod (l*n)]
  congr 2
  simp only [Nat.mul_mod, Nat.mod_mod]
lemma basisAlpha_mod (n j : ℕ) : basisAlpha (n%12) j = basisAlpha n j := by
  unfold basisAlpha
  simp only [spectralCoefficient_mod]
lemma basisBeta_mod (n j : ℕ) : basisBeta (n%12) j = basisBeta n j := by
  unfold basisBeta
  simp only [spectralCoefficient_mod]

lemma pointLambda_eq (t : ℝ) : pointLambda t = lambda t := by
  unfold pointLambda lambda b h
  push_cast
  rfl

noncomputable def basisFunction (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then v n j t else u n j t

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma sum_fin_square (N : ℕ) (f : ℕ → ℂ) :
    (∑ i : Fin N, ∑ k : Fin N, f (N*i.val+k.val)) =
      ∑ v : Fin (N*N), f v.val := by
  calc
    _ = ∑ x : Fin N × Fin N, f (N*x.1.val+x.2.val) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      convert (finProdFinEquiv.sum_comp (fun v : Fin (N*N) => f v.val)) using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      exact Nat.add_comm _ _

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerIntervals IntegerBasis

lemma complexU_ofReal (n j : ℕ) (t : ℝ) : complexU n j t = u n j t := rfl
lemma complexV_ofReal (n j : ℕ) (t : ℝ) : complexV n j t = v n j t := rfl
lemma complexLambda_ofReal (t : ℝ) : complexLambda t = lambda t := rfl


end SharpPlanar

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def waveAmplitude (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then 2*Complex.I*Real.pi*basisAlpha n j
  else -2*(Real.pi:ℂ)^2*(basisBeta n j-(t:ℂ)*basisAlpha n j)
lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod,basisBeta_mod]
lemma basisFunction_wave (d : Bool) (n j : ℕ) (t : ℝ) :
    basisFunction d n j t = waveAmplitude d n j t*Complex.exp (-Complex.I*Real.pi*t*n) := by
  cases d <;> simp only [basisFunction,waveAmplitude,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  · rw [u_factored]; ring
  · rw [v_factored]; ring

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

noncomputable def sinTable : ℕ → ℝ
  | 0 => 0 | 1 => 1/2 | 2 => b | 3 => 1 | 4 => b | 5 => 1/2
  | 6 => 0 | 7 => -1/2 | 8 => -b | 9 => -1 | 10 => -b | 11 => -1/2
  | _ => 0
noncomputable def cosTable : ℕ → ℝ
  | 0 => 1 | 1 => b | 2 => 1/2 | 3 => 0 | 4 => -1/2 | 5 => -b
  | 6 => -1 | 7 => -b | 8 => -1/2 | 9 => 0 | 10 => 1/2 | 11 => b
  | _ => 1

lemma trig_table (n : ℕ) (hn : n ≤ 12) :
    Real.sin (Real.pi * n / 6) = sinTable n ∧
    Real.cos (Real.pi * n / 6) = cosTable n := by
  induction n with
  | zero => norm_num [sinTable, cosTable]
  | succ n ih =>
    have hn' : n ≤ 12 := by omega
    obtain ⟨hs, hc⟩ := ih hn'
    rw [show Real.pi * (n+1 : ℕ) / 6 = Real.pi * n / 6 + Real.pi / 6 by push_cast; ring]
    rw [Real.sin_add, Real.cos_add, hs, hc, Real.sin_pi_div_six, Real.cos_pi_div_six]
    change sinTable n * b + cosTable n * (1/2) = sinTable (n+1) ∧
      cosTable n * b - sinTable n * (1/2) = cosTable (n+1)
    have hn11 : n ≤ 11 := by omega
    interval_cases n <;> norm_num [sinTable, cosTable] <;> constructor <;> nlinarith [b_sq]

lemma squared_sine_to_cos (x : ℝ) : (2 * Real.sin x)^2 = 2 - 2*Real.cos (2*x) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma divided_cos_to_double (x : ℝ) :
    Real.cos x / Real.sin x = Real.sin (2*x) / (1 - Real.cos (2*x)) := by
  by_cases hs : Real.sin x = 0
  · simp [Real.sin_two_mul, hs]
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have he : 1 - (2 * Real.cos x ^ 2 - 1) = 2 * Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [he]
  field_simp

lemma Q_as_table (n : ℕ) : Q n =
    (Real.pi/6)^2 * ∏ a ∈ residues.erase (n % 12),
      (2 - 2*(cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a)) := by
  unfold Q
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [squared_sine_to_cos,
    show 2 * (Real.pi * (((n%12 : ℕ):ℝ)-a)/12) =
      Real.pi*(n%12 : ℕ)/6 - Real.pi*a/6 by ring, Real.cos_sub]
  rw [(trig_table (n%12) (by omega)).1, (trig_table (n%12) (by omega)).2,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).1,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).2]


lemma D_as_table (n : ℕ) : D n = (Real.pi/6) *
    ∑ a ∈ residues.erase (n%12),
      (sinTable (n%12)*cosTable a - cosTable (n%12)*sinTable a) /
        (1 - (cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a)) := by
  unfold D
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [divided_cos_to_double,
    show 2 * (Real.pi * (((n%12 : ℕ):ℝ)-a)/12) =
      Real.pi*(n%12 : ℕ)/6 - Real.pi*a/6 by ring, Real.sin_sub, Real.cos_sub]
  rw [(trig_table (n%12) (by omega)).1, (trig_table (n%12) (by omega)).2,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).1,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).2]

lemma b_lt_one : b < 1 := by nlinarith [b_sq, b_pos]
lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1

lemma Q_0 : Q 0 = Real.pi^2/3 := by
  rw [Q_as_table, show 0 % 12 = 0 from rfl,
    show residues.erase 0 = {1, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  ring

lemma Q_1 : Q 1 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table, show 1 % 12 = 1 from rfl,
    show residues.erase 1 = {0, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq, b_pow_3]
  ring

lemma Q_3 : Q 3 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table, show 3 % 12 = 3 from rfl,
    show residues.erase 3 = {0, 1, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

lemma Q_4 : Q 4 = Real.pi^2/3 := by
  rw [Q_as_table, show 4 % 12 = 4 from rfl,
    show residues.erase 4 = {0, 1, 3, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  ring

lemma Q_7 : Q 7 = (2*Real.pi^2/3)*(2+2*b) := by
  rw [Q_as_table, show 7 % 12 = 7 from rfl,
    show residues.erase 7 = {0, 1, 3, 4, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq, b_pow_3]
  ring

lemma Q_9 : Q 9 = (2*Real.pi^2/3)*(2+2*b) := by
  rw [Q_as_table, show 9 % 12 = 9 from rfl,
    show residues.erase 9 = {0, 1, 3, 4, 7} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

lemma one_sub_b_ne : 1 - b ≠ 0 := by linarith [b_lt_one]
lemma one_add_b_ne : 1 + b ≠ 0 := by linarith [b_pos]

lemma D_0 : D 0 = -7 * Real.pi * b / 9 := by
  rw [D_as_table, show 0 % 12 = 0 from rfl,
    show residues.erase 0 = {1, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_pow_3]
  ring

lemma D_1 : D 1 = Real.pi * (3+2*b) / 18 := by
  rw [D_as_table, show 1 % 12 = 1 from rfl,
    show residues.erase 1 = {0, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

lemma D_3 : D 3 = -Real.pi * (3+2*b) / 18 := by
  rw [D_as_table, show 3 % 12 = 3 from rfl,
    show residues.erase 3 = {0, 1, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

lemma D_4 : D 4 = 7 * Real.pi * b / 9 := by
  rw [D_as_table, show 4 % 12 = 4 from rfl,
    show residues.erase 4 = {0, 1, 3, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_pow_3]
  ring

lemma D_7 : D 7 = -Real.pi * (3-2*b) / 18 := by
  rw [D_as_table, show 7 % 12 = 7 from rfl,
    show residues.erase 7 = {0, 1, 3, 4, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

lemma D_9 : D 9 = Real.pi * (3-2*b) / 18 := by
  rw [D_as_table, show 9 % 12 = 9 from rfl,
    show residues.erase 9 = {0, 1, 3, 4, 7} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


noncomputable def lambdaCap : Fin 7 → ℝ := ![2887/1000,2665/1000,2218/1000,1804/1000,1486/1000,1250/1000,1073/1000]
noncomputable def dampingCap : Fin 7 → ℝ := ![2933/1000,2440/1000,1567/1000,900/1000,482/1000,224/1000,597/10000]
noncomputable def slopeCap : Fin 6 → ℝ := ![0,48/10,317/100,1946/1000,1217/1000,792/1000]

end SharpPlanar

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def densityDen : Fin 6 → ℤ := ![1,1,1,1,1,250]

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerBasis

noncomputable def pieceMass (j : Fin 6) (s : ℝ) : ℝ :=
  if slopeCap j*s=0 then 1/6 else min (1/6) (1/(Real.pi*slopeCap j*s))
noncomputable def pieceL (j : Fin 6) (s : ℝ) : ℝ :=
  lambdaCap ⟨j.val,by omega⟩*Real.exp (-Real.pi*dampingCap ⟨j.val+1,by omega⟩*s)*pieceMass j s

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def rowTailNorm (x : X) (N : ℕ) : ℝ :=
  ∑' n : {n : Node // N<n.val}, (|x (n.val,false)|+|x (n.val,true)|)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

open scoped BigOperators
namespace SharpPlanar


noncomputable def tableRaw : ℕ → ℤ × ℤ × ℤ × ℤ
  | 1 => (-670689128, -6398628799, -250018302, 4107732082)
  | 3 => (93524468, 564897270, -186215974, -65204793)
  | 4 => (-64146977, 121133118, 82882809, -327822296)
  | 7 => (-1358193, -16329465, 1979670, 21637038)
  | 9 => (-2932910, -940875, 3636920, 2145806)
  | 12 => (3646952, -34846939, -6005382, 34369042)
  | 13 => (3183411, 63030995, -574123, -75237042)
  | 15 => (11390977, 27049982, -11312377, -34985096)
  | 16 => (-5593246, 13405071, 5915710, -10980954)
  | 19 => (54905, -1515007, -120136, 1498351)
  | 21 => (-210208, -634307, 177992, 747946)
  | 24 => (976077, -804949, -1037705, 105643)
  | 25 => (-824472, 7003719, 1011732, -6510015)
  | 27 => (611891, 4536095, -428528, -4440927)
  | 28 => (-472882, -107613, 399655, 403751)
  | 31 => (30744, -112653, -31773, 90515)
  | 33 => (-4974, -105568, 1240, 99081)
  | 36 => (128313, 246018, -114876, -267388)
  | 37 => (-176685, 505187, 166591, -396209)
  | 39 => (-21638, 472037, 32128, -402283)
  | 40 => (-18461, -165597, 10836, 164974)
  | 43 => (4565, -2296, -4050, 547)
  | 45 => (1477, -10734, -1524, 8978)
  | 48 => (10748, 50050, -8611, -45048)
  | 49 => (-20506, 7495, 17354, -266)
  | 51 => (-10361, 29035, 9641, -21534)
  | 52 => (2121, -26523, -2269, 23159)
  | 55 => (425, 858, -344, -839)
  | 57 => (302, -632, -266, 463)
  | 60 => (382, 5658, -231, -4688)
  | 61 => (-1481, -4320, 1140, 4098)
  | 63 => (-1494, -352, 1265, 647)
  | 64 => (558, -2609, -491, 2114)
  | 67 => (21, 169, -14, -145)
  | 69 => (34, 13, -28, -18)
  | 72 => (-55, 394, 53, -301)
  | 73 => (-21, -805, 5, 685)
  | 75 => (-136, -379, 108, 338)
  | 76 => (70, -144, -58, 104)
  | 79 => (-1, 19, 1, -15)
  | 81 => (2, 9, -2, -8)
  | 84 => (-13, 3, 11, 0)
  | 85 => (13, -87, -11, 70)
  | 87 => (-6, -60, 4, 49)
  | 88 => (6, 5, -4, -5)
  | 91 => (0, 1, 0, -1)
  | 93 => (0, 1, 0, -1)
  | 96 => (-2, -4, 1, 3)
  | 97 => (2, -6, -2, 4)
  | 99 => (0, -6, 0, 5)
  | 100 => (0, 2, 0, -2)
  | _ => (0,0,0,0)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourier quadrature grid

Certified rational enclosures for the quadrature points and their Fourier
kernels on each of the six subintervals.
-/

namespace SharpPlanar.IntegerGrid
open IntegerIntervals
noncomputable def quadraturePoint (j v : ℕ) : ℝ := (2*(j:ℝ)+1)/12+fejerNode v/12
end SharpPlanar.IntegerGrid

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

def node1 : Node := ⟨1,by norm_num [residues]⟩
def node3 : Node := ⟨3,by norm_num [residues]⟩
def node4 : Node := ⟨4,by norm_num [residues]⟩
def jNode : Fin 6 → Node := ![node1,node3,node4,node1,node3,node4]
def jDeriv : Fin 6 → Bool := ![false,false,false,true,true,true]
def node12 : Node := ⟨12,by norm_num [residues]⟩
open scoped BigOperators
def eNode : Fin 48 → Node := ![⟨7,by norm_num [residues]⟩,⟨9,by norm_num [residues]⟩,⟨12,by norm_num [residues]⟩,⟨13,by norm_num [residues]⟩,⟨15,by norm_num [residues]⟩,⟨16,by norm_num [residues]⟩,⟨19,by norm_num [residues]⟩,⟨21,by norm_num [residues]⟩,⟨24,by norm_num [residues]⟩,⟨25,by norm_num [residues]⟩,⟨27,by norm_num [residues]⟩,⟨28,by norm_num [residues]⟩,⟨31,by norm_num [residues]⟩,⟨33,by norm_num [residues]⟩,⟨36,by norm_num [residues]⟩,⟨37,by norm_num [residues]⟩,⟨39,by norm_num [residues]⟩,⟨40,by norm_num [residues]⟩,⟨43,by norm_num [residues]⟩,⟨45,by norm_num [residues]⟩,⟨48,by norm_num [residues]⟩,⟨49,by norm_num [residues]⟩,⟨51,by norm_num [residues]⟩,⟨52,by norm_num [residues]⟩,⟨55,by norm_num [residues]⟩,⟨57,by norm_num [residues]⟩,⟨60,by norm_num [residues]⟩,⟨61,by norm_num [residues]⟩,⟨63,by norm_num [residues]⟩,⟨64,by norm_num [residues]⟩,⟨67,by norm_num [residues]⟩,⟨69,by norm_num [residues]⟩,⟨72,by norm_num [residues]⟩,⟨73,by norm_num [residues]⟩,⟨75,by norm_num [residues]⟩,⟨76,by norm_num [residues]⟩,⟨79,by norm_num [residues]⟩,⟨81,by norm_num [residues]⟩,⟨84,by norm_num [residues]⟩,⟨85,by norm_num [residues]⟩,⟨87,by norm_num [residues]⟩,⟨88,by norm_num [residues]⟩,⟨91,by norm_num [residues]⟩,⟨93,by norm_num [residues]⟩,⟨96,by norm_num [residues]⟩,⟨97,by norm_num [residues]⟩,⟨99,by norm_num [residues]⟩,⟨100,by norm_num [residues]⟩]
def centralIndex (i : Fin 6) : Node × Bool := (jNode i,jDeriv i)
def exteriorIndex (i : Fin 48 × Fin 2) : Node × Bool := (eNode i.1,decide (i.2.val=1))
abbrev FiniteIndex := Fin 6 ⊕ (Fin 48 × Fin 2)
def finiteIndex : FiniteIndex → Node × Bool := Sum.elim centralIndex exteriorIndex
lemma centralIndex_injective : Function.Injective centralIndex := by decide +kernel
lemma exteriorIndex_injective : Function.Injective exteriorIndex := by decide +kernel
lemma finiteIndex_injective : Function.Injective finiteIndex := by decide +kernel
lemma exteriorIndex_bound (i : Fin 48 × Fin 2) : 4 < (exteriorIndex i).1.val ∧ (exteriorIndex i).1.val ≤ 100 := by revert i; decide +kernel
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


noncomputable def columnVector (n : Node) (d : Bool) : X := lp.single 1 (n,d) 1

lemma density_column (n : Node) (d : Bool) (j : ℕ) (t : ℝ) :
    density (positiveData (columnVector n d)) j t = basisFunction d n.val j t := by
  classical
  unfold density positiveData columnVector
  simp only [Complex.ofReal_zero, zero_mul, zero_add]
  rw [tsum_eq_single n]
  · cases d <;> simp [basisFunction,lp.single_apply]
  · intro k hk
    have hf : (k,false) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    have ht : (k,true) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    simp [Pi.single_eq_of_ne hf,Pi.single_eq_of_ne ht]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical
open IntegerIntervals
open scoped BigOperators
noncomputable def WplusInt : Matrix (Fin 6) (Fin 6) ℤ := ![![4159,4452,(-2003),(-10467),(-2421),(-1683)],
![2714,6573,1689,8258,104,(-335)],
![(-4675),4785,7003,(-13100),(-1355),(-1163)],
![36853,(-37142),27514,105973,1100,2012],
![57838,(-56941),36296,158623,29097,17293],
![(-4705),3589,(-3311),(-11932),(-2562),6919]]
noncomputable def Wplus : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (WplusInt i j:ℝ)/10000
noncomputable def WminusInt : Matrix (Fin 6) (Fin 6) ℤ := ![![13265,(-1358),(-385),(-381),815,(-164)],
![616,10426,686,(-484),182,775],
![(-146),4,9842,215,267,179],
![(-2761),2483,(-958),5174,(-328),206],
![(-615),(-861),730,(-1388),5619,(-4370)],
![874,820,1148,(-431),905,11927]]
noncomputable def Wminus : Matrix (Fin 6) (Fin 6) ℝ := fun i j => (WminusInt i j:ℝ)/10000
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_WUCert100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Numerical.U100
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def node : Node := ⟨100,by norm_num [residues]⟩
end SharpPlanar.Numerical.U100

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar

noncomputable def spectral (μ : Measure ℝ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ t, Complex.exp (((Real.pi*t*s : ℝ) : ℂ)*Complex.I) * f t ∂μ

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

namespace SharpPlanar


noncomputable def cardinal (p : CardinalData) (s : ℝ) : ℝ :=
  ((spectral (Measure.dirac 0) (fun _ => (p.C : ℂ) * Pcoeff 0) s) +
    (∑ j ∈ Finset.Icc (1 : ℕ) 6,
      spectral (Measure.dirac ((j : ℝ)/6)) (fun _ => 2*(p.C : ℂ)*Pcoeff j) s) +
    (∑ j ∈ Finset.range 6,
      spectral (volume.restrict (Set.Icc ((j : ℝ)/6) (((j : ℝ)+1)/6)))
        (density p j) s)).re

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
abbrev L1Finite (ι : Type*) := PiLp 1 (fun _ : ι => ℝ)

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

noncomputable def matrixL1 (A : Matrix ι κ ℝ) : L1Finite κ →L[ℝ] L1Finite ι :=
  (Matrix.toLpLin 1 1 A).toContinuousLinearMap
omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl
omit [DecidableEq ι] in
lemma l1Finite_norm (x : L1Finite ι) : ‖x‖ = ∑ i, |x i| := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_eq_of_L1 x

omit [DecidableEq ι] in
lemma matrixL1_mul (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixL1 (A*B) = (matrixL1 A).comp (matrixL1 B) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLpLin 1 1 (A*B) x = Matrix.toLpLin 1 1 A (Matrix.toLpLin 1 1 B x)
  rw [Matrix.toLpLin_mul (q:=1)]
  rfl
omit [DecidableEq ι] in
lemma matrixL1_sub (A B : Matrix ι κ ℝ) :
    matrixL1 (A-B) = matrixL1 A-matrixL1 B := by
  ext x i
  simp [matrixL1_apply,sub_mul,Finset.sum_sub_distrib]
lemma matrixL1_one : matrixL1 (1:Matrix ι ι ℝ) = 1 := by
  ext x i
  simp [matrixL1_apply,Matrix.one_apply]

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm,l1Finite_norm,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma approximate_inverse_bijective (A W : E →L[ℝ] E) (h : ‖1-W*A‖ < 1) :
    Function.Bijective A := by
  have hu : IsUnit (W*A) := by
    convert isUnit_one_sub_of_norm_lt_one h using 1
    all_goals try with_reducible_and_instances rfl
    abel
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).injective
  have hai : Function.Injective A := by
    intro x y hxy
    apply hi
    change W (A x) = W (A y)
    rw [hxy]
  exact ⟨hai,LinearMap.injective_iff_surjective.mp hai⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma approximate_inverse_estimate (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) (x : E) :
    ‖x‖ ≤ ‖W (A x)‖/(1-δ) := by
  have he : x = W (A x)+(1-W*A) x := by simp
  have hx : ‖x‖ ≤ ‖W (A x)‖+δ*‖x‖ := calc
    _ = ‖W (A x)+(1-W*A) x‖ := congrArg norm he
    _ ≤ ‖W (A x)‖+‖(1-W*A) x‖ := norm_add_le _ _
    _ ≤ ‖W (A x)‖+δ*‖x‖ := add_le_add le_rfl ((1-W*A).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _)))
  apply (le_div_iff₀ (by linarith : 0 < 1-δ)).mpr
  nlinarith
end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ENNReal
namespace SharpPlanar
lemma X_norm_scalar (x : X) : ‖x‖ = ∑' i : Node × Bool, |x i| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one,Real.rpow_one,one_div_one,Real.norm_eq_abs]
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
noncomputable def finiteRestrictionLinear : X →ₗ[ℝ] L1Finite ι where
  toFun x := WithLp.toLp 1 (fun i => x (e i))
  map_add' := by intro x y; ext i; rfl
  map_smul' := by intro r x; ext i; rfl
include he in
lemma finiteRestriction_bound (x : X) : ‖finiteRestrictionLinear e x‖ ≤ 1*‖x‖ := by
  rw [l1Finite_norm,X_norm_scalar,one_mul]
  change (∑ i, |x (e i)|) ≤ _
  simpa only [tsum_fintype, Function.comp_apply] using tsum_comp_le_tsum_of_inj (X_summable x) (fun _ => abs_nonneg _) he
noncomputable def finiteRestriction : X →L[ℝ] L1Finite ι :=
  (finiteRestrictionLinear e).mkContinuous 1 (finiteRestriction_bound e he)
lemma finiteRestriction_apply (x : X) (i : ι) : finiteRestriction e he x i = x (e i) := rfl
noncomputable def finiteEmbeddingLinear : L1Finite ι →ₗ[ℝ] X where
  toFun x := ∑ i, lp.single 1 (e i) (x i)
  map_add' := by intro x y; simp only [PiLp.add_apply,lp.single_add,Finset.sum_add_distrib]
  map_smul' := by intro r x; simp only [PiLp.smul_apply,lp.single_smul,Finset.smul_sum]; rfl
lemma finiteEmbedding_bound (x : L1Finite ι) : ‖finiteEmbeddingLinear e x‖ ≤ 1*‖x‖ := by
  rw [one_mul,l1Finite_norm]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by simp [lp.norm_single]))
noncomputable def finiteEmbedding : L1Finite ι →L[ℝ] X :=
  (finiteEmbeddingLinear e).mkContinuous 1 (finiteEmbedding_bound e)
lemma finiteEmbedding_apply (x : L1Finite ι) (i : Node × Bool) :
    finiteEmbedding e x i = ∑ j, if e j=i then x j else 0 := by
  change (∑ j, lp.single 1 (e j) (x j) : X) i = _
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply, eq_comm]
lemma finiteRestriction_embedding (x : L1Finite ι) :
    finiteRestriction e he (finiteEmbedding e x) = x := by
  classical
  ext i
  rw [finiteRestriction_apply,finiteEmbedding_apply]
  simp only [he.eq_iff]
  simp
include he in
lemma finiteEmbedding_norm (x : L1Finite ι) : ‖finiteEmbedding e x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (finiteEmbedding_bound e x).trans_eq (one_mul _)
  · have hh := finiteRestriction_bound e he (finiteEmbedding e x)
    change ‖finiteRestriction e he (finiteEmbedding e x)‖ ≤ _ at hh
    simpa only [finiteRestriction_embedding,one_mul] using hh
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite coordinate projections

Restriction and extension identify the first shell coordinates with a finite
subspace of the absolutely summable interpolation space.
-/

namespace SharpPlanar.Numerical
open scoped BigOperators
noncomputable abbrev RJ := finiteRestriction centralIndex centralIndex_injective
noncomputable abbrev IJ := finiteEmbedding centralIndex
noncomputable abbrev RE := finiteRestriction exteriorIndex exteriorIndex_injective
noncomputable abbrev IE := finiteEmbedding exteriorIndex
noncomputable abbrev RF := finiteRestriction finiteIndex finiteIndex_injective
noncomputable abbrev IF := finiteEmbedding finiteIndex
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite decompositions of ℓ¹ coordinates

The central and exterior coordinate blocks give an additive decomposition of the ℓ¹ norm.
-/

namespace SharpPlanar
open scoped BigOperators
section
variable {ι κ : Type*}
noncomputable def l1Left (x : L1Finite (ι ⊕ κ)) : L1Finite ι :=
  WithLp.toLp 1 (fun i => x (Sum.inl i))
noncomputable def l1Right (x : L1Finite (ι ⊕ κ)) : L1Finite κ :=
  WithLp.toLp 1 (fun i => x (Sum.inr i))
end
end SharpPlanar
namespace SharpPlanar.Numerical
lemma finiteEmbedding_split (x : L1Finite FiniteIndex) :
    finiteEmbedding finiteIndex x = finiteEmbedding centralIndex (l1Left x) +
      finiteEmbedding exteriorIndex (l1Right x) := by
  ext k
  change finiteEmbedding finiteIndex x k = finiteEmbedding centralIndex (l1Left x) k + finiteEmbedding exteriorIndex (l1Right x) k
  simp only [finiteEmbedding_apply]
  change (∑ j, if finiteIndex j=k then x j else 0) =
    (∑ j, if centralIndex j=k then l1Left x j else 0)+
    (∑ j, if exteriorIndex j=k then l1Right x j else 0)
  rw [Fintype.sum_sum_type]
  rfl
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar
open scoped BigOperators
noncomputable def tailScalar (x : X) (N : ℕ) : ℝ :=
  ∑' k : Node × Bool, if N<k.1.val then |x k| else 0
lemma tailScalar_summable (x : X) (N : ℕ) :
    Summable (fun k : Node × Bool => if N<k.1.val then |x k| else 0) := by
  apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) _ (X_summable x)
  intro k
  split_ifs <;> simp [abs_nonneg]
lemma tailScalar_eq (x : X) (N : ℕ) : tailScalar x N = rowTailNorm x N := by
  unfold tailScalar rowTailNorm
  rw [(tailScalar_summable x N).tsum_prod]
  change _ = ∑' n : {n : Node // n ∈ {n : Node | N<n.val}}, (fun n : Node => |x (n,false)|+|x (n,true)|) n.val
  rw [tsum_subtype {n : Node | N<n.val} (fun n : Node => |x (n,false)|+|x (n,true)|)]
  apply tsum_congr
  intro n
  simp only [tsum_fintype, Fintype.sum_bool, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp [add_comm]
section
variable {ι : Type*} [Fintype ι]
  (e : ι → Node × Bool) (he : Function.Injective e)
lemma finiteRestriction_tail (N : ℕ) (hN : ∀ i, N<(e i).1.val) (x : X) :
    ‖finiteRestriction e he x‖ ≤ rowTailNorm x N := by
  rw [l1Finite_norm,← tailScalar_eq]
  have hh := tsum_comp_le_tsum_of_inj (tailScalar_summable x N)
    (fun k => by split_ifs <;> positivity) he
  simpa only [Function.comp_apply, hN, ite_true, if_true, tsum_fintype,finiteRestriction_apply,tailScalar] using hh
end
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
noncomputable def hexPoint (v : ℤ×ℤ) : Plane :=
  WithLp.toLp 2 ![((v.1:ℝ)+(v.2:ℝ)/2)/Real.sqrt b, Real.sqrt b*(v.2:ℝ)]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticeGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def latticePoint (p : ℤ×ℤ) : Plane := hexPoint (p.2,p.1)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_LatticePoisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
structure HasLatticePoisson (f : Plane→ℂ) : Prop where
  integrable : Integrable f
  summable : Summable (fun p : ℤ×ℤ => f (latticePoint p))
  fourier_summable : Summable (fun p : ℤ×ℤ => 𝓕 f (latticePoint p))
  eq : (∑' p : ℤ×ℤ, f (latticePoint p))=∑' p : ℤ×ℤ, 𝓕 f (latticePoint p)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Inverse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def certifiedEquiv (A W : E →L[ℝ] E) (h : ‖1-W*A‖ < 1) : E ≃L[ℝ] E :=
  (LinearEquiv.ofBijective A.toLinearMap (approximate_inverse_bijective A W h)).toContinuousLinearEquiv

lemma certified_inverse_norm_le (A W : E →L[ℝ] E) {δ : ℝ}
    (hd : δ < 1) (h : ‖1-W*A‖ ≤ δ) :
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm.toContinuousLinearMap‖ ≤ ‖W‖/(1-δ) := by
  have hd0 : 0 < 1-δ := sub_pos.mpr hd
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hd0.le)
  intro x
  have he : A ((certifiedEquiv A W (h.trans_lt hd)).symm x) = x :=
    (certifiedEquiv A W (h.trans_lt hd)).apply_symm_apply x
  calc
    ‖(certifiedEquiv A W (h.trans_lt hd)).symm x‖ ≤
        ‖W (A ((certifiedEquiv A W (h.trans_lt hd)).symm x))‖/(1-δ) :=
      approximate_inverse_estimate A W hd h _
    _ = ‖W x‖/(1-δ) := by rw [he]
    _ ≤ (‖W‖*‖x‖)/(1-δ) := div_le_div_of_nonneg_right (W.le_opNorm x) hd0.le
    _ = (‖W‖/(1-δ))*‖x‖ := by ring

end Inverse
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

noncomputable def tableNum (i d : Bool) (n : ℕ) : ℤ :=
  if n=0 then (if d then (if i then -3680000000 else 4400000000) else (if i then 0 else 10000000000))
  else if d then (if i then (tableRaw n).2.2.2 else (tableRaw n).2.1)
    else (if i then (tableRaw n).2.2.1 else (tableRaw n).1)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
abbrev HeadNodeIndex := Option (Fin 21)
end SharpPlanar

end OAI
end


