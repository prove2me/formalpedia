-- Prove2me | solution 1 for AsymptoticOperator.coeff_neg
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T22:50:13.317983+00:00
-- url     : https://prove2.me/submissions/e51eb9a6-2295-497b-bd6a-0e54b0f799ea

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao9_cx_int {n : ℕ} (f : L2 n) :
    Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i) :
    Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ)).integrable_comp ((Lp.memLp f).integrable one_le_two)

lemma ao9_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k :=
  eval_integral (integrable_pi_iff.1 ((ao9_cx_int f).fourier_smul (-k))) i

theorem solution {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f (-k) i = (starRingEnd ℂ) (coeff f k i) := by
  rw [ao9_coeff_apply, ao9_coeff_apply]
  simp only [fourierCoeff]
  rw [← integral_conj]
  congr 1
  funext t
  rw [smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal, neg_neg, fourier_neg,
    Complex.conj_conj]
