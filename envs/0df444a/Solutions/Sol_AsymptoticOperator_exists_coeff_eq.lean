-- Prove2me | solution 1 for AsymptoticOperator.exists_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T12:12:46.468005+00:00
-- url     : https://prove2.me/submissions/ed6ead43-b01d-4119-9052-66687e0e3439

import Definitions.Def_AsymptoticOperator_Setting
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator ComplexConjugate

lemma ao2s_coeff_apply {n : ℕ} (f : L2 n) (k : ℤ) (i : Fin n ⊕ Fin n) :
    coeff f k i = fourierCoeff (fun t => ((f t i : ℝ) : ℂ)) k := by
  let L : Vec n →L[ℝ] (Fin n ⊕ Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hint : Integrable (fun t => complexify (f t)) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    L.integrable_comp ((Lp.memLp f).integrable one_le_two)
  exact eval_integral (integrable_pi_iff.1 (hint.fourier_smul (-k))) i

lemma ao2s_fourierCoeff_re (G : Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle)) (k : ℤ) :
    fourierCoeff (fun t => (((G t).re : ℝ) : ℂ)) k =
      (fourierCoeff G k + conj (fourierCoeff G (-k))) / 2 := by
  have hG : Integrable (G : UnitAddCircle → ℂ) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (Lp.memLp G).integrable one_le_two
  have ha := hG.fourier_smul (-k)
  have hb := hG.fourier_smul (-(-k))
  have hb' : Integrable (fun t => conj (fourier (-(-k)) t • G t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hb
  simp only [fourierCoeff]
  rw [← integral_conj, ← integral_add ha hb', ← integral_div]
  congr 1
  funext t
  rw [Complex.re_eq_add_conj, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul,
    fourier_neg (n := -k), Complex.conj_conj]
  ring

theorem solution {n : ℕ} (c : ℤ → Fin n ⊕ Fin n → ℂ)
    (hsum : Summable fun k : ℤ => ∑ i, ‖c k i‖ ^ 2)
    (hconj : ∀ k i, c (-k) i = (starRingEnd ℂ) (c k i)) :
    ∃ h : L2 n, ∀ k : ℤ, coeff h k = c k := by
  have hmem : ∀ i, Memℓp (fun k => c k i) 2 := by
    intro i
    rw [memℓp_gen_iff (by norm_num)]
    have : (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) := by norm_num
    simp only [this, Real.rpow_natCast]
    exact Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => Finset.single_le_sum (f := fun j => ‖c k j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i)) hsum
  let F : Fin n ⊕ Fin n → Lp ℂ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    fun i => fourierBasis.repr.symm ⟨fun k => c k i, hmem i⟩
  have hF : ∀ i k, fourierCoeff (F i : UnitAddCircle → ℂ) k = c k i := by
    intro i k
    rw [← fourierBasis_repr]
    simp [F]
  let φ : UnitAddCircle → Vec n := fun t => WithLp.toLp 2 (fun i => (F i t).re)
  have hφ : MemLp φ 2 (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    MemLp.of_eval_piLp fun i => (Lp.memLp (F i)).re
  refine ⟨hφ.toLp φ, fun k => ?_⟩
  funext j
  rw [ao2s_coeff_apply]
  have hae : (fun t => (((hφ.toLp φ : L2 n) t j : ℝ) : ℂ))
      =ᵐ[(AddCircle.haarAddCircle : Measure UnitAddCircle)] fun t => (((F j t).re : ℝ) : ℂ) := by
    filter_upwards [hφ.coeFn_toLp] with t ht
    rw [ht]
  rw [fourierCoeff_congr_ae hae, ao2s_fourierCoeff_re, hF, hF, hconj, Complex.conj_conj]
  ring
