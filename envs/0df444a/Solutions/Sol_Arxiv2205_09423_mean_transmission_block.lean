-- Prove2me | solution 1 for Arxiv2205_09423.mean_transmission_block
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T01:58:01.176336+00:00
-- url     : https://prove2.me/submissions/33eb902a-c676-4311-951f-c5aa7aae4819

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix
open Arxiv2205_09423

namespace S75MT
variable {Nk : ℕ}

lemma meas_amp (uo ui : Fin 3 → ℝ) (a b : Fin 3) : Measurable (fun X : Amp => X uo ui a b) :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp
    ((measurable_pi_apply ui).comp (measurable_pi_apply uo)))

lemma meas_ampRed (K : ModeSet Nk) (vin vout : Fin (2 * Nk + 1) → Fin 3 → ℝ)
    (j i : Fin (2 * Nk + 1)) (b a : Fin 2) :
    Measurable (fun X : Amp => ampRed K X vin vout j i b a) := by
  unfold ampRed reduce
  simp only [Matrix.of_apply]
  refine Finset.measurable_sum _ fun a' _ => Finset.measurable_sum _ fun b' _ => ?_
  exact (measurable_const.mul (meas_amp _ _ a' b')).mul measurable_const

lemma int_ampRed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : ModeSet Nk) (vin vout : Fin (2 * Nk + 1) → Fin 3 → ℝ)
    (j i : Fin (2 * Nk + 1)) (b a : Fin 2) (A : Ω → Amp)
    (hm : ∀ uo ui a b, MemLp (fun ω => A ω uo ui a b) 2 P) :
    Integrable (fun ω => ampRed K (A ω) vin vout j i b a) P := by
  unfold ampRed reduce
  simp only [Matrix.of_apply]
  refine integrable_finsetSum _ fun a' _ => integrable_finsetSum _ fun b' _ => ?_
  exact (((hm _ _ a' b').integrable one_le_two).const_mul _).mul_const _

end S75MT

open S75MT in
theorem solution {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) (hE : IsSlabEnsemble K dL n P r A)
    (p0 : Fin N)
    (j i : Fin (2 * Nk + 1)) (b a : Fin 2) :
    ∫ ω, tbar K (fun p => A p ω) (fun p => r p ω) j i b a ∂P =
      if i = j then
        (1 : Matrix (Fin 2) (Fin 2) ℂ) b a +
          ((2 * Real.pi * n * dL / (K.k * K.kz i) : ℝ) : ℂ) *
            ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a ∂P
      else 0 := by
  obtain ⟨hprob, hdL, hn, hrm, hAm, -, hrA, hid, hmem, hzind, -, hphase⟩ := hE
  obtain ⟨hk, hmode, -, hinj, hw⟩ := hK
  have hkz : ∀ i, 0 < K.kz i := fun i => Real.sqrt_pos.2 (by linarith [hmode i])
  have hw0 : 0 < K.w := by rw [hw]; have := hk; positivity
  set c : Fin 3 → ℝ := K.kvec i - K.kvec j with hc
  set X : Fin N → Ω → ℂ := fun p ω =>
    Complex.exp (Complex.I * ((dotProduct c (r p ω) : ℝ) : ℂ)) with hX
  set Y : Fin N → Ω → ℂ := fun p ω => ampRed K (A p ω) K.kvec K.kvec j i b a with hY
  have hent : ∀ ω, tbar K (fun p => A p ω) (fun p => r p ω) j i b a =
      (if i = j then (1 : Matrix (Fin 2) (Fin 2) ℂ) else 0) b a +
        ((K.cji j i : ℝ) : ℂ) * ∑ p, X p ω * Y p ω := by
    intro ω
    simp only [tbar, blockSum, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
      smul_eq_mul, X, Y, hc]
  have hphi : Continuous fun v : Fin 3 → ℝ =>
      Complex.exp (Complex.I * ((dotProduct c v : ℝ) : ℂ)) := by
    simp only [dotProduct, Fin.sum_univ_three]; fun_prop
  have hXm : ∀ p, Measurable (X p) := fun p => hphi.measurable.comp (hrm p)
  have hXb : ∀ p ω, ‖X p ω‖ = 1 := by
    intro p ω; simp only [X]; rw [Complex.norm_exp]; simp
  have hYi : ∀ p, Integrable (Y p) P := fun p =>
    int_ampRed P K K.kvec K.kvec j i b a (A p) (hmem p)
  have hXYi : ∀ p, Integrable (fun ω => X p ω * Y p ω) P := fun p =>
    (hYi p).bdd_mul (hXm p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => (hXb p ω).le)
  simp_rw [hent]
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun p _ => hXYi p).const_mul _),
    integral_const, integral_const_mul, integral_finsetSum _ fun p _ => hXYi p]
  simp only [probReal_univ, one_smul]
  have hNz : (N : ℂ) ≠ 0 := by
    have : 0 < N := Fin.pos p0
    exact_mod_cast this.ne'
  by_cases hij : i = j
  · subst hij
    have hc0 : c = 0 := by rw [hc, sub_self]
    have hX1 : ∀ p ω, X p ω = 1 := by intro p ω; simp [X, hc0]
    simp only [hX1, one_mul, if_true]
    have hYe : ∀ p, ∫ ω, Y p ω ∂P = ∫ ω, Y p0 ω ∂P := fun p =>
      ((hid p p0).comp (meas_ampRed K K.kvec K.kvec i i b a)).integral_eq
    simp only [hYe, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN := hphase p0 i i i i
    simp only [sub_self, zero_mul, add_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, integral_const, probReal_univ, one_smul, mul_one, and_self, if_true,
      sub_add_cancel] at hN
    congr 1
    rw [← mul_assoc, hN, ← Complex.ofReal_mul]
    congr 2
    unfold ModeSet.cji
    rw [Real.sqrt_mul_self (hkz i).le]
    have := Real.pi_pos
    have := hkz i
    field_simp
  · rw [if_neg hij, if_neg hij]
    have hXi : ∀ p, ∫ ω, X p ω ∂P = 0 := by
      intro p
      have hsplit : ∀ ω, X p ω =
          Complex.exp (Complex.I * ((((K.kx i - K.kx j) * r p ω 0 +
            (K.ky i - K.ky j) * r p ω 1 : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((((K.kz i - K.kz j) * r p ω 2 : ℝ)) : ℂ)) := by
        intro ω
        simp only [X, hc, ← Complex.exp_add]
        congr 1
        simp [dotProduct, Fin.sum_univ_three, ModeSet.kvec]
        ring
      simp_rw [hsplit]
      have hind := (hzind p).comp
        (φ := fun q : ℝ × ℝ => Complex.exp (Complex.I * ((((K.kx i - K.kx j) * q.1 +
            (K.ky i - K.ky j) * q.2 : ℝ)) : ℂ)))
        (ψ := fun z : ℝ => Complex.exp (Complex.I * ((((K.kz i - K.kz j) * z : ℝ)) : ℂ)))
        (by fun_prop) (by fun_prop)
      have hm1 : AEStronglyMeasurable ((fun q : ℝ × ℝ => Complex.exp (Complex.I * ((((K.kx i - K.kx j) * q.1 +
            (K.ky i - K.ky j) * q.2 : ℝ)) : ℂ))) ∘ fun ω => (r p ω 0, r p ω 1)) P :=
        ((Continuous.measurable (by fun_prop)).comp_aemeasurable
          (((hrm p).aemeasurable.eval (a := 0)).prodMk ((hrm p).aemeasurable.eval (a := 1)))).aestronglyMeasurable
      have hm2 : AEStronglyMeasurable ((fun z : ℝ => Complex.exp (Complex.I * ((((K.kz i - K.kz j) * z : ℝ)) : ℂ))) ∘ fun ω => r p ω 2) P :=
        ((Continuous.measurable (by fun_prop)).comp_aemeasurable
          ((hrm p).aemeasurable.eval (a := 2))).aestronglyMeasurable
      have hmul := hind.integral_fun_mul_eq_mul_integral hm1 hm2
      simp only [Function.comp_def] at hmul
      rw [hmul]
      have hN := hphase p i j i i
      have e1 : K.kx i - K.kx j - K.kx i + K.kx i = K.kx i - K.kx j := by ring
      have e2 : K.ky i - K.ky j - K.ky i + K.ky i = K.ky i - K.ky j := by ring
      rw [e1, e2, if_neg] at hN
      · have := (mul_eq_zero.1 hN).resolve_left hNz
        rw [this, zero_mul]
      · rintro ⟨h1, h2⟩
        apply hij
        apply hinj
        simp only [Prod.mk.injEq]
        constructor <;> linarith
    have hterm : ∀ p, ∫ ω, X p ω * Y p ω ∂P = 0 := by
      intro p
      have hind := (hrA p).comp (φ := fun v : Fin 3 → ℝ =>
          Complex.exp (Complex.I * ((dotProduct c v : ℝ) : ℂ)))
        (ψ := fun Z : Amp => ampRed K Z K.kvec K.kvec j i b a) hphi.measurable
        (meas_ampRed K K.kvec K.kvec j i b a)
      have := hind.integral_fun_mul_eq_mul_integral
        ((hphi.measurable.comp (hrm p)).aestronglyMeasurable)
        (((meas_ampRed K K.kvec K.kvec j i b a).comp (hAm p)).aestronglyMeasurable)
      simp only [Function.comp_def] at this
      rw [this]
      have h0 := hXi p
      simp only [X] at h0
      rw [h0, zero_mul]
    simp [hterm]
