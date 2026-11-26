-- Prove2me | solution 1 for Arxiv2205_09423.offdiagonal_transmission_circular
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T02:07:18.584134+00:00
-- url     : https://prove2.me/submissions/3c4288d3-5e0d-403a-b443-b49cd0018308

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

lemma unif_exp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) (dL : ℝ)
    (hdL : 0 < dL) (hZm : Measurable Z)
    (hZ : pdf.IsUniform Z (Set.Icc (-dL / 2) (dL / 2)) P) (a : ℝ) (ha : 0 < a) :
    ∫ ω, Complex.exp (Complex.I * ((a * Z ω : ℝ) : ℂ)) ∂P = (Real.sinc (a * dL / 2) : ℂ) := by
  have hf : Continuous fun z : ℝ => Complex.exp (Complex.I * ((a * z : ℝ) : ℂ)) := by fun_prop
  rw [← integral_map (f := fun z : ℝ => Complex.exp (Complex.I * ((a * z : ℝ) : ℂ)))
    hZm.aemeasurable hf.aestronglyMeasurable, hZ]
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, Real.volume_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∀ z : ℝ, Complex.exp (Complex.I * ((a * z : ℝ) : ℂ)) =
      Complex.exp ((Complex.I * a) * z) := by intro z; push_cast; ring_nf
  simp_rw [h1]
  have hIa : Complex.I * a ≠ 0 := by
    simp [Complex.I_ne_zero, ha.ne']
  rw [integral_exp_mul_complex hIa]
  rw [Real.sinc_of_ne_zero (by positivity)]
  have hs : ((Real.sin (a * dL / 2) : ℝ) : ℂ) = Complex.sin ((a * dL / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sin]
  push_cast
  rw [Complex.sin]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith)]
  have hdL' : (dL : ℂ) ≠ 0 := by exact_mod_cast hdL.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [Complex.real_smul]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

lemma unif_exp' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (dL : ℝ)
    (hdL : 0 < dL) (hZm : Measurable Z)
    (hZ : pdf.IsUniform Z (Set.Icc (-dL / 2) (dL / 2)) P) (a : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((a * Z ω : ℝ) : ℂ)) ∂P = (Real.sinc (a * dL / 2) : ℂ) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have h := unif_exp P Z dL hdL hZm hZ (-a) (by linarith)
    have hc : ∀ ω, Complex.exp (Complex.I * ((a * Z ω : ℝ) : ℂ)) =
        (starRingEnd ℂ) (Complex.exp (Complex.I * ((-a * Z ω : ℝ) : ℂ))) := by
      intro ω; rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
    simp_rw [hc]
    rw [integral_conj, h, Complex.conj_ofReal]
    rw [show -a * dL / 2 = -(a * dL / 2) by ring, Real.sinc_neg]
  · simp
  · exact unif_exp P Z dL hdL hZm hZ a ha

lemma memLp_ampRed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ModeSet Nk) (vin vout : Fin (2 * Nk + 1) → Fin 3 → ℝ)
    (j i : Fin (2 * Nk + 1)) (b a : Fin 2) (A : Ω → Amp)
    (hm : ∀ uo ui a b, MemLp (fun ω => A ω uo ui a b) 2 P) :
    MemLp (fun ω => ampRed K (A ω) vin vout j i b a) 2 P := by
  unfold ampRed reduce
  simp only [Matrix.of_apply]
  refine memLp_finsetSum _ fun a' _ => memLp_finsetSum _ fun b' _ => ?_
  exact ((hm _ _ a' b').const_mul _).mul_const _

end S75MT

open S75MT in
theorem mt_main {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
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

open S75MT in
theorem pc_main {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) (hE : IsSlabEnsemble K dL n P r A)
    (p0 : Fin N)
    (j i v u : Fin (2 * Nk + 1)) (hij : i ≠ j) (huv : u ≠ v) (b a d c : Fin 2) :
    pcovC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
        (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) v u d c) =
      ((K.deltaP i j u v * K.cijuv n dL i j u v *
          Real.sinc (dL / 2 * (K.kz i - K.kz j + K.kz u - K.kz v)) : ℝ) : ℂ) *
        ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a *
          ampRed K (A p0 ω) K.kvec K.kvec v u d c ∂P := by
  have m1 := mt_main K hK dL n P r A hE p0 j i b a
  rw [if_neg hij] at m1
  obtain ⟨hprob, hdL, hn, hrm, hAm, hiid, hrA, hid, hmem, hzind, hunif, hphase⟩ := hE
  obtain ⟨hk, hmode, -, hinj, hw⟩ := hK
  have hkz : ∀ i, 0 < K.kz i := fun i => Real.sqrt_pos.2 (by linarith [hmode i])
  have hw0 : 0 < K.w := by rw [hw]; have := hk; positivity
  unfold pcovC
  rw [m1, zero_mul, sub_zero]
  have hNz : (N : ℂ) ≠ 0 := by
    have : 0 < N := Fin.pos p0
    exact_mod_cast this.ne'
  set e1 : Fin 3 → ℝ := K.kvec i - K.kvec j with he1
  set e2 : Fin 3 → ℝ := K.kvec u - K.kvec v with he2
  set X1 : Fin N → Ω → ℂ := fun p ω =>
    Complex.exp (Complex.I * ((dotProduct e1 (r p ω) : ℝ) : ℂ)) with hX1
  set X2 : Fin N → Ω → ℂ := fun p ω =>
    Complex.exp (Complex.I * ((dotProduct e2 (r p ω) : ℝ) : ℂ)) with hX2
  set Y1 : Fin N → Ω → ℂ := fun p ω => ampRed K (A p ω) K.kvec K.kvec j i b a with hY1
  set Y2 : Fin N → Ω → ℂ := fun p ω => ampRed K (A p ω) K.kvec K.kvec v u d c with hY2
  have hent1 : ∀ ω, tbar K (fun p => A p ω) (fun p => r p ω) j i b a =
      ((K.cji j i : ℝ) : ℂ) * ∑ p, X1 p ω * Y1 p ω := by
    intro ω
    simp only [tbar, blockSum, if_neg hij, Matrix.add_apply, Matrix.zero_apply, zero_add,
      Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, X1, Y1, he1]
  have hent2 : ∀ ω, tbar K (fun p => A p ω) (fun p => r p ω) v u d c =
      ((K.cji v u : ℝ) : ℂ) * ∑ p, X2 p ω * Y2 p ω := by
    intro ω
    simp only [tbar, blockSum, if_neg huv, Matrix.add_apply, Matrix.zero_apply, zero_add,
      Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, X2, Y2, he2]
  have hphi : ∀ e : Fin 3 → ℝ, Continuous fun v : Fin 3 → ℝ =>
      Complex.exp (Complex.I * ((dotProduct e v : ℝ) : ℂ)) := by
    intro e; simp only [dotProduct, Fin.sum_univ_three]; fun_prop
  have hnX : ∀ (e : Fin 3 → ℝ) (v : Fin 3 → ℝ),
      ‖Complex.exp (Complex.I * ((dotProduct e v : ℝ) : ℂ))‖ = 1 := by
    intro e v; rw [Complex.norm_exp]; simp
  -- measurable functions of the pair (r_p, A_p)
  set F1 : (Fin 3 → ℝ) × Amp → ℂ := fun z =>
    Complex.exp (Complex.I * ((dotProduct e1 z.1 : ℝ) : ℂ)) * ampRed K z.2 K.kvec K.kvec j i b a
  set F2 : (Fin 3 → ℝ) × Amp → ℂ := fun z =>
    (Complex.exp (Complex.I * ((dotProduct e2 z.1 : ℝ) : ℂ)) * ampRed K z.2 K.kvec K.kvec v u d c)
  have hF1 : Measurable F1 :=
    ((hphi e1).measurable.comp measurable_fst).mul ((meas_ampRed K _ _ j i b a).comp measurable_snd)
  have hF2 : Measurable F2 :=
      (((hphi e2).measurable.comp measurable_fst).mul ((meas_ampRed K _ _ v u d c).comp measurable_snd))
  have hpair : ∀ p, Measurable fun ω => (r p ω, A p ω) := fun p => (hrm p).prodMk (hAm p)
  have hL1 : ∀ p, MemLp (fun ω => F1 (r p ω, A p ω)) 2 P := by
    intro p
    refine (memLp_ampRed P K K.kvec K.kvec j i b a (A p) (hmem p)).of_le
      (hF1.comp (hpair p)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    simp only [F1, norm_mul, hnX, one_mul]; exact le_rfl
  have hL2 : ∀ p, MemLp (fun ω => F2 (r p ω, A p ω)) 2 P := by
    intro p
    refine (memLp_ampRed P K K.kvec K.kvec v u d c (A p) (hmem p)).of_le
      (hF2.comp (hpair p)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    simp only [F2, norm_mul, hnX, one_mul]; exact le_rfl
  have hWi : ∀ p q, Integrable (fun ω => F1 (r p ω, A p ω) * F2 (r q ω, A q ω)) P :=
    fun p q => (hL1 p).integrable_mul (hL2 q)
  have hint : ∀ ω, tbar K (fun p => A p ω) (fun p => r p ω) j i b a *
      (tbar K (fun p => A p ω) (fun p => r p ω) v u d c) =
      ((K.cji j i * K.cji v u : ℝ) : ℂ) *
        ∑ p, ∑ q, F1 (r p ω, A p ω) * F2 (r q ω, A q ω) := by
    intro ω
    rw [hent1, hent2]
    simp only [F1, F2, X1, X2, Y1, Y2, Finset.mul_sum, Finset.sum_mul, Complex.ofReal_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  simp_rw [hint]
  rw [integral_const_mul, integral_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => hWi p q]
  simp_rw [integral_finsetSum _ fun q _ => hWi _ q]
  -- mean of F1 vanishes
  have hX1i : ∀ p, ∫ ω, X1 p ω ∂P = 0 := by
    intro p
    have hsplit : ∀ ω, X1 p ω =
        Complex.exp (Complex.I * ((((K.kx i - K.kx j) * r p ω 0 +
          (K.ky i - K.ky j) * r p ω 1 : ℝ)) : ℂ)) *
        Complex.exp (Complex.I * ((((K.kz i - K.kz j) * r p ω 2 : ℝ)) : ℂ)) := by
      intro ω
      simp only [X1, he1, ← Complex.exp_add]
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
    have e1' : K.kx i - K.kx j - K.kx i + K.kx i = K.kx i - K.kx j := by ring
    have e2' : K.ky i - K.ky j - K.ky i + K.ky i = K.ky i - K.ky j := by ring
    rw [e1', e2', if_neg] at hN
    · have := (mul_eq_zero.1 hN).resolve_left hNz
      rw [this, zero_mul]
    · rintro ⟨h1, h2⟩
      apply hij
      apply hinj
      simp only [Prod.mk.injEq]
      constructor <;> linarith
  have hF1i : ∀ p, ∫ ω, F1 (r p ω, A p ω) ∂P = 0 := by
    intro p
    have hind := (hrA p).comp (φ := fun v : Fin 3 → ℝ =>
        Complex.exp (Complex.I * ((dotProduct e1 v : ℝ) : ℂ)))
      (ψ := fun Z : Amp => ampRed K Z K.kvec K.kvec j i b a) (hphi e1).measurable
      (meas_ampRed K K.kvec K.kvec j i b a)
    have := hind.integral_fun_mul_eq_mul_integral
      (((hphi e1).measurable.comp (hrm p)).aestronglyMeasurable)
      (((meas_ampRed K K.kvec K.kvec j i b a).comp (hAm p)).aestronglyMeasurable)
    simp only [Function.comp_def] at this
    simp only [F1]
    rw [this]
    have h0 := hX1i p
    simp only [X1] at h0
    rw [h0, zero_mul]
  have hoff : ∀ p q, q ≠ p → ∫ ω, F1 (r p ω, A p ω) * F2 (r q ω, A q ω) ∂P = 0 := by
    intro p q hqp
    have hpq := (hiid.indepFun hqp.symm).comp hF1 hF2
    have := hpq.integral_fun_mul_eq_mul_integral
      (hF1.comp (hpair p)).aestronglyMeasurable (hF2.comp (hpair q)).aestronglyMeasurable
    simp only [Function.comp_def] at this
    rw [this, hF1i p, zero_mul]
  have hdiag : ∀ p, ∑ q, ∫ ω, F1 (r p ω, A p ω) * F2 (r q ω, A q ω) ∂P =
      ∫ ω, F1 (r p ω, A p ω) * F2 (r p ω, A p ω) ∂P := by
    intro p
    rw [Finset.sum_eq_single p (fun q _ hqp => hoff p q hqp) (fun h => absurd (Finset.mem_univ p) h)]
  simp_rw [hdiag]
  -- diagonal term
  set G : Amp → ℂ := fun Z => ampRed K Z K.kvec K.kvec j i b a *
    (ampRed K Z K.kvec K.kvec v u d c) with hG
  have hGm : Measurable G := (meas_ampRed K _ _ j i b a).mul (meas_ampRed K _ _ v u d c)
  set α : ℝ := K.kx i - K.kx j - K.kx v + K.kx u
  set β : ℝ := K.ky i - K.ky j - K.ky v + K.ky u
  set γ : ℝ := K.kz i - K.kz j + K.kz u - K.kz v
  have hdp : ∀ p, ∫ ω, F1 (r p ω, A p ω) * F2 (r p ω, A p ω) ∂P =
      (∫ ω, Complex.exp (Complex.I * (((α * r p ω 0 + β * r p ω 1 : ℝ)) : ℂ)) ∂P) *
      (Real.sinc (γ * dL / 2) : ℂ) * ∫ ω, G (A p0 ω) ∂P := by
    intro p
    have hre : ∀ ω, F1 (r p ω, A p ω) * F2 (r p ω, A p ω) =
        (Complex.exp (Complex.I * (((α * r p ω 0 + β * r p ω 1 : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((γ * r p ω 2 : ℝ) : ℂ))) * G (A p ω) := by
      intro ω
      simp only [F1, F2, G]
      have : Complex.exp (Complex.I * ((dotProduct e1 (r p ω) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((dotProduct e2 (r p ω) : ℝ) : ℂ)) =
          Complex.exp (Complex.I * (((α * r p ω 0 + β * r p ω 1 : ℝ)) : ℂ)) *
            Complex.exp (Complex.I * ((γ * r p ω 2 : ℝ) : ℂ)) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        simp only [he1, he2, α, β, γ, dotProduct, Fin.sum_univ_three, ModeSet.kvec, Pi.sub_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons]
        push_cast; ring
      rw [← this]; ring
    simp_rw [hre]
    have hind := (hrA p).comp (φ := fun w : Fin 3 → ℝ =>
        Complex.exp (Complex.I * (((α * w 0 + β * w 1 : ℝ)) : ℂ)) *
          Complex.exp (Complex.I * ((γ * w 2 : ℝ) : ℂ))) (ψ := G) (by fun_prop) hGm
    have h1 := hind.integral_fun_mul_eq_mul_integral
      ((Continuous.measurable (by fun_prop)).comp (hrm p)).aestronglyMeasurable
      (hGm.comp (hAm p)).aestronglyMeasurable
    simp only [Function.comp_def] at h1
    rw [h1]
    have hind2 := (hzind p).comp
      (φ := fun q : ℝ × ℝ => Complex.exp (Complex.I * (((α * q.1 + β * q.2 : ℝ)) : ℂ)))
      (ψ := fun z : ℝ => Complex.exp (Complex.I * ((γ * z : ℝ) : ℂ)))
      (by fun_prop) (by fun_prop)
    have hm1 : AEStronglyMeasurable ((fun q : ℝ × ℝ => Complex.exp (Complex.I * (((α * q.1 + β * q.2 : ℝ)) : ℂ))) ∘ fun ω => (r p ω 0, r p ω 1)) P :=
      ((Continuous.measurable (by fun_prop)).comp_aemeasurable
        (((hrm p).aemeasurable.eval (a := 0)).prodMk ((hrm p).aemeasurable.eval (a := 1)))).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable ((fun z : ℝ => Complex.exp (Complex.I * ((γ * z : ℝ) : ℂ))) ∘ fun ω => r p ω 2) P :=
      ((Continuous.measurable (by fun_prop)).comp_aemeasurable
        ((hrm p).aemeasurable.eval (a := 2))).aestronglyMeasurable
    have h2 := hind2.integral_fun_mul_eq_mul_integral hm1 hm2
    simp only [Function.comp_def] at h2
    rw [h2, unif_exp' P (fun ω => r p ω 2) dL hdL ((measurable_pi_apply 2).comp (hrm p)) (hunif p) γ]
    congr 1
    exact ((hid p p0).comp hGm).integral_eq
  simp_rw [hdp]
  have hT : ∀ p, (N : ℂ) * ∫ ω, Complex.exp (Complex.I * (((α * r p ω 0 + β * r p ω 1 : ℝ)) : ℂ)) ∂P
      = if α = 0 ∧ β = 0 then (((2 * Real.pi) ^ 2 * n * dL / K.w : ℝ) : ℂ) else 0 := fun p =>
    hphase p i j v u
  have hT' : ∀ p, ∫ ω, Complex.exp (Complex.I * (((α * r p ω 0 + β * r p ω 1 : ℝ)) : ℂ)) ∂P
      = (N : ℂ)⁻¹ * if α = 0 ∧ β = 0 then (((2 * Real.pi) ^ 2 * n * dL / K.w : ℝ) : ℂ) else 0 := by
    intro p; rw [← hT p, ← mul_assoc, inv_mul_cancel₀ hNz, one_mul]
  simp_rw [hT']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show dL / 2 * γ = γ * dL / 2 by ring]
  have hcond : (α = 0 ∧ β = 0) ↔ (K.kx i - K.kx j = -(K.kx u - K.kx v) ∧ K.ky i - K.ky j = -(K.ky u - K.ky v)) := by
    simp only [α, β]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold ModeSet.deltaP
  by_cases hc : α = 0 ∧ β = 0
  · rw [if_pos hc, if_pos (hcond.1 hc)]
    have hG0 : ∫ ω, G (A p0 ω) ∂P = ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a *
          (ampRed K (A p0 ω) K.kvec K.kvec v u d c) ∂P := rfl
    rw [← hG0]
    have key : K.cji j i * K.cji v u * ((2 * Real.pi) ^ 2 * n * dL / K.w) = K.cijuv n dL i j u v := by
      unfold ModeSet.cji ModeSet.cijuv
      have hj := hkz j; have hi := hkz i; have hu := hkz u; have hv := hkz v
      rw [show K.kz i * K.kz j * K.kz u * K.kz v = (K.kz j * K.kz i) * (K.kz v * K.kz u) by ring,
        Real.sqrt_mul (by positivity)]
      have s1 : 0 < Real.sqrt (K.kz j * K.kz i) := Real.sqrt_pos.2 (by positivity)
      have s2 : 0 < Real.sqrt (K.kz v * K.kz u) := Real.sqrt_pos.2 (by positivity)
      have := Real.pi_pos
      field_simp
      rw [← Real.sqrt_mul hj.le, ← Real.sqrt_mul (by positivity)]; congr 1; ring
    have key' : ((K.cji j i * K.cji v u : ℝ) : ℂ) * (((2 * Real.pi) ^ 2 * n * dL / K.w : ℝ) : ℂ) =
        ((K.cijuv n dL i j u v : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, key]
    push_cast at key' ⊢
    rw [← key']
    field_simp
  · rw [if_neg hc, if_neg (fun h => hc (hcond.2 h))]
    simp

open S75MT in
theorem solution {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) (hE : IsSlabEnsemble K dL n P r A)
    (p0 : Fin N)
    (j i : Fin (2 * Nk + 1)) (hij : i ≠ j) :
    (∀ b a : Fin 2, ∫ ω, tbar K (fun p => A p ω) (fun p => r p ω) j i b a ∂P = 0) ∧
    (∀ b a d c : Fin 2,
      pcovC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
        (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i d c) = 0) ∧
    K.deltaP i j j i = 1 ∧
    (∀ b a d c : Fin 2,
      pcovC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
          (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) i j d c) =
        ((K.cijuv n dL i j j i : ℝ) : ℂ) *
          ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a *
            ampRed K (A p0 ω) K.kvec K.kvec i j d c ∂P ∧
      (pcovC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
          (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) i j d c) ≠ 0 ↔
        ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a *
          ampRed K (A p0 ω) K.kvec K.kvec i j d c ∂P ≠ 0)) := by
  have hdP : K.deltaP i j j i = 1 := by
    unfold ModeSet.deltaP; rw [if_pos]; constructor <;> ring
  have hdP0 : K.deltaP i j i j = 0 := by
    unfold ModeSet.deltaP; rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hij
    apply hK.2.2.2.1
    simp only [Prod.mk.injEq]
    constructor <;> linarith
  have hE' := hE
  obtain ⟨hprob, hdL, hn, -⟩ := hE'
  have hK' : K.IsValid := hK
  obtain ⟨hk, hmode, -, hinj, hw⟩ := hK
  have hkz : ∀ i, 0 < K.kz i := fun i => Real.sqrt_pos.2 (by linarith [hmode i])
  have hw0 : 0 < K.w := by rw [hw]; have := hk; positivity
  have hpos : 0 < K.cijuv n dL i j j i := by
    unfold ModeSet.cijuv
    have := hkz i; have := hkz j
    have : 0 < Real.sqrt (K.kz i * K.kz j * K.kz j * K.kz i) := Real.sqrt_pos.2 (by positivity)
    positivity
  refine ⟨fun b a => ?_, fun b a d c => ?_, hdP, fun b a d c => ?_⟩
  · rw [mt_main K hK' dL n P r A hE p0 j i b a, if_neg hij]
  · rw [pc_main K hK' dL n P r A hE p0 j i j i hij hij b a d c, hdP0]; simp
  · have h := pc_main K hK' dL n P r A hE p0 j i i j hij hij.symm b a d c
    rw [hdP, show K.kz i - K.kz j + K.kz j - K.kz i = 0 by ring, mul_zero, Real.sinc_zero,
      one_mul, mul_one] at h
    refine ⟨h, ?_⟩
    rw [h]
    have : ((K.cijuv n dL i j j i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    constructor
    · intro h1 h2; exact h1 (by rw [h2, mul_zero])
    · intro h1; exact mul_ne_zero this h1
