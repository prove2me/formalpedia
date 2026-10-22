-- Prove2me | solution 1 for AccelVI.AVC.spectrum_LPol_Icc
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:03:35.835089+00:00
-- url     : https://prove2.me/submissions/a0835c0b-234b-4945-9097-569122049218

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

set_option autoImplicit false
open AccelVI.AVC

section mmD
variable {S : Type*} [Fintype S] [DecidableEq S]

lemma mmD_eig (M : Matrix S S ℂ) (μ : ℂ) (h : μ ∈ spectrum ℂ M) :
    ∃ v : S → ℂ, v ≠ 0 ∧ M.mulVec v = μ • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, ?_⟩
  have : (algebraMap ℂ (Matrix S S ℂ) μ - M).mulVec v = μ • v - M.mulVec v := by
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [this] at hv0
  exact (sub_eq_zero.mp hv0).symm

lemma mmD_pow_nonneg (L : Matrix S S ℝ) (hL : ∀ x y, 0 ≤ L x y) (t : ℕ) :
    ∀ x y, 0 ≤ (L ^ t) x y := by
  induction t with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hL z y)

lemma mmD_stat_pow (L : Matrix S S ℝ) (ν : S → ℝ) (h : Matrix.vecMul ν L = ν) (t : ℕ) :
    Matrix.vecMul ν (L ^ t) = ν := by
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, h]

lemma mmD_pos (L : Matrix S S ℝ) (hL : MarkovMixing.IsStochastic L)
    (hirr : MarkovMixing.Irreducible L) (ν : S → ℝ) (hν : MarkovMixing.IsStationary L ν) :
    ∀ y, 0 < ν y := by
  obtain ⟨⟨hν0, hν1⟩, hst⟩ := hν
  have : ∃ x, 0 < ν x := by
    by_contra hcon
    push_neg at hcon
    have : ∑ x, ν x ≤ 0 := Finset.sum_nonpos fun x _ => hcon x
    linarith
  obtain ⟨x, hx⟩ := this
  intro y
  obtain ⟨t, ht⟩ := hirr x y
  have h1 := mmD_stat_pow L ν hst t
  have h2 : ν y = ∑ z, ν z * (L ^ t) z y := by
    conv_lhs => rw [← h1]
    rfl
  rw [h2]
  calc (0 : ℝ) < ν x * (L ^ t) x y := mul_pos hx ht
    _ ≤ ∑ z, ν z * (L ^ t) z y :=
      Finset.single_le_sum (f := fun z => ν z * (L ^ t) z y)
        (fun z _ => mul_nonneg (hν0 z) (mmD_pow_nonneg L hL.1 t z y)) (Finset.mem_univ x)

lemma mmD_real (L : Matrix S S ℝ) (ν : S → ℝ) (hpos : ∀ y, 0 < ν y)
    (hdb : MarkovMixing.DetailedBalance L ν) :
    ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), μ.im = 0 := by
  intro μ hμ
  obtain ⟨v, hv, hLv⟩ := mmD_eig _ μ hμ
  set Q : ℂ := ∑ i, ∑ j, (ν i : ℂ) * (L i j : ℂ) * (starRingEnd ℂ (v i)) * v j with hQ
  have hQconj : starRingEnd ℂ Q = Q := by
    rw [hQ, map_sum]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hdb j i
    have h' : (ν j : ℂ) * (L j i : ℂ) = (ν i : ℂ) * (L i j : ℂ) := by
      exact_mod_cast this
    calc (ν j : ℂ) * (L j i : ℂ) * v j * starRingEnd ℂ (v i)
        = ((ν j : ℂ) * (L j i : ℂ)) * v j * starRingEnd ℂ (v i) := by ring
      _ = ((ν i : ℂ) * (L i j : ℂ)) * v j * starRingEnd ℂ (v i) := by rw [h']
      _ = _ := by ring
  have hQeq : Q = μ * ((∑ i, ν i * Complex.normSq (v i) : ℝ) : ℂ) := by
    have hrow : ∀ i, ∑ j, (L i j : ℂ) * v j = μ * v i := by
      intro i
      have := congrFun hLv i
      simpa [Matrix.mulVec, dotProduct] using this
    rw [hQ]
    have : ∀ i, ∑ j, (ν i : ℂ) * (L i j : ℂ) * (starRingEnd ℂ (v i)) * v j
        = (ν i : ℂ) * (starRingEnd ℂ (v i)) * (μ * v i) := by
      intro i
      rw [← hrow i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => this i]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hN : 0 < ∑ i, ν i * Complex.normSq (v i) := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hv (funext hcon)
    calc (0 : ℝ) < ν i * Complex.normSq (v i) := mul_pos (hpos i) (Complex.normSq_pos.mpr hi)
      _ ≤ _ := Finset.single_le_sum (f := fun i => ν i * Complex.normSq (v i))
        (fun j _ => mul_nonneg (hpos j).le (Complex.normSq_nonneg _)) (Finset.mem_univ i)
  have hQim : Q.im = 0 := by
    have := congrArg Complex.im hQconj
    simp at this
    linarith
  rw [hQeq] at hQim
  simp [Complex.mul_im] at hQim
  rcases hQim with h | h
  · exact h
  · exact absurd h hN.ne'


lemma mmD_bound (L : Matrix S S ℝ) (hL : MarkovMixing.IsStochastic L) :
    ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), ‖μ‖ ≤ 1 := by
  intro μ hμ
  obtain ⟨v, hv, hLv⟩ := mmD_eig _ μ hμ
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon; push_neg at hcon; exact hv (funext hcon)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset S) (fun j => ‖v j‖) ⟨i0, Finset.mem_univ _⟩
  have hpos : 0 < ‖v i‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hi0) (hi i0 (Finset.mem_univ _))
  have hrow : ∑ j, (L i j : ℂ) * v j = μ * v i := by
    have := congrFun hLv i
    simpa [Matrix.mulVec, dotProduct] using this
  have h1 : ‖μ‖ * ‖v i‖ ≤ ‖v i‖ := by
    calc ‖μ‖ * ‖v i‖ = ‖μ * v i‖ := (norm_mul _ _).symm
      _ = ‖∑ j, (L i j : ℂ) * v j‖ := by rw [hrow]
      _ ≤ ∑ j, ‖(L i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, L i j * ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hL.1 i j)]
      _ ≤ ∑ j, L i j * ‖v i‖ :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ _)) (hL.1 i j)
      _ = ‖v i‖ := by rw [← Finset.sum_mul, hL.2 i, one_mul]
  by_contra hc
  push_neg at hc
  nlinarith

lemma mmD_LPol_stoch {A : Type*} [Fintype A] (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ)
    (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) :
    MarkovMixing.IsStochastic (LPol M pol) := by
  obtain ⟨hK, -, -⟩ := hM
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · simp only [LPol, Matrix.of_apply, FoundationsML.ReinforcementLearning.InducedTransition]
    exact Finset.sum_nonneg fun a _ => mul_nonneg ((hpol x).1 a) ((hK x a).1 y)
  · simp only [LPol, Matrix.of_apply, FoundationsML.ReinforcementLearning.InducedTransition]
    rw [Finset.sum_comm]
    have : ∀ a ∈ (Finset.univ : Finset A), ∑ y, pol x a * M.P x a y = pol x a := by
      intro a _
      rw [← Finset.mul_sum, (hK x a).2, mul_one]
    rw [Finset.sum_congr rfl this]
    exact (hpol x).2

end mmD

theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (hrev : IsReversible (LPol M pol)) :
    ∀ μ ∈ spectrum ℂ ((LPol M pol).map (algebraMap ℝ ℂ)),
      ∃ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 ∧ μ = (t : ℂ) := by
  have hst := mmD_LPol_stoch M hM pol hpol
  obtain ⟨hirr, ν, hν, hdb⟩ := hrev
  intro μ hμ
  have him : μ.im = 0 := mmD_real _ ν (mmD_pos _ hst hirr ν hν) hdb μ hμ
  have hb := mmD_bound _ hst μ hμ
  refine ⟨μ.re, ?_, ?_⟩
  · have : |μ.re| ≤ 1 := le_trans (Complex.abs_re_le_norm μ) hb
    exact abs_le.mp this
  · apply Complex.ext <;> simp [him]
