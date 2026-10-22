-- Prove2me | solution 1 for AccelVI.AVC.real_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:01:54.374676+00:00
-- url     : https://prove2.me/submissions/0b0fbe08-3364-42ae-a26b-8ff1473769c8

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

end mmD

theorem solution {S : Type*} [Fintype S] [DecidableEq S] (L : Matrix S S ℝ) (hL : MarkovMixing.IsStochastic L)
    (hrev : IsReversible L) :
    ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), μ.im = 0 := by
  obtain ⟨hirr, ν, hst, hdb⟩ := hrev
  exact mmD_real L ν (mmD_pos L hL hirr ν hst) hdb
