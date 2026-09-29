-- Prove2me | solution 1 for ArithmeticE.minimal_operator_coefficient_descent
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:11:02.991419+00:00
-- url     : https://prove2.me/submissions/84bb6c51-a1b7-4c3d-a038-7ad895b0e8a7

import Definitions.Def_beukersLiftingData
set_option autoImplicit false
set_option maxHeartbeats 1600000
open ArithmeticE Polynomial PowerSeries
namespace ClassicalDescent

lemma coefficient_projection_relation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {ι : Type*} [Fintype ι] (v : ι → ℕ → K) (a : ι → L)
    (ha : ∀ n, ∑ i, a i * algebraMap K L (v i n) = 0)
    (j : ι) (hj : a j ≠ 0) :
    ∃ b : ι → K, b j = 1 ∧ ∀ n, ∑ i, b i * v i n = 0 := by
  obtain ⟨σ, hσ⟩ := Module.Projective.exists_dual_eq_one K hj
  refine ⟨fun i => σ (a i), hσ, ?_⟩
  intro n
  have hh := congrArg σ (ha n)
  simpa only [map_sum, map_zero, mul_comm (a _), ← Algebra.smul_def,
    map_smul, smul_eq_mul, mul_comm (v _ _)] using hh

lemma polynomial_coefficient_descent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L →ₗ[K] K) (p : Polynomial L) :
    ∃ q : Polynomial K, ∀ d, q.coeff d = σ (p.coeff d) := by
  classical
  refine ⟨∑ d ∈ p.support, Polynomial.monomial d (σ (p.coeff d)), ?_⟩
  intro d
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · have hp : p.coeff d = 0 := by simpa using hd
    simp [hp]

lemma polynomial_relation_descent
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (m : ℕ) (f : Fin m → PowerSeries K) (p : Fin m → Polynomial L)
    (hz : ∑ i, (p i : PowerSeries L) * (f i).map (algebraMap K L) = 0)
    (j : Fin m) (d : ℕ) (hj : (p j).coeff d ≠ 0) :
    ∃ q : Fin m → Polynomial K, (q j).coeff d = 1 ∧
      ∑ i, (q i : PowerSeries K) * f i = 0 := by
  classical
  obtain ⟨σ, hσ⟩ := Module.Projective.exists_dual_eq_one K hj
  choose q hq using fun i => polynomial_coefficient_descent σ (p i)
  refine ⟨q, (hq j d).trans hσ, ?_⟩
  ext n
  have hh := congrArg (fun F : PowerSeries L => σ (PowerSeries.coeff n F)) hz
  simp only [map_sum, PowerSeries.coeff_mul, PowerSeries.coeff_map,
    Polynomial.coeff_coe, map_zero] at hh ⊢
  simp only [hq]
  simpa only [mul_comm ((p _).coeff _), ← Algebra.smul_def,
    map_smul, smul_eq_mul, mul_comm (PowerSeries.coeff _ (f _))] using hh
lemma derivative_map {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (f : PowerSeries K) :
    (PowerSeries.derivative K f).map φ = PowerSeries.derivative L (f.map φ) := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_derivative]

lemma iterate_derivative_map {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (f : PowerSeries K) (n : ℕ) :
    ((PowerSeries.derivative K)^[n] f).map φ = (PowerSeries.derivative L)^[n] (f.map φ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', derivative_map, ih, Function.iterate_succ_apply']

lemma minimal_operator_coefficient_descent {K : Type*} [Field K] [Algebra K ℂ] (f : PowerSeries K)
    (p : ℕ → Polynomial ℂ) (n : ℕ)
    (hm : MinimalEquation p n (f.map (algebraMap K ℂ))) :
    ∃ q : ℕ → Polynomial K,
      MinimalEquation (fun k => (q k).map (algebraMap K ℂ)) n (f.map (algebraMap K ℂ)) ∧
      ∃ d, (q n).coeff d = 1 := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, (p n).coeff d ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hm.1
    ext d
    simpa using hh d
  have he : ∑ i : Fin (n+1), (p i : PowerSeries ℂ)*
      ((PowerSeries.derivative K)^[i.val] f).map (algebraMap K ℂ) = 0 := by
    simp only [iterate_derivative_map]
    rw [Fin.sum_univ_eq_sum_range (fun k => (p k : PowerSeries ℂ)*
      (PowerSeries.derivative ℂ)^[k] (f.map (algebraMap K ℂ)))]
    exact hm.2.1
  obtain ⟨q, hqd, hq⟩ := polynomial_relation_descent (n+1)
    (fun i => (PowerSeries.derivative K)^[i.val] f) (fun i => p i.val) he
    ⟨n, by omega⟩ d hd
  let q' : ℕ → Polynomial K := fun k => if hk : k < n+1 then q ⟨k,hk⟩ else 0
  have hqi (i : Fin (n+1)) : q' i.val = q i := by simp only [q', dif_pos i.isLt]
  have hqn : (q' n).coeff d = 1 := by simpa [q'] using hqd
  refine ⟨q', ⟨?_, ?_, ?_⟩, d, hqn⟩
  · intro hh
    have hc := congrArg (Polynomial.coeff · d) hh
    simp [Polynomial.coeff_map, hqn] at hc
  · have hh := congrArg (PowerSeries.map (algebraMap K ℂ)) hq
    simp only [map_sum, map_mul, map_zero, Polynomial.polynomial_map_coe,
      iterate_derivative_map] at hh
    unfold operatorValue
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [hqi, Polynomial.polynomial_map_coe] using hh
  · exact hm.2.2
end ClassicalDescent

theorem solution {K : Type*} [Field K] [Algebra K ℂ] (f : PowerSeries K)
    (p : ℕ → Polynomial ℂ) (n : ℕ)
    (hm : MinimalEquation p n (f.map (algebraMap K ℂ))) :
    ∃ q : ℕ → Polynomial K,
      MinimalEquation (fun k => (q k).map (algebraMap K ℂ)) n (f.map (algebraMap K ℂ)) ∧
      ∃ d, (q n).coeff d = 1 := by
  exact ClassicalDescent.minimal_operator_coefficient_descent f p n hm
#print axioms solution
