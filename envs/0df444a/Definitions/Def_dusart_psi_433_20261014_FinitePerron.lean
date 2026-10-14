-- Prove2me | Definitions.Def_dusart_psi_433_20261014_FinitePerron
-- name    : dusart_psi_433_20261014_FinitePerron
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:37:41.024442+00:00
-- url     : https://prove2.me/theorems/f0240175-e785-4124-ba45-155dc9418e58
-- title:
--   Dusart smoothing: Finite Perron
-- statement:
--   This module gives the complete finite perron component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PerronAnalytic
noncomputable section
namespace DusartSmoothing
open Complex Set Topology Filter Asymptotics Real
open DusartSmoothing.Contour

lemma mem_perron_rectangle (T : ℝ) (hT : 0 ≤ T) (s : ℂ) :
    s ∈ Rectangle (-(1/2 : ℂ) - T * I) (2 + T * I) ↔
      (-(1/2 : ℝ) ≤ s.re ∧ s.re ≤ 2) ∧ -T ≤ s.im ∧ s.im ≤ T := by
  norm_num [Rectangle, Complex.mem_reProdIm, Set.uIcc,
    min_eq_left (by linarith : -T ≤ T), max_eq_right (by linarith : -T ≤ T)]

lemma perron_rectangle_mem_nhds (T : ℝ) (hT : 0 ≤ T) (s : ℂ)
    (hre : -(1/2 : ℝ) < s.re ∧ s.re < 2) (him : -T < s.im ∧ s.im < T) :
    Rectangle (-(1/2 : ℂ) - T * I) (2 + T * I) ∈ 𝓝 s := by
  rw [rectangle_mem_nhds_iff]
  norm_num [Complex.mem_reProdIm, Set.uIoo,
    min_eq_left (by linarith : -T ≤ T), max_eq_right (by linarith : -T ≤ T)]
  exact ⟨hre, him⟩

/-- The exact finite Perron rectangle formula, with all actual zeros and both poles. -/
theorem perron_finite_rectangle (x : ℝ) (hx : 0 < x) (T : ℝ) (hT : 4 < T)
    (hg : RvM.GoodHeight T) :
    let hfin := RvM.finite_symmetric_zero_window T
    RectangleIntegral' (perronIntegrand x) (-(1/2 : ℂ) - T * I) (2 + T * I) =
      (x : ℂ)^3 / 6 - (x : ℂ)^2 / 2 * logDeriv riemannZeta 0 -
        ∑ ρ ∈ hfin.toFinset, (RvM.zeroMult ρ : ℂ) * quadraticKernel x ρ := by
  classical
  dsimp only
  let Z := (RvM.finite_symmetric_zero_window T).toFinset
  let P : Finset ℂ := insert 0 (insert 1 Z)
  let A : ℂ → ℂ := fun q => if q = 0 then -(x : ℂ)^2 / 2 * logDeriv riemannZeta 0
    else if q = 1 then (x : ℂ)^3 / 6 else -((RvM.zeroMult q : ℂ) * quadraticKernel x q)
  have hT0 : 0 < T := by linarith
  have hre : (-(1/2 : ℂ) - T * I).re ≤ (2 + T * I : ℂ).re := by norm_num
  have him : (-(1/2 : ℂ) - T * I).im ≤ (2 + T * I : ℂ).im := by simp; linarith
  have hZ : ∀ q : ℂ, q ∈ Z ↔ RvM.IsNontrivialZero q ∧ |q.im| ≤ T := by
    intro q
    exact Set.Finite.mem_toFinset _
  have hne : ∀ q ∈ Z, q ≠ 0 ∧ q ≠ 1 := by
    intro q hq
    obtain ⟨hz, _⟩ := (hZ q).mp hq
    constructor
    · intro h; have hh := hz.2.1; rw [h] at hh; norm_num at hh
    · intro h; have hh := hz.2.2; rw [h] at hh; norm_num at hh
  have h0Z : (0 : ℂ) ∉ Z := fun h => (hne 0 h).1 rfl
  have h1Z : (1 : ℂ) ∉ Z := fun h => (hne 1 h).2 rfl
  have hPint : ∀ q ∈ P, Rectangle (-(1/2 : ℂ) - T * I) (2 + T * I) ∈ 𝓝 q := by
    intro q hq
    simp only [P, Finset.mem_insert] at hq
    rcases hq with rfl | rfl | hq
    · apply perron_rectangle_mem_nhds T hT0.le 0 <;> simp <;> linarith
    · apply perron_rectangle_mem_nhds T hT0.le 1 <;> simp <;> linarith
    · obtain ⟨hz, hγ⟩ := (hZ q).mp hq
      have hbounds := abs_le.mp hγ
      apply perron_rectangle_mem_nhds T hT0.le q
      · constructor <;> linarith [hz.2.1, hz.2.2]
      · exact ⟨lt_of_le_of_ne hbounds.1 (fun h => RvM.goodHeight_neg hg q hz h.symm),
          lt_of_le_of_ne hbounds.2 (fun h => hg q hz h)⟩
  have hholo : HolomorphicOn (perronIntegrand x)
      (Rectangle (-(1/2 : ℂ) - T * I) (2 + T * I) \ (P : Set ℂ)) := by
    intro s hs
    have hm := (mem_perron_rectangle T hT0.le s).mp hs.1
    have hnot : s ≠ 0 ∧ s ≠ 1 ∧ s ∉ Z := by
      simpa only [P, Finset.mem_coe, Finset.mem_insert, not_or] using hs.2
    have hnz : riemannZeta s ≠ 0 := by
      intro hz
      apply hnot.2.2
      exact (hZ s).mpr ⟨(zeta_zero_iff_nontrivial_in_half_strip s hm.1.1).mp hz,
        abs_le.mpr hm.2⟩
    exact (perronIntegrand_analyticAt x hx s hm.1.1 hnot.1 hnot.2.1 hnz).differentiableAt.differentiableWithinAt
  have hnear : ∀ q ∈ P,
      (perronIntegrand x - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
    intro q hq
    simp only [P, Finset.mem_insert] at hq
    rcases hq with rfl | rfl | hq
    · simpa only [A, if_pos rfl, sub_zero] using perron_zero_kernel_principal_part x hx
    · simpa [A] using perron_one_principal_part x hx
    · have hq0 := (hne q hq).1
      have hq1 := (hne q hq).2
      simpa only [A, if_neg hq0, if_neg hq1] using
        perron_zero_principal_part x hx q ((hZ q).mp hq).1
  have h := residueTheorem_finset hre him P A hPint hholo hnear
  rw [h]
  rw [Finset.sum_insert (by simp [h0Z]), Finset.sum_insert h1Z]
  have hsum : ∑ q ∈ Z, A q = -∑ q ∈ Z, (RvM.zeroMult q : ℂ) * quadraticKernel x q := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [A, if_neg (hne q hq).1, if_neg (hne q hq).2]
  rw [hsum]
  simp only [A, if_pos rfl, if_neg one_ne_zero, if_true]
  dsimp only [Z]
  ring

end DusartSmoothing


