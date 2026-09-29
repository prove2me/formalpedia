-- Prove2me | solution 1 for ArithmeticE.ordinary_cyclic_combination
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T17:36:36.414855+00:00
-- url     : https://prove2.me/submissions/62fd3ee0-9203-4ef3-a8f7-5685b2844641

import Theorems.Thm_ArithmeticE_cleared_derivative_jet_interpolation
import Theorems.Thm_ArithmeticE_cyclic_jet_test
import Theorems.Thm_ArithmeticE_polynomial_derivative_frame_minimal_equation
open ArithmeticE

theorem solution
    (m : ℕ) (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (hcoeff : ∀ i n, IsAlgebraic ℚ (PowerSeries.coeff n (f i)))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ) : PowerSeries ℂ) * PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ) : PowerSeries ℂ) * f j)
    (hbasis : RelationBasis f)
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ) (hreg : T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hnot : ¬ ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i : PowerSeries ℂ) * f i = 0) ∧ ∀ i, (p i).eval ξ = a i) :
    ∃ (P : Fin m → Polynomial ℂ) (p : ℕ → Polynomial ℂ) (n : ℕ),
      (∀ i k, IsAlgebraic ℚ ((P i).coeff k)) ∧
      (∀ i, (P i).eval ξ = a i) ∧ 0 < n ∧
      MinimalEquation p n (∑ i, (P i : PowerSeries ℂ) * f i) ∧ (p n).eval ξ ≠ 0  := by
  obtain ⟨n,w,hn,hw,hw0,htest⟩ := cyclic_jet_test m f T B hode hbasis ξ hreg a ha hnot
  obtain ⟨P,hP,hjets⟩ := cleared_derivative_jet_interpolation m T B ξ hξ hreg n w hw
  obtain ⟨p,hmin,hpn⟩ := polynomial_derivative_frame_minimal_equation
    (∑ i, (P i : PowerSeries ℂ) * f i) ξ n (htest P hjets)
  refine ⟨P,p,n,hP,?_,hn,hmin,hpn⟩
  intro i
  have h := hjets 0 hn i
  simpa only [clearedDerivativeRows, hw0] using h

