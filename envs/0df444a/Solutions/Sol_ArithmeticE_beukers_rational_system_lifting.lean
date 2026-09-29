-- Prove2me | solution 1 for ArithmeticE.beukers_rational_system_lifting
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:35:57.136228+00:00
-- url     : https://prove2.me/submissions/38a76cce-83d4-4074-9d48-09aac55b57b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ArithmeticE_ordinary_cyclic_combination
import Theorems.Thm_ArithmeticE_algebraic_e_combination_zero_singularity
import Theorems.Thm_ArithmeticE_polynomial_relation_basis
open ArithmeticE

theorem solution
    (m : ℕ) (f : Fin m → PowerSeries ℂ)
    (T : Polynomial ℚ) (B : Matrix (Fin m) (Fin m) (Polynomial ℚ))
    (harith : ∀ i, RationalSeriesArithmetic (f i))
    (hode : ∀ i, (T.map (algebraMap ℚ ℂ):PowerSeries ℂ)*PowerSeries.derivative ℂ (f i) =
      ∑ j, ((B i j).map (algebraMap ℚ ℂ):PowerSeries ℂ)*f j)
    (ξ : ℂ) (hξ : IsAlgebraic ℚ ξ)
    (hreg : ξ*T.eval₂ (algebraMap ℚ ℂ) ξ ≠ 0)
    (a : Fin m → ℂ) (ha : ∀ i, IsAlgebraic ℚ (a i))
    (hrel : ∑ i, a i*seriesValue (f i) ξ=0) :
    ∃ p : Fin m → Polynomial ℂ,
      (∑ i, (p i:PowerSeries ℂ)*f i=0) ∧ ∀ i, (p i).eval ξ=a i := by
  classical
  by_contra hnot
  have hcoeff : ∀ i n, IsAlgebraic ℚ (PowerSeries.coeff n (f i)) := by
    intro i n
    obtain ⟨c, hc, _⟩ := harith i
    have he : PowerSeries.coeff n (f i) = (c n : ℂ) / (n.factorial : ℂ) := by
      apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
      simpa [mul_comm] using hc n
    rw [he]
    simpa using (isAlgebraic_ratCast ℚ (A := ℂ) (c n / (n.factorial : ℚ)))
  obtain ⟨P, p, n, hP, hPa, hn, hmin, hpn⟩ :=
    ordinary_cyclic_combination m f T B hcoeff hode (polynomial_relation_basis m f)
      ξ hξ (mul_ne_zero_iff.mp hreg).2 a ha hnot
  exact hpn (algebraic_e_combination_zero_singularity m f harith P hP ξ hξ
    (mul_ne_zero_iff.mp hreg).1 (by simpa only [hPa] using hrel) p n hn hmin)
#print axioms solution
