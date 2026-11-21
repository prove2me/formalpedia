-- Prove2me | Definitions.Def_MasulloAudit_Chapter13Scalar
-- name    : MasulloAudit_Chapter13Scalar
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T01:51:43.296884+00:00
-- url     : https://prove2.me/theorems/a8f9efd4-11d8-4c33-ad21-b86d91cd97df
-- title:
--   Rational scalar terms of Masullo’s Chapter 13 trace
-- statement:
--   The scalar norm test of a shrinking compact real function, the degree-one capped critical-line sum, the two polar Mellin values, and the local test functions in the real and rational finite-place principal values of Chapter 13. The real cutoff is written in the additive coordinate of (B.4.3.13).
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, pp. 519, 522, Eqs. (12.5.1.1), (13.3.1.1)–(13.3.1.5), and Appendix B, (B.4.3.13), (B.4.4.1)–(B.4.4.2), (B.4.4.16). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The shrinking-test obstruction was pointed out by Calvin Yost-Wolff in the Prove2Me discussion of Theorem 13.3.1.1.

import Mathlib

open MeasureTheory Set

namespace MasulloAudit

noncomputable def shrinkingRadialTest (h : ℝ → ℝ) (ε : ℝ) (t : ℝ) : ℂ :=
  if 0 < t then (h (Real.log t / ε) : ℂ) else 0

def CriticalZetaZeroSet : Set ℂ := {ρ | ρ.re = 1 / 2 ∧ riemannZeta ρ = 0}

noncomputable def rationalCappedSpectralTerm (h : ℝ → ℝ) (ε : ℝ)
    (ρ : CriticalZetaZeroSet) : ℝ :=
  ((min (analyticOrderNatAt riemannZeta ρ.val) (1 : ℕ) : ℕ) : ℝ) *
    (mellin (shrinkingRadialTest h ε) (ρ.val - (1 / 2 : ℂ))).re

noncomputable def rationalPolarPair (h : ℝ → ℝ) (ε : ℝ) : ℝ :=
  (mellin (shrinkingRadialTest h ε) (1 / 2 : ℂ) +
    mellin (shrinkingRadialTest h ε) (-1 / 2 : ℂ)).re

noncomputable def padicShiftedRadialTest {p : ℕ} [Fact p.Prime] (φ : ℝ → ℂ) (x : ℚ_[p]) : ℂ :=
  φ ‖1 + x‖ * (Real.exp (-Real.log ‖1 + x‖ / 2) : ℂ)

noncomputable def shiftedRealRadialTest (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = -1 then 0 else h (Real.log |1 + x|) * Real.exp (-Real.log |1 + x| / 2)

noncomputable def cutoffRealPlaceTranslated (h : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in {x | δ ≤ |x|}, shiftedRealRadialTest h x / |x|) + 2 * h 0 * Real.log δ

end MasulloAudit


