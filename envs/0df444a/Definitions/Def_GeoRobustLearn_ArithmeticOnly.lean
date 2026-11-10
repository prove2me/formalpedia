-- Prove2me | Definitions.Def_GeoRobustLearn_ArithmeticOnly
-- name    : GeoRobustLearn_ArithmeticOnly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:26.464482+00:00
-- url     : https://prove2.me/theorems/75c6063f-3ee2-4bbb-89db-15a3ca2bb190
-- title:
--   Arithmetic-only real-RAM programs and the running-time budget of Theorem 6.1
-- statement:
--   The running time of the paper's learner is "measured in exact real-arithmetic operations". A program of the published real RAM of the companion mission is **arithmetic-only** if each of its instructions is a core instruction (exact $+,-,\times,\div$, rational literals, comparisons, loads, stores, pointer moves), a pointer-to-real cast, the drawing of one labelled example, or halt. It excludes $\sqrt{\cdot}$, $\exp$, $\log$, $\Phi^{-1}$ and Gaussian draws.
--
--   For a constant $C\in\mathbb N$, the budget is
--
--   $$R=(d+1)^{C\,(K^2/\varepsilon^2+K^4r^2/\varepsilon^4)\,(\log(2+K/\varepsilon+1/(Kr)))^{C}}\cdot(\log(2/\delta))^{C},$$
--
--   the reading of $(d+1)^{O(k)}\,\mathrm{poly}(\log 1/\delta)$ with $k=\tilde O(K^2/\varepsilon^2+K^4r^2/\varepsilon^4)$, the suppressed logarithmic factors depending on $K$, $1/\varepsilon$ and $1/(Kr)$.
--
--   **Formalization Note** Each excluded instruction would be an extra unit-cost primitive and make the theorems weaker. The predicate restricts only the program chosen under "there is an algorithm".
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Theorem 6.1, pp.30–31; Appendix B, p.47

import Definitions.Def_GeoLipLearn_Agnostic_Machine

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-!
# Arithmetic-only programs and the running-time bound of Theorem 6.1

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…): Theorem 6.1, pp.30–31 ("running time, measured in exact real-arithmetic
operations"), Appendix B, p.47.

**Formalization Note.** The machine is the published real RAM `GeoLipLearn.Agnostic.Machine` of
Part II of the series. `ArithmeticOnly` keeps only its core instructions (exact `+ − × ÷` with
rational literals by `Admissible`, comparisons, loads, stores, pointer moves), the pointer-to-real
cast, `sample` and `halt`; it excludes `√`, `exp`, `log`, `Φ⁻¹` and Gaussian draws, each of which
would be an extra unit-cost primitive and weaken the theorem.
-/

/-- Every instruction is a core real-RAM instruction, a pointer-to-real cast, `sample` or `halt`. -/
def ArithmeticOnly (P : Program) : Prop :=
  ∀ i ∈ P, (∃ c, i = .core c) ∨ (∃ a b, i = .pointerReal a b) ∨ (∃ a, i = .sample a) ∨
    (∃ a, i = .halt a)

/-- The budget `R = (d+1)^{C (K²/ε² + K⁴r²/ε⁴) (log(2 + K/ε + 1/(Kr)))^C} · (log(2/δ))^C`,
the reading of `(d+1)^{O(k)} poly(log 1/δ)`, `k = Õ(K²/ε² + K⁴r²/ε⁴)` with the suppressed logarithmic
factors depending on `K`, `1/ε`, `1/(Kr)` (Theorem 6.1, p.31). -/
noncomputable def robustBound (C d : ℕ) (K r ε δ : ℝ) : ℝ :=
  (d + 1 : ℝ) ^ ((C : ℝ) * (K ^ 2 / ε ^ 2 + K ^ 4 * r ^ 2 / ε ^ 4) *
      (Real.log (2 + K / ε + 1 / (K * r))) ^ C) * (Real.log (2 / δ)) ^ C

end GeoRobustLearn


