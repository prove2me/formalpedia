-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_agreeProb
-- name    : QAdvFew_PoQOracle_agreeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:55:21.935899+00:00
-- url     : https://prove2.me/theorems/24ed13bf-d8f7-4d4d-b73f-e187e4f7c096
-- title:
--   The probability in Lemma 4.9
-- statement:
--   The probability
--   $$
--   \Pr_{O=(A,B,C)\leftarrow\mathcal D',\ x\leftarrow\mathrm{Samp}^A(1^n)}\bigl[M^O(x)=f^A_n(x)\bigr]
--   $$
--   for $\mathcal D'=\mathcal D$ or $\mathcal D^{(n)}$: the seed is drawn first, then $x$ from $\mathrm{Samp}$ applied to the $A$ part, and the event is that the output of the machine after $T$ steps with the joined oracle equals $f^A_n(x)$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 4.9, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_sampleABC

open MeasureTheory QAlgorithms.Complexity
open scoped ENNReal

namespace QAdvFew.PoQOracle

open Classical in
/-- The probability `Pr_{O=(A,B,C)←D', x←Samp^A(1^n)}[M^O(x) = f^A_n(x)]` of Lemma 4.9 (Goldin,
Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Lemma 4.9,
p. 24 (PDF p. 26)), for `D' = D` (`cut = ⊤`) or `D' = D^(n)` (`cut = n`): the seed is drawn from
`seedMeasure F`, then `x ∈ {0,1}^s` from `Samp A`, and the event is that the output of the oracle
machine `M`, run for `T` steps with the joined oracle, is `f A x`. -/
noncomputable def agreeProb (F : (N : ℕ) → PMF (Fin N → Bool)) (cut : ℕ∞) (s q : ℕ)
    (f : Oracle → (Fin s → Bool) → (Fin q → Bool)) (Samp : Oracle → PMF (Fin s → Bool))
    (M : OTM) (T : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ x : Fin s → Bool, Samp (sampleABC cut ω).1 x *
      (if M.output (sampleO cut ω) (List.ofFn x) T = List.ofFn (f (sampleABC cut ω).1 x)
        then 1 else 0) ∂(seedMeasure F)

end QAdvFew.PoQOracle


