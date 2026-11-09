-- Prove2me | Definitions.Def_BosonicLearn_successProb
-- name    : BosonicLearn_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:29:41.573386+00:00
-- url     : https://prove2.me/theorems/8dea4f62-20d5-4da4-99f6-7333887f1d72
-- title:
--   Success probability of an adaptive single-copy learner
-- statement:
--   Let $S$ be an adaptive single-copy scheme on $N$ copies and let the estimator $\hat\rho$ be a Markov kernel from transcripts to density operators (internal randomness allowed). For a state $\rho$ and $\varepsilon>0$,
--
--   $$\Pr_{x\sim\mathcal T_\rho,\ \hat\rho}\Big[\tfrac12\|\hat\rho(x)-\rho\|_1\le\varepsilon\Big]$$
--
--   is the probability that the protocol learns $\rho$ to trace distance $\varepsilon$. Theorem 3 asks that it be at least $2/3$ for every state in the promise class.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 3, pp. 6–7; Eq. (105), p. 40

import Mathlib
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_traceDist

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn

/-- **Success probability of an adaptive single-copy learner.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 3, pp. 6–7 ("learn ρ to ε trace distance with probability at least 2/3 using single-copy
measurements") and Eq. (105), p. 40 ("the state estimator ρ̂(x) that allows internal randomness").

For an adaptive scheme `S` with outcomes in `O`, a (possibly randomized) estimator `est`, a Markov kernel from
transcripts to density operators, a state `ρ` and `ε`, `successProb S est ρ ε` is the probability, over the
transcript `x ∼ T_ρ` and the estimator's internal randomness, that `½‖ρ̂ − ρ‖₁ ≤ ε`.

**Formalization Note.** The success set `{σ | ½‖σ − ρ‖₁ ≤ ε}` is a countable intersection of open trace-norm
balls of `Dependency50.P33`'s state topology, hence Borel; the estimator must be a Markov kernel in every
statement that uses this quantity. -/
noncomputable def successProb {n N : ℕ} {O : Type} [MeasurableSpace O] (S : AdaptiveScheme n N O)
    (est : Kernel (Fin N → O) (State (Occupation (Fin n))))
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, est x {σ | traceDist σ.coefficients ρ ≤ ENNReal.ofReal ε} ∂(transcriptLaw S ρ)

end BosonicLearn


