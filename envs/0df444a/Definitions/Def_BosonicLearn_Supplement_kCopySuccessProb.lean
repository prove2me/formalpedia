-- Prove2me | Definitions.Def_BosonicLearn_Supplement_kCopySuccessProb
-- name    : BosonicLearn_Supplement_kCopySuccessProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:01:05.614848+00:00
-- url     : https://prove2.me/theorems/dfac2ae3-6a22-4a41-b32c-a475ce0c8ca8
-- title:
--   Success probability of an adaptive $k$-copy learner
-- statement:
--   Let $\mathcal A$ be an adaptive $k$-copy protocol with $R$ rounds and budget $N$ and outcomes in $\mathcal O$, and let $\hat\rho$ be an **estimator**: a Markov kernel from transcripts $x\in\mathcal O^R$ to density operators on $\ell^2(\mathbb N^n)$ (a randomized post-processing). For a state $\rho$ and a precision $\varepsilon$, the success probability is
--
--   $$p_{\mathcal A,\hat\rho}(\rho,\varepsilon)=\Pr_{x\sim T_\rho,\ \hat\rho\sim\hat\rho(x)}\Big[\tfrac12\|\hat\rho-\rho\|_1\le\varepsilon\Big],$$
--
--   where $T_\rho$ is the law of the full transcript when every round acts on fresh copies of $\rho$ (the round laws composed in order).
--
--   A protocol **learns** a class of states to precision $\varepsilon$ with probability $2/3$ when $p_{\mathcal A,\hat\rho}(\rho,\varepsilon)\ge 2/3$ for every state $\rho$ of the class.
--
--   **Formalization Note** It is the base mission's `successProb` with the single-copy scheme replaced by a $k$-copy protocol; the transcript law is the base `sequentialLaw` of the round kernels.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 4, p. 23; §4, p. 19; footnote 1, p. 3

import Mathlib
import Definitions.Def_BosonicLearn_Supplement_KCopyScheme
import Definitions.Def_BosonicLearn_sequentialLaw
import Definitions.Def_BosonicLearn_traceDist

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn.Supplement

/-- **Success probability of an adaptive `k`-copy learner.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705,
Theorem 4, p. 23 ("learns every n-mode Gaussian state to trace-distance error ε with probability at least 2/3, using
only k-copy measurements") with the model of §4, p. 19.

For a `k`-copy protocol `S` with `R` rounds, outcomes in `O`, a (possibly randomized) estimator `est`, a Markov kernel from
transcripts to density operators, a state `ρ` and `ε`, `kCopySuccessProb S est ρ ε` is the probability, over the
transcript `x ∼ T_ρ` (the rounds composed in order, each on fresh copies of `ρ`, via `BosonicLearn.sequentialLaw`)
and the estimator's internal randomness, that `½‖ρ̂ − ρ‖₁ ≤ ε`.

**Formalization Note.** It is `BosonicLearn.successProb` with the single-copy scheme replaced by a `k`-copy one;
the estimator must be a Markov kernel in every statement that uses this quantity. -/
noncomputable def kCopySuccessProb {n k R N : ℕ} {O : Type} [MeasurableSpace O] (S : KCopyScheme n k R N O)
    (est : Kernel (Fin R → O) (State (Occupation (Fin n))))
    (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, est x {σ | traceDist σ.coefficients ρ ≤ ENNReal.ofReal ε} ∂(sequentialLaw (S.round ρ) R le_rfl)

end BosonicLearn.Supplement


