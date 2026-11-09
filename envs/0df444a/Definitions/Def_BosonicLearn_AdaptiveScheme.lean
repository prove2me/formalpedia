-- Prove2me | Definitions.Def_BosonicLearn_AdaptiveScheme
-- name    : BosonicLearn_AdaptiveScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:20:25.859383+00:00
-- url     : https://prove2.me/theorems/5c1b1c73-0276-485d-811d-a27045d1e9c8
-- title:
--   Adaptive single-copy measurement scheme on $N$ copies
-- statement:
--   An **adaptive single-copy scheme** on $N$ copies of an $n$-mode state, with outcomes in a measurable space $\mathcal O$, chooses for each round $t<N$ and each record $x_{<t}$ of earlier outcomes a POVM $M^{(x_{<t})}$ on the $n$-mode Fock space, which is applied to a fresh copy. No quantum memory is kept between rounds. On a state $\rho$ the outcome of round $t$ has the Born law of $M^{(x_{<t})}$ on $\rho$, which is required to depend measurably on $x_{<t}$.
--
--   This is the measurement model of the lower bounds (Theorems 3 and 5): every non-entangled protocol, adaptive or not, Gaussian or not, with discrete or continuous outcomes.
--
--   **Formalization Note** Randomized choices of POVM need no extra field: a round may output a random seed with its outcome. The classical estimator is a separate kernel.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §4, p. 19; §5.1, p. 30

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open MeasureTheory ProbabilityTheory

namespace BosonicLearn

/-- **Adaptive single-copy measurement scheme on `N` copies of an `n`-mode state.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §4, p. 19 ("the choice of POVM may depend on all previous classical outcomes. No quantum system is
retained") and §5.1, p. 30: "A non-entangled adaptive learning protocol on N copies can be specified by a
family of sequences of POVMs {M_{x_1}}, …, {M^{(x_{<t})}_{x_t}}, … Here, the t-th POVM can depend on the first
t − 1 measurement outcomes x_{<t}."

An `AdaptiveScheme n N O` gives, for every round `t < N` and every record `x : Fin t → O` of earlier outcomes,
a POVM `povm t x` on the `n`-mode Fock space with outcomes in the measurable space `O`, applied to a fresh
copy. `round ρ t` is the round-`t` outcome law as a Markov kernel in the earlier outcomes; on a density `ρ` it is
the Born law of `povm t x` on `ρ`.

**Formalization Note.** Measurability of the round laws in the earlier outcomes is the kernel structure of
`round`; it is what makes the transcript a random variable. On arrays that are not densities `round` is an
arbitrary Markov kernel. Randomized choices of POVM need no extra field: a round may output a random seed
along with its outcome, and `O` is an arbitrary measurable space (continuous outcomes such as heterodyne are
included). The classical post-processing (the estimator) is a separate kernel, see `successProb`. -/
structure AdaptiveScheme (n N : ℕ) (O : Type) [MeasurableSpace O] where
  /-- the POVM of round `t` after the earlier outcomes `x` -/
  povm : (t : Fin N) → (Fin t → O) → FockPOVM (Occupation (Fin n)) O
  /-- the round-`t` outcome law on the state `ρ`, as a kernel in the earlier outcomes -/
  round : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ → (t : Fin N) → Kernel (Fin t → O) O
  /-- each round kernel is Markov -/
  round_markov : ∀ ρ t, IsMarkovKernel (round ρ t)
  /-- on densities the round law is the Born law of the chosen POVM -/
  round_born : ∀ ρ, IsDensity ρ → ∀ (t : Fin N) (x : Fin t → O), round ρ t x = (povm t x).law ρ

end BosonicLearn


