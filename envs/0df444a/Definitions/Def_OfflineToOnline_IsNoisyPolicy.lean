-- Prove2me | Definitions.Def_OfflineToOnline_IsNoisyPolicy
-- name    : OfflineToOnline_IsNoisyPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:21.385689+00:00
-- url     : https://prove2.me/theorems/67553581-c89e-420b-9637-c205d918da41
-- title:
--   Noisy (adapted) parameter policy of Definition 6
-- statement:
--   In Definition 6 a hypothetical variant of Algorithm 1 chooses "noisy" update parameters $\tilde\theta_t^{(i)}$ instead of locally optimal ones. A **noisy policy** for $T$ runs is a family $\tilde\theta_t^{(i)}$ of random parameters such that
--
--   1. every $\tilde\theta_t^{(i)}$ takes values in $\Theta$;
--   2. every $\tilde\theta_t^{(i)}$ is a measurable function of the seeds;
--   3. $\tilde\theta_t^{(i)}$ is **adapted**: it depends only on the seeds revealed before $\textsc{Local-update}$ is called in subproblem $i$ of run $t$, that is on $\omega_{s,j}$ with $s<t$, or $s=t$ and $j<i$.
--
--   The policy may depend on the whole sequence $f_1,\dots,f_T$, which is fixed in advance.
--
--   **Formalization Note** Definition 6 does not say what $\tilde\theta_t^{(i)}$ may depend on. A variant of Algorithm 1 chooses each parameter from the random past of its run, so the parameters are read as adapted random variables. Indices are $0$-indexed.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Definition 6, p.16

import Mathlib
import Definitions.Def_OfflineToOnline_IGInstance

namespace OfflineToOnline

/-- A "noisy" parameter policy of the hypothetical variant of Algorithm 1 in Definition 6, p.16:
`θ t i ω = θ̃_t^(i+1)` takes values in `Θ`, is a measurable function of the seeds, and is adapted:
it depends only on the seeds revealed before Local-update of subproblem `i + 1` in run `t` is
called, i.e. on `ω s j` with `s < t`, or `s = t` and `j < i`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Definition 6, p.16.

Formalization Note: Definition 6 does not say what `θ̃_t^(i)` may depend on. A variant of
Algorithm 1 chooses its parameter from the (random) past of the run, so it is read as an adapted
random variable. It may depend on the whole sequence `f_1, …, f_T`, which is fixed in advance. -/
def IsNoisyPolicy {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω] {m d : ℕ}
    (I : IGInstance D Ω m d) (T : ℕ)
    (θ : Fin T → Fin I.N → (Fin T → Fin I.N → Ω) → Fin m → ℝ) : Prop :=
  (∀ t i ω, θ t i ω ∈ I.Θ) ∧ (∀ t i, Measurable (θ t i)) ∧
  ∀ t i (ω ω' : Fin T → Fin I.N → Ω),
    (∀ s j, (s < t ∨ (s = t ∧ j < i)) → ω s j = ω' s j) → θ t i ω = θ t i ω'

end OfflineToOnline


