-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_policyValue
-- name    : BauerleRiederMDP_RegimeSwitching_policyValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:00.19427+00:00
-- url     : https://prove2.me/theorems/0a47ffb0-9f46-450a-9ae3-44958280dc7c
-- title:
--   Expected total reward $V_{n\pi}(x)$ of a Markov policy
-- statement:
--   For an $N$-stage problem with terminal reward $g_N$, the **expected total reward** of the Markov policy $\pi=(f_k)$ from state $x$ at time $n\le N$ is
--
--   $$
--   V_{n\pi}(x)=\mathbb E^\pi_{nx}\Big[\sum_{k=n}^{N-1}r_k\big(X_k,f_k(X_k)\big)+g_N(X_N)\Big]\in[-\infty,\infty],
--   $$
--
--   the expectation taken under the path law $\mathbb P^\pi_{nx}$ with the extended-real expectation.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.18 (PDF p.33)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_pathMeasure
open MeasureTheory ProbabilityTheory Finset

namespace BauerleRiederMDP.RegimeSwitching

/-- The expected total reward of the Markov policy `π` from state `x` at time `n` up to the
horizon `N` with terminal reward `g = g_N` (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.18, PDF p.33):
`V_{nπ}(x) = 𝔼^π_{nx}[∑_{k=n}^{N-1} r_k(X_k, f_k(X_k)) + g_N(X_N)]`.

**Formalization Note.** The expectation is `eint` (values in `[-∞, ∞]`, no junk value) over
`pathMeasure M π n x`, whose coordinate `l` is `X_{n+l}`. Meaningful for `n ≤ N`. -/
noncomputable def policyValue {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (M : DisturbanceMDM E A Z) (g : E → ℝ) (N : ℕ)
    (π : MarkovPolicy E A) (n : ℕ) (x : E) : EReal :=
  eint (pathMeasure M π n x) (fun ω =>
    ((∑ l ∈ range (N - n), M.r (n + l) (ω l, π.f (n + l) (ω l)) + g (ω (N - n)) : ℝ) : EReal))

end BauerleRiederMDP.RegimeSwitching


