-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_stateLaw
-- name    : BauerleRiederMDP_LPDuality_stateLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:13.737706+00:00
-- url     : https://prove2.me/theorems/604baafa-e19d-4a0d-8a02-f4c8ce985b02
-- title:
--   Law $p_k$ of the state $X_k$ under a Markov policy started from $p$
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a stationary Markov Decision Model with infinite horizon, $p$ a measure on the state space $E$ and $\pi=(f_0,f_1,\dots)\in F^\infty$ a Markov policy. The **law of the state at time $k$** is defined recursively by
--   $$
--   p_0:=p,\qquad p_{k+1}(B):=\int Q\big(B\mid x,f_k(x)\big)\,p_k(dx),\quad B\subseteq E \text{ measurable}.
--   $$
--   When $p$ is the initial distribution, $p_k(B)=\mathbb P^\pi_p(X_k\in B)$.
--
--   These marginal laws are the building blocks of the discounted occupation measure $\mu_\pi$ that is feasible for the dual linear program (D).
--
--   **Formalization Note** The recursion uses `Measure.bind` with the kernel $x\mapsto Q(\cdot\mid x,f_k(x))$ instead of the Ionescu–Tulcea path measure; both give the same marginals. For a policy every $f_k$ is measurable.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.2, p.215 (PDF 226), the measure ℙ^π_p((X_k, A_k) ∈ B) in the definition of μ_π

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- The law `p_k` of the state `X_k` under a Markov policy `π = (f_0, f_1, …) ∈ F^∞` started
from the initial distribution `p` (Bäuerle & Rieder, *Markov Decision Processes with Applications
to Finance* (2011), §7.5.2, p.215, PDF 226, the measure `ℙ^π_p(X_k ∈ ·)` inside `μ_π`):
`p_0 := p` and `p_{k+1}(B) := ∫ Q(B | x, f_k(x)) p_k(dx)`.

**Formalization Note** The marginal laws are built by iterated `Measure.bind` with the kernel
`x ↦ Q(·|x, f_k(x))` rather than from the Ionescu–Tulcea path measure; the two give the same
marginals. `π k` is the decision rule `f_k`; for a policy (`IsPolicyOf`) every `f_k` is measurable,
so the bind is the genuine composition. -/
noncomputable def stateLaw {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (π : ℕ → E → A) (p : Measure E) : ℕ → Measure E
  | 0 => p
  | (k + 1) => (stateLaw M π p k).bind fun x => M.Q (x, π k x)

end BauerleRiederMDP.LPDuality


