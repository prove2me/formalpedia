-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_valueFunction
-- name    : BauerleRiederMDP_RegimeSwitching_valueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:47.001083+00:00
-- url     : https://prove2.me/theorems/235bcc3f-d80b-451d-9d4a-e976d8e6a640
-- title:
--   Value function $V_n(x)=\sup_\pi V_{n\pi}(x)$
-- statement:
--   The **value function** of an $N$-stage Markov Decision Model with terminal reward $g_N$ is
--
--   $$
--   V_n(x)=\sup_{\pi}V_{n\pi}(x),\qquad x\in E,
--   $$
--
--   the supremum over all Markov policies whose rules $f_n,\dots,f_{N-1}$ are admissible. A policy is optimal for the $N$-stage problem if $V_{0\pi}=V_0$.
--
--   **Formalization Note** The supremum is taken in $[-\infty,\infty]$, so an unbounded problem has value $+\infty$. Markov policies suffice by Theorem 2.2.3.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.18 (PDF p.33); Theorem 2.2.3, p.19 (PDF p.34)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_MarkovPolicy_IsAdmissible
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_policyValue

namespace BauerleRiederMDP.RegimeSwitching

/-- The **value function** `V_n(x) = sup_π V_{nπ}(x)` of the `N`-stage problem with terminal
reward `g = g_N` (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.18, PDF p.33), the supremum over all Markov policies whose decision
rules `f_n, …, f_{N-1}` are admissible.

**Formalization Note.** The supremum is taken in `EReal`, so an unbounded problem has value
`⊤` rather than a junk value. Markov policies suffice by Theorem 2.2.3 (p.19). -/
noncomputable def valueFunction {E A Z : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [MeasurableSpace Z] (M : DisturbanceMDM E A Z) (g : E → ℝ) (N n : ℕ) (x : E) : EReal :=
  ⨆ (π : MarkovPolicy E A) (_ : π.IsAdmissible M n N), policyValue M g N π n x

end BauerleRiederMDP.RegimeSwitching


