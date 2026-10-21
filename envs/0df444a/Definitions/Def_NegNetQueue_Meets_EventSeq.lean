-- Prove2me | Definitions.Def_NegNetQueue_Meets_EventSeq
-- name    : NegNetQueue_Meets_EventSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:42.372104+00:00
-- url     : https://prove2.me/theorems/5f0650ed-8f9e-4f6b-a2e1-7197307cb15b
-- title:
--   §3, §4, pp. 6, 9 — the event sequence of an M/M/c/n queue with all servers busy; q = cµ/(λ+cµ) and ρ = λ/(cµ)
-- statement:
--   Consider an FCFS M/M/c/n service facility with arrival rate $\lambda>0$, service rate $\mu>0$ per server, $c\ge 1$ servers and a waiting room of capacity $n$. The **server utilization factor** is
--   $$\rho=\frac{\lambda}{c\mu},$$
--   and
--   $$q=\frac{c\mu}{\lambda+c\mu}=\frac{1}{1+\rho}$$
--   is the probability that the next change of the queue, while all $c$ servers are busy, is a service completion rather than an arrival.
--
--   An **event sequence** for these parameters on a probability space $(\Omega,\mathcal F,P)$ is a sequence $\varepsilon_0,\varepsilon_1,\dots$ of measurable, mutually independent random variables with values in $\{\mathrm{true},\mathrm{false}\}$ such that
--   $$P(\varepsilon_t=\mathrm{true})=q\qquad\text{for every } t .$$
--   The value true stands for a service completion and false for an arrival (which is lost if the waiting room is full).
--
--   This is the probabilistic input of every statement of the mission: the successive changes of the queue during a tagged customer's wait.
--
--   **Formalization Note.** While a customer waits, all $c$ servers are busy, so the next change is a completion with probability $c\mu/(\lambda+c\mu)$ independently of the past, by the memorylessness of the exponential clocks; the paper uses exactly this ("q … is the probability that the next change will be a service completion", p. 9). The reduction from the continuous-time queue to this i.i.d. sequence is disclosed, not formalized. $q$ is `qComp lam mu c` and $\rho$ is `rho lam mu c`; the parameters $\lambda,\mu,c$ are kept so that the statements read as on the page.
-- source:
--   Hassin, Meilijson & Perlman, Queueing with Negative Network Effects, SSRN 4097977 (version of July 2, 2022), p. 6 (§3, ρ = λ/(cµ)) and p. 9 (§4, q = cµ/(λ+cµ) = 1/(1+ρ))

import Mathlib

namespace NegNetQueue.Meets

open MeasureTheory ProbabilityTheory

/-- The probability `q = cµ/(λ + cµ)` that the next change of an M/M/c/n queue whose `c` servers
are all busy is a service completion (§4, p. 9). -/
noncomputable def qComp (lam mu : ℝ) (c : ℕ) : ℝ := c * mu / (lam + c * mu)

/-- The server utilization factor `ρ = λ/(cµ)` (§3, p. 6). -/
noncomputable def rho (lam mu : ℝ) (c : ℕ) : ℝ := lam / (c * mu)

/-- The event sequence of an M/M/c/n queue while all `c` servers are busy: an i.i.d. sequence of
`Bool`-valued random variables on `(Ω, P)`, where `true` is a service completion, with probability
`q = cµ/(λ + cµ)`, and `false` is an arrival (lost if the waiting room is full). -/
structure IsEventSeq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam mu : ℝ) (c : ℕ)
    (ε : ℕ → Ω → Bool) : Prop where
  isProb : IsProbabilityMeasure P
  meas : ∀ t, Measurable (ε t)
  indep : iIndepFun ε P
  law : ∀ t, P {ω | ε t ω = true} = ENNReal.ofReal (qComp lam mu c)

end NegNetQueue.Meets


