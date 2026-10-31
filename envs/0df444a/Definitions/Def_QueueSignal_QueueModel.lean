-- Prove2me | Definitions.Def_QueueSignal_QueueModel
-- name    : QueueSignal_QueueModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:44.820561+00:00
-- url     : https://prove2.me/theorems/f78979f0-ada0-4484-bb56-60c3c529067a
-- title:
--   Queue-disclosure game with uninformed customers: Naor threshold $n(d)$, effective arrival rates $\lambda^O(d)$ (1) and $\lambda^U(d)$ (3), server payoffs
-- statement:
--   This module defines the queueing primitives of §3.1 and §4.1 of Guo, Haviv, Luo and Wang.
--
--   1. **Parameters.** A single server with exponential service at rate $\mu$; customers arrive as a Poisson process with potential arrival rate $\lambda$; each customer pays $\theta$ per unit time in the system and receives $V_H$ from a high-quality server, $V_L$ from a low-quality one; the server is of high quality with prior probability $\delta$. The standing assumptions are $\mu>0$, $\theta>0$, $V_H>V_L>\theta/\mu$ and $0<\delta<1$. The potential arrival rate $\lambda$ is kept as a separate variable, and $\rho=\lambda/\mu$.
--   2. **Expected reward** at belief $d$: $\bar V(d)=dV_H+(1-d)V_L$.
--   3. **Naor threshold** (p.548):
--   $$n(d)=\Big\lfloor \frac{[dV_H+(1-d)V_L]\mu}{\theta}\Big\rfloor-1 .$$
--   4. **Observable queue**, (1): the effective arrival rate of the $M/M/1/(n+1)$ queue with $n=n(d)$,
--   $$\lambda^O(d)=\frac{\lambda\sum_{k=0}^{n(d)}\rho^k}{\sum_{i=0}^{n(d)+1}\rho^i}.$$
--   5. **Unobservable queue**, (3):
--   $$\lambda^U(d)=\begin{cases}\lambda,&\text{if }\lambda<\mu-\theta/[dV_H+(1-d)V_L],\\ \mu-\theta/[dV_H+(1-d)V_L],&\text{otherwise.}\end{cases}$$
--   6. **Server payoffs** in the baseline of §4 (all customers uninformed): the server's reward per served customer is normalized to $1$, so a server that reveals the queue while the customers hold belief $d$ after $R$ earns $\lambda^O(d)$, and one that conceals it under belief $d$ after $C$ earns $\lambda^U(d)$, whatever its type.
--
--   These are the payoffs of the signaling game of `QueueSignal.SignalingGame` in which Proposition 1 is stated.
--
--   **Formalization Note** Every rate is a function of $\lambda$ and of the belief. $n(d)$ is computed in $\mathbb Z$, so the $-1$ is exact, and enters the sums through `Int.toNat`; under the standing assumptions and $d\in[0,1]$ it is nonnegative, so the conversion is exact. The first branch of (3) keeps the strict inequality as printed (both branches agree at equality).
-- source:
--   Guo, Haviv, Luo, Wang, Signaling Service Quality Through Queue Disclosure, MSOM 25(2) (2023), doi:10.1287/msom.2022.1170, §3.1, p.546; §4.1, threshold n(δ^R) and eqs. (1), (3), p.548; §4.2, p.548 (payoffs)

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame

namespace QueueSignal

/-- The fixed parameters of the queue-disclosure signaling game (Guo, Haviv, Luo, Wang,
*Signaling Service Quality Through Queue Disclosure*, MSOM 25(2) (2023),
doi:10.1287/msom.2022.1170, §3.1, p.546, PDF p.5): service rate `μ` (exponential service),
waiting cost `θ` per unit time in the system, rewards `V_H` (high quality) and `V_L` (low
quality), and prior `δ` of the high-quality type. The potential arrival rate `λ` is **not** a
field: every rate below is a function of `λ`, the variable of Proposition 1. -/
structure Params where
  /-- service rate `μ` -/
  μ : ℝ
  /-- waiting cost `θ` per unit time in the system -/
  θ : ℝ
  /-- reward `V_H` from a high-quality server -/
  VH : ℝ
  /-- reward `V_L` from a low-quality server -/
  VL : ℝ
  /-- prior probability `δ` that the server is of high quality -/
  δ : ℝ

/-- The standing assumptions of §3.1 (p.546, PDF p.5): `μ > 0`, `θ > 0`,
`V_H > V_L > θ/μ` and `0 < δ < 1`. (The arrival rate `λ > 0` is assumed separately in each
statement.) -/
def Params.Valid (P : Params) : Prop :=
  0 < P.μ ∧ 0 < P.θ ∧ P.θ / P.μ < P.VL ∧ P.VL < P.VH ∧ 0 < P.δ ∧ P.δ < 1

/-- The expected reward `V̄(d) = d V_H + (1 − d) V_L` of a customer who believes the server is of
high quality with probability `d` (p.548, PDF p.7, inside `n(δ^R)`, (2) and (3)). -/
def Params.Vbar (P : Params) (d : ℝ) : ℝ :=
  d * P.VH + (1 - d) * P.VL

/-- Naor's joining threshold `n(d) := ⌊[d V_H + (1 − d) V_L] μ/θ⌋ − 1` (§4.1, p.548, PDF p.7):
uninformed customers with belief `d` join a revealed queue iff the queue length on arrival
(including the one in service) does not exceed `n(d)`.

**Formalization Note.** Computed in `ℤ` (so the `− 1` is exact). Under `V_L > θ/μ` and
`d ∈ [0, 1]` it is `≥ 0`; it is converted to `ℕ` with `Int.toNat` where it is used as a
summation bound. -/
noncomputable def Params.naorN (P : Params) (d : ℝ) : ℤ :=
  ⌊P.Vbar d * P.μ / P.θ⌋ - 1

/-- The customers' effective arrival rate to the **observable** (revealed) queue, (1) (§4.1,
p.548, PDF p.7): with `ρ = λ/μ` and `n = n(d)`,
`λ^O(d) = λ Σ_{k=0}^{n} ρ^k / Σ_{i=0}^{n+1} ρ^i`,
the throughput of the `M/M/1/(n + 1)` queue.

**Formalization Note.** `λ` is the explicit argument `lam`; `n(d)` enters through
`Int.toNat`, which is exact for beliefs in `[0, 1]` under `Params.Valid`. -/
noncomputable def lamO (P : Params) (lam d : ℝ) : ℝ :=
  lam * (∑ k ∈ Finset.range ((P.naorN d).toNat + 1), (lam / P.μ) ^ k) /
    ∑ i ∈ Finset.range ((P.naorN d).toNat + 2), (lam / P.μ) ^ i

/-- The customers' effective arrival rate to the **unobservable** (concealed) queue, (3) (§4.1,
p.548, PDF p.7): `λ^U(d) = λ` if `λ < μ − θ/[d V_H + (1 − d) V_L]`, and
`μ − θ/[d V_H + (1 − d) V_L]` otherwise (strict `<` in the first branch, as printed). -/
noncomputable def lamU (P : Params) (lam d : ℝ) : ℝ :=
  if lam < P.μ - P.θ / P.Vbar d then lam else P.μ - P.θ / P.Vbar d

/-- The server's payoff in the baseline game of §4 (all customers uninformed), pp.546 and 548
(PDF pp.5, 7): the server's reward per customer served is normalized to `1`, so its payoff is
the customers' effective arrival rate. A server that sends `R` while the customers hold the
belief `d` after `R` gets `λ^O(d)`; one that sends `C` under belief `d` after `C` gets
`λ^U(d)`. With all customers uninformed the payoff does not depend on the type `t`
(`π_{i,H} = π_{i,L}`, p.548).

**Formalization Note.** This encodes the customers' equilibrium play (Naor's threshold rule in
the revealed queue, the joining probability (2) in the concealed queue) by its effective
arrival rate, the reduction the paper makes on p.548. -/
noncomputable def pay (P : Params) (lam : ℝ) : QType → Sig → ℝ → ℝ
  | _, .R, d => lamO P lam d
  | _, .C, d => lamU P lam d

end QueueSignal


