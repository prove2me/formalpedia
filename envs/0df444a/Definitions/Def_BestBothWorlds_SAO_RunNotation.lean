-- Prove2me | Definitions.Def_BestBothWorlds_SAO_RunNotation
-- name    : BestBothWorlds_SAO_RunNotation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:32:41.88264+00:00
-- url     : https://prove2.me/theorems/e73f5ffb-8808-4384-9f2d-af2adaf28ade
-- title:
--   Run quantities of SAO: τ₀, τᵢ ← min(τᵢ, τ₀), qᵢ = p_{i,min(τᵢ,τ₀)} (§4)
-- statement:
--   This file defines the notation of §4 (p. 14) for a single run of SAO, with parameter $\beta$, against a fixed adversary and along a fixed arm path.
--
--   1. $\tau_0$ is the last time step before Exp3.P is started, with the convention $\tau_0=n$ if Exp3.P is never started.
--   2. $\tau_i$ denotes $\min(\tau_i,\tau_0)$: the smaller of the time arm $i$ is deactivated ($n$ if never) and $\tau_0$.
--   3. $q_i:=p_{i,\min(\tau_i,\tau_0)}$, the probability of arm $i$ at that time. If $\tau_i<\tau_0$ this is the probability of arm $i$ when it was deactivated.
--
--   The file also names the two bounds that recur in Lemmas 4.5 and 4.7 and in (21)–(24). For a logarithmic factor $L$ they are
--   $$r_i(t,L)=\sqrt{4\Big(\frac{K\min(\tau_i,t)}{t^2}+\frac{\max(t-\tau_i,0)}{q_i\tau_i t}\Big)L+5\Big(\frac{K L}{\min(\tau_i,t)}\Big)^2}$$
--   and
--   $$b_i(t,L)=q_i\tau_i(1+\log t)+\sqrt{4q_i\tau_i(1+\log t)L+5L^2}.$$
--
--   All these quantities are computed from the run itself, never assumed.
--
--   **Formalization Note** A test that fires on round $t$ starts Exp3.P on round $t+1$, so $\tau_0=t$. Then $\tau_0\ge1$, every $\tau_i\ge1$, and $q_i>0$, so neither bound divides by zero for $t\ge1$.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 14, §4 (notation); p. 15, Lemma 4.5; p. 16, Lemma 4.7

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Algorithm

namespace BestBothWorlds.SAO

/-- SAO's internal state at the end of round `t` of the run along the arm path `I` against
`adv`. -/
noncomputable def runState (K n : ℕ) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) (t : ℕ) :
    SAOState K :=
  saoState K n β ((history adv I).take t)

/-- `τ₀`, the last time step before Exp3.P is started, with `τ₀ = n` if Exp3.P is never started
(§4, p. 14). -/
noncomputable def tau0 (K n : ℕ) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) : ℕ :=
  match (runState K n β adv I n).tau0 with
  | some τ => τ
  | none => n

/-- `τ_i ← min(τ_i, τ₀)`: the minimum of the time arm `i` is deactivated (`n` if never) and `τ₀`
(§4, p. 14). -/
noncomputable def tauEff (K n : ℕ) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) (i : Fin K) :
    ℕ :=
  min ((runState K n β adv I n).tau i) (tau0 K n β adv I)

/-- `q_i := p_{i, min(τ_i, τ₀)}` (§4, p. 14). -/
noncomputable def qEff (K n : ℕ) (β : ℝ) (adv : Adversary K) (I : Fin n → Fin K) (i : Fin K) :
    ℝ :=
  probAt (sao K n β) adv I (tauEff K n β adv I i) i

/-- The confidence radius of Lemma 4.5 and of (21)–(22), with `L` in place of the logarithm:
`√(4 (K min(τ, t)/t² + max(t - τ, 0)/(q τ t)) L + 5 (K L / min(τ, t))²)`. -/
noncomputable def estRadius (K : ℕ) (τ : ℕ) (q : ℝ) (t : ℕ) (L : ℝ) : ℝ :=
  Real.sqrt (4 * (K * (min τ t : ℕ) / (t : ℝ) ^ 2 + max ((t : ℝ) - τ) 0 / (q * τ * t)) * L +
    5 * (K * L / (min τ t : ℕ)) ^ 2)

/-- The bound of Lemma 4.7 and of (24), with `L` in place of the logarithm:
`q τ (1 + log t) + √(4 q τ (1 + log t) L + 5 L²)`. -/
noncomputable def pullBound (q : ℝ) (τ t : ℕ) (L : ℝ) : ℝ :=
  q * τ * (1 + Real.log t) + Real.sqrt (4 * q * τ * (1 + Real.log t) * L + 5 * L ^ 2)

end BestBothWorlds.SAO


