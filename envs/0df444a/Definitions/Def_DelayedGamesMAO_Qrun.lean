-- Prove2me | Definitions.Def_DelayedGamesMAO_Qrun
-- name    : DelayedGamesMAO_Qrun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:52.444216+00:00
-- url     : https://prove2.me/theorems/8e2237d0-8c07-430e-ba14-c489d8ff7370
-- title:
--   Running maximum $Q_t=\max_{s\in[t]}q_s$, $Q_0=0$
-- statement:
--   For a delay sequence, $Q_t=\max_{s\in[t]}q_s$ for $t\ge1$ and $Q_0=0$: the largest number of active rounds seen up to round $t$.
--
--   **Formalization Note** The formula is used for every $t$. The coefficients (8) read $\beta_{T+1}$ and hence $Q_{T+1}$, which the paper leaves undefined; the formula gives $Q_{T+1}=\max(Q_T,q_{T+1})=Q_T=q_{\max}$ when every feedback arrives by the end of round $T$ (then $q_{T+1}=1$), which is the value the proof of Theorem 5 uses.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, p.11

import Mathlib
import Definitions.Def_DelayedGamesMAO_q

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Running maximum of active rounds** `Q_t := max_{s ∈ [t]} q_s`, `Q_0 = 0`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, p.11: "let `Q_t := max_{s∈[t]} q_s` for every `t ∈ [T]` with `Q_0 = 0`".

**Formalization Note.** The same formula is used for every `t` (`Finset.sup` over
`Finset.Icc 1 t`, which is `0` at `t = 0`). The paper's (8) also uses `β_{T+1}`, hence
`Q_{T+1}`, which it leaves undefined; the formula gives `Q_{T+1} = max(Q_T, q_{T+1}) = Q_T`
when every feedback arrives by the end of round `T` (then `q_{T+1} = 1`), which is the value
`Q_{T+1} = q_max` the proof of Theorem 5 uses. -/
def Qrun (d : ℕ → ℕ) (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).sup (q d)

end DelayedGamesMAO


