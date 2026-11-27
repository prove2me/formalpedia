-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_state
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_state
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:16:37.449127+00:00
-- url     : https://prove2.me/theorems/46cdb331-eb2c-593d-baf9-fb2eaf724434
-- title:
--   The jump times and post-jump wealths $(T_n, Z_n)$
-- statement:
--   **The jump times and post-jump wealths $(T_n, Z_n)$** under a strategy (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, pp.281–282, PDF 291–292, wealth dynamics (9.10)): $T_0 = t$, $Z_0 = x$, and, if $S_n = T_{n+1} - T_n$ is the $n$-th sojourn time and $Y_{n+1}$ the jump height, $T_{n+1} = T_n + S_n$ and $Z_{n+1} = \varphi ^{\alpha }_{S_n}(Z_n)(1 + \alpha _{S_n} \cdot  Y_{n+1})$, where $\alpha  = f_n(\dots )$ is the control function used after $T_n$.
--
--   **Formalization Note.** $\omega  n = (S_n, Y_{n+1})$ (0-indexed). The fractions at the jump are those of the predictable control at $t = T_{n+1} \in  (T_n, T_{n+1}]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, pp.281–282, PDF 291–292, wealth dynamics (9.10)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_flow
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy

open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **The jump times and post-jump wealths `(T_n, Z_n)`** under a strategy (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), §9.3, pp.281–282, PDF 291–292,
wealth dynamics (9.10)): `T_0 = t`, `Z_0 = x`, and, if `S_n = T_{n+1} − T_n` is the `n`-th sojourn
time and `Y_{n+1}` the jump height, `T_{n+1} = T_n + S_n` and
`Z_{n+1} = φ^{α}_{S_n}(Z_n)(1 + α_{S_n} · Y_{n+1})`, where `α = f_n(…)` is the control function used
after `T_n`.

**Formalization Note.** `ω n = (S_n, Y_{n+1})` (0-indexed). The fractions at the jump are those of
the predictable control at `t = T_{n+1} ∈ (T_n, T_{n+1}]`. -/
noncomputable def JumpMarket.state {d : ℕ} (Mk : JumpMarket d) (R : JMStrategy d) (t x : ℝ)
    (ω : ℕ → ℝ × (Fin d → ℝ)) : ℕ → ℝ × ℝ
  | 0 => (t, x)
  | n + 1 =>
      let s := JumpMarket.state Mk R t x ω n
      let α := (R n).control ((fun j : Fin n => ω j), s)
      (s.1 + (ω n).1, Mk.flow α.toRelaxed s.2 (ω n).1 * (1 + (α.1 (ω n).1).1 ⬝ᵥ (ω n).2))

end BauerleRiederMDP.LQ.Supplement


