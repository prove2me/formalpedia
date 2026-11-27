-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_state
-- name    : BauerleRiederMDP_LQ_Supplement_TradeExec_state
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:39:39.439586+00:00
-- url     : https://prove2.me/theorems/94c95173-178a-59da-8a2c-5bba4ed0f6c0
-- title:
--   The jump times and post-jump numbers of shares $(T_n, Z_n)$
-- statement:
--   **The jump times and post-jump numbers of shares $(T_n, Z_n)$** of the trade execution problem (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.4, p.294, PDF 304, $X_t = x_0 - \int _0^t \pi _s dN_s$): $T_0 = t$, $Z_0 = x$, $T_{n+1} = T_n + S_n$ and $Z_{n+1} = Z_n - \pi _{T_{n+1}}$, $\pi _{T_{n+1}} = g_n(S_n; S_0, \dots , S_{n-1}; T_n, Z_n)$.
--
--   **Formalization Note.** $\omega  n = S_n$, the $n$-th sojourn time of the Poisson process (0-indexed).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.4, p.294, PDF 304, `X_t = x_0 − ∫_0^t π_s dN_s`

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeStrategy

namespace BauerleRiederMDP.LQ.Supplement

/-- **The jump times and post-jump numbers of shares `(T_n, Z_n)`** of the trade execution problem
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.4, p.294,
PDF 304, `X_t = x_0 − ∫_0^t π_s dN_s`): `T_0 = t`, `Z_0 = x`, `T_{n+1} = T_n + S_n` and
`Z_{n+1} = Z_n − π_{T_{n+1}}`, `π_{T_{n+1}} = g_n(S_n; S_0, …, S_{n−1}; T_n, Z_n)`.

**Formalization Note.** `ω n = S_n`, the `n`-th sojourn time of the Poisson process (0-indexed). -/
def TradeExec.state (_P : TradeExec) (g : TradeStrategy) (t : ℝ) (x : ℕ) (ω : ℕ → ℝ) :
    ℕ → ℝ × ℕ
  | 0 => (t, x)
  | n + 1 =>
      let s := TradeExec.state _P g t x ω n
      (s.1 + ω n, s.2 - (g n).1 (ω n, ((fun j : Fin n => ω j), s)))

end BauerleRiederMDP.LQ.Supplement


