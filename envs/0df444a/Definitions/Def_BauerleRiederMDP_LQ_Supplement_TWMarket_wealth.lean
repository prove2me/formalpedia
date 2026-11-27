-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_wealth
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_wealth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:35:56.966158+00:00
-- url     : https://prove2.me/theorems/be8b1570-344b-53b3-92b0-84dc43840bac
-- title:
--   The wealth under a Markov portfolio strategy
-- statement:
--   **The wealth under a Markov portfolio strategy** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.2, p.79, PDF 93, wealth equation $X_{n+1} = (1 + i_{n+1})(X_n + \varphi _n \cdot  R_{n+1})$, and the transition function (4.5), $T_n(x, a, z) = (1 + i_{n+1})(x + a \cdot  z)$, p.80, PDF 94). `Mk.wealth f n x k r` is the wealth at time $n + k$ when the wealth at time $n$ is $x$, the amount $f_m(X_m)$ is invested in the stocks at each time $m$, and $r = (R_{n+1}, \dots , R_{n+k})$ is the path of relative risks.
--
--   **Formalization Note.** The path is 0-indexed: $r j = R_{n+j+1}$. $f m : \mathbb R  \to  \mathbb R ^d$ is the decision rule at time $m$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.2, p.79, PDF 93, wealth equation `X_{n+1} = (1 + i_{n+1})(X_n + φ_n · R_{n+1})`, and the transition function (4.5), `T_n(x, a, z) = (1 + i_{n+1})(x + a · z)`, p.80, PDF 94

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket

namespace BauerleRiederMDP.LQ.Supplement

/-- **The wealth under a Markov portfolio strategy** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), §4.2, p.79, PDF 93, wealth equation
`X_{n+1} = (1 + i_{n+1})(X_n + φ_n · R_{n+1})`, and the transition function (4.5),
`T_n(x, a, z) = (1 + i_{n+1})(x + a · z)`, p.80, PDF 94). `Mk.wealth f n x k r` is the wealth at time
`n + k` when the wealth at time `n` is `x`, the amount `f_m(X_m)` is invested in the stocks at each
time `m`, and `r = (R_{n+1}, …, R_{n+k})` is the path of relative risks.

**Formalization Note.** The path is 0-indexed: `r j = R_{n+j+1}`. `f m : ℝ → ℝ^d` is the decision
rule at time `m`. -/
noncomputable def TWMarket.wealth {d : ℕ} (Mk : TWMarket d) (f : ℕ → ℝ → Fin d → ℝ) (n : ℕ)
    (x : ℝ) : (k : ℕ) → (Fin k → Fin d → ℝ) → ℝ
  | 0, _ => x
  | k + 1, r =>
      (1 + Mk.i (n + k + 1)) * (TWMarket.wealth Mk f n x k (Fin.init r) +
        f (n + k) (TWMarket.wealth Mk f n x k (Fin.init r)) ⬝ᵥ r (Fin.last k))

end BauerleRiederMDP.LQ.Supplement


