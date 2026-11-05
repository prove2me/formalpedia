-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_statePath
-- name    : BauerleRiederMDP_TransactionCosts_Market_statePath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:13.832598+00:00
-- url     : https://prove2.me/theorems/e1693096-27b9-4819-a6c8-24552a6acc95
-- title:
--   State process under a Markov policy
-- statement:
--   For a Markov policy $\pi$ started at time $n$ in state $x$, the state process is
--   $$X_n=x,\qquad X_{m+1}=T_m\big(X_m,f_m(X_m),\tilde R_{m+1}\big)=\big(f^0_m(X_m)(1+i_{m+1}),\ f^1_m(X_m)\tilde R_{m+1}\big).$$
--
--   **Formalization Note** The process is built pathwise on $\Omega$ from the independent disturbances; this realizes the Markov chain with transition kernel $Q_n(\cdot\mid x,a)=$ law of $T_n(x,a,\tilde R_{n+1})$ (Theorem 2.1.3). `statePath π n x k` is $X_{n+k}$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 2.1.3, p.15 (PDF 30); §4.5, eq. (4.24), p.106 (PDF 120)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_transition

namespace BauerleRiederMDP.TransactionCosts

/-- The state process of the transaction cost model under a Markov policy `π` started at time
`n` in state `x` (Bäuerle & Rieder 2011, Theorem 2.1.3 and Remark 2.3.2 c), pp.15–20, with the
transition (4.24) of §4.5, p.106): `statePath π n x k ω` is the state `X_{n+k}(ω)`, given by
`X_n = x` and `X_{m+1} = T_m(X_m, f_m(X_m), R̃_{m+1})`.

**Formalization Note.** The process is built pathwise on `Ω` from the independent disturbances
`R̃_{n+1}, R̃_{n+2}, …`; this realizes the Markov chain with transition kernel
`Q_n(·|x, a) = law of T_n(x, a, R̃_{n+1})` (Theorem 2.1.3). -/
def Market.statePath {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n : ℕ) (x : ℝ × ℝ) : ℕ → Ω → ℝ × ℝ
  | 0, _ => x
  | k + 1, ω =>
      M.transition (n + k) (π (n + k) (M.statePath π n x k ω)) (M.R (n + k + 1) ω)

end BauerleRiederMDP.TransactionCosts


