-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_Vpi
-- name    : BauerleRiederMDP_TransactionCosts_Market_Vpi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:19.396132+00:00
-- url     : https://prove2.me/theorems/d911c9f0-59ab-4096-9bf3-3a94de4a5ce5
-- title:
--   Expected terminal utility $V_{n\pi}$ of a policy
-- statement:
--   For a Markov policy $\pi$, a time $n\le N$ and a state $x\in E$,
--   $$V_{n\pi}(x)=\mathbb E^\pi_{nx}\,U\big(X^0_N+X^1_N\big),$$
--   the expected utility of terminal wealth; here $r_n\equiv0$ and $g_N(x_0,x_1)=U(x_0+x_1)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.18 (PDF 33); §4.5, eq. (4.25), p.107 (PDF 121)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_statePath
import Definitions.Def_BauerleRiederMDP_TransactionCosts_eexp

namespace BauerleRiederMDP.TransactionCosts

/-- The expected reward `V_{nπ}(x) = IE^π_{nx} g_N(X_N) = IE^π_{nx} U(X⁰_N + X¹_N)` of a Markov
policy `π` from time `n` in state `x` (Bäuerle & Rieder 2011, p.18, PDF 33; for §4.5, (4.25),
p.107, PDF 121: `r_n ≡ 0`, `g_N(x₀, x₁) = U(x₀ + x₁)`).

**Formalization Note.** `X_N` is `statePath π n x (N − n)`; the definition is used for
`n ≤ N`. The expectation is `eexp`, valued in `EReal`. -/
noncomputable def Market.Vpi {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω)
    (π : ℕ → ℝ × ℝ → ℝ × ℝ) (n : ℕ) (x : ℝ × ℝ) : EReal :=
  eexp M.P (fun ω => ((M.U ((M.statePath π n x (M.N - n) ω).1
    + (M.statePath π n x (M.N - n) ω).2) : ℝ) : EReal))

end BauerleRiederMDP.TransactionCosts


