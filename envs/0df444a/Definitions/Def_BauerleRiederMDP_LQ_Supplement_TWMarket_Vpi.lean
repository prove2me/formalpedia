-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_Vpi
-- name    : BauerleRiederMDP_LQ_Supplement_TWMarket_Vpi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:36:37.740265+00:00
-- url     : https://prove2.me/theorems/b760a6a3-d447-4e8d-953b-04ef2e20f5e2
-- title:
--   The expected utility of terminal wealth of a policy
-- statement:
--   **The expected utility of terminal wealth of a policy** $V_{n\pi }(x) = \mathbb E ^\pi _{nx} U(X_N)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (4.6), p.80, PDF 94).
--
--   **Formalization Note.** Under $\mathbb P ^\pi _{nx}$ the wealth at time $n$ is $x$ and the relative risks $R_{n+1}, \dots , R_N$ are independent with laws $\nu  (n+1), \dots , \nu  N$, so the expectation is taken under the product law of the path $(R_{n+1}, \dots , R_N)$, along which $X_N$ is `Mk.wealth f n x (N − n)`. It is the published `eint` ($\int  U^+ - \int  U^-$, two Lebesgue integrals), never a Bochner integral, so $-\infty $ is a possible value. Only $n \le  N$ is meaningful.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (4.6), p.80, PDF 94

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_eint
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TWMarket_wealth

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The expected utility of terminal wealth of a policy** `V_{nπ}(x) = 𝔼^π_{nx} U(X_N)`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (4.6),
p.80, PDF 94).

**Formalization Note.** Under `ℙ^π_{nx}` the wealth at time `n` is `x` and the relative risks
`R_{n+1}, …, R_N` are independent with laws `ν (n+1), …, ν N`, so the expectation is taken under
the product law of the path `(R_{n+1}, …, R_N)`, along which `X_N` is `Mk.wealth f n x (N − n)`.
It is the published `eint` (`∫ U⁺ − ∫ U⁻`, two Lebesgue integrals), never a Bochner integral, so
`−∞` is a possible value. Only `n ≤ N` is meaningful. -/
noncomputable def TWMarket.Vpi {d : ℕ} (Mk : TWMarket d) (U : ℝ → ℝ) (N : ℕ)
    (f : ℕ → ℝ → Fin d → ℝ) (n : ℕ) (x : ℝ) : EReal :=
  BauerleRiederMDP.RegimeSwitching.eint
    (Measure.pi fun j : Fin (N - n) => (Mk.ν (n + j + 1) : Measure (Fin d → ℝ)))
    (fun r => ((U (Mk.wealth f n x (N - n) r) : ℝ) : EReal))

end BauerleRiederMDP.LQ.Supplement


