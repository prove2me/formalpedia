-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_flow
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_flow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:13:35.549452+00:00
-- url     : https://prove2.me/theorems/9f041341-a27c-5522-99a8-7bc2464457bf
-- title:
--   The wealth between two jumps
-- statement:
--   **The wealth between two jumps** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (9.13), p.281, PDF 291, and its relaxed form, p.287, PDF 297): $\varphi ^\alpha _t(x) = x \exp (\int _0^t (\rho  + \int _U u \cdot  (\mu  - \rho e) \alpha _s(du)) ds)$, the wealth $t$ time units after the last jump when the wealth directly after it was $x$, under the fractions $\alpha $.
--
--   **Formalization Note.** $\alpha $ is a published relaxed control ($\alpha _s$ a probability measure on $U$); a deterministic control $\alpha  \in  A$ enters as its one-point relaxed control, for which the inner integral is $\alpha _s \cdot  (\mu  - \rho e)$. The integrands are bounded ($U$ is compact), so the integrals are true integrals.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (9.13), p.281, PDF 291, and its relaxed form, p.287, PDF 297

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac

open MeasureTheory
open BauerleRiederMDP.PDMDP (RelaxedControl)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The wealth between two jumps** (Bäuerle & Rieder, *Markov Decision Processes with Applications
to Finance* (2011), eq. (9.13), p.281, PDF 291, and its relaxed form, p.287, PDF 297):
`φ^α_t(x) = x exp(∫_0^t (ρ + ∫_U u · (μ − ρe) α_s(du)) ds)`, the wealth `t` time units after the last
jump when the wealth directly after it was `x`, under the fractions `α`.

**Formalization Note.** `α` is a published relaxed control (`α_s` a probability measure on `U`); a
deterministic control `α ∈ A` enters as its one-point relaxed control, for which the inner integral
is `α_s · (μ − ρe)`. The integrands are bounded (`U` is compact), so the integrals are true
integrals. -/
noncomputable def JumpMarket.flow {d : ℕ} (Mk : JumpMarket d) (α : RelaxedControl (Ufrac d))
    (x t : ℝ) : ℝ :=
  x * Real.exp (∫ s in (0 : ℝ)..t,
    (Mk.ρ + ∫ u, (u.1 ⬝ᵥ fun k => Mk.μ k - Mk.ρ) ∂(α.1 s)))

end BauerleRiederMDP.LQ.Supplement


