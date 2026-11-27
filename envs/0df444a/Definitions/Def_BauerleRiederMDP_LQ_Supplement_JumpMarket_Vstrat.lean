-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Vstrat
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_Vstrat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:17:34.362582+00:00
-- url     : https://prove2.me/theorems/e9e45bd0-9d1d-4d43-8767-3fcd67e84213
-- title:
--   The expected utility of terminal wealth of a strategy
-- statement:
--   **The expected utility of terminal wealth of a strategy** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, p.281, PDF 291): $V_\pi (t, x) := \mathbb E ^\pi _{tx}[U(X_T)]$, the expected utility of the wealth at the horizon $T$ when $X_t = x$.
--
--   **Formalization Note.** The randomness is the uncontrolled compound Poisson process: the pairs $(S_n, Y_{n+1})$ of sojourn times and jump heights are i.i.d. with law $Exp(\lambda ) \otimes  Q^Y$ (`Measure.infinitePi`), and the strategy acts deterministically along $\omega $. $X_T = \varphi ^{\alpha }_{T-T_k}(Z_k)$ with $k$ the index of the sojourn containing $T$ ($T_k \le  T < T_{k+1}$, the largest $k$ with $T_k \le  T$; the sojourn times sum to $\infty $ almost surely). $U \ge  0$ on $[0, \infty )$ and the wealth stays in $[0, \infty )$, so the expectation is a Lebesgue integral in $[0, \infty ]$, cast to `EReal`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, p.281, PDF 291

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_ControlFn
import Definitions.Def_BauerleRiederMDP_PDMDP_RelaxedControl
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_flow
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_state

open MeasureTheory ProbabilityTheory
open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **The expected utility of terminal wealth of a strategy** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §9.3, p.281, PDF 291):
`V_π(t, x) := 𝔼^π_{tx}[U(X_T)]`, the expected utility of the wealth at the horizon `T` when
`X_t = x`.

**Formalization Note.** The randomness is the uncontrolled compound Poisson process: the pairs
`(S_n, Y_{n+1})` of sojourn times and jump heights are i.i.d. with law `Exp(λ) ⊗ Q^Y`
(`Measure.infinitePi`), and the strategy acts deterministically along `ω`. `X_T = φ^{α}_{T−T_k}(Z_k)`
with `k` the index of the sojourn containing `T` (`T_k ≤ T < T_{k+1}`, the largest `k` with
`T_k ≤ T`; the sojourn times sum to `∞` almost surely). `U ≥ 0` on `[0, ∞)` and the wealth stays
in `[0, ∞)`, so the expectation is a Lebesgue integral in `[0, ∞]`, cast to `EReal`. -/
noncomputable def JumpMarket.Vstrat {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ) (R : JMStrategy d)
    (p : ℝ × ℝ) : EReal :=
  haveI := isProbabilityMeasure_expMeasure Mk.lam_pos
  ((∫⁻ ω, ENNReal.ofReal (U (
      let k := sSup {n : ℕ | (Mk.state R p.1 p.2 ω n).1 ≤ Mk.T}
      let s := Mk.state R p.1 p.2 ω k
      Mk.flow ((R k).control ((fun j : Fin k => ω j), s)).toRelaxed s.2 (Mk.T - s.1)))
    ∂(Measure.infinitePi fun _ : ℕ => (expMeasure Mk.lam).prod Mk.QY) : ENNReal) : EReal)

end BauerleRiederMDP.LQ.Supplement


