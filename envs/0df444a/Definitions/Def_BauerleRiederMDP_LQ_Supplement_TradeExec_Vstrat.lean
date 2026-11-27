-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_Vstrat
-- name    : BauerleRiederMDP_LQ_Supplement_TradeExec_Vstrat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:40:21.546663+00:00
-- url     : https://prove2.me/theorems/782ec08d-bb69-4cd5-9d83-13d62edfa04b
-- title:
--   The expected cost of a control process
-- statement:
--   **The expected cost of a control process** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.4, p.294, PDF 304): $V_\pi (t, x) := \mathbb E ^\pi _{tx}[\int _t^T C(\pi _s) dN_s + C(X_T)]$.
--
--   **Formalization Note.** The sojourn times are i.i.d. $Exp(\lambda )$ (`Measure.infinitePi`). $\int _t^T C(\pi _s) dN_s$ is the sum of $C(\pi _{T_{n+1}})$ over the jump times $T_{n+1} \le  T$, and $X_T = Z_k$ with $k$ the largest index with $T_k \le  T$ (finite almost surely). All terms are nonnegative, so the expectation is a Lebesgue integral in $[0, \infty ]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.4, p.294, PDF 304

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_state

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The expected cost of a control process** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §9.4, p.294, PDF 304):
`V_π(t, x) := 𝔼^π_{tx}[∫_t^T C(π_s) dN_s + C(X_T)]`.

**Formalization Note.** The sojourn times are i.i.d. `Exp(λ)` (`Measure.infinitePi`). `∫_t^T C(π_s) dN_s`
is the sum of `C(π_{T_{n+1}})` over the jump times `T_{n+1} ≤ T`, and `X_T = Z_k` with `k` the largest
index with `T_k ≤ T` (finite almost surely). All terms are nonnegative, so the expectation is a
Lebesgue integral in `[0, ∞]`. -/
noncomputable def TradeExec.Vstrat (P : TradeExec) (g : TradeStrategy) (p : ℝ × ℕ) : ENNReal :=
  haveI := isProbabilityMeasure_expMeasure P.lam_pos
  ∫⁻ ω, ((∑' n : ℕ, ENNReal.ofReal
      (if (P.state g p.1 p.2 ω (n + 1)).1 ≤ P.T then
        P.C ((g n).1 (ω n, ((fun j : Fin n => ω j), P.state g p.1 p.2 ω n))) else 0)) +
    ENNReal.ofReal (P.C (P.state g p.1 p.2 ω (sSup {n : ℕ | (P.state g p.1 p.2 ω n).1 ≤ P.T})).2))
    ∂(Measure.infinitePi fun _ : ℕ => expMeasure P.lam)

end BauerleRiederMDP.LQ.Supplement


