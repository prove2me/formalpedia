-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Jinf
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_Jinf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:15:49.89802+00:00
-- url     : https://prove2.me/theorems/1f151b5b-e243-4835-b64c-4be597be95ca
-- title:
--   The value $J_\infty $ of the discrete-time model of §9.3
-- statement:
--   **The value $J_\infty $ of the discrete-time model of §9.3** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.283, PDF 293): $J_\infty (t, x) = \sup _{(f_n) \in  F^\infty } J_{\infty (f_n)}(t, x)$, with $J_{\infty (f_n)}(t, x) = \mathbb E ^{(f_n)}_{tx} [\sum _k r(T'_k, Z'_k, f_k(T'_k, Z'_k))]$.
--
--   **Formalization Note.** A decision rule $f : E \to  A$ is a jointly measurable published `DecisionRule (ℝ × ℝ) (Ufrac d)`, $f(t, x)(s) = f.1 (s, (t, x))$; $J_{\infty (f_n)}$ is the published `StageModel.Jinf` of `JumpMarket.stage` along the controls $f_n(T'_n, Z'_n)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.283, PDF 293

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_stage

open BauerleRiederMDP.PDMDP (DecisionRule)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The value `J_∞` of the discrete-time model of §9.3** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), p.283, PDF 293):
`J_∞(t, x) = sup_{(f_n) ∈ F^∞} J_{∞(f_n)}(t, x)`, with
`J_{∞(f_n)}(t, x) = 𝔼^{(f_n)}_{tx} [∑_k r(T′_k, Z′_k, f_k(T′_k, Z′_k))]`.

**Formalization Note.** A decision rule `f : E → A` is a jointly measurable published
`DecisionRule (ℝ × ℝ) (Ufrac d)`, `f(t, x)(s) = f.1 (s, (t, x))`; `J_{∞(f_n)}` is the published
`StageModel.Jinf` of `JumpMarket.stage` along the controls `f_n(T′_n, Z′_n)`. -/
noncomputable def JumpMarket.Jinf {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ) (p : ℝ × ℝ) : EReal :=
  ⨆ f : ℕ → DecisionRule (ℝ × ℝ) (Ufrac d), (Mk.stage U).Jinf (fun n => (f n).control) p

end BauerleRiederMDP.LQ.Supplement


