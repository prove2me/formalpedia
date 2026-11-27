-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_finiteChainEmbJinf
-- name    : BauerleRiederMDP_LQ_Supplement_finiteChainEmbJinf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:43:19.659049+00:00
-- url     : https://prove2.me/theorems/daadc90d-02a0-5d80-82b9-ab9d01240d8b
-- title:
--   The value $J_\infty (t, x)$ of the embedded model of a finite-horizon chain
-- statement:
--   **The value $J_\infty (t, x)$ of the embedded model of a finite-horizon chain** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.259, PDF 270): $J_\infty (t, x) = \sup _{(f_n)} J_{\infty (f_n)}(t, x)$, the supremum over all Markov policies $f_n : [0, T] \times  E \to  A$ of the embedded model `finiteChainEmbStage`.
--
--   **Formalization Note.** $J_{\infty (f_n)}$ is the published `StageModel.Jinf` along the controls $f_n(T'_n, Z'_n)$; a rule is a jointly measurable `DecisionRule (ℝ × E) U`, as in the published `FiniteChain.Vpi`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.259, PDF 270

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
import Definitions.Def_BauerleRiederMDP_PDMDP_FiniteChain
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_finiteChainEmbStage

open BauerleRiederMDP.PDMDP

namespace BauerleRiederMDP.LQ.Supplement

/-- **The value `J_∞(t, x)` of the embedded model of a finite-horizon chain** (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), p.259, PDF 270):
`J_∞(t, x) = sup_{(f_n)} J_{∞(f_n)}(t, x)`, the supremum over all Markov policies
`f_n : [0, T] × E → A` of the embedded model `finiteChainEmbStage`.

**Formalization Note.** `J_{∞(f_n)}` is the published `StageModel.Jinf` along the controls
`f_n(T′_n, Z′_n)`; a rule is a jointly measurable `DecisionRule (ℝ × E) U`, as in the published
`FiniteChain.Vpi`. -/
noncomputable def finiteChainEmbJinf {E U : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [MeasurableSpace U] (C : FiniteChain E U) (p : ℝ × E) : EReal :=
  ⨆ f : ℕ → DecisionRule (ℝ × E) U, (finiteChainEmbStage C).Jinf (fun n => (f n).control) p

end BauerleRiederMDP.LQ.Supplement


