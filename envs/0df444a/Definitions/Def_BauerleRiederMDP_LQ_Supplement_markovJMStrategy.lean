-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_markovJMStrategy
-- name    : BauerleRiederMDP_LQ_Supplement_markovJMStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:45:00.512735+00:00
-- url     : https://prove2.me/theorems/da0b3baa-1a3d-47a9-85e6-6cd3e919c5e0
-- title:
--   The Markov portfolio strategy of a sequence of decision rules
-- statement:
--   **The Markov portfolio strategy of a sequence of decision rules** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, pp.281–282, PDF 291–292): $\pi _t = f_n(T_n, Z_n)(t - T_n)$ for $t \in  (T_n, T_{n+1}]$, for decision rules $f_n : E \to  A$.
--
--   **Formalization Note.** The strategy that ignores the jump history except through $(T_n, Z_n)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, pp.281–282, PDF 291–292

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy

open BauerleRiederMDP.PDMDP (DecisionRule)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The Markov portfolio strategy of a sequence of decision rules** (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), §9.3, pp.281–282, PDF 291–292):
`π_t = f_n(T_n, Z_n)(t − T_n)` for `t ∈ (T_n, T_{n+1}]`, for decision rules `f_n : E → A`.

**Formalization Note.** The strategy that ignores the jump history except through `(T_n, Z_n)`. -/
def markovJMStrategy {d : ℕ} (f : ℕ → DecisionRule (ℝ × ℝ) (Ufrac d)) : JMStrategy d :=
  fun n => ⟨fun q => (f n).1 (q.1, q.2.2),
    (f n).2.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))⟩

end BauerleRiederMDP.LQ.Supplement


