-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy
-- name    : BauerleRiederMDP_LQ_Supplement_JMStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:10:54.459962+00:00
-- url     : https://prove2.me/theorems/426be187-723e-50de-a220-a9fff4ecbee5
-- title:
--   A predictable portfolio strategy in the pure jump market
-- statement:
--   **A predictable portfolio strategy in the pure jump market** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.3, p.281, PDF 291, and the representation of a predictable process in the proof of Theorem 9.3.1 b), pp.283–284, PDF 293–294, Remark 8.1.2): $\pi _t = f_n(T_0, Z_0, \dots , T_n, Z_n)(t - T_n)$ for $t \in  (T_n, T_{n+1}]$, with measurable $f_n$ and values in $U$.
--
--   **Formalization Note.** $F_t = F^C_t$, and the history $(T_0, Z_0, \dots , T_n, Z_n)$ is a function of the initial state and of the first $n$ sojourn times and jump heights $(S_j, Y_{j+1})_{j<n}$; the $n$-th rule is a jointly measurable map of $(t - T_n, (S_j, Y_{j+1})_{j<n}, (T_n, Z_n))$, a published `DecisionRule`. Markov strategies are those ignoring the first component of the pair.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.3, p.281, PDF 291, and the representation of a predictable process in the proof of Theorem 9.3.1 b), pp.283–284, PDF 293–294, Remark 8.1.2

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_DecisionRule
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Ufrac

open BauerleRiederMDP.PDMDP (DecisionRule)

namespace BauerleRiederMDP.LQ.Supplement

/-- **A predictable portfolio strategy in the pure jump market** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §9.3, p.281, PDF 291, and the representation of a
predictable process in the proof of Theorem 9.3.1 b), pp.283–284, PDF 293–294, Remark 8.1.2):
`π_t = f_n(T_0, Z_0, …, T_n, Z_n)(t − T_n)` for `t ∈ (T_n, T_{n+1}]`, with measurable `f_n` and
values in `U`.

**Formalization Note.** `F_t = F^C_t`, and the history `(T_0, Z_0, …, T_n, Z_n)` is a function of the
initial state and of the first `n` sojourn times and jump heights `(S_j, Y_{j+1})_{j<n}`; the
`n`-th rule is a jointly measurable map of `(t − T_n, (S_j, Y_{j+1})_{j<n}, (T_n, Z_n))`, a
published `DecisionRule`. Markov strategies are those ignoring the first component of the pair. -/
def JMStrategy (d : ℕ) : Type :=
  (n : ℕ) → DecisionRule ((Fin n → ℝ × (Fin d → ℝ)) × (ℝ × ℝ)) (Ufrac d)

end BauerleRiederMDP.LQ.Supplement


