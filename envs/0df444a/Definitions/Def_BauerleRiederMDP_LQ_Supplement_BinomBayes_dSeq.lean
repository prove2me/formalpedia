-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_dSeq
-- name    : BauerleRiederMDP_LQ_Supplement_BinomBayes_dSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:03:00.953817+00:00
-- url     : https://prove2.me/theorems/37505eec-4d4c-56e0-a0ff-302b1f50a0a0
-- title:
--   The sequence $(d_n)$ of the binomial model
-- statement:
--   **The sequence $(d_n)$ of the binomial model** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (6.4), p.179, PDF 192, the recursion (6.3) of Theorem 6.1.2 for the binomial model without short sales, $\tilde A  = [0, 1]$): $d_0 ≡ 1/\gamma $ and $d_n(\rho ) = \sup _{0 \le  \alpha  \le  1} obj(d_{n-1}, \rho , \alpha )$; for $\gamma  < 0$ (Remark 6.1.3) the same recursion, with negative values.
--
--   **Formalization Note.** A real supremum over the compact interval $[0, 1]$ of a continuous function of $\alpha $, hence the true maximum (no junk value). $n$ is the number of stages to go.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (6.4), p.179, PDF 192, the recursion (6.3) of Theorem 6.1.2 for the binomial model without short sales, `Ã = [0, 1]`

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BinomBayes_obj

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **The sequence `(d_n)` of the binomial model** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), eq. (6.4), p.179, PDF 192, the recursion (6.3) of Theorem 6.1.2
for the binomial model without short sales, `Ã = [0, 1]`): `d_0 ≡ 1/γ` and
`d_n(ρ) = sup_{0 ≤ α ≤ 1} obj(d_{n−1}, ρ, α)`; for `γ < 0` (Remark 6.1.3) the same recursion, with
negative values.

**Formalization Note.** A real supremum over the compact interval `[0, 1]` of a continuous
function of `α`, hence the true maximum (no junk value). `n` is the number of stages to go. -/
noncomputable def BinomBayes.dSeq (B : BinomBayes) : ℕ → Measure ℝ → ℝ
  | 0, _ => 1 / B.γ
  | n + 1, ρ => ⨆ α : Set.Icc (0 : ℝ) 1, B.obj (BinomBayes.dSeq B n) ρ α

end BauerleRiederMDP.LQ.Supplement


