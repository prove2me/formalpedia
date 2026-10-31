-- Prove2me | Definitions.Def_LearnManip_Gclosed
-- name    : LearnManip_Gclosed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:06.159179+00:00
-- url     : https://prove2.me/theorems/4e026793-7fa3-45a0-88c3-151434e67456
-- title:
--   Closed form (18) of the manipulation value
-- statement:
--   The closed form of the manipulation value: with $\kappa=\kappa(s,c)$ and $\bar\eta=\min(\eta,1)$,
--   $$G(s,c)=\alpha^{\kappa-1}\Biggl(\frac{c\bar\eta^{\,\kappa-1}}{s}+\frac{s}{2\gamma(1-\alpha)^2}-2\sqrt{\frac{c\bar\eta^{\,\kappa-1}(1-\alpha\bar\eta)}{2\gamma(1-\alpha\sqrt{\bar\eta})^2(1-\alpha)}}\Biggr),$$
--   and $G(s,c)=0$ when no $\kappa$ exists.
--
--   **Formalization Note.** When the set is empty, footnote 9 has $\kappa=\infty$, and (18) is read as its limit $0$. This happens at $s=0$ and at $\bar\eta=1$, $s\le s_{TH}(c)$. Since $\kappa$ exists only for $s>0$, the division by $s$ is genuine.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (18), p.15; footnote 9, p.19

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_effEta
import Definitions.Def_LearnManip_coeffK
import Definitions.Def_LearnManip_dissemIndices
import Definitions.Def_LearnManip_kappa

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

open Classical in
/-- The closed form (18), p.15, of the manipulation value of Keppo, Kim, Zhang (SSRN 3465030,
2021-09-04):
`G(s, c) = α^{κ−1} (c η̄^{κ−1}/s + s/(2γ(1−α)²) − 2 √(c η̄^{κ−1}(1−αη̄) / (2γ(1−α√η̄)²(1−α))))`,
with `η̄ = min(η, 1)` by the last sentence of Theorem 1.

**Formalization Note.** When no `j` exists, footnote 9, p.19, has `κ = ∞`, and (18) is read as its
limit `0`. This happens at `s = 0` and at `η̄ = 1`, `s ≤ s_TH(c)`. `c η̄^{κ−1}/s` never divides by zero,
since `κ` exists only for `s > 0`. The radicand is nonnegative. -/
noncomputable def Gclosed (P : Params) (s c : ℝ≥0) : ℝ :=
  if (dissemIndices P s c).Nonempty then
    (P.α : ℝ) ^ (kappa P s c - 1) *
      (((c : ℝ) * (effEta P : ℝ) ^ (kappa P s c - 1)) / (s : ℝ) + coeffK P * (s : ℝ)
        - 2 * Real.sqrt
          (((c : ℝ) * (effEta P : ℝ) ^ (kappa P s c - 1) * (1 - (P.α : ℝ) * (effEta P : ℝ))) /
            (2 * (P.γ : ℝ) * (1 - (P.α : ℝ) * Real.sqrt (effEta P : ℝ)) ^ 2 * (1 - (P.α : ℝ)))))
  else 0

end LearnManip


