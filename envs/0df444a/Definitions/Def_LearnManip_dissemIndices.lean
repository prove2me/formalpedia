-- Prove2me | Definitions.Def_LearnManip_dissemIndices
-- name    : LearnManip_dissemIndices
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:43.480981+00:00
-- url     : https://prove2.me/theorems/63ebceed-ad40-4e45-83ec-d0f85cf77fd9
-- title:
--   The set of indices in the dissemination time
-- statement:
--   The set
--   $$\{\,j\in\mathbb N:\ s>s_{TH}(c\bar\eta^{\,j-1})\,\}$$
--   of the definition of the dissemination time, with $\mathbb N$ starting at $1$.
--
--   **Formalization Note.** The power at $j=1$, $\bar\eta=0$ is $0^0=1$, as $c\eta^{j-1}$ means.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Theorem 1, p.15

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_effEta
import Definitions.Def_LearnManip_sTH

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The set `{j ∈ ℕ : s > s_TH(c η̄^{j−1})}` in the definition of the dissemination time `κ(s, c)`,
Theorem 1, p.15, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04).

**Formalization Note.** The paper's `ℕ` starts at `1`, so `1 ≤ j` is required, and `j - 1` is genuine
natural-number subtraction. At `j = 1` and `η̄ = 0` the power is `0⁰ = 1`, as `c η^{j−1}` means. -/
def dissemIndices (P : Params) (s c : ℝ≥0) : Set ℕ :=
  {j : ℕ | 1 ≤ j ∧ sTH P (c * effEta P ^ (j - 1)) < s}

end LearnManip


