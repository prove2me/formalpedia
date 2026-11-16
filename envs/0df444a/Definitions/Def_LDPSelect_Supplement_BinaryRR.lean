-- Prove2me | Definitions.Def_LDPSelect_Supplement_BinaryRR
-- name    : LDPSelect_Supplement_BinaryRR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:03:07.436066+00:00
-- url     : https://prove2.me/theorems/a7648d7f-f1a0-4483-b0a5-5f6232ec53ed
-- title:
--   Binary randomized-response mechanisms
-- statement:
--   A **binary randomized-response mechanism** with parameter $a$ lets each user $i$ report one bit $Z_i$ from a kernel fixed in advance,
--   $$\Pr(Z_i=1\mid X_i=x)=\frac{1+(a-1)\varphi_i(x)}{a+1},$$
--   for a measurable $\varphi_i:\mathbb R_{\ge0}\to[0,1]$, whatever the earlier reports. The acceptance rule is unrestricted: it may use all earlier reports and decisions and independent randomness.
--
--   Such mechanisms achieve the lower bound of Theorem 6 and are the mechanisms of the proof of Theorem 18.
--
--   **Formalization Note** The Bernoulli law is the published `LDPSelect.bern`.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 6, p.3 (pdf p.4); proof of Theorem 18, p.12 (pdf p.13)

import Mathlib
import Definitions.Def_LDPSelect_Mechanism
import Definitions.Def_LDPSelect_Fa

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect.Supplement

/-!
# Binary randomized-response mechanisms

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Theorem 6, p.3; proof of
Theorem 18, p.12.

**Formalization Note.** A binary randomized-response mechanism reports one bit per user, from a kernel
fixed in advance: `Pr(Z_i = true | X_i = x) = (1 + (a − 1) φ_i(x)) / (a + 1)` for a measurable
`φ_i : ℝ≥0 → [0, 1]`, whatever the earlier reports. `bern p` is the published Bernoulli law. The
acceptance kernels are unrestricted, as in `LDPSelect.Mechanism`: they may use every earlier report and
decision and independent randomness.
-/

open LDPSelect

/-- `M` is a binary randomized-response mechanism with parameter `a` (proof of Theorem 18, p.12). -/
def IsBinaryRR {n : ℕ} (a : ℝ) (M : Mechanism n Bool) : Prop :=
  ∃ φ : Fin n → ℝ≥0 → ℝ, (∀ i, Measurable (φ i) ∧ ∀ x, 0 ≤ φ i x ∧ φ i x ≤ 1) ∧
    ∀ (i : Fin n) (h : Fin i → Bool) (x : ℝ≥0),
      M.Q i (h, x) = bern ((1 + (a - 1) * φ i x) / (a + 1))

end LDPSelect.Supplement


