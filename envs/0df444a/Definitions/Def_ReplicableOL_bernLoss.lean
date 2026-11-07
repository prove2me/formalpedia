-- Prove2me | Definitions.Def_ReplicableOL_bernLoss
-- name    : ReplicableOL_bernLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:44:01.939981+00:00
-- url     : https://prove2.me/theorems/9e64f6c2-f930-4491-b58c-c34ba8403923
-- title:
--   Loss law of one round inside an epoch
-- statement:
--   In an epoch with mean $\mu$, a round has $\ell_t=(B_t,1-B_t)$ with $B_t\sim\mathrm{Bern}(1/2+\mu)$. So expert 1 has mean loss $1/2+\mu$ and expert 2 has mean loss $1/2-\mu$, and expert 2 is the better one when $\mu>0$ (the sign convention (H6)).
--
--   **Formalization Note** `ℓ_t = (1, 0)` has mass `1/2 + μ`, which is the sign convention (H6): Lean's expert `0` is the paper's expert 1 and has mean loss `1/2 + μ`. The law is a probability measure for `|μ| ≤ 1/2`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Loss law of one round inside an epoch.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. `B_t ∼ Bern(1/2 + μ_j)` and `ℓ_t := (B_t, 1 − B_t)`.

**Formalization Note.** `ℓ_t = (1, 0)` has mass `1/2 + μ`, which is the sign convention (H6): Lean's expert `0` is the paper's expert 1 and has mean loss `1/2 + μ`. The law is a probability measure for `|μ| ≤ 1/2`. -/
noncomputable def bernLoss (μ : ℝ) : Measure (Fin 2 → ℝ) :=
  ENNReal.ofReal (1 / 2 + μ) • Measure.dirac ![1, 0] + ENNReal.ofReal (1 / 2 - μ) • Measure.dirac ![0, 1]

end ReplicableOL


