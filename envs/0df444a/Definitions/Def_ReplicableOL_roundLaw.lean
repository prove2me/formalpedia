-- Prove2me | Definitions.Def_ReplicableOL_roundLaw
-- name    : ReplicableOL_roundLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:00.249983+00:00
-- url     : https://prove2.me/theorems/058e70df-c03b-4ffd-be00-aedb1b9c23bf
-- title:
--   Law of the loss vector of round $t$
-- statement:
--   The law of $\ell_t$ under $P_\theta$: if round $t$ lies in epoch $j\le k$, it is the loss law with mean $\mu_j$; otherwise round $t$ is trailing and $\ell_t=(1/2,1/2)$ deterministically.
--
--   **Formalization Note** Rounds and epochs are 0-based: round `t` lies in epoch `t / L` when `t / L < k`. With `L = 0`, `t / 0 = 0`; no theorem of the mission reads that case with `k > 0`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7

import Mathlib
import Definitions.Def_ReplicableOL_bernLoss
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Law of the loss vector of round $t$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7. Inside epoch `j` the round has the law of `bernLoss μ_j`; "the trailing rounds t > kL have ℓ_t := (1/2, 1/2)".

**Formalization Note.** Rounds and epochs are 0-based: round `t` lies in epoch `t / L` when `t / L < k`. With `L = 0`, `t / 0 = 0`; no theorem of the mission reads that case with `k > 0`. -/
noncomputable def roundLaw (k L : ℕ) (θ : Fin k → ℝ) (t : ℕ) : Measure (Fin 2 → ℝ) :=
  if h : t / L < k then bernLoss (θ ⟨t / L, h⟩) else Measure.dirac ![1 / 2, 1 / 2]

end ReplicableOL


