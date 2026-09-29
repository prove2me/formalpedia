-- Prove2me | Definitions.Def_HighDimProb_SparseRecovery_RIP
-- name    : HighDimProb_SparseRecovery_RIP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:16.445832+00:00
-- url     : https://prove2.me/theorems/706f4afe-6f2c-4117-9a3a-3c31e9533182
-- title:
--   The restricted isometry property (RIP)
-- statement:
--   An $m\times n$ matrix $A$ satisfies the **restricted isometry property (RIP)** with parameters
--   $\alpha,\beta,s$ if $\alpha\|v\|_2 \le \|Av\|_2 \le \beta\|v\|_2$ for every $s$-sparse vector
--   $v\in\mathbb R^n$. This is the deterministic condition Theorem 10.5.10 shows is sufficient for
--   exact sparse recovery.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 260, Definition 10.5.8

import Mathlib
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Definitions.Def_HighDimProb_SparseRecovery_Sparsity

namespace HighDimProb.SparseRecovery

/-- **`SatisfiesRIP A α β s`**: the `m × n` matrix `A` satisfies the **restricted isometry
property (RIP)** with parameters `α, β, s`. Vershynin, *High-Dimensional Probability* (2018),
Definition 10.5.8, p. 260 (PDF p. 268): "An `m × n` matrix `A` satisfies the restricted isometry
property (RIP) with parameters `α`, `β` and `s` if the inequality `α‖v‖₂ ≤ ‖Av‖₂ ≤ β‖v‖₂` holds
for all vectors `v ∈ ℝⁿ` such that `‖v‖₀ ≤ s`." Direct transcription: `A.mulVec v` is `Av`,
`l2Norm` is `‖·‖₂`, `IsSSparse v s` is `‖v‖₀ ≤ s`. -/
def SatisfiesRIP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (α β s : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, IsSSparse v s →
    α * l2Norm v ≤ l2Norm (A.mulVec v) ∧ l2Norm (A.mulVec v) ≤ β * l2Norm v

end HighDimProb.SparseRecovery


