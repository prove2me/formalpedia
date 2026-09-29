-- Prove2me | Definitions.Def_HighDimProb_SparseRecovery_Sparsity
-- name    : HighDimProb_SparseRecovery_Sparsity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:10:42.63744+00:00
-- url     : https://prove2.me/theorems/660c76fd-3f0c-45eb-a13f-a7534b898cae
-- title:
--   An $s$-sparse vector
-- statement:
--   A vector $v$ (indexed by a finite type) is **$s$-sparse**, $\|v\|_0 \le s$, where $\|v\|_0$ is
--   the number of non-zero coordinates of $v$.
--
--   **Formalization Note** $s$ is real-valued, not natural: the restricted isometry property is
--   stated for the third parameter $(1+\lambda)s$ for a real $\lambda>0$, not generally an integer
--   even when the base sparsity level $s$ is.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Section 10.3.1 / footnote 2, p. 260

import Mathlib

namespace HighDimProb.SparseRecovery

/-- **`IsSSparse v s`**: the vector `v : ι → ℝ` is `s`-sparse, `‖v‖₀ ≤ s`, where `‖v‖₀` (Vershynin,
*High-Dimensional Probability* (2018), Section 10.3.1 / footnote 2 of p. 260 (PDF p. 268): "by
`‖v‖₀` we denote the number of non-zero coordinates of `v`") is the cardinality of `v`'s support.
`s : ℝ`, not `ℕ`: the restricted isometry property (`SatisfiesRIP`) is stated for the third
parameter `(1+λ)s` for a real `λ > 0`, which need not be an integer even when the base sparsity
level `s` is, so the comparison `‖v‖₀ ≤ s` is with a real right-hand side throughout. -/
def IsSSparse {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (s : ℝ) : Prop :=
  ((Finset.univ.filter (fun i => v i ≠ 0)).card : ℝ) ≤ s

end HighDimProb.SparseRecovery


