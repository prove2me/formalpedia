-- Prove2me | Definitions.Def_SparseBatchBandit_phiMin
-- name    : SparseBatchBandit_phiMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:36.592586+00:00
-- url     : https://prove2.me/theorems/b2b9ba8f-f16b-4d36-b336-84beab7012f0
-- title:
--   Restricted eigenvalue $\phi_{\min}(s,A)$
-- statement:
--   For a sparsity level $s$ and a square matrix $A\in\mathbb R^{d\times d}$, the **lower restricted eigenvalue** is
--
--   $$
--   \phi_{\min}(s,A)=\min_{v\in\mathbb R^d:\ \|v\|_0\le s}\ \frac{v^\top A v}{\|v\|_2^2},
--   $$
--
--   the minimum running over nonzero $v$. It lower-bounds the quadratic form of $A$ on sparse directions, which is what a Lasso analysis needs when $A$ itself is singular.
--
--   **Formalization Note** The minimum is an infimum of the set of Rayleigh quotients. For $s\ge1$ and $d\ge1$ this set is nonempty and bounded and the infimum is attained, and the mission uses it only there.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.2.1, p.17

import Mathlib
import Definitions.Def_SparseBatchBandit_l0Norm
open Matrix

namespace SparseBatchBandit

/-- The lower restricted eigenvalue `φ_min(s, A) = min_{v : ‖v‖₀ ≤ s} v⊤Av / ‖v‖₂²`,
Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4.2.1, p.17 (PDF 17).

**Formalization Note.** The minimum is an `sInf` of the Rayleigh quotients of the nonzero
`s`-sparse vectors. For `1 ≤ s`, `1 ≤ d` this set is nonempty and bounded, and the infimum is
attained. Every statement of the mission uses `s ≥ 1` and `d ≥ 1`. -/
noncomputable def phiMin {d : ℕ} (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin d → ℝ, v ≠ 0 ∧ l0Norm v ≤ s ∧
    r = (v ⬝ᵥ A.mulVec v) / (∑ j, v j ^ 2)}

end SparseBatchBandit


