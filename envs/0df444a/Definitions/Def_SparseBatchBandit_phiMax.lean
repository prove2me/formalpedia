-- Prove2me | Definitions.Def_SparseBatchBandit_phiMax
-- name    : SparseBatchBandit_phiMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:36.071429+00:00
-- url     : https://prove2.me/theorems/a1193e52-2c17-417c-b405-c3fa07a38c44
-- title:
--   Restricted eigenvalue $\phi_{\max}(s,A)$
-- statement:
--   For a sparsity level $s$ and a square matrix $A\in\mathbb R^{d\times d}$, the **upper restricted eigenvalue** is
--
--   $$
--   \phi_{\max}(s,A)=\max_{v\in\mathbb R^d:\ \|v\|_0\le s}\ \frac{v^\top A v}{\|v\|_2^2},
--   $$
--
--   the maximum running over nonzero $v$.
--
--   **Formalization Note** The maximum is a supremum of the set of Rayleigh quotients. For $s\ge1$ and $d\ge1$ this set is nonempty and bounded and the supremum is attained, and the mission uses it only there.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.2.1, p.17

import Mathlib
import Definitions.Def_SparseBatchBandit_l0Norm
open Matrix

namespace SparseBatchBandit

/-- The upper restricted eigenvalue `φ_max(s, A) = max_{v : ‖v‖₀ ≤ s} v⊤Av / ‖v‖₂²`,
Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4.2.1, p.17 (PDF 17).

**Formalization Note.** The maximum is an `sSup` of the Rayleigh quotients of the nonzero
`s`-sparse vectors. For `1 ≤ s`, `1 ≤ d` this set is nonempty and bounded, and the supremum is
attained. Every statement of the mission uses `s ≥ 1` and `d ≥ 1`. -/
noncomputable def phiMax {d : ℕ} (s : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin d → ℝ, v ≠ 0 ∧ l0Norm v ≤ s ∧
    r = (v ⬝ᵥ A.mulVec v) / (∑ j, v j ^ 2)}

end SparseBatchBandit


