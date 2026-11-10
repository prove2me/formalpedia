-- Prove2me | Definitions.Def_GreedNorm_expansion
-- name    : GreedNorm_expansion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:03.116516+00:00
-- url     : https://prove2.me/theorems/c15a48af-3329-48d1-b481-4cb0f1e66097
-- title:
--   Expansion $\bar t$ of a threshold vector
-- statement:
--   The **expansion** of a threshold vector $t$ is the vector $\bar t\in\mathbb R^m_{\ge0}$ with
--
--   $$
--   \bar t_i = t_{\mathrm{prev}(i)},\qquad i\in[m].
--   $$
--
--   **Formalization Note** Indexed by `Fin m`: coordinate $i$ (0-based) is the paper's coordinate $i+1$.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 2.1, p.5 (PDF 7)

import Mathlib
import Definitions.Def_GreedNorm_prev

namespace GreedNorm

/-- **The expansion `t̄ ∈ ℝ^m` of a threshold vector**, `t̄_i = t_{prev(i)}`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 2.1, p.5 (PDF 7): "The expansion of t is the vector t̄ ∈ R^m_{≥0} where
t̄i := tprev(i) for each i ∈ [m]."

**Formalization Note** The vector is indexed by `Fin m` (0-based): coordinate `i : Fin m` is the
paper's coordinate `i + 1`, so its value is `t (prev m ε (i + 1))`. -/
noncomputable def expansion (m : ℕ) (ε : ℝ) (t : ℕ → ℝ) : Fin m → ℝ :=
  fun i => t (prev m ε (i.val + 1))

end GreedNorm


