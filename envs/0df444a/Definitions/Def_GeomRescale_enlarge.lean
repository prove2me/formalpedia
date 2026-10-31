-- Prove2me | Definitions.Def_GeomRescale_enlarge
-- name    : GeomRescale_enlarge
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:39.180425+00:00
-- url     : https://prove2.me/theorems/caf33390-c8ea-4c0d-b016-8e6cf7290178
-- title:
--   The $\mu$-enlargement $f_\mu$, display (8)
-- statement:
--   For a set function $f$ and a value $\mu$, the $\mu$-enlargement is
--
--   $$f_\mu(S) = \begin{cases} 0 & \text{if } S = \emptyset \text{ or } S = V, \\ f(S) + \mu & \text{otherwise.} \end{cases}$$
--
--   The shift is not applied at $\emptyset$ and $V$, so $x(V) = 0$ on $B(f_\mu)$. If $\mu$ is at least the negative of the minimum of $f$, then $0 \in B(f_\mu)$; this is what lets the algorithm test the current estimate $-\mu$ of the minimum.
--
--   **Formalization Note** The function is real valued; for integer $f$ and $\mu$ it is `enlarge (fR f) μ`.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (8), p.7

import Mathlib

namespace GeomRescale

/-- The `μ`-enlargement of `f` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (8), p.7): `f_μ(S) = 0` if `S = ∅` or `S = V`, and
`f_μ(S) = f(S) + μ` otherwise.

**Formalization Note.** Real valued, so that Section 2 applies to it. For integer `f` and `μ` it is
`enlarge (fR f) μ`, the page's `f_μ : 2^V → ℤ` read in `ℝ`. -/
noncomputable def enlarge {n : ℕ} (f : Finset (Fin n) → ℝ) (μ : ℝ) : Finset (Fin n) → ℝ :=
  fun S => if S = ∅ ∨ S = Finset.univ then 0 else f S + μ

end GeomRescale


