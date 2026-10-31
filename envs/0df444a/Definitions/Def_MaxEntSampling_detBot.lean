-- Prove2me | Definitions.Def_MaxEntSampling_detBot
-- name    : MaxEntSampling_detBot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:37.746747+00:00
-- url     : https://prove2.me/theorems/9c5580e2-1d3e-4b01-bcba-2aba67a1ebaf
-- title:
--   $\det_s(X)$: product of the $s$ smallest eigenvalues (Definition 1 (ii))
-- statement:
--   For a $d\times d$ matrix $X\succeq 0$ with eigenvalues $\lambda_1\ge\cdots\ge\lambda_d\ge 0$ and an integer $s\in[d]$,
--
--   $$
--   {\det}_{s}(X) := \prod_{i\in[d-s+1,d]}\lambda_i ,
--   $$
--
--   the product of the $s$ smallest eigenvalues of $X$. It appears in the objective $-\log\det_s(\Lambda)$ of the Lagrangian dual (5).
--
--   **Formalization Note** The range $[d-s+1,d]$ is the 0-based range $d-s\le i$; the paper always has $s\le d$.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Definition 1 (ii), p.6 (PDF p.6)

import Mathlib
import Definitions.Def_MaxEntSampling_eigDesc

open Finset

namespace MaxEntSampling

/-- **`det_s(X)`: the product of the `s` smallest eigenvalues (Definition 1 (ii)).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Definition 1 (ii), p.6 (PDF p.6): "det_s(X) := ∏_{i∈[d−s+1,d]} λi" for a d × d
matrix X ⪰ 0 with eigenvalues λ1 ≥ ··· ≥ λd ≥ 0.

**Formalization Note.** The 1-based range `[d−s+1, d]` is the 0-based range `d - s ≤ i.val` of the
decreasingly sorted eigenvalues `eigDesc X` (the last `s` entries). The paper always has
`s ≤ d`, so the natural-number subtraction `d - s` is exact. -/
noncomputable def detBot {d : ℕ} (s : ℕ) (X : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∏ i ∈ univ.filter (fun i : Fin d => d - s ≤ i.val), eigDesc X i

end MaxEntSampling


