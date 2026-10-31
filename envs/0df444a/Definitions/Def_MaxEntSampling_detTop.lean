-- Prove2me | Definitions.Def_MaxEntSampling_detTop
-- name    : MaxEntSampling_detTop
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:38.916972+00:00
-- url     : https://prove2.me/theorems/3b41fd7f-b59f-45a0-bff7-aaf5dad77140
-- title:
--   $\det^s(X)$: product of the $s$ largest eigenvalues (Definition 1 (i))
-- statement:
--   For a $d\times d$ matrix $X\succeq 0$ with eigenvalues $\lambda_1\ge\cdots\ge\lambda_d\ge 0$ and an integer $s\in[d]$,
--
--   $$
--   {\det}^{s}(X) := \prod_{i\in[s]}\lambda_i ,
--   $$
--
--   the product of the $s$ largest eigenvalues of $X$. For $s=d$ it is the determinant. The MESP objective is $\log\det^s$ of the sum $\sum_{i\in S}v_iv_i^\top$ (Observation 1).
--
--   **Formalization Note** The range $[s]=\{1,\dots,s\}$ is the 0-based range $i<s$ of the decreasingly sorted eigenvalues.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Definition 1 (i), p.6 (PDF p.6)

import Mathlib
import Definitions.Def_MaxEntSampling_eigDesc

open Finset

namespace MaxEntSampling

/-- **`det^s(X)`: the product of the `s` largest eigenvalues (Definition 1 (i)).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Definition 1 (i), p.6 (PDF p.6): "det^s(X) := ∏_{i∈[s]} λi" for a d × d matrix
X ⪰ 0 with eigenvalues λ1 ≥ ··· ≥ λd ≥ 0.

**Formalization Note.** The 1-based range `[s] = {1,…,s}` is the 0-based range `i.val < s` of the
decreasingly sorted eigenvalues `eigDesc X`. The paper always has `s ≤ d`; for `s > d` the
product runs over all `d` eigenvalues (never used). -/
noncomputable def detTop {d : ℕ} (s : ℕ) (X : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∏ i ∈ univ.filter (fun i : Fin d => i.val < s), eigDesc X i

end MaxEntSampling


