-- Prove2me | Definitions.Def_DepthOptQC_Synth_bmax
-- name    : DepthOptQC_Synth_bmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:13:38.541405+00:00
-- url     : https://prove2.me/theorems/1cfd9f9b-1359-418b-bbfb-719dab8cec13
-- title:
--   The width bound $b_{\max}=\lceil m^{2^{k-1}/(2^k-1)}\rceil$ of Lemma 4
-- statement:
--   For integers $m\ge1$ and $k\ge1$,
--   $$
--   b_{\max} := \Big\lceil m^{\,2^{k-1}/(2^k-1)} \Big\rceil .
--   $$
--   It is the largest branching factor of the $k$-level comparison tree of Lemma 4, hence the largest Fan-Out width and Toffoli width that tree uses. For $k=1$ it is $m$; as $k$ grows the exponent decreases to $1/2$.
--
--   **Formalization Note** The exponent is computed in the reals and the ceiling is the natural-number ceiling. Only $k\ge1$ is used.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Lemma 4, Eq. (44), p.18

import Mathlib

namespace DepthOptQC.Synth

/-- **The width bound `b_max` of Lemma 4** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Eq. (44), p.18): `b_max := ⌈m^{2^{k−1}/(2^k−1)}⌉`.

**Formalization Note.** The exponent is computed in `ℝ` and the ceiling is `Nat.ceil`. The
subtraction `k − 1` is in `ℕ`; the paper takes `k ≥ 1`, where it is exact (at `k = 0` Lean's
`x / 0 = 0` would give `b_max = 1`; no statement uses `k = 0`). -/
noncomputable def bmax (m k : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ ((2 : ℝ) ^ (k - 1) / ((2 : ℝ) ^ k - 1))⌉₊

end DepthOptQC.Synth


