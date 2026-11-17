-- Prove2me | Definitions.Def_SecondBestBT_Supplement_alg2Loop
-- name    : SecondBestBT_Supplement_alg2Loop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:37:21.621251+00:00
-- url     : https://prove2.me/theorems/b926d247-45fc-4e84-a169-4addf0576374
-- title:
--   Algorithm 2, outer loop (lines 1–12)
-- statement:
--   The outer loop of **Algorithm 2** in local coordinates. Input: the initial threshold allocation $y^{(0)}$, the concatenated ratio list $R=\mathbf r^{(0)}\|\mathbf r^{(1)}$, and $n_0=|\mathbf r^{(0)}|$.
--
--   1. $b_0\leftarrow n_0$, $\ell\leftarrow0$, $t_{b_0}\leftarrow0$, and $x(s,b_0)\leftarrow y^{(0)}\mathbf 1\{s=0\}$ for every $s\ge0$.
--   2. For $b=n_0+1,n_0+2,\dots$: copy $x(\cdot,b)\leftarrow x(\cdot,b-1)$ and $t_b\leftarrow t_{b-1}$; run the inner loop (lines 5–11); if it fails, return fail; if afterwards $\hat H_{\ell,b_0}(b;x)=0$, reset $(b_0,\ell)\leftarrow(b,t_b)$.
--
--   After $n$ buyer values the result is fail or the allocation, the threshold and the reference pair.
--
--   **Formalization Note** The local ratio at seller index $j$ is $R_j$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, Algorithm 2, p.18

import Mathlib
import Definitions.Def_SecondBestBT_Supplement_normResidual
import Definitions.Def_SecondBestBT_Supplement_alg2Fill

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- The outer loop of **Algorithm 2** (State Transition) after `n` buyer values (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…,
Section 5.1, Algorithm 2, lines 1–12, p.18), in local coordinates.

Input: the initial threshold allocation `y0`, the concatenated ratio list `R = r(0) ∥ r(1)` and
`n0 = |r(0)|`. Line 1: `b0 ← n0`, `ℓ ← 0`, `t_{b0} ← 0`; line 2: `x(s, b0) ← y0 · 1{s = 0}`.
For each `b = n0 + 1, n0 + 2, …` (line 3): line 4 copies `x(·, b) ← x(·, b − 1)` and
`t_b ← t_{b−1}`; lines 5–11 are `alg2Fill`; line 12: if `Ĥ_{ℓ,b0}(b; x) = 0`, reset
`(b0, ℓ) ← (b, t_b)`.

The result is `none` (fail) or `some (x, t, ℓ, b0)` after processing `b = n0 + 1, …, n0 + n`.

**Formalization Note** The local ratio at seller index `j` is `R_j` (`R.getD j ⊤`; only indices
`j < |R|` are read when `n0 + n ≤ |R|`). Columns other than `b0, …, n0 + n` are `0` and are never
read by `Ĥ`. -/
noncomputable def alg2Loop (α β y0 : ℝ) (R : List ℝ≥0∞) (n0 : ℕ) :
    ℕ → Option ((ℕ → ℕ → ℝ) × ℕ × ℕ × ℕ)
  | 0 => some (fun s b' => if s = 0 ∧ b' = n0 then y0 else 0, 0, 0, n0)
  | n + 1 =>
    (alg2Loop α β y0 R n0 n).bind fun st =>
      let r : ℕ → ℝ≥0∞ := fun j => R.getD j ⊤
      let b := n0 + n + 1
      let xc : ℕ → ℕ → ℝ := fun s b' => if b' = b then st.1 s (b - 1) else st.1 s b'
      (alg2Fill α β r st.2.2.1 st.2.2.2 b xc st.2.1).map fun q =>
        if normResidual α β r st.2.2.1 st.2.2.2 q.1 b = 0 then (q.1, q.2, q.2, b)
        else (q.1, q.2, st.2.2.1, st.2.2.2)

end SecondBestBT.Supplement


