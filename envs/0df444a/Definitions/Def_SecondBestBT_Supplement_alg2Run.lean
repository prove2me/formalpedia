-- Prove2me | Definitions.Def_SecondBestBT_Supplement_alg2Run
-- name    : SecondBestBT_Supplement_alg2Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:38:01.881953+00:00
-- url     : https://prove2.me/theorems/7edc693f-211c-4156-87ba-e1231e8de1f2
-- title:
--   Algorithm 2: full run and terminal threshold
-- statement:
--   The full run of **Algorithm 2** from a clear state $\omega=(y^{(0)};\mathbf r^{(0)})$ on an appended ratio sequence $\mathbf r^{(1)}$: with $R=\mathbf r^{(0)}\|\mathbf r^{(1)}$ it processes the buyer values $b=|\mathbf r^{(0)}|+1,\dots,|R|$ and returns fail or the final allocation together with the **terminal threshold** $t_{|R|}$ (in local coordinates).
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, Algorithm 2, p.18

import Mathlib
import Definitions.Def_SecondBestBT_Supplement_alg2Loop

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- The full run of **Algorithm 2** (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 5.1, Algorithm 2, p.18) from the clear
state `ω = (y(0) ; r(0))` on the appended ratio sequence `r(1)`: it processes the buyer values
`b = |r(0)| + 1, …, |R|` with `R = r(0) ∥ r(1)` and returns `none` (fail) or
`some (x, t_{|R|})`, the final allocation and the **terminal threshold** `t_{|R|}` (local
coordinates). -/
noncomputable def alg2Run (α β : ℝ) (ω : ℝ × List ℝ≥0∞) (r1 : List ℝ≥0∞) :
    Option ((ℕ → ℕ → ℝ) × ℕ) :=
  (alg2Loop α β ω.1 (ω.2 ++ r1) ω.2.length r1.length).map fun st => (st.1, st.2.1)

end SecondBestBT.Supplement


