-- Prove2me | Definitions.Def_RobustMultitask_Estimator_TrimmedMean
-- name    : RobustMultitask_Estimator_TrimmedMean
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:06.471627+00:00
-- url     : https://prove2.me/theorems/0c6cb99b-6197-4d51-a9dd-dbcac065878b
-- title:
--   §3.1, p. 10 — the trimmed mean TrimmedMean({Z_j}, ω), trimming ⌊Nω⌋ values from each end
-- statement:
--   Let $Z_1,\dots,Z_N$ be real numbers and $\omega\ge 0$ a trimming level. Sort them increasingly, $Z_{j_1}\le\dots\le Z_{j_N}$, where $j_\iota$ is the index of the $\iota$-th smallest sample. Remove the $m=\lfloor N\omega\rfloor$ smallest and the $m$ largest values and average the remaining ones:
--   $$\mathrm{TrimmedMean}\big(\{Z_j\}_{j\in[N]},\omega\big)=\frac{1}{N-2m}\sum_{\iota=m+1}^{N-m} Z_{j_\iota},\qquad m=\lfloor N\omega\rfloor .$$
--   When $N\omega$ is an integer this is exactly the paper's formula
--   $$\mathrm{TrimmedMean}\big(\{Z_j\}_{j\in[N]},\omega\big)=\frac{1}{N(1-2\omega)}\sum_{\iota=N\omega+1}^{N(1-\omega)} Z_{j_\iota}.$$
--   For $N\ge 1$ and $0\le\omega<1/2$ the number $N-2m$ of retained values is a positive integer.
--
--   The trimmed mean is a classical estimator of a location parameter that is robust to a small fraction of arbitrarily corrupted samples; Step 1 of the paper's estimator applies it componentwise to the per-task least-squares estimates.
--
--   **Formalization Note** The paper's formula presupposes $N\omega\in\mathbb N$; for other $\omega$ this file removes $\lfloor N\omega\rfloor$ values from each end, the natural reading of "removes … $N\omega$ values". The order statistics come from Mathlib's `Tuple.sort`; ties do not affect the value. The retained 0-based positions are $m\le\iota$ and $\iota+m<N$, and the denominator is the real number $N-2m$.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 10, §3.1 (TrimmedMean)

import Mathlib

namespace RobustMultitask.Estimator

/-- The number of samples trimmed from each end, `⌊Nω⌋`. When `Nω ∈ ℕ` this is the paper's `Nω`. -/
noncomputable def trimCount (N : ℕ) (ω : ℝ) : ℕ :=
  ⌊(N : ℝ) * ω⌋₊

/-- `TrimmedMean({Z_j}_{j∈[N]}, ω)` (§3.1, p. 10). Sort the `N` samples increasingly,
`Z_{j_1} ≤ ⋯ ≤ Z_{j_N}`, remove the `m = ⌊Nω⌋` smallest and the `m` largest, and average the
remaining order statistics `Z_{j_{m+1}}, …, Z_{j_{N-m}}`:
`TrimmedMean = (N − 2m)⁻¹ ∑_{ι = m+1}^{N − m} Z_{j_ι}`.
When `Nω ∈ ℕ` this is the paper's `1/(N(1 − 2ω)) ∑_{ι=Nω+1}^{N(1−ω)} Z_{j_ι}` exactly.
Indices are 0-based: the sorted sample is `z ∘ Tuple.sort z`, and the kept positions are the
`ι : Fin N` with `m ≤ ι` and `ι + m < N`. For `0 ≤ ω < 1/2` and `N ≥ 1` the denominator
`N − 2m` is a positive integer. -/
noncomputable def trimmedMean {N : ℕ} (z : Fin N → ℝ) (ω : ℝ) : ℝ :=
  (∑ ι ∈ Finset.univ.filter
      (fun ι : Fin N => trimCount N ω ≤ ι.val ∧ ι.val + trimCount N ω < N),
      z (Tuple.sort z ι)) /
    ((N : ℝ) - 2 * (trimCount N ω : ℝ))

end RobustMultitask.Estimator


