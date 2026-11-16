-- Prove2me | Definitions.Def_AuditAdapt_Supplement_blockMeans
-- name    : AuditAdapt_Supplement_blockMeans
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:34:46.752237+00:00
-- url     : https://prove2.me/theorems/7bd5734e-ebe8-414c-9368-be8cd84e3955
-- title:
--   Block means and medians of the median-of-means auditor
-- statement:
--   Given a sequence of samples $y_0,y_1,\dots$ and integers $m,k$, the **block means** are
--
--   $$
--   \bar y_j=\frac1m\sum_{i=0}^{m-1}y_{jm+i},\qquad j=0,\dots,k-1,
--   $$
--
--   the means of $k$ consecutive blocks of $m$ samples (the first $mk$ samples). A real number $r$ is a **median** of $k$ values $v_0,\dots,v_{k-1}$ if at least half of them are $\le r$ and at least half are $\ge r$. The sample sequence of a finite sample $\omega_0,\dots,\omega_{T-1}$ under a statistic $f$ is $i\mapsto f(\omega_i)$ (and $0$ beyond $T$).
--
--   These are the ingredients of the median-of-means auditors of Theorems 5.3 and 5.5: split the rounds into $k=\lceil 8\ln(1/\eta)\rceil$ blocks of $m$ rounds and output the median of the block means.
--
--   **Formalization Note** Samples are indexed from $0$. For $m=0$ each block mean is $0$ in Lean (an empty sum divided by $0$).
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), Theorem 5.3, p.5 (PDF p.5), the auditor's construction

import Mathlib

namespace AuditAdapt.Supplement

/-- The block means of the median-of-means auditor (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), Theorem 5.3, p.5: "Split T rounds
into k = ⌈8 ln(1/η)⌉ blocks of m = ⌈4 χ̄²(π)/δ²⌉ rounds each, and output the median of the block means").

`blockMeans m k y j = (1/m) Σ_{i<m} y(j·m + i)` for `j < k`: block `j` is the `j`-th run of `m`
consecutive samples, so the blocks use the first `m·k` samples `y 0, …, y (m·k − 1)`.

**Formalization Note** Samples are indexed from `0`. For `m = 0` every block mean is the empty sum
divided by `0`, i.e. `0` in Lean. -/
noncomputable def blockMeans (m k : ℕ) (y : ℕ → ℝ) : Fin k → ℝ :=
  fun j => (∑ i ∈ Finset.range m, y (j.1 * m + i)) / m

/-- `r` is a median of the `k` values `v`: at least half of them are `≤ r` and at least half are
`≥ r` (the median of Theorem 5.3, p.5). Every finite family with `k ≥ 1` has a median (e.g. its
lower median); for even `k` it may have several. -/
def IsMedian {k : ℕ} (v : Fin k → ℝ) (r : ℝ) : Prop :=
  k ≤ 2 * (Finset.univ.filter (fun j => v j ≤ r)).card ∧
    k ≤ 2 * (Finset.univ.filter (fun j => r ≤ v j)).card

/-- The sample sequence `i ↦ f(ω_i)` of a finite sample `ω : Fin T → α`, extended by `0` beyond
index `T` (used only below `T`: the auditors read the first `m·k ≤ T` samples). -/
noncomputable def sampleSeq {α : Type*} {T : ℕ} (f : α → ℝ) (ω : Fin T → α) (i : ℕ) : ℝ :=
  if h : i < T then f (ω ⟨i, h⟩) else 0

end AuditAdapt.Supplement


