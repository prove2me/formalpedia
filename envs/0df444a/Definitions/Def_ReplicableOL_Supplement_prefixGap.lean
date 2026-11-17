-- Prove2me | Definitions.Def_ReplicableOL_Supplement_prefixGap
-- name    : ReplicableOL_Supplement_prefixGap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:17:11.032199+00:00
-- url     : https://prove2.me/theorems/db96f69a-365a-4986-bc64-719027076497
-- title:
--   Cumulative gap $D_s$
-- statement:
--   For two experts, the **gap** at round $t$ is $g_t=\ell_t(1)-\ell_t(2)\in[-1,1]$, and the **cumulative gap** is
--
--   $$
--   D_s=\sum_{t\le s} g_t,\qquad D_0=0 .
--   $$
--
--   DALR reads the losses only through these values.
--
--   **Formalization Note** Rounds are $0$-based in Lean, so $D_s$ is the sum over Lean rounds $u<s$, and Lean expert $0$ is the paper's expert $1$. The value is computed from a loss prefix of length $t$ and is the paper's $D_s$ for every $s\le t$, which is all DALR reads. The module also proves measurability in the prefix.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5, p.17 (Table 1 notation)

import Mathlib

namespace ReplicableOL.Supplement

/-- **Cumulative gap $D_s$ from a loss prefix.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5, p.17. "g_t = ℓ_t(1) − ℓ_t(2) ∈ [−1, 1] and D_s = Σ_{t≤s} g_t, D_0 = 0."

**Formalization Note.** Rounds are 0-based, so the paper's `D_s` is the sum over Lean rounds `u < s`; Lean expert `0` is the paper's expert 1. From a prefix of length `t` the value is the paper's `D_s` for every `s ≤ t` (DALR reads only such `s`). -/
noncomputable def prefixGap {t : ℕ} (x : Fin t → Fin 2 → ℝ) (s : ℕ) : ℝ :=
  ∑ u : Fin t, if u.val < s then x u 0 - x u 1 else 0

/-- The gap is a measurable function of the prefix. -/
theorem measurable_prefixGap {t : ℕ} (s : ℕ) :
    Measurable fun x : Fin t → Fin 2 → ℝ => prefixGap x s := by
  unfold prefixGap
  refine Finset.measurable_sum _ fun u _ => ?_
  split_ifs
  · fun_prop
  · exact measurable_const

end ReplicableOL.Supplement


