-- Prove2me | Definitions.Def_KnownFidelity_Rank_worstCopyComplexity
-- name    : KnownFidelity_Rank_worstCopyComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:49:28.546496+00:00
-- url     : https://prove2.me/theorems/868f5fdf-4f12-4dd6-a1b9-f34678d8ce49
-- title:
--   Worst-case copy complexity $\mathsf S(r,s,\varepsilon)=\sup_{\operatorname{rank}\sigma\le r}\mathsf S^{(\le s)}_\sigma(\varepsilon)$
-- statement:
--   For rank bounds $r,s$ and an accuracy $\varepsilon$,
--
--   $$\mathsf S(r,s,\varepsilon)=\sup_{\sigma:\ \operatorname{rank}\sigma\le r}\ \mathsf S^{(\le s)}_\sigma(\varepsilon),$$
--
--   where the supremum ranges over every finite ambient dimension $d$ and every state $\sigma$ on $\mathbb C^d$ of rank at most $r$. This is the quantity Theorem 1.2 determines up to logarithmic factors.
--
--   **Formalization Note** The supremum is taken in $\mathbb N\cup\{\infty\}$ over all $d$; no ambient dimension is fixed.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1 (unnumbered display), p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_copyComplexity

namespace KnownFidelity.Rank

/-- **Worst-case copy complexity `S(r, s, ε)`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1 (unnumbered display), printed p. 1 (PDF p. 3): "define
S(r, s, ε) = sup_{σ: rank σ≤r} S^(≤s)_σ(ε), where the supremum also ranges over finite ambient
dimensions."

`worstCopyComplexity r s ε` is the supremum, over every ambient dimension `d` and every state `σ`
on `ℂ^d` with `rank σ ≤ r`, of `S^{(≤s)}_σ(ε) = copyComplexity σ s ε`.

**Formalization Note.** The supremum is taken in `ℕ∞` over all `d : ℕ` (no ambient dimension is
fixed). When no state has rank at most `r` (only `r = 0`) the supremum is empty and equals `0`. -/
noncomputable def worstCopyComplexity (r s : ℕ) (ε : ℝ) : ℕ∞ :=
  ⨆ (d : ℕ) (σ : Matrix (Fin d) (Fin d) ℂ)
    (_ : QAlgorithms.IsDensityMatrix σ ∧ σ.rank ≤ r), copyComplexity σ s ε

end KnownFidelity.Rank


