-- Prove2me | Definitions.Def_MarkdownReadjust_eta
-- name    : MarkdownReadjust_eta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:45.692319+00:00
-- url     : https://prove2.me/theorems/712f6161-c645-44eb-b4c6-080fa4c69195
-- title:
--   Adjustment shift terms $\eta_n$ of (15)
-- statement:
--   For $n=0,\dots,N$ the adjustment shift terms are
--
--   $$
--   \eta_n=\frac{(\ln(x_0+1))^\alpha}{(\lambda T)^{1/2}}\left[\frac{T^{1/2}}{(t_{n+1}-t_n)^{1/2}}\mathbf 1\{n<N\}-\sum_{m=0}^{n-1}\frac{T^{1/2}(t_{m+1}-t_m)^{1/2}}{T-t_{m+1}}\right],
--   $$
--
--   with $\{t_n\}$ from (14). They are fixed at time $0$ and shift the target purchase rate of the policy (Lemma 7: they satisfy conditions (2) and (3)).
--
--   **Formalization Note** $(\cdot)^{1/2}$ is the real square root and $(\ln(x_0+1))^\alpha$ a real power. For $x_0\ge1$, $T>0$ every divisor is positive.
-- source:
--   Chen, Jasin, Simple monotonic readjustment policies with applications to markdown pricing and pricing in the presence of strategic customers, SSRN 3740871 (2023-10-09), §7.1, eq. (15), p.19

import Mathlib
import Definitions.Def_MarkdownReadjust_tgrid

namespace MarkdownReadjust

/-- The adjustment shift terms of (15) (Chen–Jasin, SSRN 3740871, §7.1, p.19): for
`n = 0, …, N`,
`ηₙ = (ln(x₀+1))^α/(λT)^{1/2} · [T^{1/2}/(t_{n+1} − tₙ)^{1/2} · 1{n < N}
  − Σ_{m=0}^{n−1} T^{1/2}(t_{m+1} − tₘ)^{1/2}/(T − t_{m+1})]`,
with `tₙ = tgrid x τ N n` from (14), for arrival rate `lam`, inventory `x`, horizon `τ`.

**Formalization Note.** `(·)^{1/2}` is `Real.sqrt`, `(ln(x₀+1))^α` is the real power
`Real.log (x+1) ^ α`, and `1{n < N}` is an `if`. For `x ≥ 1`, `τ > 0` every divisor is positive
when `n ≤ N`: `t_{n+1} − tₙ > 0` and `T − t_{m+1} > 0` for `m + 1 ≤ N`. -/
noncomputable def eta (lam α : ℝ) (x : ℕ) (τ : ℝ) (N n : ℕ) : ℝ :=
  Real.log ((x : ℝ) + 1) ^ α / Real.sqrt (lam * τ) *
    ((if n < N then Real.sqrt τ / Real.sqrt (tgrid x τ N (n + 1) - tgrid x τ N n) else 0)
      - ∑ m ∈ Finset.range n,
          Real.sqrt τ * Real.sqrt (tgrid x τ N (m + 1) - tgrid x τ N m) / (τ - tgrid x τ N (m + 1)))

end MarkdownReadjust


