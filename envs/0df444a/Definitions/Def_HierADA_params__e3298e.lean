-- Prove2me | Definitions.Def_HierADA_params__e3298e
-- name    : HierADA_params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:14.776809+00:00
-- url     : https://prove2.me/theorems/e3298ed0-545f-448c-9799-0d99040efa73
-- title:
--   Parameter choices of Sections 3.2–3.3
-- statement:
--   For an accuracy $\alpha$, a failure probability $\xi$ and a number of queries $k$, the paper chooses (with blocks and edges numbered from $1$):
--
--   1. $p$ the smallest integer with $4^{p-2}\big(\frac{\alpha}{4p}\big)^2\ge1$, and $\tau=\frac{\alpha}{4p}$;
--   2. $\varepsilon_j=\frac{1}{2^{j-1}\sqrt p}$ for the learned blocks $j<p$, and $\varepsilon_p=\frac{\tau}{512}$ for the anchor;
--   3. $B_j=\big\lceil\frac{32}{4^{j-1}\tau^2}\big\rceil$ for the edges $j\in[1,p)$;
--   4. $C_1=k+B_1$, $C_j=B_{j-1}+B_j$ for $2\le j<p$, and $C_p=B_{p-1}$;
--   5. $\delta=\frac{\tau\xi}{4096(p+1)}$, $L=\ln\Big[\frac{2p}{\delta}\Big(k+\sum_{j=1}^{p-1}B_j+1\Big)\Big]$ and $b=\frac{\tau}{256L}$.
--
--   For $\alpha<1/10$ these give $p=O(\log\frac1\alpha)$ and $1\le4^{p-2}\tau^2<4$.
--
--   **Formalization Note** Indices are 0-based, so $2^{j-1}$ and $4^{j-1}$ are written $2^j$ and $4^j$. The exponent $p-2$ is an integer exponent. $p$ is the infimum of the defining set of natural numbers; that set is nonempty for every $\alpha>0$ (proved in the verification file), so the infimum is the least element. $B$ is recorded as $0$ at the anchor, which has no edge, so the sum of $B$ over all blocks is the paper's $\sum_{j=1}^{p-1}B_j$. The logarithm is natural.
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Section 3.2, p.18 (p, τ, ε_j, B_j), and Section 3.3, p.24 (Equation (15), δ, L, b)

import Mathlib
import Definitions.Def_HierADA_Params

set_option autoImplicit false

namespace HierADA

/-- **The parameter choices of Sections 3.2–3.3** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), p.18 and p.24.

For accuracy `α`, failure probability `ξ` and query budget `k`:
1. `p` is the smallest integer with `4^{p-2} (α/(4p))² ≥ 1`, and `τ = α/(4p)` (p.18);
2. `ε_j = 1/(2^{j-1}√p)` for the learned blocks `j < p` and `ε_p = τ/512` for the anchor (p.18);
3. `B_j = ⌈32/(4^{j-1}τ²)⌉` for the edges `j ∈ [1, p)` (p.18);
4. `C_1 = k + B_1`, `C_j = B_{j-1} + B_j` for `2 ≤ j < p`, `C_p = B_{p-1}` (Equation (15), p.24);
5. `δ = τξ/(4096(p+1))`, `L = ln[(2p/δ)(k + ∑_{j<p} B_j + 1)]` and `b = τ/(256 L)` (p.24).

**Formalization Note.** Indices are 0-based (Lean's `j` is the paper's `j + 1`), so the paper's
`2^{j-1}` and `4^{j-1}` are written `2^j` and `4^j`. The exponent `p − 2` is an integer exponent
(`zpow`). `p` is `sInf` of the defining set of natural numbers; for every `α > 0` that set is nonempty
(proved in the verification file), so `sInf` is its least element (`p = 0` is never in the set, since
then `α/(4p) = 0` in Lean). `B` is recorded as `0` at the anchor, which has no edge; then
`∑_j B_j` over all blocks is the paper's `∑_{j=1}^{p-1} B_j`, and `C` at the anchor is
`B_{p-1} + 0`. `ln` is the natural logarithm. -/
noncomputable def params (α ξ : ℝ) (k : ℕ) : Params :=
  let p : ℕ := sInf {p : ℕ | 1 ≤ (4 : ℝ) ^ ((p : ℤ) - 2) * (α / (4 * p)) ^ 2}
  let τ : ℝ := α / (4 * p)
  let B : Fin p → ℕ := fun j =>
    if j.val + 1 < p then ⌈(32 : ℝ) / ((4 : ℝ) ^ j.val * τ ^ 2)⌉₊ else 0
  let δ : ℝ := τ * ξ / (4096 * ((p : ℝ) + 1))
  let L : ℝ := Real.log (2 * p / δ * ((k : ℝ) + ∑ j, (B j : ℝ) + 1))
  { p := p
    τ := τ
    ε := fun j => if j.val + 1 < p then 1 / ((2 : ℝ) ^ j.val * Real.sqrt p) else τ / 512
    B := B
    C := fun j => (if j.val = 0 then k else B ⟨j.val - 1, by omega⟩) + B j
    δ := δ
    L := L
    b := τ / (256 * L) }

end HierADA


