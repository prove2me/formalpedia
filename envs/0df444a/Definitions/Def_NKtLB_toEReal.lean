-- Prove2me | Definitions.Def_NKtLB_toEReal
-- name    : NKtLB_toEReal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:45.248535+00:00
-- url     : https://prove2.me/theorems/bd39cf6d-2e39-479f-8442-d4bae175256f
-- title:
--   Complexities with value $\infty$ as extended reals
-- statement:
--   The map $\mathbb N\cup\{\infty\}\to[-\infty,\infty]$ that sends $k$ to $k$ and $\infty$ to $+\infty$. It is used to compare complexities, which are $\infty$ when no program qualifies, with real-valued bounds such as $m+C\log^3 n$.
--
--   **Formalization Note** Only $\infty+a$ and $\infty-a$ with $a$ real occur, and both equal $+\infty$. So $\mathrm{rK}(x)=\infty$ makes an upper bound on $\mathrm{rK}(x)$ false and a hypothesis $m\le\mathrm{rK}(x)-a$ true, as with the paper's $\min\emptyset=\infty$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §12, pp.67–77

import Mathlib

namespace NKtLB

/-- **`ℕ∞`-valued complexities as extended reals**: `k ↦ k`, `⊤ ↦ ⊤`. Used to compare a complexity
(`⊤` when no program qualifies) with real-valued bounds such as `m + C · log³ n`
(Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §12, pp.67–77).

**Formalization Note.** Only `⊤ + a` and `⊤ - a` with `a` real occur in the statements; both are
`⊤`, so "`rK(x) = ∞`" makes an upper bound on `rK(x)` false and a hypothesis
"`m ≤ rK(x) - a`" true, as for the paper's `min ∅ = ∞`. -/
noncomputable def toEReal (a : ℕ∞) : EReal := ((a : ENNReal) : EReal)

end NKtLB


