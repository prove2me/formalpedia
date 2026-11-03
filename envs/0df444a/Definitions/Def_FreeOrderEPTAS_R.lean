-- Prove2me | Definitions.Def_FreeOrderEPTAS_R
-- name    : FreeOrderEPTAS_R
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:58.829128+00:00
-- url     : https://prove2.me/theorems/6e719f20-25ca-4b34-8246-3c133ffbab40
-- title:
--   The backward recursion $R_t$
-- statement:
--   For a permutation $\sigma$, the recursion is
--   $$R_{n+1}=0,\qquad R_t=\mathbb E[\max\{X_{\sigma(t)},R_{t+1}\}]\quad(1\le t\le n).$$
--   For an optimal permutation $\sigma^*$ these are the values $V^*_t$ of the paper.
--
--   It computes $V(\sigma)=R_1$ with $n$ oracle calls and drives the bucket analysis.
--
--   **Formalization Note** Time is 0-based: `R I σ t` is the paper's $R_{t+1}$, `R I σ 0` is $R_1$, and `R I σ t = 0` for $t\ge n$. It is a right fold over the times $\ge t$, so no natural subtraction occurs.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, p.17; §3.5, p.20

import Mathlib
import Definitions.Def_FreeOrderEPTAS_orc

namespace FreeOrderEPTAS

/-- The backward recursion of pp.17, 20 (arXiv:2007.13121v3): `R_{n+1} = 0` and
`R_t = E[max{X_{σ(t)}, R_{t+1}}]`.

**Formalization Note.** Time is 0-based: `R I σ t` is the paper's `R_{t+1}`, so `R I σ 0` is `R_1`
and `R I σ n = 0`; for `σ = σ*` it is `V*_{t+1}`. Defined as a right fold over the times `≥ t`, so no
natural subtraction occurs; `R I σ t = 0` for every `t ≥ n`. -/
noncomputable def R {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) (t : ℕ) : ℝ :=
  ((List.finRange n).drop t).foldr (fun s v => orc I (σ s) v) 0

end FreeOrderEPTAS


