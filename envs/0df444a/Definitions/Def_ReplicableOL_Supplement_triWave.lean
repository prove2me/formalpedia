-- Prove2me | Definitions.Def_ReplicableOL_Supplement_triWave
-- name    : ReplicableOL_Supplement_triWave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:18:55.407945+00:00
-- url     : https://prove2.me/theorems/eb32d540-11a5-4001-9460-d9760664aab0
-- title:
--   Triangle-wave loss sequence $S^{\triangle}$
-- statement:
--   For a horizon $T$ and a half-period $A_1$ with $\Pi=T/(2A_1)$ periods, the **triangle wave** $S^\triangle$ has
--
--   $$
--   g_t=+1 \text{ for } t\in(2qA_1,(2q+1)A_1],\qquad g_t=-1 \text{ for } t\in((2q+1)A_1,(2q+2)A_1],
--   $$
--
--   $q=0,\dots,\Pi-1$, realized by $\ell_t=(1,0)$ when $g_t=+1$ and $\ell_t=(0,1)$ when $g_t=-1$. The cumulative gap rises from $0$ to $A_1$ and falls back once per period, so $D_T=0$. It is a deterministic sequence, hence a product law.
--
--   **Formalization Note** Rounds are $0$-based: Lean round $t$ (the paper's round $t+1$) has $\ell=(1,0)$ iff $\lfloor t/A_1\rfloor$ is even. Lean expert $0$ is the paper's expert $1$.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 5.4, p.21

import Mathlib

namespace ReplicableOL.Supplement

/-- **The triangle wave $S^\triangle$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 5.4, p.21. "Let S^△ have g_t = +1 for t ∈ (2qA_1, (2q + 1)A_1] and g_t = −1 for t ∈ ((2q+1)A_1, (2q+2)A_1], for q = 0, …, Π−1 with Π := T/(2A_1) periods, realized by ℓ_t ∈ {(1, 0), (0, 1)}."

**Formalization Note.** Rounds are 0-based: Lean round `t` is the paper's round `t + 1`, which has `g = +1`, i.e. `ℓ = (1, 0)`, iff `⌊t/A_1⌋` is even; Lean expert `0` is the paper's expert 1. -/
noncomputable def triWave (T A₁ : ℕ) : Fin T → Fin 2 → ℝ :=
  fun t i => if Even (t.val / A₁) then (if i = 0 then 1 else 0) else (if i = 0 then 0 else 1)

end ReplicableOL.Supplement


