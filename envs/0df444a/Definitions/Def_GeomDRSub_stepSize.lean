-- Prove2me | Definitions.Def_GeomDRSub_stepSize
-- name    : GeomDRSub_stepSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:12.248287+00:00
-- url     : https://prove2.me/theorems/65d30304-b54a-4433-8f6e-7379f0cac27f
-- title:
--   Step size $\eta=D/\sqrt{TV_{\mathrm{gen}}}$ of Algorithm 1
-- statement:
--   For a diameter bound $D$, a moment bound $V$ and a horizon $T$,
--   $$
--   \eta=\begin{cases}D/\sqrt{T\,V},& D>0\text{ and }V>0,\\ 0,&\text{otherwise.}\end{cases}
--   $$
--   Algorithm 1 uses $\eta=D/\sqrt{TV_{\mathrm{gen}}}$ for $D,V_{\mathrm{gen}}>0$; when $D=0$ or $V_{\mathrm{gen}}=0$ the paper holds the state fixed at $x_1$, which is the update with $\eta=0$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Algorithm 1, p.20; Lemma 5.2 and Corollary 5.3, pp.20–21

import Mathlib

namespace GeomDRSub

/-- **The step size of Algorithm 1.** Aggarwal–Lu, arXiv:2610.00545, Algorithm 1, p.20:
"Input: … diameter bound `D > 0`, moment bound `V_gen > 0`. Initialize: `x₁ = 0` and
`η = D/√(T V_gen)`", and p.21 (after Corollary 5.3): "If `D = 0` or `V_gen = 0`, Lemma 5.2 with a
fixed state gives zero linear regret and the same bound"; Lemma 5.2, p.20: "If `D = 0` or `V = 0`,
then (62) holds with the state held fixed at `x₁`."

`stepSize D V T` is `D/√(T·V)` when `D > 0` and `V > 0`, and `0` otherwise.

**Formalization Note.** Step size `0` holds the state fixed (`x_{t+1} = Π_K(x_t) = x_t` for
`x_t ∈ K`), which is the paper's degenerate case. For `T = 0` the value is irrelevant (no round
is played). -/
noncomputable def stepSize (D V : ℝ) (T : ℕ) : ℝ :=
  if 0 < D ∧ 0 < V then D / Real.sqrt (T * V) else 0

end GeomDRSub


