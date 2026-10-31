-- Prove2me | Definitions.Def_ExitSpirals_coupledMap
-- name    : ExitSpirals_coupledMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:45.849327+00:00
-- url     : https://prove2.me/theorems/e8bf8a84-b132-4ed9-98fc-3bdc6f41ac68
-- title:
--   Coupled map $F(s,x)=x\,g_R(x\,g_C(s))$, its greatest fixed point $s^*(x)$ and the limit activity $a(x)$
-- statement:
--   Let $g_R,g_C$ be the corrected giant-component fractions of the two markets. The **coupled map** is
--   $$F(s,x)=x\,g_R\big(x\,g_C(s)\big),\qquad s,x\in[0,1].$$
--   Its **greatest fixed point** is written in Tarski's form,
--   $$s^*(x)=\sup\{s\in[0,1]:\ s\le F(s,x)\},$$
--   and the **limit activity** is
--   $$a(x)=s^*(x)\,g_C\big(s^*(x)\big).$$
--   With $s_R=s^*$ and $s_C=x\,g_C(s_R)$, one has $a(x)=x\,g_R(s_C)\,g_C(s_R)$: an agent is active when it is unshocked and supported through both markets.
--
--   **Formalization Note** The set in the supremum contains $0$ and is bounded by $1$. Lemma 6 prints the activity as $s^*$ itself; that counts support through $R$ only (in the $(2,2)$-regular case at $x=0.95$: $s^*=0.94703$ against activity $0.94406$). The two vanish together, so the threshold is the same.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Lemma 6, pp.51–52 (greatest solution, Tarski); p.54 (F(s, x) := x g_R(x g_C(s))); activity corrected (C3 of the plan)

import Mathlib
import Definitions.Def_ExitSpirals_giantFrac

namespace ExitSpirals

/-- **The coupled map** `F(s, x) := x g_R(x g_C(s))`.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, p.54: "Let
F(s, x) := x g_R(x g_C(s))". With `g_µ = giantFrac p_µ` (corrected (9)). -/
noncomputable def coupledMap (pR pC : ℕ → ℕ → ℝ) (s x : ℝ) : ℝ :=
  x * giantFrac pR (x * giantFrac pC s)

/-- **`s*(x)`, the greatest fixed point of `F(·, x)` in `[0, 1]`** (Lemma 6, pp.51–52: "by Tarski's
fixed point theorem a maximum fixed point s* exists"), written in Tarski's form
`sup {s ∈ [0,1] : s ≤ F(s, x)}`. That it is the greatest fixed point is the milestone
`ExitSpirals.lemma_6_greatest_fixed_point`.

**Formalization Note.** The set contains `0` and is bounded above by `1`, so `sSup` is a genuine
supremum. -/
noncomputable def sStar (pR pC : ℕ → ℕ → ℝ) (x : ℝ) : ℝ :=
  sSup {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ s ≤ coupledMap pR pC s x}

/-- **Limit activity** `a(x) = s_R g_C(s_R)` with `s_R = s*(x)` and `s_C = x g_C(s_R)`, which equals
`x g_R(s_C) g_C(s_R)`: an agent is active when unshocked and supported through both markets.

**Formalization Note.** Lemma 6 prints `Â(x) := s* = x g_R(x g_C(s*))`, which counts support through
R only; in the (2,2)-regular example at `x = 0.95` it gives `0.94703`, while the activity is
`0.94406` (simulation `≈ 0.944`). The two vanish together. -/
noncomputable def limitActivity (pR pC : ℕ → ℕ → ℝ) (x : ℝ) : ℝ :=
  sStar pR pC x * giantFrac pC (sStar pR pC x)

end ExitSpirals


