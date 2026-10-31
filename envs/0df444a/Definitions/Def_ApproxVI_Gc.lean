-- Prove2me | Definitions.Def_ApproxVI_Gc
-- name    : ApproxVI_Gc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:58.4145+00:00
-- url     : https://prove2.me/theorems/06bd9428-21a2-4d5e-a9a3-180abca3f52e
-- title:
--   The piecewise-constant projection trajectory $G_c$
-- statement:
--   For the projection corrections $g_n$ of (19),
--
--   $$
--   G_c(t)=\sum_{m=0}^{n-1}g_m,\qquad t\in[t_n,t_{n+1}).
--   $$
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §6.1, p.22

import Mathlib
import Definitions.Def_ApproxVI_segIdx

namespace ApproxVI

/-- The piecewise-constant trajectory `G_c(t) := Σ_{m=0}^{n−1} g_m` for `t ∈ [tₙ, tₙ₊₁)` of
Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*, arXiv:1709.04673v5,
§6.1, p.22, where `gₙ` is the projection correction of (19).

**Formalization Note** `n` is `segIdx a t`, the index of the interval containing `t`. -/
noncomputable def Gc {d : ℕ} (a : ℕ → ℝ) (g : ℕ → Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  ∑ m ∈ Finset.range (segIdx a t), g m

end ApproxVI


