-- Prove2me | Definitions.Def_IAFTRL_actionNorm
-- name    : IAFTRL_actionNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:39.004659+00:00
-- url     : https://prove2.me/theorems/a4d78c7f-0264-41fb-8b96-d2b7ab500324
-- title:
--   The action norm $\|z\|_{\mathcal A}$
-- statement:
--   For a finite action set $\mathcal A=\{a_1,\dots,a_K\}\subset\mathbb R^d$ and $z\in\mathbb R^d$, the **action norm** is
--   $$
--   \|z\|_{\mathcal A}=\max_{a\in\mathcal A}|a^\top z| .
--   $$
--   It measures loss vectors: the environment's loss vectors satisfy $\|\theta_t\|_{\mathcal A}\le 1$, and the corruption at round $t$ has size $\kappa_t=\|\theta_t-\theta\|_{\mathcal A}$. For a spanning set it is a norm.
--
--   **Formalization Note** A real supremum over the finite index set `Fin K`, which is a maximum whenever $K\ge 1$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 1.1, p.5; Appendix J.1, p.204

import Mathlib

namespace IAFTRL

open Matrix

/-- **The action norm `‖z‖_𝒜`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 1.1, p.5: "`‖θ_t‖_𝒜 := sup_{a∈𝒜} |a^⊤θ_t|`";
Appendix J.1, p.204: "For a compact spanning set define the action norm
`‖z‖_𝒜 = sup_{a∈𝒜} |a^⊤z|`".

For the finite action set `arms : Fin K → ℝ^d`, `actionNorm arms z = max_j |⟨arms j, z⟩|`.

**Formalization Note.** A real `⨆` over the finite index `Fin K`, hence a maximum when `K ≥ 1`
(which every spanning action set in dimension `d ≥ 1` satisfies). -/
noncomputable def actionNorm {d K : ℕ} (arms : Fin K → Fin d → ℝ) (z : Fin d → ℝ) : ℝ :=
  ⨆ j, |arms j ⬝ᵥ z|

end IAFTRL


