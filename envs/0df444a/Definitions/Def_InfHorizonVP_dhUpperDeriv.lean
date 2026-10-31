-- Prove2me | Definitions.Def_InfHorizonVP_dhUpperDeriv
-- name    : InfHorizonVP_dhUpperDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:39.122734+00:00
-- url     : https://prove2.me/theorems/dbbee555-eb14-45da-8d3c-5aa023b67c89
-- title:
--   Upper Dini–Hadamard directional derivative $\varphi^+(\bar x;v)$
-- statement:
--   For $\varphi:E\to[-\infty,+\infty]$, $\bar x\in E$ and $v\in E$,
--   $$
--   \varphi^+(\bar x;v)=\limsup_{u\to v,\ \theta\downarrow0}\frac{\varphi(\bar x+\theta u)-\varphi(\bar x)}{\theta}\in\mathbb R\cup\{\pm\infty\}.
--   $$
--
--   **Formalization Note** The $\limsup$ is taken in `EReal`.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.5

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Upper Dini–Hadamard directional derivative `φ⁺(x̄; v)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.5: "the upper directional derivative (or
Dini–Hadamard directional superderivative) of ϕ at x̄ in the direction v ∈ E is defined by
ϕ⁺(x̄; v) := limsup_{u→v, θ↓0} (ϕ(x̄ + θu) − ϕ(x̄))/θ ∈ R ∪ {±∞}."

**Formalization Note.** As for `dhLowerDeriv`: `EReal`-valued `φ`, `limsup` in `EReal` along
`𝓝[>] 0 ×ˢ 𝓝 v`. -/
noncomputable def dhUpperDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → EReal) (x v : E) : EReal :=
  limsup (fun q : ℝ × E => ((q.1⁻¹ : ℝ) : EReal) * (φ (x + q.1 • q.2) - φ x))
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝 v)

end InfHorizonVP


