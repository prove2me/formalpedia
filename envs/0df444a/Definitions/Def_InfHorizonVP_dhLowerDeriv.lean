-- Prove2me | Definitions.Def_InfHorizonVP_dhLowerDeriv
-- name    : InfHorizonVP_dhLowerDeriv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:37.609237+00:00
-- url     : https://prove2.me/theorems/d5369a49-1ce3-4179-9d97-ef595b8c2601
-- title:
--   Lower Dini–Hadamard directional derivative $\varphi^-(\bar x;v)$
-- statement:
--   For $\varphi:E\to[-\infty,+\infty]$, $\bar x\in E$ and $v\in E$,
--   $$
--   \varphi^-(\bar x;v)=\liminf_{u\to v,\ \theta\downarrow0}\frac{\varphi(\bar x+\theta u)-\varphi(\bar x)}{\theta}\in\mathbb R\cup\{\pm\infty\}.
--   $$
--
--   **Formalization Note** The $\liminf$ is taken in `EReal`; the derivative is only used at points where $\varphi(\bar x)$ is finite.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §2, p.5

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Lower Dini–Hadamard directional derivative `φ⁻(x̄; v)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §2, p.5: "The lower directional derivative (or
contingent, or Dini–Hadamard directional subderivative) of ϕ : E → R ∪ {+∞} at x̄ ∈ dom ϕ in the
direction v ∈ E is defined by ϕ⁻(x̄; v) := liminf_{u→v, θ↓0} (ϕ(x̄ + θu) − ϕ(x̄))/θ ∈ R ∪ {±∞}".

**Formalization Note.** `φ` is `EReal`-valued and the `liminf` is taken in `EReal` along
`𝓝[>] 0 ×ˢ 𝓝 v` (pairs `(θ, u)` with `θ ↓ 0`, `u → v`), so an unbounded quotient gives `±∞`
rather than a junk value. The quotient is `θ⁻¹ · (φ(x̄ + θu) − φ(x̄))`; it is used only at points
`x̄` where `φ(x̄)` is finite (see `dhSubdiff`), where no `∞ − ∞` arises. -/
noncomputable def dhLowerDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E → EReal) (x v : E) : EReal :=
  liminf (fun q : ℝ × E => ((q.1⁻¹ : ℝ) : EReal) * (φ (x + q.1 • q.2) - φ x))
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝 v)

end InfHorizonVP


