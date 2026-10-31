-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_srt
-- name    : KallMayerSLP_SimpleRecourse_srt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:25.395659+00:00
-- url     : https://prove2.me/theorems/1ce88071-a649-401d-9217-459db5f68414
-- title:
--   Simple recourse type (SRT) function $\varphi(z,\xi)=\alpha[\xi-z]^+ + \beta[\xi-z]^- - \gamma$
-- statement:
--   For real constants $\alpha,\beta,\gamma$ (with $\alpha+\beta\ge 0$ in every result that uses it), the **simple recourse type function** is
--
--   $$
--   \varphi(z,\xi) := \alpha\,[\xi-z]^+ + \beta\,[\xi-z]^- - \gamma ,\qquad z,\xi\in\mathbb R,
--   $$
--
--   where $x^+=\max\{x,0\}$ and $x^-=\max\{-x,0\}$. As a function of $z$ it is piecewise linear with a kink at $z=\xi$: slope $-\alpha$ to the left and $\beta$ to the right. It is the optimal value of a one-row recourse problem with constant surplus and shortage costs.
--
--   **Formalization Note** The condition $\alpha+\beta\ge0$ of Definition 2.3 is a hypothesis of the theorems, not part of the definition.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Definition 2.3, p.228 (PDF 237)

import Mathlib

namespace KallMayerSLP.SimpleRecourse

/-- **Simple recourse type (SRT) function, Definition 2.3.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Definition 2.3, p.228 (PDF 237):
for real constants `α, β, γ` with `α + β ≥ 0`,
`φ(z, ξ) := α · [ξ − z]⁺ + β · [ξ − z]⁻ − γ`.

**Formalization Note.** `x⁺ = max x 0` and `x⁻ = max (−x) 0` (Mathlib's `posPart`/`negPart`), so
`[ξ − z]⁻ = max (z − ξ) 0`, the book's convention (Fig. 2.1: slope `−α` left of `z = ξ`, `β`
right of it). The condition `α + β ≥ 0` is a hypothesis of every theorem that uses `srt`, not part
of this definition. -/
def srt (α β γ z ξ : ℝ) : ℝ :=
  α * (ξ - z)⁺ + β * (ξ - z)⁻ - γ

end KallMayerSLP.SimpleRecourse


