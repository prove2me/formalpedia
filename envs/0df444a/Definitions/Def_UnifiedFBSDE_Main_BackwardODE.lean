-- Prove2me | Definitions.Def_UnifiedFBSDE_Main_BackwardODE
-- name    : UnifiedFBSDE_Main_BackwardODE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:22.472721+00:00
-- url     : https://prove2.me/theorems/25e6c04d-13b5-4ee7-a219-1edff4f77c2f
-- title:
--   (5.1)–(5.2), p. 20 — solutions of the backward integral equation y_t = h + ∫ₜᵀ F(s, y_s) ds on [0, T]
-- statement:
--   Let $T>0$, $h\in\mathbb R$ and $F:[0,T]\times\mathbb R\to\mathbb R$. A function $y:[0,T]\to\mathbb R$ **solves the backward ODE**
--
--   $$
--   y_t = h + \int_t^T F(s,y_s)\,ds,\qquad t\in[0,T],
--   $$
--
--   if for every $t\in[0,T]$ the function $s\mapsto F(s,y_s)$ is Lebesgue integrable on $[t,T]$ and the identity holds. A function is **bounded on $[0,T]$** if $\sup_{t\in[0,T]}|y_t|<\infty$.
--
--   Every ordinary differential equation of the paper — (3.13), (5.1), (5.2) — is of this backward form; the comparison lemma (Lemma 5.1) and the dominating ODEs of §5 are stated with it.
--
--   **Formalization Note** Integrability is required explicitly: Lean's integral of a non-integrable function is $0$, and without the requirement any $y$ with $y_T=h$ would count as a solution. Values of $y$ outside $[0,T]$ play no role.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, pp. 19–20, (5.1), (5.2)

import Mathlib

namespace UnifiedFBSDE.Main

open MeasureTheory Set

/-- `y` solves the backward integral equation `y_t = h + ∫ₜᵀ F(s, y_s) ds` on `[0, T]`:
for every `t ∈ [0, T]`, the integrand `s ↦ F(s, y_s)` is integrable on `[t, T]` and the equation
holds. Values of `y` outside `[0, T]` are irrelevant. -/
def SolvesBackwardODE (T h : ℝ) (F : ℝ → ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T,
    IntegrableOn (fun s => F s (y s)) (Icc t T) ∧ y t = h + ∫ s in t..T, F s (y s)

/-- `y` is bounded on `[0, T]`. -/
def BoundedOn (T : ℝ) (y : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, |y t| ≤ C

end UnifiedFBSDE.Main


