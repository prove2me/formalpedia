-- Prove2me | Definitions.Def_OnlineUBSR_Jfun
-- name    : OnlineUBSR_Jfun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:19:46.447982+00:00
-- url     : https://prove2.me/theorems/d564a379-4c7c-46d3-ba1f-62170bc851ba
-- title:
--   The averaged derivative $J(t)=\int_0^1 g'(mt+(1-m)SR_\lambda(X))\,dm$
-- statement:
--   For $t\in\mathbb R$ let
--
--   $$
--   J(t)=\int_0^1 g'\big(m\,t+(1-m)\,SR_\lambda(X)\big)\,dm ,
--   $$
--
--   the average slope of $g$ on the segment between $SR_\lambda(X)$ and $t$. The proof of Theorem 1 sets $J_k=J(t_k)$ and writes $g(t_k)=J_k\,(t_k-SR_\lambda(X))$, which turns the recursion into a linear one in $z_k=t_k-SR_\lambda(X)$.
--
--   **Formalization Note** $g'$ is the two-sided derivative of $g$ on $\mathbb R$ and the integral is the interval integral over $[0,1]$. $J$ is a function of the point $t$; the proof uses it at $t_0$ as well.
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §7.1, eq. (27), p.18

import Mathlib
import Definitions.Def_OnlineUBSR_gFun
import Definitions.Def_OnlineUBSR_ubsr

open MeasureTheory

namespace OnlineUBSR

/-- **The averaged derivative `J` of (27).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §7.1, (27), p.18: "For any k ≥ 1,
define Jk = ∫₀¹ g′(mtk + (1 − m)SRλ(X))dm."

`Jfun μ ℓ lam X t = ∫_0^1 g′(m t + (1 − m) SR_λ(X)) dm`, so that `J_k = Jfun … (t_k)`.

**Formalization Note.** `J` is defined as a function of the point `t`, so that `J_k = J(t_k)`;
the proof also uses it at `k = 0`. `g′` is Mathlib's two-sided `deriv` of `g = OnlineUBSR.gFun`
on `ℝ`, and the integral is the interval integral over `[0, 1]`. -/
noncomputable def Jfun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ℓ : ℝ → ℝ) (lam : ℝ)
    (X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ m in (0 : ℝ)..1, deriv (gFun μ ℓ lam X) (m * t + (1 - m) * ubsr μ ℓ lam X)

end OnlineUBSR


