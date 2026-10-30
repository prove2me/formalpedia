-- Prove2me | Definitions.Def_KarimiPL_ProxCD_sepDom
-- name    : KarimiPL_ProxCD_sepDom
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:51:20.802516+00:00
-- url     : https://prove2.me/theorems/e2e33efe-f3f0-4d5c-9584-e306d77d2995
-- title:
--   Effective domain of a separable function: $D_1 \times \dots \times D_d$
-- statement:
--   Throughout, $\mathbb{R}^d$ carries the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$, $e_i$ is the $i$-th unit vector, $x_i$ the $i$-th coordinate of $x$, and $\nabla_i f(x)$ the $i$-th coordinate of $\nabla f(x)$. The composite objective is $F = f + g$ with $f : \mathbb{R}^d \to \mathbb{R}$ differentiable and $g : \mathbb{R}^d \to (-\infty, +\infty]$ extended-valued.
--
--   Let $D_1, \dots, D_d \subseteq \mathbb{R}$ be the effective domains of univariate functions $g_i : \mathbb{R} \to (-\infty, +\infty]$, i.e. $D_i = \{t : g_i(t) < +\infty\}$. The effective domain of the separable function $g(x) = \sum_i g_i(x_i)$ is
--   $$\operatorname{dom} g = \{x \in \mathbb{R}^d : x_i \in D_i \text{ for every } i\} .$$
--
--   For an indicator of a box $\prod_i [a_i, b_i]$ this is the box itself; for $g = \lambda\|x\|_1$ it is all of $\mathbb{R}^d$.
--
--   **Formalization Note** No closedness of the $D_i$ is assumed anywhere in the mission.
-- source:
--   Karimi, Nutini, Schmidt, Linear Convergence of Gradient and Proximal-Gradient Methods Under the Polyak-Łojasiewicz Condition, arXiv:1608.04636v4, §4.3, p. 10 and §4, p. 8

import Mathlib

namespace KarimiPL.ProxCD

/-- **The effective domain of a separable extended-valued `g(x) = ∑ᵢ gᵢ(xᵢ)`.**
Karimi, Nutini, Schmidt, *Linear Convergence of Gradient and Proximal-Gradient Methods Under the
Polyak-Łojasiewicz Condition*, arXiv:1608.04636v4, §4.3, p. 10: "g is a separable function. This means that g(x) = Σi gi(xi) for a set of
univariate functions gi"; §4, p. 8: g may be an indicator function "that [is] zero if x lies in
a simple convex set and [is] infinity otherwise".

`sepDom Dc = {x | ∀ i, x i ∈ Dc i}`: `g(x) < +∞` exactly when every `gᵢ(xᵢ) < +∞`.

**Formalization Note.** `Dc i` is the effective domain of `gᵢ`; together with the finite
values `gc i` (see `sepG`) it encodes `gᵢ : ℝ → (−∞, ∞]`. No closedness of `Dc i` is
assumed anywhere. -/
def sepDom {d : ℕ} (Dc : Fin d → Set ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, x i ∈ Dc i}

end KarimiPL.ProxCD


