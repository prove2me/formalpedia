-- Prove2me | Definitions.Def_PhiDivRobust_Barrier_IsSelfConcordant
-- name    : PhiDivRobust_Barrier_IsSelfConcordant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:53:06.49799+00:00
-- url     : https://prove2.me/theorems/5c9db8b5-9288-4596-ac3a-db64a8057067
-- title:
--   κ-self-concordant function on an open convex set (Definition 1)
-- statement:
--   Let $E$ be a real normed vector space (in this mission $E=\mathbb R^3$), let $F\subseteq E$ and let $\kappa\in\mathbb R$. A function $\varphi:E\to\mathbb R$ is called **$\kappa$-self-concordant on $F$** if
--
--   1. $\kappa\ge 0$;
--   2. $F$ is open and convex;
--   3. $\varphi$ is three times continuously differentiable on $F$;
--   4. for every $y\in F$ and every direction $h\in E$,
--
--   $$\bigl|\nabla^3\varphi(y)[h,h,h]\bigr|\;\le\;2\kappa\,\bigl(h^{\mathsf T}\nabla^2\varphi(y)h\bigr)^{3/2},$$
--
--   where $\nabla^3\varphi(y)[h,h,h]$ is the third-order differential of $\varphi$ at $y$ in direction $h$ and $h^{\mathsf T}\nabla^2\varphi(y)h=\nabla^2\varphi(y)[h,h]$ the second-order one.
--
--   For $\kappa=1$ this is the classical self-concordance of Nesterov and Nemirovski; in general $\varphi$ is $\kappa$-self-concordant exactly when $\kappa^2\varphi$ is $1$-self-concordant. Self-concordance of a logarithmic barrier is what makes interior-point methods run in polynomial time on the corresponding constraint set.
--
--   **Formalization Note** The differentials are Mathlib's `iteratedFDeriv` applied to the constant tuple $(h,\dots,h)$; on the open set $F$ they coincide with the within-$F$ differentials. The power $x^{3/2}$ is `Real.rpow`, which returns $0$ for $x<0$; the definition does not require convexity of $\varphi$, and at a point where the second differential is negative in direction $h$ the Lean inequality then forces the third differential to vanish, which is stricter than the page, never weaker. The page states the definition on $F\subset\mathbb R^n$; the Lean definition is stated over an arbitrary real normed space and used only at $E=\mathbb R\times\mathbb R\times\mathbb R$.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 350, Definition 1

import Mathlib

namespace PhiDivRobust.Barrier

/-- Definition 1 (Ben-Tal et al. 2013, p. 350): `φ : F → ℝ` is `κ`-self-concordant on the open
convex set `F` if `κ ≥ 0`, `φ` is `C³` on `F`, and for every `y ∈ F` and every direction `h`,
`|∇³φ(y)[h,h,h]| ≤ 2κ (hᵀ∇²φ(y)h)^{3/2}`. -/
def IsSelfConcordant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : ℝ) (F : Set E) (φ : E → ℝ) : Prop :=
  0 ≤ κ ∧ IsOpen F ∧ Convex ℝ F ∧ ContDiffOn ℝ 3 φ F ∧
    ∀ y ∈ F, ∀ h : E,
      |iteratedFDeriv ℝ 3 φ y (fun _ => h)| ≤
        2 * κ * (iteratedFDeriv ℝ 2 φ y (fun _ => h)) ^ (3 / 2 : ℝ)

end PhiDivRobust.Barrier


