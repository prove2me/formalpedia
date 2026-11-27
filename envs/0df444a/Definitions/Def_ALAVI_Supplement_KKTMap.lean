-- Prove2me | Definitions.Def_ALAVI_Supplement_KKTMap
-- name    : ALAVI_Supplement_KKTMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:28:08.43088+00:00
-- url     : https://prove2.me/theorems/684ff20a-10aa-44be-b696-544bf94e22f7
-- title:
--   The KKT mapping $H(u,p)$ of (VIP) (§5.1) (corrected: $\partial(J+\delta_U)$ for $\partial J+\mathcal N_U$)
-- statement:
--   Let $E=\mathbb R^n$ and $F=\mathbb R^m$ be finite-dimensional real inner product spaces, $U\subseteq E$, $C\subseteq F$ a closed convex cone with dual cone $C^*$, $G:E\to E$, $J:E\to(-\infty,+\infty]$ and $\Theta:E\to F$. The **KKT mapping** of (VIP) is the set-valued map $H:E\times F\rightrightarrows E\times F$,
--
--   $$
--   H(u,p)=\begin{pmatrix}G(u)+\partial(J+\delta_U)(u)+(\partial\Theta(u))^\top p\\[2pt]-\Theta(u)+\mathcal N_{C^*}(p)\end{pmatrix},
--   $$
--
--   where
--   - $\partial(J+\delta_U)(u)=\{g\in E: J(u)+\langle g,y-u\rangle\le J(y)\ \forall y\in U\}$ for $u\in U\cap\operatorname{dom}J$, and $\emptyset$ otherwise;
--   - $\partial\Theta(u)$ is Clarke's generalized Jacobian, the convex hull of all limits $\lim_i D\Theta(x_i)$ along sequences $x_i\to u$ of points where $\Theta$ is differentiable, and $(\partial\Theta(u))^\top p=\{M^\top p: M\in\partial\Theta(u)\}$;
--   - $\mathcal N_{C^*}(p)=\{n\in F:\langle n,p'-p\rangle\le0\ \forall p'\in C^*\}$ for $p\in C^*$, and $\emptyset$ otherwise.
--
--   The paper writes the first component as $G(u)+\partial J(u)+(\partial\Theta(u))^\top p+\mathcal N_U(u)$.
--
--   **Formalization Note.** Two changes from the printed formula. (1) $\partial J(u)+\mathcal N_U(u)$ is replaced by $\partial(J+\delta_U)(u)$. The second set always contains the first, and the two are equal under a qualification condition such as $\operatorname{ri}\operatorname{dom}J\cap\operatorname{ri}U\neq\emptyset$, which the paper does not assume. Without it the printed $H(u^k,p^k)$ can be empty along a whole ALAVI run (see `ALAVI.Supplement.theorem_2` and DISPROOF.md), and the bound (54) and the KKT clause of Theorem 2 fail. (2) The paper does not define $\partial\Theta$ for a nonsmooth $C$-convex $\Theta$. It is read as Clarke's generalized Jacobian (the published `NonsmoothNewton.Shared.clarkeJac`). This is the standard object for a map that is Lipschitz on an open set, which is the paper's (H5). It contains the Jacobian when $\Theta$ is differentiable, and its elements satisfy the bound $\|\theta^k\|\le\tau$ that (54) uses.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, §5.1, KKT mapping H, p.19

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac

namespace ALAVI.Supplement

/-- **The KKT mapping `H` of (VIP), §5.1** (corrected):
`H(u, p) = (G(u) + ∂(J + δ_U)(u) + (∂Θ(u))ᵀp, -Θ(u) + N_{C*}(p)) ⊆ E × F`.
The page writes the first component as `G(u) + ∂J(u) + (∂Θ(u))ᵀp + N_U(u)`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, §5.1, display after (52), p.19.

Formalization Notes:
- `∂(J + δ_U)(u)` is the convex subdifferential of `J` restricted to `U`: the `g` with
  `J(u) + ⟨g, y - u⟩ ≤ J(y)` for every `y ∈ U`, at a point `u ∈ U ∩ dom J` (empty otherwise).
  It replaces the page's `∂J(u) + N_U(u)`. The two sets agree when a qualification condition
  holds (`ri dom J ∩ ri U ≠ ∅`), and `∂(J + δ_U)(u)` always contains `∂J(u) + N_U(u)`. This is a
  correction: with the page's sum, `H(uᵏ, pᵏ)` can be empty along every ALAVI run, and then the
  KKT residual bound (54) fails (see `ALAVI.Supplement.theorem_2`).
- `∂Θ(u)` is read as Clarke's generalized Jacobian, the published
  `NonsmoothNewton.Shared.clarkeJac` (convex hull of the limits of `fderiv Θ` along sequences of
  differentiability points converging to `u`). The paper does not define `∂Θ` for nonsmooth
  `Θ`. It assumes `Θ` is `τ`-Lipschitz on an open set `O ⊇ U` ((H5)), which is the setting of
  Clarke's Jacobian, and (35)/(54) use a matrix `θᵏ ∈ ∂Θ(uᵏ)` with `‖θᵏ‖ ≤ τ`.
- `(∂Θ(u))ᵀp` is the set of `h ∈ E` with `⟨h, d⟩ = ⟨p, M d⟩` for every `d`, for some
  `M ∈ ∂Θ(u)` (that is, `h = Mᵀp`).
- `N_{C*}(p) = {n | ⟨n, p' - p⟩ ≤ 0 ∀ p' ∈ C*}` for `p ∈ C*` (empty for `p ∉ C*`),
  with `C* = ProperCone.innerDual C`. -/
def KKTMap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (u : E) (p : F) :
    Set (E × F) :=
  {z | (∃ g h : E,
        (u ∈ U ∧ u ∈ GoldenRatioVI.Fixed.effDom J ∧
          ∀ y ∈ U, J u + ((inner ℝ g (y - u) : ℝ) : EReal) ≤ J y) ∧
        (∃ M ∈ NonsmoothNewton.Shared.clarkeJac Θ u, ∀ d : E, inner ℝ h d = inner ℝ p (M d)) ∧
        z.1 = G u + g + h) ∧
      ∃ n : F,
        (p ∈ ProperCone.innerDual (C : Set F) ∧
          ∀ p' ∈ ProperCone.innerDual (C : Set F), inner ℝ n (p' - p) ≤ 0) ∧
        z.2 = -Θ u + n}

end ALAVI.Supplement


