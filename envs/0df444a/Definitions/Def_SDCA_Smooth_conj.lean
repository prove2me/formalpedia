-- Prove2me | Definitions.Def_SDCA_Smooth_conj
-- name    : SDCA_Smooth_conj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:56.947841+00:00
-- url     : https://prove2.me/theorems/35e5f3e0-d074-4a05-9e52-3861da1b7fa7
-- title:
--   $\gamma$-strong convexity of the convex conjugate $\varphi^*$ of a scalar loss
-- statement:
--   Let $\varphi:\mathbb R\to\mathbb R$. Its **convex conjugate** (the series' shared definition `SDCA.Lipschitz.conj`, imported here) is the extended-real function
--   $$\varphi^*(u)=\sup_{z\in\mathbb R}\big(zu-\varphi(z)\big)\in(-\infty,+\infty],\qquad u\in\mathbb R .$$
--   The paper writes $\max_z$; the supremum is used because it need not be attained and may be $+\infty$ (for a Lipschitz or a logistic loss, $\varphi^*$ is $+\infty$ outside a bounded interval). It is never $-\infty$, since $z=0$ gives $\varphi^*(u)\ge-\varphi(0)$.
--
--   For $\gamma\in\mathbb R$, the conjugate $\varphi^*$ is called **$\gamma$-strongly convex** when, for all $u,v\in\mathbb R$ and $s\in[0,1]$,
--   $$-\varphi^*\big(su+(1-s)v\big)\ \ge\ -s\,\varphi^*(u)-(1-s)\,\varphi^*(v)+\frac{\gamma s(1-s)}{2}(u-v)^2 .$$
--
--   The conjugates $\varphi_i^*$ of the losses define the dual problem of regularized loss minimization; strong convexity of $\varphi_i^*$ is the hypothesis of Lemma 1, the key estimate behind the linear rate of SDCA for smooth losses.
--
--   **Formalization Note** $\varphi^*$ takes values in `EReal` (`⨆ z, ((z*u - φ z : ℝ) : EReal)`), so it is $+\infty$ where the supremum is unbounded and never a junk real value. The strong-convexity inequality is stated in `EReal` with the real coefficients $s$, $1-s$ coerced; Mathlib's conventions $0\cdot(+\infty)=0$ and $(-\infty)+(+\infty)=-\infty$ make it the usual convex-analysis inequality (it holds trivially when a right-hand conjugate value with a positive coefficient is $+\infty$, and the endpoint cases $s\in\{0,1\}$ reduce to equalities).
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 2, conjugate φ*ᵢ(u) = max_z(zu − φᵢ(z)) and the γ-strong-convexity display after Definition 1

import Mathlib
import Definitions.Def_SDCA_Lipschitz_conj

namespace SDCA.Smooth

/-- `φ*` is `γ`-strongly convex in the form displayed on p. 2 (after Definition 1): for all
`u, v ∈ ℝ` and `s ∈ [0, 1]`,
`−φ*(s u + (1 − s) v) ≥ −s φ*(u) − (1 − s) φ*(v) + γ s (1 − s)/2 · (u − v)²`.
The inequality is in `EReal` with real coefficients coerced; Mathlib's `0 * ⊤ = 0` gives the
convex-analysis convention at `s ∈ {0, 1}`. -/
def ConjStronglyConvex (φ : ℝ → ℝ) (γ : ℝ) : Prop :=
  ∀ u v : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
    -SDCA.Lipschitz.conj φ (s * u + (1 - s) * v) ≥
      -(((s : ℝ) : EReal) * SDCA.Lipschitz.conj φ u) - ((1 - s : ℝ) : EReal) * SDCA.Lipschitz.conj φ v +
        ((γ * s * (1 - s) / 2 * (u - v) ^ 2 : ℝ) : EReal)

end SDCA.Smooth


