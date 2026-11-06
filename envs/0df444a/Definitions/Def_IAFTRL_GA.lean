-- Prove2me | Definitions.Def_IAFTRL_GA
-- name    : IAFTRL_GA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:38.644442+00:00
-- url     : https://prove2.me/theorems/2e908ab4-63d9-4ae5-9874-8aae9f8b8f06
-- title:
--   Finite geometric interpolation constant $G_{\mathcal A}$
-- statement:
--   For each nonzero action $b\in\mathcal A$ let $u_b=b/\|b\|$, let $U_b$ be an orthonormal basis matrix of $u_b^\perp$, and for $a\ne b$ set
--   $$
--   x_{b,a}=U_b^\top a\in\mathbb R^{d-1},\qquad z_{b,a}=u_b^\top a .
--   $$
--   For every set $I$ of $d-1$ actions other than $b$ such that the $(d-1)\times(d-1)$ matrix $B_{b,I}$ with rows $x_{b,a}^\top$, $a\in I$, is invertible, let $v_{b,I}=B_{b,I}^{-1}(z_{b,a})_{a\in I}$ be the exact interpolant. The **finite geometric interpolation constant** is
--   $$
--   G_{\mathcal A}=\max\Big\{1,\ \max_{b\ne0}\ \max_{I:\det B_{b,I}\ne0}\ \max_{a\ne b}\frac{|z_{b,a}-x_{b,a}^\top v_{b,I}|}{\|b\|}\Big\}.
--   $$
--   In dimension one the basis is empty and the prediction $x_{b,a}^\top v_{b,I}$ is zero.
--
--   The residual measures how much of $a$ in the direction of $b$ is not predicted by an interpolant on $b^\perp$. Lemma C.3 uses $G_{\mathcal A}$ to bound the extra mass placed on the optimal action.
--
--   **Formalization Note** $U_b$ is one fixed choice (`perpBasis`); by Lemma C.1 the value does not depend on it. The rows of $B_{b,I}$ follow the increasing order of the index set $I$; neither $v_{b,I}$ nor the residual depends on the row order. The maximum is the supremum of a finite set of reals containing $1$. For $d=1$ the only index set is $I=\emptyset$, whose $0\times0$ matrix has determinant $1$, and the prediction is $0$, which is the paper's empty-basis convention.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Definition C.1, p.56, Eq. (C.6)

import Mathlib
import Definitions.Def_IAFTRL_perpBasis

namespace IAFTRL

open Matrix

/-- **Finite geometric interpolation constant `G_𝒜`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Definition C.1, p.56: "For each
nonzero action `b`, set `u_b = b/‖b‖` and let `U_b` be an orthonormal basis matrix of `u_b^⊥`. For
`a ≠ b`, define `x_{b,a} = U_b^⊤ a`, `z_{b,a} = u_b^⊤ a`. For each invertible `(d − 1)`-row submatrix
`B_{b,I}` with rows `x_{b,a}^⊤`, let `v_{b,I} = B_{b,I}^{-1}(z_{b,a})_{a∈I}` and define
`G_𝒜 = max{1, max_{b:b≠0} max_{I:det B_{b,I}≠0} max_{a≠b} |z_{b,a} − x_{b,a}^⊤ v_{b,I}| / ‖b‖}`. (C.6)
In dimension one, use the empty basis and the zero prediction."

Here `b = arms jb` ranges over the nonzero actions, `I` over the `(d − 1)`-element sets of actions
other than `b`, with `B_{b,I}` the `(d − 1) × (d − 1)` matrix whose rows are `x_{b,a}^⊤`, `a ∈ I`,
and `a` over the actions other than `b`. `G_𝒜` is the maximum of `1` and of all residual ratios
`|z_{b,a} − x_{b,a}^⊤ v_{b,I}| / ‖b‖` with `det B_{b,I} ≠ 0`.

**Formalization Note.** `U_b` is `perpBasis (arms jb)` (one fixed choice; by Lemma C.1 the value
does not depend on it). The rows of `B_{b,I}` are listed in the increasing order of `I ⊆ Fin K`
(`I.orderEmbOfFin`); neither `v_{b,I}` nor the residual depends on the row order. The maximum is
the real `sSup` of the finite set consisting of `1` and the residual ratios. For `d = 1` the basis
is `d × 0`, the only `I` is `∅` with `det = 1`, and the prediction `x^⊤ v` is `0`: this is the
paper's empty-basis convention. -/
noncomputable def GA {d K : ℕ} (arms : Fin K → Fin d → ℝ) : ℝ :=
  sSup ({1} ∪ {g : ℝ | ∃ (jb : Fin K) (I : Finset (Fin K)) (hI : I.card = d - 1) (a : Fin K),
    arms jb ≠ 0 ∧ jb ∉ I ∧ a ≠ jb ∧
    (Matrix.of fun i k => ((perpBasis (arms jb))ᵀ *ᵥ arms (I.orderEmbOfFin hI i)) k :
        Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ).det ≠ 0 ∧
    g = |(arms jb ⬝ᵥ arms a) / Real.sqrt (arms jb ⬝ᵥ arms jb) -
          ((perpBasis (arms jb))ᵀ *ᵥ arms a) ⬝ᵥ
            ((Matrix.of fun i k => ((perpBasis (arms jb))ᵀ *ᵥ arms (I.orderEmbOfFin hI i)) k :
                Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ)⁻¹ *ᵥ
              fun i => (arms jb ⬝ᵥ arms (I.orderEmbOfFin hI i)) /
                Real.sqrt (arms jb ⬝ᵥ arms jb))| /
        Real.sqrt (arms jb ⬝ᵥ arms jb)})

end IAFTRL


