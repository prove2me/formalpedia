-- Prove2me | Definitions.Def_AdaGradDHS_Diag_IsDualBound
-- name    : AdaGradDHS_Diag_IsDualBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:33.694848+00:00
-- url     : https://prove2.me/theorems/f3015639-ed3f-407f-b85e-c98aac936fbd
-- title:
--   $G$ bounds the dual seminorm: $\|g\|_{\psi^*} \le G$
-- statement:
--   Let $\|\cdot\|_\psi$ be a seminorm on $\mathbb{R}^d$, $g \in \mathbb{R}^d$ and $G \in \mathbb{R}$. We say **$G$ bounds the dual seminorm of $g$** if
--   $$\langle g, v\rangle \le G\,\|v\|_\psi \qquad \text{for every } v \in \mathbb{R}^d .$$
--
--   The dual norm $\|g\|_{\psi^*} = \sup\{\langle g, v\rangle : \|v\|_\psi \le 1\}$ appears squared in the regret bounds (10) and (11). It may be $+\infty$ when $\|\cdot\|_\psi$ is only a seminorm. If it is finite, $G = \|g\|_{\psi^*}$ satisfies the condition, and every $G$ satisfying it is at least $\|g\|_{\psi^*}$ whenever the latter is positive.
--
--   **Formalization Note** Each squared dual norm $\|g_t\|^2_{\psi^*}$ of a regret bound is written $G_t^2$ together with this hypothesis, instead of a real supremum (which Lean would set to $0$ on an unbounded set). When the dual norm is $+\infty$, no real $G_t$ exists and the paper's bound is vacuous as well.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), §2, p. 2129 ("We also denote the dual norm of ‖·‖ψt by ‖·‖ψ∗t")

import Mathlib

namespace AdaGradDHS.Diag

/-- **`G` bounds the dual (semi)norm of `g`: `‖g‖_{ψ*} ≤ G`.**
Duchi, Hazan, Singer, *Adaptive Subgradient Methods for Online Learning and Stochastic
Optimization*, JMLR 12 (2011), §2, p. 2129 (unnumbered): "We also denote the dual norm of ‖·‖ψt by ‖·‖ψ∗t."

`IsDualBound n g G` says `⟨g, v⟩ ≤ G · n(v)` for every vector `v`.

**Formalization Note.** The dual norm `‖g‖_* = sup {⟨g, v⟩ : n(v) ≤ 1}` of a seminorm `n` may be
`+∞` (when `g` is not orthogonal to the kernel of `n`), so it is not encoded as a real
supremum (which Lean would set to `0` on an unbounded set). Instead every term `‖g‖²_*` of a
regret bound is written `G ^ 2` together with the hypothesis `IsDualBound n g G`. If `‖g‖_*` is
finite, `G = ‖g‖_*` satisfies the hypothesis and recovers the paper's bound; any valid `G` is at
least `‖g‖_*` when `‖g‖_* > 0`. If `‖g‖_* = +∞` no real `G` exists and the paper's bound is
vacuous as well. -/
def IsDualBound {d : ℕ} (n : Seminorm ℝ (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d)) (G : ℝ) : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin d), inner ℝ g v ≤ G * n v

end AdaGradDHS.Diag


