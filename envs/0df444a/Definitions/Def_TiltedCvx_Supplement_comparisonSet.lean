-- Prove2me | Definitions.Def_TiltedCvx_Supplement_comparisonSet
-- name    : TiltedCvx_Supplement_comparisonSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:25:29.379953+00:00
-- url     : https://prove2.me/theorems/96375027-ade7-4806-bb4e-8adf324ba9cf
-- title:
--   Comparison set (43)
-- statement:
--   Let $K\subseteq\mathbb R^d$, $f:K\to\mathbb R$, $x\in K$, $\gamma\in(0,1]$ and $q=q_f(x)$ a support vector at $x$. The **comparison set** is
--
--   $$
--   \big\{\,v\in[\gamma q,\gamma^{-1}q]\ :\ f(x)-\overline\psi_\gamma(f(y))\le\langle v,x-y\rangle\ \text{for every }y\in K\,\big\},\qquad\text{(43)}
--   $$
--
--   where $[p,p']$ is the closed segment between $p$ and $p'$. Its elements are comparison vectors valid against every comparator $y$ at once. Here $\overline\psi_\gamma(z)=\max\{\gamma z,\gamma^{-1}z\}$ is the upper tilt of §3 (the published `TiltedCvx.psiBar`).
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 26, (43), p.42

import Mathlib
import Definitions.Def_TiltedCvx_psiBar

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **The comparison set (43).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, Theorem 26,
(43), p.42: for `f : K → ℝ`, `x ∈ K` and a support vector `q = q_f(x)`, the set
`{v ∈ [γq, γ⁻¹q] : f(x) − ψ̄γ(f(y)) ≤ ⟨v, x − y⟩ for every y ∈ K}`, where `[p, p′]` is the closed
segment between `p` and `p′`.

**Formalization Note** `[γq, γ⁻¹q]` is `segment ℝ (γ • q) (γ⁻¹ • q)`. The comparison inequality is
in `EReal` (for `γ > 0`, `ψ̄γ` of a real is real). The tilt is the upper tilt
`ψ̄γ(z) = max{γz, γ⁻¹z}` (the published `TiltedCvx.psiBar`): the rendered (43) has the bar, which the
text layer drops. -/
def comparisonSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ : ℝ) (K : Set E) (f : E → ℝ) (x q : E) : Set E :=
  {v | v ∈ segment ℝ (γ • q) (γ⁻¹ • q) ∧
    ∀ y ∈ K, (f x : EReal) - TiltedCvx.psiBar γ (f y : EReal) ≤ ((⟪v, x - y⟫_ℝ : ℝ) : EReal)}

end TiltedCvx.Supplement


