-- Prove2me | Definitions.Def_TiltedCvx_Supplement_IsComparisonMap
-- name    : TiltedCvx_Supplement_IsComparisonMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:25:55.64152+00:00
-- url     : https://prove2.me/theorems/b9899e64-7895-4ef1-9bde-504f967d2633
-- title:
--   Comparison map for lower-linearizability ((40)–(41))
-- statement:
--   Let $K\subseteq\mathbb R^d$, $\alpha\in(0,1]$ and $\mathcal C$ a class of functions on $K$. The class is lower-linearizable with coefficient $\alpha$ if there are maps $g:\mathcal C\times K\to\mathbb R^d$, $\chi:K\to K$ and $\beta>0$ with $f(\chi(x))-\overline\psi_\alpha(f(y))\le\beta\langle g(f,x),x-y\rangle$ (40). The paper uses the case $\chi=\mathrm{id}$, $\beta=1$:
--
--   $$
--   f(x)-\overline\psi_\alpha(f(y))\ \le\ \langle g(f,x),x-y\rangle\qquad\text{for all }f\in\mathcal C,\ x,y\in K .\qquad\text{(41)}
--   $$
--
--   Here $\overline\psi_\alpha(z)=\max\{\alpha z,\alpha^{-1}z\}$ is the upper tilt of §3 (the published `TiltedCvx.psiBar`), so $\overline\psi_\alpha(z)=\alpha z$ for $z\le 0$. A map $g$ satisfying (41) is called here a comparison map for $\mathcal C$; it reduces online optimization over $\mathcal C$ to online linear optimization with $\alpha$–regret.
--
--   **Formalization Note** Functions on $K$ are real functions on $\mathbb R^d$ read on $K$; $g$ is read only at $f\in\mathcal C$, $x\in K$. A comparison map witnesses (40) with $\chi=\mathrm{id}$, $\beta=1$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §8.2, (40)–(41), p.41

import Mathlib
import Definitions.Def_TiltedCvx_psiBar

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **Comparison map for lower-linearizability with coefficient α ((40)–(41)).**
Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472, §8.2, (40)–(41), p.41: a class `𝓒` of
functions on `K` is lower-linearizable with coefficient `α` if there are maps
`g : 𝓒 × K → ℝ^d`, `χ : K → K` and `β > 0` with `f(χ(x)) − ψ̄α(f(y)) ≤ β⟨g(f, x), x − y⟩` (40);
in the special case `χ = id`, `β = 1` used by the paper this reads
`f(x) − ψ̄α(f(y)) ≤ ⟨g(f, x), x − y⟩` for all `f ∈ 𝓒` and `x, y ∈ K` (41).
`IsComparisonMap α K 𝓒 g` says that `g` satisfies (41).

**Formalization Note** Functions on `K` are `E → ℝ` (only values on `K` enter); `g` is a map
`(E → ℝ) → E → E`, read only at `f ∈ 𝓒`, `x ∈ K`. A map satisfying (41) witnesses (40) with
`χ = id`, `β = 1`. The tilt is the upper tilt `ψ̄α(z) = max{αz, α⁻¹z}` (the published
`TiltedCvx.psiBar`; the rendered (40)–(41) have the bar, which the text layer drops), so that
`ψ̄α(z) = αz` for `z ≤ 0`, as the paper notes after (40). -/
def IsComparisonMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (α : ℝ) (K : Set E) (C : Set (E → ℝ)) (g : (E → ℝ) → E → E) : Prop :=
  ∀ f ∈ C, ∀ x ∈ K, ∀ y ∈ K,
    (f x : EReal) - TiltedCvx.psiBar α (f y : EReal) ≤ ((⟪g f x, x - y⟫_ℝ : ℝ) : EReal)

end TiltedCvx.Supplement


