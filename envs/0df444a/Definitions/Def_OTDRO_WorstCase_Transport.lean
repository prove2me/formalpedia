-- Prove2me | Definitions.Def_OTDRO_WorstCase_Transport
-- name    : OTDRO_WorstCase_Transport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:14.514621+00:00
-- url     : https://prove2.me/theorems/5f383d71-63fe-4ad0-a9ed-43ed3ba8072d
-- title:
--   Theorem 6(c), p. 14 — the map x ↦ x + √δ g(x)A(x)⁻¹β of (10), graph couplings, c̄, c̲ and the Bernoulli mixture law of (X, X*)
-- statement:
--   Fix $\delta>0$, $\beta\in\mathbb R^d$ and $A$ as in Assumption 1. For a scalar function $g:\mathbb R^d\to\mathbb R$ define the transport map of display (10)
--   $$T_g(x)=x+\sqrt\delta\,g(x)\,A(x)^{-1}\beta ,$$
--   and for any map $T$ the **graph coupling** $\mathrm{Law}(X,T(X))$, $X\sim P_0$ (the pushforward of $P_0$ under $x\mapsto(x,T(x))$). For two functions $G_-,G_+$ set
--   $$\bar c=E_{P_0}\bigl[G_+(X)^2\,\beta^{\mathsf T}A(X)^{-1}\beta\bigr],\qquad \underline c=E_{P_0}\bigl[G_-(X)^2\,\beta^{\mathsf T}A(X)^{-1}\beta\bigr],\qquad q=\frac{\bar c-1}{\bar c-\underline c},$$
--   and define the **mixture coupling**
--   $$\pi^*=q\cdot\mathrm{Law}\bigl(X,T_{G_-}(X)\bigr)+(1-q)\cdot\mathrm{Law}\bigl(X,T_{G_+}(X)\bigr).$$
--   If $Z$ is a Bernoulli variable independent of $X$ with $P(Z=1)=q$ and $G=ZG_-(X)+(1-Z)G_+(X)$, then $\pi^*$ is exactly the joint law of $(X,X^*)$ with $X^*=X+\sqrt\delta\,G\,A(X)^{-1}\beta$, the random worst-case point of Theorem 6(c).
--
--   **Formalization Note** The random variable $X^*$ is encoded by the joint law of $(X,X^*)$, a measure on $\mathbb R^d\times\mathbb R^d$, because the transport cost $E[c(X,X^*)]$ depends on the pair. The weights enter as `ENNReal.ofReal q` and `ENNReal.ofReal (1 - q)`, which is the intended mixture when $0\le q\le1$; Theorem 6(c) states that this range holds. When $\bar c=\underline c$ Lean evaluates $q=0/0$ as $0$. The moments $\bar c,\underline c$ are Bochner integrals; the theorems that use them assert the integrability.
-- source:
--   arXiv:1810.02403v3, Theorem 6(c), p. 14, (10); §5.4, proof of Theorem 6(c), p. 40

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.WorstCase

open MeasureTheory Matrix

/-- The direction `A(x)⁻¹β ∈ ℝ^d` along which the worst case moves the point `x`
(display (10), arXiv:1810.02403v3, p. 14). -/
noncomputable def invDir {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (β x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 ((A x)⁻¹ *ᵥ β.ofLp)

/-- The transport map `x ↦ x + √δ g(x) A(x)⁻¹β` of display (10), p. 14, for a scalar
displacement function `g : ℝ^d → ℝ`. -/
noncomputable def shiftMap {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (δ : ℝ) (β : EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun x => x + (Real.sqrt δ * g x) • invDir A β x

/-- The joint law of `(X, T(X))` for `X ∼ P₀`: the pushforward of `P₀` under `x ↦ (x, T x)`. -/
noncomputable def graphCoupling {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  P0.map (fun x => (x, T x))

/-- The weighted second moment `E_{P₀}[g(X)² βᵀA(X)⁻¹β]` (a Bochner integral). With `g = G₊` it
is `c̄`, with `g = G₋` it is `c̲` (Theorem 6(c), p. 14). -/
noncomputable def sqMoment {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (β : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ x, g x ^ 2 * OTDRO.Dual.quadInv A β x ∂P0

/-- The Bernoulli weight `P(Z = 1) = (c̄ − 1)/(c̄ − c̲)` of Theorem 6(c), p. 14
(Lean's `x / 0 = 0` gives `0` when `c̄ = c̲`). -/
noncomputable def bernoulliWeight (cbar clow : ℝ) : ℝ :=
  (cbar - 1) / (cbar - clow)

/-- The joint law of `(X, X*)` in Theorem 6(c), p. 14, where `X ∼ P₀`,
`X* = X + √δ G A(X)⁻¹β`, `G = Z G₋(X) + (1 − Z) G₊(X)` and `Z` is a Bernoulli variable independent
of `X` with `P(Z = 1) = q = (c̄ − 1)/(c̄ − c̲)`: the mixture
`q · Law(X, X + √δ G₋ A⁻¹β) + (1 − q) · Law(X, X + √δ G₊ A⁻¹β)`. -/
noncomputable def mixtureCoupling {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (Gminus Gplus : EuclideanSpace ℝ (Fin d) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  ENNReal.ofReal (bernoulliWeight (sqMoment P0 A β Gplus) (sqMoment P0 A β Gminus)) •
      graphCoupling P0 (shiftMap A δ β Gminus) +
    ENNReal.ofReal (1 - bernoulliWeight (sqMoment P0 A β Gplus) (sqMoment P0 A β Gminus)) •
      graphCoupling P0 (shiftMap A δ β Gplus)

end OTDRO.WorstCase


