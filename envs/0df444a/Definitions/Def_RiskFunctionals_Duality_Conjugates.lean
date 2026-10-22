-- Prove2me | Definitions.Def_RiskFunctionals_Duality_Conjugates
-- name    : RiskFunctionals_Duality_Conjugates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:24.104607+00:00
-- url     : https://prove2.me/theorems/3d0df6ba-63ed-40f5-94e8-4e964c7d8442
-- title:
--   The pairing $\mathbb E(YZ)$ of $L_p$ and $L_q$, proper functionals, and the convex and concave conjugates $h^*$, $h^{**}$, $\mathcal A^+$
-- statement:
--   Let $\mathcal Y=L_p(\Omega,\mathcal F,P)$ and $\mathcal Z=L_q(\Omega,\mathcal F,P)$ on a probability space; in every theorem $1\le p<\infty$ and $\frac1p+\frac1q=1$, so that $L_q$ is the topological dual of $L_p$ and $(\mathcal Y,\mathcal Z)$ are paired by
--   $$\langle Y,Z\rangle=\mathbb E(YZ)=\int_\Omega Y(\omega)Z(\omega)\,dP(\omega).$$
--   For functionals with values in $\overline{\mathbb R}=[-\infty,+\infty]$:
--
--   1. $h:\mathcal Y\to\overline{\mathbb R}$ is **proper** if $h(y)>-\infty$ for all $y$ and $\operatorname{dom}(h)=\{y:h(y)<+\infty\}\ne\emptyset$; a concave-type $g$ is proper if $-g$ is, i.e. $g(y)<+\infty$ for all $y$ and $g(y)>-\infty$ for some $y$.
--   2. The **epigraph** of $h$ is $\operatorname{epi}(h)=\{(y,r)\in\mathcal Y\times\mathbb R: h(y)\le r\}$; $h$ is **convex** if $\operatorname{epi}(h)$ is convex.
--   3. The **convex conjugate** and the **biconjugate** are
--   $$h^*(Z)=\sup_{Y\in\mathcal Y}\{\mathbb E(YZ)-h(Y)\},\qquad h^{**}(Y)=\sup_{Z\in\mathcal Z}\{\mathbb E(YZ)-h^*(Z)\}.$$
--   4. The **concave conjugate** of $\mathcal A:\mathcal Y\to\overline{\mathbb R}$ is
--   $$\mathcal A^+(Z)=\inf\{\mathbb E(YZ)-\mathcal A(Y):Y\in\mathcal Y\}.$$
--
--   The conjugates are the dual objects through which §2.2.2 represents convex and concave risk functionals: $\mathcal D^*$ in (2.6) is the convex conjugate of a deviation functional $\mathcal D$ and $\mathcal A^+$ in (2.7) the concave conjugate of an acceptability functional $\mathcal A$.
--
--   **Formalization Note** Suprema and infima are taken in `EReal`, a complete lattice, so they are the book's values in $[-\infty,+\infty]$, never a junk default; since $\mathbb E(YZ)$ is a real number, $\mathbb E(YZ)-h(Y)$ is $+\infty$ when $h(Y)=-\infty$ and $-\infty$ when $h(Y)=+\infty$. The pairing is the Bochner integral of $YZ$, which is integrable by Hölder's inequality under the exponent hypotheses carried by every theorem. The book states Appendix B for general paired locally convex spaces; the mission instantiates the pairing $(L_p,L_q)$, $1\le p<\infty$, which the book gives as its example on p. 269.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 269–270, Appendix B; p. 41, Eqs. (2.6)–(2.7)

import Mathlib

namespace RiskFunctionals.Duality

open MeasureTheory

/-- The dual pairing `⟨Y, Z⟩ = 𝔼(Y Z) = ∫ Y Z dP` between `𝒴 = L_p(Ω, ℱ, P)` and
`𝒵 = L_q(Ω, ℱ, P)` (Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific
2007, p. 269, Appendix B). Every theorem using it takes `1 ≤ p < ∞` and `1/p + 1/q = 1`, so the
product is integrable (Hölder). -/
noncomputable def pairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p q : ENNReal}
    (Y : Lp ℝ p P) (Z : Lp ℝ q P) : ℝ :=
  ∫ ω, Y ω * Z ω ∂P

/-- A proper convex-type functional `h : 𝒴 → [−∞, +∞]` (p. 270, Appendix B): `h(y) > −∞` for all
`y`, and its domain `dom(h) = {y : h(y) < +∞}` is nonempty. -/
def IsProperConvex {Y : Type*} (h : Y → EReal) : Prop :=
  (∀ y, h y ≠ ⊥) ∧ ∃ y, h y ≠ ⊤

/-- A proper concave-type functional `g : 𝒴 → [−∞, +∞]` (p. 270, Appendix B): `−g` is proper,
i.e. `g(y) < +∞` for all `y` and `{y : g(y) > −∞}` is nonempty. -/
def IsProperConcave {Y : Type*} (g : Y → EReal) : Prop :=
  (∀ y, g y ≠ ⊤) ∧ ∃ y, g y ≠ ⊥

/-- The epigraph `epi(h) = {(y, r) ∈ 𝒴 × ℝ : h(y) ≤ r}` (p. 270, Appendix B). -/
def epigraph {Y : Type*} (h : Y → EReal) : Set (Y × ℝ) :=
  {x | h x.1 ≤ (x.2 : EReal)}

/-- Convexity of an extended-real functional as on p. 270 (Appendix B): its epigraph is convex. -/
def ConvexEpi {Y : Type*} [AddCommGroup Y] [Module ℝ Y] (h : Y → EReal) : Prop :=
  _root_.Convex ℝ (epigraph h)

/-- The convex conjugate `h*(z) = sup_{y ∈ 𝒴} {⟨y, z⟩ − h(y)}` (p. 270, Appendix B; it is the
`𝒟*` of Eq. (2.6), p. 41), as a supremum in `EReal`. -/
noncomputable def convexConj {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (q : ENNReal) (h : Lp ℝ p P → EReal) (Z : Lp ℝ q P) : EReal :=
  ⨆ Y : Lp ℝ p P, ((pairing Y Z : ℝ) : EReal) - h Y

/-- The biconjugate `h**(y) = sup_{z ∈ 𝒵} {⟨y, z⟩ − h*(z)}` (p. 270, Appendix B). -/
noncomputable def convexBiconj {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (q : ENNReal) (h : Lp ℝ p P → EReal) (Y : Lp ℝ p P) : EReal :=
  ⨆ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - convexConj q h Z

/-- The concave conjugate `𝒜⁺(Z) = inf{𝔼(Y Z) − 𝒜(Y) : Y ∈ 𝒴}` (p. 41, after Eq. (2.7); p. 270,
`g⁺`), as an infimum in `EReal`. -/
noncomputable def concaveConj {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : ENNReal}
    (q : ENNReal) (A : Lp ℝ p P → EReal) (Z : Lp ℝ q P) : EReal :=
  ⨅ Y : Lp ℝ p P, ((pairing Y Z : ℝ) : EReal) - A Y

end RiskFunctionals.Duality


