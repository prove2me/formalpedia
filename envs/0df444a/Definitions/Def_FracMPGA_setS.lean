-- Prove2me | Definitions.Def_FracMPGA_setS
-- name    : FracMPGA_setS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:52.782501+00:00
-- url     : https://prove2.me/theorems/9230d80e-2216-4d61-b26d-65499c9ef40d
-- title:
--   The sets $\mathcal X$, $\mathcal X_{\underline\alpha}$, $\mathcal Y$ and $\mathcal S$
-- statement:
--   For the initial point $x^{(0)}$ of the algorithm, a bound $\bar g_{\mathcal X}>0$ and the lower step size $\underline\alpha>0$:
--   $$
--   \mathcal X=\{x: F(x)\le F(x^{(0)})\},\qquad \mathcal X_{\underline\alpha}=\{z:\operatorname{dist}^2(z,\mathcal X)\le\bar g_{\mathcal X}/\underline\alpha\},
--   $$
--   $$
--   \mathcal Y=\bigcup_{z\in\mathcal X_{\underline\alpha}}\partial g(z),\qquad \mathcal S=\{(x,y)\in\mathcal X\times\mathcal Y:\ \eta(x,y)>0\}.
--   $$
--   Assumption 2 is compactness of $\mathcal X$; Remark 1(i) gives a $\bar g_{\mathcal X}$ with $g\le\bar g_{\mathcal X}$ on $\mathcal X$. The iterates of the algorithm stay in $\mathcal S$, and the KL hypothesis of the main theorem is posed on $\mathcal S$.
--
--   **Formalization Note** $\bar g_{\mathcal X}$ is a parameter: statements take any $\bar g_{\mathcal X}>0$ bounding $g$ on $\mathcal X$. $\mathcal X$ contains $x^{(0)}$, so the distance to it is never taken to the empty set. $\mathcal S$ is a subset of the Euclidean product.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §4, p.14 (Assumption 2), p.15 (Remark 1(i), Lemma 4.4), p.16 (22)

import Mathlib
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_ProxAlg_FixedPoint_Basic

namespace FracMPGA

namespace Problem

variable {n N : ℕ} (P : Problem n N)

/-- The **level set** `X := {x ∈ ℝⁿ : F(x) ≤ F(x⁽⁰⁾)}` of Assumption 2 (Zhou, Zhang, Li,
arXiv:2311.00957v2, p.14), for the initial point `x⁽⁰⁾ = x0` of Algorithm 1. Assumption 2 is
`IsCompact (P.levelX x0)`. -/
def levelX (x0 : Vec n) : Set (Vec n) := {x | P.F x ≤ P.F x0}

/-- `X_α̲ := {z ∈ ℝⁿ : dist²(z, X) ≤ ḡ_X / α̲}` of Lemma 4.4 (p.15), for a bound `ḡ_X = gbar`
of Remark 1(i) and the lower step size `α̲ = αlo` of Algorithm 1.

**Formalization Note** `dist(z, X)` is `Metric.infDist z X`; `X` contains `x⁽⁰⁾`, so it is
nonempty and Mathlib's convention `infDist z ∅ = 0` never applies. -/
def Xlow (x0 : Vec n) (gbar αlo : ℝ) : Set (Vec n) :=
  {z | Metric.infDist z (P.levelX x0) ^ 2 ≤ gbar / αlo}

/-- `Y := ⋃_{z ∈ X_α̲} ∂g(z)` of Lemma 4.4 (p.15). -/
def setY (x0 : Vec n) (gbar αlo : ℝ) : Set (Vec n) :=
  ⋃ z ∈ P.Xlow x0 gbar αlo, ProxAlg.FixedPoint.subdifferential (fun w => (P.g w : EReal)) z

/-- `S := {(x, y) ∈ X × Y : η(x, y) > 0}`, equation (22) of Zhou, Zhang, Li,
arXiv:2311.00957v2, p.16, as a subset of the Euclidean product `ℝⁿ × ℝⁿ`.

**Formalization Note** `S` depends on the bound `ḡ_X = gbar` of Remark 1(i) ("there exists
`ḡ_X > 0` such that `η(x, y) ≤ g(x) ≤ ḡ_X` for any `(x, y) ∈ X × ℝⁿ`", p.15) and on `α̲ = αlo`
through `Y`. Statements that use `S` take `gbar` with `0 < gbar` and `g ≤ gbar` on `X`. -/
def setS (x0 : Vec n) (gbar αlo : ℝ) : Set (Pair n) :=
  {p | p.ofLp.1 ∈ P.levelX x0 ∧ p.ofLp.2 ∈ P.setY x0 gbar αlo ∧ 0 < P.eta p.ofLp.1 p.ofLp.2}

end Problem

end FracMPGA


