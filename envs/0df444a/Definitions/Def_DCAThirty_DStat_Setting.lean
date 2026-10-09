-- Prove2me | Definitions.Def_DCAThirty_DStat_Setting
-- name    : DCAThirty_DStat_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:33.238684+00:00
-- url     : https://prove2.me/theorems/a0b350c1-96fd-40a6-a5cd-7ecb3040bd7f
-- title:
--   §1.1, pp. 8–9 — directional derivatives, d-stationarity, strong criticality and the support function χ*_C
-- statement:
--   Let $X=\mathbb R^n$ with its canonical inner product $\langle\cdot,\cdot\rangle$; the dual space $Y$ is identified with $X$. Functions take values in $\mathbb R\cup\{\pm\infty\}$, and $\Gamma_0(X)$ is the set of proper, lower semicontinuous, convex functions $X\to\mathbb R\cup\{+\infty\}$. For $g,h\in\Gamma_0(X)$ the DC function is $f=g-h$, with the convention $+\infty-(+\infty)=+\infty$, so that $\operatorname{dom} f=\operatorname{dom} g$. This file introduces the objects of §1.1 of Le Thi and Pham Dinh in terms of which Theorem 1 is stated.
--
--   1. **Directional derivative of a convex function.** For $\varphi:X\to\mathbb R\cup\{\pm\infty\}$ and $x,u\in X$,
--   $$\varphi'(x;u)=\inf_{t>0}\frac{\varphi(x+tu)-\varphi(x)}{t}\in\mathbb R\cup\{\pm\infty\}.$$
--   This is the paper's formula for convex $\varphi$ at $x\in\operatorname{dom}\varphi$; it is applied to the DC components $g$ and $h$ at points where both are finite.
--   2. **Directional derivative as a limit.** For a general $\varphi$, the statement "$\varphi'(x;u)=d$" with $d\in\mathbb R\cup\{\pm\infty\}$ means that the limit
--   $$\lim_{t\downarrow 0}\frac{\varphi(x+tu)-\varphi(x)}{t}$$
--   exists in the extended reals and equals $d$. It is applied to the DC function $f$.
--   3. **d-stationarity.** A point $x$ is d-stationary of $\varphi$ if $x\in\operatorname{dom}\varphi$ and, for every $u\in X$, the directional derivative $\varphi'(x;u)$ exists and satisfies $\varphi'(x;u)\ge0$.
--   4. **Strong criticality.** A point $x$ is a strongly critical point of $f=g-h$ if
--   $$\emptyset\ne\partial h(x)\subset\partial g(x),$$
--   where $\partial\varphi(x)$ is the exact subdifferential: the set of $y$ with $\varphi(x)<+\infty$ and $\varphi(x)+\langle y,v-x\rangle\le\varphi(v)$ for all $v\in X$.
--   5. **Support function.** For a set $C\subset X$, $\chi^*_C(u)=\sup_{y\in C}\langle u,y\rangle$, the conjugate of the indicator function $\chi_C$. It takes values in $\mathbb R\cup\{\pm\infty\}$, and $\chi^*_\emptyset\equiv-\infty$.
--
--   These are the two stationarity notions of DC programming that Theorem 1 relates: d-stationarity of the objective $f$, and strong criticality, the property that DCA's iterates are designed to reach.
--
--   **Formalization Note** $X$ is `EuclideanSpace ℝ (Fin n)` and all functions map into `EReal`. The DC objective, $\operatorname{dom}$ and $\partial$ are the published `TaoAnDCA.GlobalOpt.dcSub`, `effDom` and `subdiff` (the last through `InertialFB.IFB.IsSubgradient`). The subgradient inequality is the standard one, $\varphi(v)\ge\varphi(x)+\langle y,v-x\rangle$; display (1) on p. 8 prints $\langle x-u,y\rangle$, a sign slip which would make $\partial\varphi$ the negative of the subdifferential. Difference quotients are computed in `EReal` as $(\varphi(x+tu)-\varphi(x))\cdot t^{-1}$. The limit in item 2 is a predicate `HasDirDerivE` (a `Tendsto` along $t\downarrow0$), never a junk-valued `limUnder`; d-stationarity asserts the existence of the limit in every direction, so it cannot hold vacuously where the limit fails to exist. The support function is an extended-real supremum, so it is $-\infty$ on the empty set rather than $0$.
-- source:
--   Le Thi & Pham Dinh, DC programming and DCA: thirty years of developments, Math. Program. 169 (2018), pp. 7–9, §1.1: (P_dc) (p. 7), dom and ∂ (p. 8, display (1)), 'Critical and strongly critical points' (p. 8), the directional derivative and 'The d-stationarity of a proper function' (p. 9), the support function χ*_C (p. 9)

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open Filter Topology

namespace DCAThirty.DStat

/-- The directional derivative of a convex function, by the paper's own formula (p. 9):
`φ′(x; u) = inf_{t > 0} (φ(x + t u) − φ(x)) / t`, computed in `EReal`. It is used only for the
DC components `g, h ∈ Γ₀(X)` at points `x` where both are finite. -/
noncomputable def convDirDeriv {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (x u : EuclideanSpace ℝ (Fin n)) : EReal :=
  ⨅ t : ℝ, ⨅ (_ : 0 < t), (φ (x + t • u) - φ x) * ((t⁻¹ : ℝ) : EReal)

/-- `φ′(x; u) = d` in the sense of the limit `lim_{t ↓ 0} (φ(x + t u) − φ(x)) / t = d` in
`EReal` (p. 9). This is a predicate: it asserts that the limit exists and equals `d`. -/
def HasDirDerivE {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (x u : EuclideanSpace ℝ (Fin n)) (d : EReal) : Prop :=
  Tendsto (fun t : ℝ => (φ (x + t • u) - φ x) * ((t⁻¹ : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 d)

/-- `x ∈ dom φ` is d-stationary of `φ` if `φ′(x; u) ≥ 0` for every `u ∈ X` (p. 9): for every
direction the directional derivative exists (in `EReal`) and is nonnegative. -/
def IsDStationary {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  φ x ≠ ⊤ ∧ ∀ u, ∃ d : EReal, HasDirDerivE φ x u d ∧ 0 ≤ d

/-- `x` is a strongly critical point of `f = g − h` if `∅ ≠ ∂h(x) ⊂ ∂g(x)` (p. 8). -/
def IsStronglyCritical {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  (TaoAnDCA.GlobalOpt.subdiff h x).Nonempty ∧
    TaoAnDCA.GlobalOpt.subdiff h x ⊆ TaoAnDCA.GlobalOpt.subdiff g x

/-- The support function `χ*_C(u) = sup_{y ∈ C} ⟨u, y⟩` of a set `C` (p. 9), the conjugate of the
indicator function `χ_C`. It takes values in `EReal`; on `C = ∅` it is `⊥ = −∞`. -/
noncomputable def supportFn {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n)) : EReal :=
  ⨆ y ∈ C, ((inner ℝ u y : ℝ) : EReal)

end DCAThirty.DStat


