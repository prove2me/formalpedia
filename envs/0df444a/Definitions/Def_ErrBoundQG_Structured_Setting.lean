-- Prove2me | Definitions.Def_ErrBoundQG_Structured_Setting
-- name    : ErrBoundQG_Structured_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:08.461992+00:00
-- url     : https://prove2.me/theorems/bc6b8265-0f0a-42bc-85c9-b89dd3473580
-- title:
--   §§2–4 — conjugate, structured primal and dual, firm convexity, proximal-gradient error bound, and Moreau envelope
-- statement:
--   This file fixes the objects of §4 of the paper, the composite problem $\min_x f(Ax)+g(x)$ and its Fenchel dual.
--
--   Write $E_k=\mathbb R^k$ with the Euclidean inner product. Throughout, $f:E_m\to\mathbb R$, $g:E_n\to[-\infty,+\infty]$ and $A:E_n\to E_m$ is linear, with adjoint $A^\top$.
--
--   1. The **Fenchel conjugate** of $h:E_k\to[-\infty,+\infty]$ is $h^\star(y)=\sup_x\{\langle y,x\rangle-h(x)\}$, and its **domain** is $\operatorname{dom}h=\{x: h(x)<+\infty\}$.
--   2. The **primal objective** (4.1) and the **dual objective** $\Psi$ of (4.2) are
--   $$\varphi(x)=f(Ax)+g(x),\qquad \Psi(y)=f^\star(y)+g^\star(-A^\top y).$$
--   3. **Dual nondegeneracy** (Assumption 1) is $0\in A^\top(\operatorname{ri}\operatorname{dom}f^\star)+\operatorname{ri}\operatorname{dom}g^\star$, and **dual strict complementarity** at $\bar y$ (Assumption 2) is $0\in\operatorname{ri}\partial\Psi(\bar y)$, where $\operatorname{ri}$ is the relative interior and $\partial$ the convex subdifferential.
--   4. **Firm convexity** (Definition 4.1). A function $h$ is firmly convex relative to $v$ if the tilted function $h_v(x)=h(x)-\langle v,x\rangle$ has a minimizer and, for every compact set $\mathcal X$, there is $\alpha>0$ with
--   $$h_v(x)\ge \inf h_v+\frac{\alpha}{2}\operatorname{dist}^2\bigl(x,(\partial h_v)^{-1}(0)\bigr)\qquad\text{for all }x\in\mathcal X.$$
--   5. The **proximal-gradient step** at $x$ with step $t$ is any minimizer $p$ of $y\mapsto g(y)+\frac1{2t}\|y-(x-t\nabla(f\circ A)(x))\|^2$, so that $\mathcal G_t(x)=t^{-1}(x-p)$ is the prox-gradient mapping of §3. The **error bound condition** (Definition 3.1) with parameters $(\gamma,\nu)$ for the minimizer set $S\neq\emptyset$ and minimal value $\varphi^*$ is
--   $$\operatorname{dist}(x,S)\le\gamma\,\|\mathcal G_t(x)\|\qquad\text{for all }x\text{ with }\varphi(x)\le\varphi^*+\nu.$$
--   6. The **Moreau envelope** is $h^t(x)=\inf_y\{h(y)+\frac1{2t}\|y-x\|^2\}$, used for $t>0$.
--
--   These definitions are shared by every statement of the mission: the solution-set description, the relative-interior identity (4.3), linear regularity (4.4), the growth estimates (4.5), Theorem 4.2 and Theorem 4.5.
--
--   **Formalization Note.** Extended-real values live in `EReal`; conjugates and infima are `EReal` suprema and infima, so they never take a junk value. The paper's distance to an empty set is $+\infty$, while Lean's `Metric.infDist` to the empty set is $0$; firm convexity therefore states the nonemptiness of $(\partial h_v)^{-1}(0)$ explicitly (on the page it follows by testing a singleton $\mathcal X$), and the error bound states $S\ne\emptyset$. The page leaves the sign of $\alpha$ in Definition 4.1 implicit; it is read as $\alpha>0$, since with $\alpha=0$ every convex function would be firmly convex, contradicting the page's example $x^4$. The proximal point is the argmin predicate of $t\cdot g+\frac12\|\cdot-z\|^2$, which for $t>0$ has the same minimizers as the page's $g+\frac1{2t}\|\cdot-z\|^2$. The proximal-gradient step and error bound repeat, in this namespace, objects of mission I of the series, whose definitions are not yet published.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, pp. 3–5, 10–11, Fenchel conjugate, Definition 3.1, (4.1)–(4.2), Assumptions 1–2, Definition 4.1

import Mathlib
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_GoldenRatioVI_Shared_IsProxPoint

namespace ErrBoundQG.Structured

open scoped InnerProductSpace Pointwise

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Fenchel conjugate, §2, p. 3. The dual variable is identified with the primal
Euclidean space through its inner product. -/
noncomputable def conj {k : ℕ} (h : E k → EReal) (y : E k) : EReal :=
  ⨆ x : E k, ((⟪y, x⟫_ℝ : ℝ) : EReal) - h x

/-- Effective domain of an extended-real function, §2, p. 3. -/
def dom {k : ℕ} (h : E k → EReal) : Set (E k) := {x | h x ≠ ⊤}

/-- The objective of (4.1), p. 10. -/
noncomputable def primalObj {m n : ℕ} (f : E m → ℝ) (g : E n → EReal)
    (A : E n →L[ℝ] E m) (x : E n) : EReal :=
  (f (A x) : EReal) + g x

/-- The negative dual objective Ψ of (4.2), p. 10. -/
noncomputable def dualObj {m n : ℕ} (f : E m → ℝ) (g : E n → EReal)
    (A : E n →L[ℝ] E m) (y : E m) : EReal :=
  conj (fun z => (f z : EReal)) y + conj g (-(ContinuousLinearMap.adjoint A y))

/-- Assumption 1 (dual nondegeneracy), p. 10. -/
def DualNondegenerate {m n : ℕ} (f : E m → ℝ) (g : E n → EReal)
    (A : E n →L[ℝ] E m) : Prop :=
  (0 : E n) ∈ (ContinuousLinearMap.adjoint A) ''
      intrinsicInterior ℝ (dom (conj (fun z => (f z : EReal)))) +
    intrinsicInterior ℝ (dom (conj g))

/-- Assumption 2 (dual strict complementarity), p. 10. -/
def DualStrictComplementarity {m n : ℕ} (f : E m → ℝ) (g : E n → EReal)
    (A : E n →L[ℝ] E m) (ybar : E m) : Prop :=
  (0 : E m) ∈ intrinsicInterior ℝ
    (ProxAlg.FixedPoint.subdifferential (dualObj f g A) ybar)

/-- Definition 4.1, p. 11. The nonempty minimizer clause preserves the paper's
infinite distance to the empty set. -/
def FirmlyConvexRel {k : ℕ} (h : E k → EReal) (v : E k) : Prop :=
  let hv : E k → EReal := fun x => h x - ((⟪v, x⟫_ℝ : ℝ) : EReal)
  let T : Set (E k) := {x | (0 : E k) ∈ ProxAlg.FixedPoint.subdifferential hv x}
  T.Nonempty ∧ ∀ X : Set (E k), IsCompact X →
    ∃ α : ℝ, 0 < α ∧ ∀ x ∈ X,
      (⨅ y : E k, hv y) + ((α / 2 * Metric.infDist x T ^ 2 : ℝ) : EReal) ≤ hv x

/-- The proximal-gradient step for f ∘ A + g, from §3, p. 4. -/
def IsProxGradStep {m n : ℕ} (f : E m → ℝ) (g : E n → EReal)
    (A : E n →L[ℝ] E m) (t : ℝ) (x p : E n) : Prop :=
  GoldenRatioVI.Shared.IsProxPoint (fun y => (t : EReal) * g y)
    (x - t • gradient (fun z => f (A z)) x) p

/-- Definition 3.1, p. 5, specialized to (4.1). -/
def ErrorBound {m n : ℕ} (f : E m → ℝ) (g : E n → EReal)
    (A : E n →L[ℝ] E m) (t : ℝ) (S : Set (E n))
    (φstar γ ν : ℝ) : Prop :=
  S.Nonempty ∧ ∀ x : E n, primalObj f g A x ≤ ((φstar + ν : ℝ) : EReal) →
    ∀ p : E n, IsProxGradStep f g A t x p →
      Metric.infDist x S ≤ γ * ‖t⁻¹ • (x - p)‖

/-- The Moreau envelope `h^t` of §2, p. 4, defined there for a real `t > 0`; every
statement using it assumes `0 < t`. The page's `min` is written as an `EReal` infimum. -/
noncomputable def moreauEnv {k : ℕ} (t : ℝ) (h : E k → EReal)
    (x : E k) : EReal :=
  ⨅ y : E k, h y + ((‖y - x‖ ^ 2 / (2 * t) : ℝ) : EReal)

end ErrBoundQG.Structured


