-- Prove2me | Definitions.Def_TaoAnDCA_LocalOpt_Setting
-- name    : TaoAnDCA_LocalOpt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:19.282409+00:00
-- url     : https://prove2.me/theorems/224fc7de-79af-4263-8960-f0181b60b175
-- title:
--   §3 opening and §3.2, pp. 481–485 — dom, the d.c. difference with +∞ − (+∞) = +∞, ∂, standing assumptions (3), 𝒫_l, 𝒟_l, critical points, (strict) local minimizers (4)
-- statement:
--   Let $X = \mathbb R^n$ with its canonical inner product $\langle\cdot,\cdot\rangle$ and Euclidean norm $\|\cdot\|$; the dual space $Y$ is identified with $X$. Functions take values in $\mathbb R\cup\{\pm\infty\}$. $\Gamma_0(X)$ is the set of proper lower semicontinuous convex functions on $X$, and the conjugate of $\theta$ is $\theta^*(y) = \sup\{\langle x, y\rangle - \theta(x) : x \in X\}$. This file fixes the objects of the local optimality theory of d.c. programming.
--
--   1. **Effective domain.** $\operatorname{dom}\theta = \{x \in X : \theta(x) < +\infty\}$.
--   2. **The d.c. difference.** For $g, h$ the value $(g-h)(x) = g(x) - h(x)$ is taken under the convention $+\infty - (+\infty) = +\infty$: it is $+\infty$ whenever $g(x) = +\infty$, and the ordinary difference otherwise.
--   3. **Subdifferential.** For $x_0 \in \operatorname{dom}\theta$,
--   $$\partial\theta(x_0) = \{y \in Y : \theta(x) \ge \theta(x_0) + \langle x - x_0, y\rangle \ \ \forall x \in X\},$$
--   and $\partial\theta(x_0) = \emptyset$ when $\theta(x_0) = +\infty$.
--   4. **Standing assumptions.** $g, h \in \Gamma_0(X)$ and
--   $$\operatorname{dom} g \subset \operatorname{dom} h, \qquad \operatorname{dom} h^* \subset \operatorname{dom} g^*. \tag{3}$$
--   5. **Local optimality sets.** $\mathcal P_l = \{x^* \in X : \partial h(x^*) \subset \partial g(x^*)\}$ and $\mathcal D_l = \{y^* \in Y : \partial g^*(y^*) \subset \partial h^*(y^*)\}$.
--   6. **Critical point.** $x^*$ is a critical point of $g - h$ if $\partial g(x^*) \cap \partial h(x^*) \ne \emptyset$.
--   7. **Local minimizer.** $x^*$ is a local minimizer of $g - h$ if $g(x^*) - h(x^*)$ is finite and there is a neighbourhood $U$ of $x^*$ with
--   $$g(x^*) - h(x^*) \le g(x) - h(x) \qquad \forall x \in U. \tag{4}$$
--   8. **Strict local minimizer.** $x^*$ is a strict local minimizer of $g - h$ if $g(x^*) - h(x^*)$ is finite and there is a neighbourhood $U$ of $x^*$ with $g(x^*) - h(x^*) < g(x) - h(x)$ for every $x \in U$, $x \ne x^*$.
--
--   These are the objects in which Theorem 3.2 and Corollaries 3.3–3.5 of Pham Dinh and Le Thi are stated. The dual d.c. program is $\inf\{h^*(y) - g^*(y)\}$, so "local minimizer of $h^* - g^*$" is item 7 applied to the pair $(h^*, g^*)$, with the same convention.
--
--   **Formalization Note.** $X$ is `EuclideanSpace ℝ (Fin n)` and values are in `EReal`. $\Gamma_0$, $\partial$ and the conjugate are the published definitions `IsProperClosedConvex`, `IsSubgradient` (which requires $\theta(x_0) \ne +\infty$) and `CondatPD.FinDim.conj` (an `EReal` supremum over all of $X$). Mathlib's `EReal` subtraction has $\top - \top = \bot$, so the paper's difference is the separate function `dcSub g h x := if g x = ⊤ then ⊤ else g x - h x`; when $g(x)$ is finite, (3) and properness make $h(x)$ finite, so the subtraction is the real one. A local minimizer carries the finiteness clause explicitly (it is not Mathlib's `IsLocalMin`), and "neighbourhood" is membership in the neighbourhood filter. The paper does not define "strict local minimizer"; item 8 is the standard reading of (4) with strict inequality off $x^*$. The objects other than item 8 are restated identically in the sibling missions of this paper, for later consolidation.
-- source:
--   Pham Dinh & Le Thi, A d.c. optimization algorithm for solving the trust-region subproblem, SIAM J. Optim. 8 (1998), pp. 481–483, §3 opening (Γ₀, conjugate, dom, ∂, convention +∞ − (+∞) = +∞), (3), (4), critical point (p. 482), 𝒫_l and 𝒟_l (p. 483); p. 485, Corollary 3.4 (strict local minimizer)

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open Filter Topology

namespace TaoAnDCA.LocalOpt

/-- `𝒫_l = {x* : ∂h(x*) ⊂ ∂g(x*)}` (p. 483). -/
def Pl {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | TaoAnDCA.GlobalOpt.subdiff h x ⊆ TaoAnDCA.GlobalOpt.subdiff g x}

/-- `𝒟_l = {y* : ∂g*(y*) ⊂ ∂h*(y*)}` (p. 483). -/
def Dl {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) y ⊆ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj h) y}

/-- `x*` is a critical point of `g − h`: `∂g(x*) ∩ ∂h(x*) ≠ ∅` (p. 482). -/
def IsCritical {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  (TaoAnDCA.GlobalOpt.subdiff g x ∩ TaoAnDCA.GlobalOpt.subdiff h x).Nonempty

/-- `x*` is a local minimizer of `g − h` (4) (p. 482): `(g − h)(x*)` is finite and
`(g − h)(x*) ≤ (g − h)(x)` on a neighbourhood of `x*`. -/
def IsDCLocalMin {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊤ ∧ TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊥ ∧ ∃ U ∈ 𝓝 x, ∀ z ∈ U, TaoAnDCA.GlobalOpt.dcSub g h x ≤ TaoAnDCA.GlobalOpt.dcSub g h z

/-- `x*` is a strict local minimizer of `g − h` (Corollary 3.4, p. 485): `(g − h)(x*)` is finite
and `(g − h)(x*) < (g − h)(x)` for every `x ≠ x*` in a neighbourhood of `x*` ((4) with strict
inequality off `x*`). -/
def IsDCStrictLocalMin {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊤ ∧ TaoAnDCA.GlobalOpt.dcSub g h x ≠ ⊥ ∧ ∃ U ∈ 𝓝 x, ∀ z ∈ U, z ≠ x → TaoAnDCA.GlobalOpt.dcSub g h x < TaoAnDCA.GlobalOpt.dcSub g h z

end TaoAnDCA.LocalOpt


