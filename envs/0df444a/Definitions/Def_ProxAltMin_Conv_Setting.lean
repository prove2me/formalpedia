-- Prove2me | Definitions.Def_ProxAltMin_Conv_Setting
-- name    : ProxAltMin_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:09.371979+00:00
-- url     : https://prove2.me/theorems/4865debc-bc30-4f2e-8bc3-c2df4987dc26
-- title:
--   Assumptions (H) and (H1): L = f + Q + g on ℝⁿ × ℝᵐ, partial gradients, the proximal alternating run (5)–(6), and the vector of Lemma 5 (iii)
-- statement:
--   This file fixes the model of Attouch, Bolte, Redont and Soubeyran's proximal alternating minimization scheme.
--
--   **Spaces.** $\mathbb R^n$ and $\mathbb R^m$ carry their Euclidean inner products, and the product $Z=\mathbb R^n\times\mathbb R^m$ carries the Euclidean product structure
--   $$\langle (x,y),(x',y')\rangle=\langle x,x'\rangle+\langle y,y'\rangle,\qquad \|(x,y)\|^2=\|x\|^2+\|y\|^2 .$$
--   The point with components $x\in\mathbb R^n$, $y\in\mathbb R^m$ is written $(x,y)$.
--
--   **The objective (H).** Given $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$, $g:\mathbb R^m\to\mathbb R\cup\{+\infty\}$ and $Q:Z\to\mathbb R$, set
--   $$L(x,y)=f(x)+Q(x,y)+g(y).$$
--   Assumption (H) requires:
--   1. $f$ and $g$ are proper (never $-\infty$, finite somewhere) and lower semicontinuous;
--   2. $Q$ is continuously differentiable ($C^1$);
--   3. $\nabla Q$ is Lipschitz continuous on every bounded subset of $Z$.
--
--   The partial gradients $\nabla_xQ(z)\in\mathbb R^n$ and $\nabla_yQ(z)\in\mathbb R^m$ are the two components of $\nabla Q(z)$ in the Euclidean product, so that $\nabla Q=(\nabla_xQ,\nabla_yQ)$.
--
--   **Assumption (H1)**, relative to the initial ordinate $y_0\in\mathbb R^m$ and to step sizes $(\lambda_k)_{k\ge0}$, $(\mu_k)_{k\ge0}$, with constants $r_-,r_+$:
--   1. $\inf_{\mathbb R^n\times\mathbb R^m}L>-\infty$, i.e. some real $c$ satisfies $c\le L(z)$ for all $z$;
--   2. the function $L(\cdot,y_0)$ is proper (finite somewhere);
--   3. $0<r_-<r_+$ and $\lambda_k,\mu_k\in(r_-,r_+)$ for every $k\ge0$.
--
--   **The scheme (5)–(6).** Sequences $(x_k)_{k\ge0}$ in $\mathbb R^n$ and $(y_k)_{k\ge0}$ in $\mathbb R^m$ comply with the proximal alternating scheme when, for every $k\ge0$,
--   $$x_{k+1}\in\operatorname{argmin}\Big\{L(u,y_k)+\frac1{2\lambda_k}\|u-x_k\|^2:u\in\mathbb R^n\Big\},\qquad y_{k+1}\in\operatorname{argmin}\Big\{L(x_{k+1},v)+\frac1{2\mu_k}\|v-y_k\|^2:v\in\mathbb R^m\Big\}.$$
--   The minimizers are selections: any minimizer may be chosen at each step, and the statements about the scheme hold for every sequence so produced. The initial point $(x_0,y_0)$ is arbitrary.
--
--   **The vector of Lemma 5 (iii).** For $k\ge1$,
--   $$(x_k^*,y_k^*)=\big(\nabla_xQ(x_k,y_k)-\nabla_xQ(x_k,y_{k-1}),\,0\big)-\Big(\frac1{\lambda_{k-1}}(x_k-x_{k-1}),\ \frac1{\mu_{k-1}}(y_k-y_{k-1})\Big).$$
--
--   These are the standing objects of every statement in the mission.
--
--   **Formalization Note** $\mathbb R\cup\{+\infty\}$ is `EReal` with "never $-\infty$" part of properness (`IsProperFn`), and $L$ is the `EReal` sum $f(x)+Q(x,y)+g(y)$. The product is `WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))`, not the sup-norm product. "Lipschitz on bounded subsets" is: for each bounded $B$ some constant $C$ makes $\nabla Q$ $C$-Lipschitz on $B$. The argmin conditions are written as the inequality "value at $x_{k+1}$ $\le$ value at every $u$" in `EReal`. The vector $(x_k^*,y_k^*)$ is only used for $k\ge1$; at $k=0$ the natural-number subtraction gives a meaningless value.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), pp. 1, 6, (H), (H1), (5), (6), Lemma 5 (iii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
open NonconvexSplitting.Shared

namespace ProxAltMin.Conv

/-- The Euclidean product `ℝⁿ × ℝᵐ`, with `‖(x, y)‖² = ‖x‖² + ‖y‖²` and the inner product
`⟪(x, y), (x', y')⟫ = ⟪x, x'⟫ + ⟪y, y'⟫` (not the sup-norm product). -/
abbrev Z (n m : ℕ) : Type :=
  WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))

/-- The point `(x, y)` of the Euclidean product. -/
def pt {n m : ℕ} (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) : Z n m :=
  WithLp.toLp 2 (x, y)

/-- The objective (H): `L(x, y) = f(x) + Q(x, y) + g(y)`, with values in `ℝ ∪ {+∞}` (as `EReal`). -/
noncomputable def L {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (z : Z n m) : EReal :=
  f z.fst + (Q z : EReal) + g z.snd

/-- The partial gradient `∇ₓQ(z)`: the `x`-component of `∇Q(z)` in the Euclidean product. -/
noncomputable def gradX {n m : ℕ} (Q : Z n m → ℝ) (z : Z n m) : EuclideanSpace ℝ (Fin n) :=
  (gradient Q z).fst

/-- The partial gradient `∇ᵧQ(z)`: the `y`-component of `∇Q(z)` in the Euclidean product. -/
noncomputable def gradY {n m : ℕ} (Q : Z n m → ℝ) (z : Z n m) : EuclideanSpace ℝ (Fin m) :=
  (gradient Q z).snd

/-- Assumption (H) (p. 1): `f` and `g` are proper and lower semicontinuous with values in
`ℝ ∪ {+∞}`, `Q` is `C¹`, and `∇Q` is Lipschitz continuous on bounded subsets. -/
structure AssumptionH {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (Q : Z n m → ℝ) (g : EuclideanSpace ℝ (Fin m) → EReal) : Prop where
  f_proper : IsProperFn f
  f_lsc : LowerSemicontinuous f
  g_proper : IsProperFn g
  g_lsc : LowerSemicontinuous g
  Q_C1 : ContDiff ℝ 1 Q
  gradQ_lipschitz_on_bounded :
    ∀ B : Set (Z n m), Bornology.IsBounded B → ∃ C : NNReal, LipschitzOnWith C (gradient Q) B

/-- Assumption (H1) (p. 6), for the initial ordinate `y0` and the step sizes `lam = (λₖ)`,
`mu = (μₖ)`: `inf L > -∞`, the function `L(·, y0)` is proper, and for some `0 < rm < rp` every
`λₖ` and `μₖ` lies in the open interval `(rm, rp)`. -/
structure AssumptionH1 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (Q : Z n m → ℝ) (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ)
    (y0 : EuclideanSpace ℝ (Fin m)) (rm rp : ℝ) : Prop where
  inf_gt_bot : ∃ c : ℝ, ∀ z, (c : EReal) ≤ L f Q g z
  slice_proper : ∃ u, L f Q g (pt u y0) ≠ ⊤
  rm_pos : 0 < rm
  rm_lt_rp : rm < rp
  steps : ∀ k, lam k ∈ Set.Ioo rm rp ∧ mu k ∈ Set.Ioo rm rp

/-- The sequences `x = (xₖ)`, `y = (yₖ)` comply with the proximal alternating scheme (5)–(6)
(p. 6): for every `k`, `x (k+1)` is a minimizer of `u ↦ L(u, yₖ) + ‖u - xₖ‖² / (2λₖ)` and
`y (k+1)` is a minimizer of `v ↦ L(x (k+1), v) + ‖v - yₖ‖² / (2μₖ)`. The minimizers are selections:
any minimizer is allowed. -/
def IsPAMRun {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (Q : Z n m → ℝ) (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ k,
    (∀ u : EuclideanSpace ℝ (Fin n),
      L f Q g (pt (x (k + 1)) (y k)) + ((‖x (k + 1) - x k‖ ^ 2 / (2 * lam k) : ℝ) : EReal) ≤
        L f Q g (pt u (y k)) + ((‖u - x k‖ ^ 2 / (2 * lam k) : ℝ) : EReal)) ∧
    (∀ v : EuclideanSpace ℝ (Fin m),
      L f Q g (pt (x (k + 1)) (y (k + 1))) +
          ((‖y (k + 1) - y k‖ ^ 2 / (2 * mu k) : ℝ) : EReal) ≤
        L f Q g (pt (x (k + 1)) v) + ((‖v - y k‖ ^ 2 / (2 * mu k) : ℝ) : EReal))

/-- The vector `(x*ₖ, y*ₖ)` of Lemma 5 (iii) (p. 6), meaningful for `k ≥ 1`:
`(∇ₓQ(xₖ, yₖ) - ∇ₓQ(xₖ, yₖ₋₁), 0) - ((xₖ - xₖ₋₁)/λₖ₋₁, (yₖ - yₖ₋₁)/μₖ₋₁)`.
(At `k = 0` the natural-number subtraction makes it a meaningless value; it is only used for
`k ≥ 1`.) -/
noncomputable def zstar {n m : ℕ} (Q : Z n m → ℝ) (lam mu : ℕ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m)) (k : ℕ) : Z n m :=
  pt (gradX Q (pt (x k) (y k)) - gradX Q (pt (x k) (y (k - 1))) -
        (1 / lam (k - 1)) • (x k - x (k - 1)))
     (-((1 / mu (k - 1)) • (y k - y (k - 1))))

end ProxAltMin.Conv


