-- Prove2me | Definitions.Def_RelSmoothFOM_DualAvg_Setting
-- name    : RelSmoothFOM_DualAvg_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:33:54.080987+00:00
-- url     : https://prove2.me/theorems/a784f092-be47-489d-acb8-ec71376621f4
-- title:
--   (7), Definitions 1.1–1.2, Algorithm 2, pp. 334–346 — Bregman distance, relative smoothness and strong convexity, dual averaging runs
-- statement:
--   This file fixes the objects of the dual averaging scheme of Lu, Freund and Nesterov (2018).
--
--   Let $E$ be a finite-dimensional real inner-product space, $Q \subseteq E$ a convex set, and $f, h : E \to \mathbb R$. The **Bregman distance** of $h$ (equation (7)) is
--   $$D_h(y,x) := h(y) - h(x) - \langle \nabla h(x), y - x\rangle ,$$
--   with the gradient taken at the second argument.
--
--   1. $f$ is **$L$-smooth relative to $h$ on $Q$** (Definition 1.1) if $f(y) \le f(x) + \langle \nabla f(x), y-x\rangle + L D_h(y,x)$ for all $x, y$ in the interior of $Q$, or in the relative interior of $Q$ when $Q$ has empty interior.
--   2. $f$ is **$\mu$-strongly convex relative to $h$ on $Q$** (Definition 1.2) if $f(y) \ge f(x) + \langle \nabla f(x), y-x\rangle + \mu D_h(y,x)$ for all such $x, y$.
--   3. The **weights** of Algorithm 2 are $a_{k+1} := \frac{1}{L-\mu}\left(\frac{L}{L-\mu}\right)^k$ for $k \ge 0$, and $A_k := \sum_{i=0}^{k-1} a_{i+1}$.
--   4. Given points $x^0, x^1, \dots$, the **model** at stage $k$ is
--   $$\psi_k(u) := h(u) + \sum_{i=0}^{k-1} a_{i+1}\big(f(x^i) + \langle \nabla f(x^i), u - x^i\rangle + \mu D_h(u, x^i)\big).$$
--   5. A **run of the dual averaging scheme** (Algorithm 2) is a sequence $(x^k)_{k\ge0}$ in $Q$ such that $x^0$ is the $h$-center of $Q$, i.e. $x^0$ minimises $h$ over $Q$ and $h(x^0) = 0$, and, for every $k \ge 0$, $x^{k+1}$ minimises $\psi_{k+1}$ over $Q$.
--
--   These objects are used by Theorem 3.2 and every step of its proof.
--
--   **Formalization Note** The pairing $\langle \nabla g(x), v\rangle$ is the Fréchet derivative `fderiv ℝ g x v`. "int $Q$, or the relative interior of $Q$" is Mathlib's `intrinsicInterior ℝ Q`, which is the interior when that is nonempty and the relative interior otherwise. The constants $L$ and $\mu$ are fixed before the points are quantified; the page's requirement $\mu \ge 0$ is a separate hypothesis of every theorem. Each argmin step is stated as a property of the next iterate (it lies in $Q$ and its model value is at most that at every point of $Q$), never via a choice function. Iterates are indexed from $0$, as on the page; `daWeight L μ i` is $a_{i+1}$, `daSum L μ k` is $A_k$, and `daModel f h L μ x k` is $\psi_k$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 334 (7), p. 336 Definitions 1.1–1.2, p. 346 Algorithm 2, p. 347 (ψ_k and A_k in the proof of Theorem 3.2)

import Mathlib

namespace RelSmoothFOM.DualAvg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Bregman distance (7), p. 334: `D_h(y, x) = h(y) − h(x) − ⟨∇h(x), y − x⟩`.
The pairing `⟨∇h(x), y − x⟩` is the Fréchet derivative of `h` at `x` applied to `y − x`.
The derivative is taken at the **second** argument `x`, as on the page. -/
noncomputable def bregman (h : E → ℝ) (y x : E) : ℝ :=
  h y - h x - fderiv ℝ h x (y - x)

/-- Definition 1.1, p. 336: `f` is `L`-smooth relative to `h` on `Q`, i.e.
`f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + L·D_h(y, x)` for all `x, y` in the interior of `Q`, or in the
relative interior of `Q` when `Q` has empty interior (`intrinsicInterior ℝ Q` covers both cases). -/
def IsRelSmooth (Q : Set E) (f h : E → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ intrinsicInterior ℝ Q, ∀ y ∈ intrinsicInterior ℝ Q,
    f y ≤ f x + fderiv ℝ f x (y - x) + L * bregman h y x

/-- Definition 1.2, p. 336: `f` is `μ`-strongly convex relative to `h` on `Q`, i.e.
`f(y) ≥ f(x) + ⟨∇f(x), y − x⟩ + μ·D_h(y, x)` for all `x, y` in the (relative) interior of `Q`.
The page's requirement `μ ≥ 0` is a separate hypothesis wherever this predicate is used. -/
def IsRelStronglyConvex (Q : Set E) (f h : E → ℝ) (μ : ℝ) : Prop :=
  ∀ x ∈ intrinsicInterior ℝ Q, ∀ y ∈ intrinsicInterior ℝ Q,
    f y ≥ f x + fderiv ℝ f x (y - x) + μ * bregman h y x

/-- The weight of Algorithm 2, p. 346: `daWeight L μ k = (1/(L − μ))·(L/(L − μ))^k`, which is the
page's `a_{k+1}` (computed at iteration `k`). Thus `a_{i+1}` is `daWeight L μ i`. -/
noncomputable def daWeight (L μ : ℝ) (k : ℕ) : ℝ :=
  1 / (L - μ) * (L / (L - μ)) ^ k

/-- `A_k := Σ_{i=0}^{k−1} a_{i+1}` of the proof of Theorem 3.2, p. 347. -/
noncomputable def daSum (L μ : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, daWeight L μ i

/-- The objective minimised by Algorithm 2 (p. 346), given the iterates `x 0, x 1, …`:
`daModel f h L μ x k u = h(u) + Σ_{i=0}^{k−1} a_{i+1}(f(x^i) + ⟨∇f(x^i), u − x^i⟩ + μ D_h(u, x^i))`.
Iteration `k` of Algorithm 2 minimises `daModel f h L μ x (k + 1)` over `Q`. The proof of
Theorem 3.2 (p. 347) calls `daModel f h L μ x k` by the name `ψ_k`. -/
noncomputable def daModel (f h : E → ℝ) (L μ : ℝ) (x : ℕ → E) (k : ℕ) (u : E) : ℝ :=
  h u + ∑ i ∈ Finset.range k, daWeight L μ i *
    (f (x i) + fderiv ℝ f (x i) (u - x i) + μ * bregman h u (x i))

/-- A run of Algorithm 2 (Dual Averaging Scheme with reference function `h`, p. 346), 0-based as on
the page:
* `x 0` is the `h`-center of `Q`: `x 0 ∈ Q` minimises `h` over `Q`, normalised so that `h (x 0) = 0`;
* for every `k`, `x (k + 1) ∈ Q` minimises
  `h(u) + Σ_{i=0}^{k} a_{i+1}(f(x^i) + ⟨∇f(x^i), u − x^i⟩ + μ D_h(u, x^i))` over `u ∈ Q`. -/
def IsDualAveragingRun (Q : Set E) (f h : E → ℝ) (L μ : ℝ) (x : ℕ → E) : Prop :=
  x 0 ∈ Q ∧ h (x 0) = 0 ∧ (∀ u ∈ Q, h (x 0) ≤ h u) ∧
    ∀ k : ℕ, x (k + 1) ∈ Q ∧
      ∀ u ∈ Q, daModel f h L μ x (k + 1) (x (k + 1)) ≤ daModel f h L μ x (k + 1) u

end RelSmoothFOM.DualAvg


