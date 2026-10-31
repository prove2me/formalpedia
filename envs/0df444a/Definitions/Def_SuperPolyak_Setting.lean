-- Prove2me | Definitions.Def_SuperPolyak_Setting
-- name    : SuperPolyak_Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:50.165893+00:00
-- url     : https://prove2.me/theorems/b47fa41c-b66a-4a67-b043-04f144a6b470
-- title:
--   Sharpness (A1), $(b)$-regularity (A2) and the setting of Theorem 2.2
-- statement:
--   Fix $f:\mathbb R^d\to\mathbb R$, a point $\bar x\in X^*$ with optimal value $f^*=f(\bar x)$, and a radius $\delta>0$. Write $B_\varepsilon(x)$ for the open ball.
--
--   1. **(A1) Sharpness.** $\mu>0$ and $f(x)-f^*\ge\mu\,\operatorname{dist}(x,X^*)$ for all $x\in B_\delta(\bar x)$.
--   2. **Locally bounded map.** A set-valued map $G:\mathbb R^d\rightrightarrows\mathbb R^d$ is locally bounded if $G(X)=\bigcup_{x\in X}G(x)$ is bounded for every bounded $X$.
--   3. **(A2) $(b)$-regularity.** The map $g:\mathbb R^d\rightrightarrows\mathbb R^d$ is nonempty-valued and locally bounded, $C_{(b)}>0$, $\eta>0$, and
--   $$
--   |f(x)+\langle v,y-x\rangle-f^*|\le C_{(b)}\|y-x\|^{1+\eta}
--   $$
--   for all $x\in B_\delta(\bar x)$, $v\in g(x)$ and $y\in X^*\cap B_{2\delta}(\bar x)$.
--   4. **The setting of Theorem 2.2.** $f$ is locally Lipschitz, $\bar x\in X^*$, $\delta>0$, (A1) holds with $\mu$, (A2) holds with $g,C_{(b)},\eta$, and $L>0$ is both an upper bound for $\|v\|$ over $v\in g(B_\delta(\bar x))$ and a Lipschitz constant of $f$ on $B_\delta(\bar x)$.
--
--   These are the hypotheses of the goal theorem and the standing setting of every lemma of §4.2 of the paper.
--
--   **Formalization Note** $g$ is an arbitrary set-valued map (`EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d))`), not the Clarke subdifferential. $\|y-x\|^{1+\eta}$ is `Real.rpow`. $L>0$ is assumed because the region of Theorem 2.2 contains $\mu^{1-\eta}/(LC_s)$.
-- source:
--   Charisopoulos & Davis, arXiv:2201.04611v1, §1.1 p.5 (locally bounded), §2 p.7 (standing assumptions, (A1), (A2), display (7)), Theorem 2.2 p.11 (L)

import Mathlib
import Definitions.Def_SuperPolyak_solutionSet

namespace SuperPolyak

/-- **Assumption (A1), sharpness** (Charisopoulos & Davis, arXiv:2201.04611v1, §2.1.1, p.7):
`µ > 0` and `f(x) − f* ≥ µ · dist(x, X*)` for all `x ∈ B_δ(x̄)`.

**Formalization Note** `B_δ(x̄)` is the open ball `Metric.ball x̄ δ` (§1.1, p.5), `dist(x, X*)` is
`Metric.infDist x (solutionSet f)`, and `f*` is `f x̄` (the statements using this predicate assume
`x̄ ∈ X*`). -/
def Sharp {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (xbar : EuclideanSpace ℝ (Fin d))
    (δ μ : ℝ) : Prop :=
  0 < μ ∧ ∀ x ∈ Metric.ball xbar δ, μ * Metric.infDist x (solutionSet f) ≤ f x - f xbar

/-- **Locally bounded set-valued map** (arXiv:2201.04611v1, §1.1, p.5): `G : ℝᵈ ⇒ ℝᵈ` is locally
bounded if `G(X) := ⋃_{x ∈ X} G(x)` is bounded for every bounded `X ⊆ ℝᵈ`. -/
def IsLocallyBounded {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ X : Set (EuclideanSpace ℝ (Fin d)), Bornology.IsBounded X →
    Bornology.IsBounded (⋃ x ∈ X, G x)

/-- **Assumption (A2), (b)-regularity** (arXiv:2201.04611v1, §2.1.2, display (7), p.7): the
set-valued map `g : ℝᵈ ⇒ ℝᵈ` is nonempty-valued and locally bounded, `C_(b) > 0`, `η > 0`, and
`|f(x) + ⟨v, y − x⟩ − f*| ≤ C_(b) ‖y − x‖^{1+η}` for all `x ∈ B_δ(x̄)`, `v ∈ g(x)` and
`y ∈ X* ∩ B_{2δ}(x̄)`.

**Formalization Note** `g` is an arbitrary set-valued map (`ℝᵈ → Set ℝᵈ`), not the Clarke
subdifferential. The balls are open, `f* = f x̄`, and the power is `Real.rpow` of a nonnegative
base. -/
def BRegular {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (xbar : EuclideanSpace ℝ (Fin d)) (δ Cb η : ℝ) : Prop :=
  (∀ x, (g x).Nonempty) ∧ IsLocallyBounded g ∧ 0 < Cb ∧ 0 < η ∧
    ∀ x ∈ Metric.ball xbar δ, ∀ v ∈ g x, ∀ y ∈ solutionSet f ∩ Metric.ball xbar (2 * δ),
      |f x + inner ℝ v (y - x) - f xbar| ≤ Cb * ‖y - x‖ ^ (1 + η)

/-- **The setting of Theorem 2.2** (arXiv:2201.04611v1, §2, p.7, and Theorem 2.2, p.11), which is
also the standing setting of §4.2 (p.24). It collects:

1. the standing assumptions of §2 (p.7): `f : ℝᵈ → ℝ` is locally Lipschitz, `x̄ ∈ X*` (so
   `X* ≠ ∅` and `f* = f x̄`), and `δ > 0`;
2. Assumption (A1) at `x̄` with constant `µ` and Assumption (A2) at `x̄` with `g`, `C_(b)`, `η`;
3. the constant `L` of Theorem 2.2: an upper bound for the norm of every element of
   `g(B_δ(x̄))` and a Lipschitz constant of `f` on `B_δ(x̄)`.

**Formalization Note** `0 < L` is assumed: Theorem 2.2's region contains `µ^{1−η}/(L C_s)`, which
is undefined at `L = 0`. The Lipschitz condition is written `|f x − f y| ≤ L ‖x − y‖` on the open
ball. -/
structure Setting {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin d)))
    (xbar : EuclideanSpace ℝ (Fin d)) (δ μ Cb η L : ℝ) : Prop where
  locallyLipschitz : LocallyLipschitz f
  xbar_mem : xbar ∈ solutionSet f
  δ_pos : 0 < δ
  sharp : Sharp f xbar δ μ
  bRegular : BRegular f g xbar δ Cb η
  L_pos : 0 < L
  norm_le : ∀ x ∈ Metric.ball xbar δ, ∀ v ∈ g x, ‖v‖ ≤ L
  lipschitz : ∀ x ∈ Metric.ball xbar δ, ∀ y ∈ Metric.ball xbar δ, |f x - f y| ≤ L * ‖x - y‖

end SuperPolyak


