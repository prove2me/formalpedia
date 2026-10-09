-- Prove2me | Definitions.Def_SGDKaczmarz_SGD_Setting
-- name    : SGDKaczmarz_SGD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:23.15389+00:00
-- url     : https://prove2.me/theorems/3bdb3c1a-73dc-4327-9d32-6d5c41a7fbd8
-- title:
--   §2, pp. 3–4 — objective F = E f_i (2.1), residual σ², i.i.d. sampling law, SGD iterates (2.2)
-- statement:
--   This file fixes the objects of Section 2 of Needell, Srebro and Ward.
--
--   Let $\mathcal D$ be a probability distribution (the **source distribution**) on an arbitrary measurable index space $I$, let $\mathcal H$ be a real Hilbert space, and let $f_i : \mathcal H \to \mathbb R$, $i \in I$, be a family of differentiable functions. Expectations $\mathbb E$ are over $i \sim \mathcal D$.
--
--   1. The **objective** of (2.1) is
--   $$F(x) = \mathbb E_{i\sim\mathcal D} f_i(x).$$
--   2. The **residual** at a point $x_\star$ is
--   $$\sigma^2 = \mathbb E\|\nabla f_i(x_\star)\|_2^2 \in [0,\infty],$$
--   which is $+\infty$ when $\|\nabla f_i(x_\star)\|^2$ is not integrable.
--   3. The **sampling law** is the law of an i.i.d. sequence $\{i_k\}_{k\ge 0}$ with each $i_k \sim \mathcal D$: the infinite product measure $\mathcal D^{\otimes\mathbb N}$ on index sequences $\omega = (\omega_0, \omega_1, \dots)$, with $i_k = \omega_k$.
--   4. The **SGD iterates** (2.2) with fixed step size $\gamma$ and initial point $x_0$ are
--   $$x_{k+1} = x_k - \gamma \nabla f_{i_k}(x_k), \qquad k \ge 0,$$
--   so $x_k$ is a function of the first $k$ sampled indices $i_0, \dots, i_{k-1}$.
--
--   These are the objects about which Theorem 2.1 and its proof speak; every statement of the mission imports them.
--
--   **Formalization Note** $F$ is a Bochner integral and equals the paper's $F$ only when $i \mapsto f_i(x)$ is integrable for every $x$, which every theorem using it assumes. The residual is a lower Lebesgue integral with values in $[0,\infty]$, so a non-integrable gradient gives $\sigma^2 = \infty$ rather than a junk value $0$. The gradient is Mathlib's `gradient` (the Riesz representative of the Fréchet derivative). The sampling law is `Measure.infinitePi` of copies of $\mathcal D$. The iterate index is the paper's: $x_0$ is the initial point and $x_k$ the point after $k$ steps.
-- source:
--   Needell, Srebro & Ward, Stochastic gradient descent, weighted sampling, and the randomized Kaczmarz algorithm, arXiv:1310.5715v5, §2, (2.1), definition of σ², (2.2), pp. 3–4

import Mathlib

namespace SGDKaczmarz.SGD

open MeasureTheory
open scoped ENNReal

/-- The objective `F(x) = E_{i ∼ 𝒟} f_i(x)` of (2.1) (Needell–Srebro–Ward, §2, p. 3), as a Bochner
integral. It is the paper's `F` only when `i ↦ f_i(x)` is integrable for every `x`; every theorem using
it carries that hypothesis. -/
noncomputable def objective {I : Type*} [MeasurableSpace I] {H : Type*}
    (D : Measure I) (f : I → H → ℝ) : H → ℝ :=
  fun x => ∫ i, f i x ∂D

/-- The residual `σ² = E‖∇f_i(x⋆)‖²₂` (§2, p. 3), as a lower Lebesgue integral in `[0, ∞]`
(it is `∞` when `‖∇f_i(x⋆)‖²` is not integrable). -/
noncomputable def residual {I : Type*} [MeasurableSpace I]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (D : Measure I) (f : I → H → ℝ) (xstar : H) : ℝ≥0∞ :=
  ∫⁻ i, ENNReal.ofReal (‖gradient (f i) xstar‖ ^ 2) ∂D

/-- The law of the i.i.d. index sequence `{i_k}` drawn from `𝒟` (§2, p. 4): the infinite product of
copies of `D` on sequences `ω : ℕ → I`, with `i_k = ω k`. -/
noncomputable def iidLaw {I : Type*} [MeasurableSpace I] (D : Measure I) [IsProbabilityMeasure D] :
    Measure (ℕ → I) :=
  Measure.infinitePi (fun _ : ℕ => D)

/-- The SGD iterates (2.2) with fixed step size `γ` (§2, p. 4): `x_0 = x0` and
`x_{k+1} = x_k − γ ∇f_{i_k}(x_k)` with `i_k = ω k`. The iterate `x_k` depends only on
`ω 0, …, ω (k−1)`. -/
noncomputable def sgdIter {I : Type*}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : I → H → ℝ) (γ : ℝ) (x0 : H) : ℕ → (ℕ → I) → H
  | 0, _ => x0
  | k + 1, ω => sgdIter f γ x0 k ω - γ • gradient (f (ω k)) (sgdIter f γ x0 k ω)

end SGDKaczmarz.SGD


