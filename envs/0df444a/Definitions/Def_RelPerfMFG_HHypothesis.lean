-- Prove2me | Definitions.Def_RelPerfMFG_HHypothesis
-- name    : RelPerfMFG_HHypothesis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:44.544544+00:00
-- url     : https://prove2.me/theorems/a9169e20-533f-40e9-ab35-bd9ace8f1700
-- title:
--   H Hypothesis (Definition 3.1) and the growth bounds (3.6), (3.7)
-- statement:
--   Let $Y$ be the common-noise path and $C_0,\dots,C_{N-1}$ the costs. A jointly Borel measurable $J:\mathbb R_+\times(\mathbb R^e)^N\to\mathbb R_+$ **satisfies H Hypothesis** (Definition 3.1, p.11) if
--
--   1. $x\mapsto J(x,y)$ is concave and continuously differentiable;
--   2. $J'(x,y):=\frac{\partial}{\partial x}J(x,y)>0$ for all $y$;
--   3. for any $x>0$, $\mathbb E[J'(x,Y)]<\infty$;
--   4. there are a constant $\alpha\in(0,1)$ and a random variable $A\ge0$ with $\mathbb E[A]<\infty$ such that
--   $$J(x,Y)\le(1-\alpha)C_k(x)+A,\qquad\forall x\ge0,\ k=0,\dots,N-1.\quad(3.6)$$
--
--   The module also names the bound (3.6) itself (`Bound36`) and the bound of Remark 3.1 (`Bound37`):
--   $$J\Big(\sum_{k=0}^{N-1}x_k,Y\Big)<(1-\alpha)\sum_{k=0}^{N-1}C_k(x_k)+A,\qquad\forall(x_0,\dots,x_{N-1})\in\mathbb R_+^N.\quad(3.7)$$
--
--   H Hypothesis is the sufficient condition (Proposition 3.1) under which the centralized problem has an interior optimum, and it is the class of terminal rewards preserved by the value recursion of §4.3 (Lemma 4.1).
--
--   **Formalization Note** "Continuously differentiable" is footnote 2: continuous on $\mathbb R_+$ and $C^1$ on $(0,\infty)$, so (2) is required at $x>0$. (1)–(2) hold for every $y$. (3) is integrability of the nonnegative $J'(x,Y)$. The random bounds (3.6), (3.7) hold almost surely, simultaneously for all $x$ and $k$.
-- source:
--   Zhou, Optimal relative performance criteria in mean field contribution games, SSRN 3742584 (Nov. 13, 2022), Definition 3.1, p.11 (with (3.6)); Remark 3.1, p.11 ((3.7)); footnote 2, p.5

import Mathlib
import Definitions.Def_RelPerfMFG_Setup

open MeasureTheory ProbabilityTheory

namespace RelPerfMFG

variable {Ω : Type*} [MeasurableSpace Ω] {N e : ℕ}

/-- **The growth bound (3.6)**, Zhou, *Optimal relative performance criteria in mean field
contribution games*, SSRN 3742584 (Nov. 13, 2022), Definition 3.1(4), p.11:
`J(x, Y) ≤ (1 − α) C_k(x) + A` for all `x ≥ 0` and `k = 0, …, N − 1`.

**Formalization Note.** The random-variable inequality holds almost surely, simultaneously for
all `x ≥ 0` and all `k`. `Y` is the common-noise path. -/
def Bound36 (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (J : ℝ → NoisePath N e → ℝ) (α : ℝ) (A : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ x : ℝ, 0 ≤ x → ∀ k : Fin N, J x (Y ω) ≤ (1 - α) * C k x + A ω

/-- **The growth bound (3.7)**, SSRN 3742584 (Nov. 13, 2022), Remark 3.1, p.11:
`J(Σ_{k=0}^{N−1} x_k, Y) < (1 − α) Σ_{k=0}^{N−1} C_k(x_k) + A` for all `(x₀, …, x_{N−1}) ∈ ℝ₊ᴺ`
(strict inequality, as printed).

**Formalization Note.** Almost surely, simultaneously for all nonnegative vectors `x`. -/
def Bound37 (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (J : ℝ → NoisePath N e → ℝ) (α : ℝ) (A : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ x : Fin N → ℝ, (∀ k, 0 ≤ x k) →
    J (∑ k, x k) (Y ω) < (1 - α) * ∑ k, C k (x k) + A ω

/-- **H Hypothesis**, SSRN 3742584 (Nov. 13, 2022), Definition 3.1, p.11. A jointly Borel
measurable `J : ℝ₊ × (ℝᵉ)ᴺ → ℝ₊` satisfies H Hypothesis (w.r.t. `C_k`, `k = 0, …, N − 1`) if
1. `x ↦ J(x, y)` is concave and continuously differentiable;
2. `J′(x, y) := ∂J/∂x (x, y) > 0`;
3. for any `x > 0`, `E[J′(x, Y)] < ∞`;
4. there are a constant `α ∈ (0, 1)` and a random variable `A ≥ 0` with `E[A] < ∞` such that
   (3.6) `J(x, Y) ≤ (1 − α) C_k(x) + A` for all `x ≥ 0`, `k = 0, …, N − 1`.

**Formalization Note.** "Continuously differentiable" is footnote 2 (p.5): continuous on `ℝ₊`,
`C¹` on `(0, ∞)`; so (2) is required at `x > 0` (`J′(0)` may be `+∞`). (1)–(2) are required for
every `y`, as printed. (3) for the nonnegative `J′` is integrability. `J` is defined on
`ℝ × (ℝᵉ)ᴺ`, is jointly measurable there and nonnegative at `x ≥ 0`. -/
def HHypothesis (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (J : ℝ → NoisePath N e → ℝ) : Prop :=
  IsReward J ∧
  (∀ y, ConcaveOn ℝ (Set.Ici 0) (fun x => J x y) ∧ IsC1Fn2 (fun x => J x y) ∧
    ∀ x : ℝ, 0 < x → 0 < rderiv (fun x => J x y) x) ∧
  (∀ x : ℝ, 0 < x → Integrable (fun ω => rderiv (fun x => J x (Y ω)) x) μ) ∧
  ∃ α ∈ Set.Ioo (0 : ℝ) 1, ∃ A : Ω → ℝ, IsAdmissibleBound μ A ∧ Bound36 μ Y C J α A

end RelPerfMFG


