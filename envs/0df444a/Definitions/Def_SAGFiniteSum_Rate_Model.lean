-- Prove2me | Definitions.Def_SAGFiniteSum_Rate_Model
-- name    : SAGFiniteSum_Rate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:39.574054+00:00
-- url     : https://prove2.me/theorems/5bd7a293-b531-42c7-bbd0-71e37b3de50d
-- title:
--   §1 (1), (5)–(6), §3 and App. B.1 — standing assumptions, the SAG step and iterates xᵗ, the average x̄ᵏ, σ², the two initial tables y⁰ and Theorem 1's C₀
-- statement:
--   This file fixes the setting of the convergence analysis of the stochastic average gradient (SAG) method.
--
--   **Problem.** Let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ and $g(x)=\frac1n\sum_{i=1}^n f_i(x)$, problem (1). Write $f'_i$ for the gradient of $f_i$ and $g'(x)=\frac1n\sum_i f'_i(x)$.
--
--   **Standing assumptions (§3).** The data satisfy:
--   1. $n\ge1$ and $L>0$;
--   2. each $f_i$ is differentiable with gradient $f'_i$ at every point, and convex;
--   3. each gradient is $L$-Lipschitz, $\|f'_i(x)-f'_i(y)\|\le L\|x-y\|$ for all $x,y$ (8);
--   4. $x^*$ is a minimizer of $g$: $g(x^*)\le g(x)$ for all $x$.
--
--   **The SAG step.** A state is $\theta=(y,x)$ with a table $y=(y_1,\dots,y_n)\in(\mathbb R^p)^n$ and an iterate $x\in\mathbb R^p$. The step with index $i$ and step size $\alpha$ first refreshes $y_i\leftarrow f'_i(x)$, keeping the other entries, and then moves
--   $$
--   x\leftarrow x-\frac{\alpha}{n}\sum_{j=1}^n y_j
--   $$
--   with the refreshed table. This is the recursion of App. B.1: $y^k_i=f'_i(x^{k-1})$ if $i=i_k$, $y^k_i=y^{k-1}_i$ otherwise, and $x^k=x^{k-1}-\frac\alpha n\sum_i y^k_i$.
--
--   **Iterates.** For an index sequence $i_1,\dots,i_k$ and an initial state $\theta^0=(y^0,x^0)$, $\theta^t=(y^t,x^t)$ is the state after the first $t$ steps. The average iterate is
--   $$
--   \bar x^k=\frac1k\sum_{i=0}^{k-1}x^i ,
--   $$
--   which includes $x^0$ and excludes $x^k$.
--
--   **Constants.** $\sigma^2=\frac1n\sum_i\|f'_i(x^*)\|^2$. The two initial tables of §3 are $y^0_i=0$ and the centered table $y^0_i=f'_i(x^0)-g'(x^0)$. Theorem 1's constants are
--   $$
--   C_0^{\mathrm{zero}}=g(x^0)-g(x^*)+\frac{4L}{n}\|x^0-x^*\|^2+\frac{\sigma^2}{16L},\qquad
--   C_0^{\mathrm{cent}}=\frac32\big[g(x^0)-g(x^*)\big]+\frac{4L}{n}\|x^0-x^*\|^2 .
--   $$
--
--   These objects are what Theorem 1 and the lemmas of Appendix B speak about.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`; the components are indexed by `Fin n` (0-based). $g$ and $g'$ are the published `SAGA.Convex.fAvg` and `SAGA.Convex.gradAvg`. The step `sagStep` has the same body as the published `SAG.SmallStep.step` (the published module could not be imported in this run; see the mission notes). The gradients are an explicit map `f'`, tied to `f` by the `hasGradient` field. Strong convexity is not part of `SAGAssumptions`; it is a hypothesis of the statements that use it. $n\ge1$ and $L>0$ make $1/n$, $\sigma^2/(16L)$ and $4L/n$ meaningful.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, Eq. (1), p. 2; Eqs. (5)–(6), p. 3; §3 (assumptions, (8), x̄ᵏ, σ², y⁰, Theorem 1's C₀), p. 7; App. B.1 recursion, p. 35

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaRun

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- The standing assumptions of §3 (p. 7) and App. B.1 (Schmidt, Le Roux & Bach,
arXiv:1309.2388v2) on the data of problem (1), `g(x) = (1/n) ∑ᵢ fᵢ(x)` over `ℝᵖ`:
`n ≥ 1` components, a Lipschitz constant `L > 0`, each `fᵢ` convex and differentiable with
gradient `f' i`, each gradient `L`-Lipschitz (8), and `xstar` a minimizer of `g`.
Strong convexity of `g` is not part of this structure; it is a hypothesis where the paper
assumes it. -/
structure SAGAssumptions {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p)) : Prop where
  n_pos : 0 < n
  L_pos : 0 < L
  hasGradient : ∀ i x, HasGradientAt (f i) (f' i x) x
  convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  lipschitz : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖
  minimizer : ∀ x, SAGA.Convex.fAvg f xstar ≤ SAGA.Convex.fAvg f x

/-- One SAG step with index `i` (App. B.1, p. 35; iteration (5)–(6), p. 3) on the state
`θ = (y, x)`: first the table entry `i` is refreshed, `yᵢ ← f'ᵢ(x)`, the other entries are
kept; then `x ← x − (α/n) ∑ⱼ yⱼ` with the refreshed table. (Same body as the published
`SAG.SmallStep.step`.) -/
noncomputable def sagStep {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ) (i : Fin n)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) :=
  (Function.update θ.1 i (f' i θ.2),
    θ.2 - (α / (n : ℝ)) • ∑ j, Function.update θ.1 i (f' i θ.2) j)

/-- The SAG state `θᵗ = (yᵗ, xᵗ)` after the first `t` steps, with indices
`js 0, …, js (t-1)` (the paper's `i₁, …, i_t`), from the initial state `θ0 = (y⁰, x⁰)`.
For `t ≥ k` it is the state after all `k` steps. -/
noncomputable def sagIter {p n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p))
    (js : Fin k → Fin n) (t : ℕ) :
    (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) :=
  ((List.ofFn js).take t).foldl (fun θ i => sagStep f' α i θ) θ0

/-- The average iterate `x̄ᵏ = (1/k) ∑_{i=0}^{k-1} xⁱ` (§3, p. 7), which includes `x⁰` and
excludes `xᵏ`. -/
noncomputable def avgIter {p n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p))
    (js : Fin k → Fin n) : EuclideanSpace ℝ (Fin p) :=
  (1 / (k : ℝ)) • ∑ t ∈ Finset.range k, (sagIter f' α θ0 js t).2

/-- The variance of the gradient norms at the optimum, `σ² = (1/n) ∑ᵢ ‖f'ᵢ(x*)‖²` (§3, p. 7). -/
noncomputable def sigmaSq {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (xstar : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ‖f' i xstar‖ ^ 2

/-- The zero initial table `y⁰ᵢ = 0` (§3, p. 7). -/
def zeroTable {p n : ℕ} : Fin n → EuclideanSpace ℝ (Fin p) := fun _ => 0

/-- The centered initial table `y⁰ᵢ = f'ᵢ(x⁰) − g'(x⁰)` (§3, p. 7). -/
noncomputable def centeredTable {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (x0 : EuclideanSpace ℝ (Fin p)) : Fin n → EuclideanSpace ℝ (Fin p) :=
  fun i => f' i x0 - SAGA.Convex.gradAvg f' x0

/-- Theorem 1's constant for the zero initialization:
`C₀ = g(x⁰) − g(x*) + (4L/n)‖x⁰ − x*‖² + σ²/(16L)` (p. 7). -/
noncomputable def C0zero {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar x0 : EuclideanSpace ℝ (Fin p)) : ℝ :=
  SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar + 4 * L / (n : ℝ) * ‖x0 - xstar‖ ^ 2
    + sigmaSq f' xstar / (16 * L)

/-- Theorem 1's constant for the centered initialization:
`C₀ = (3/2)[g(x⁰) − g(x*)] + (4L/n)‖x⁰ − x*‖²` (p. 7). -/
noncomputable def C0centered {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (L : ℝ)
    (xstar x0 : EuclideanSpace ℝ (Fin p)) : ℝ :=
  3 / 2 * (SAGA.Convex.fAvg f x0 - SAGA.Convex.fAvg f xstar)
    + 4 * L / (n : ℝ) * ‖x0 - xstar‖ ^ 2

end SAGFiniteSum.Rate


