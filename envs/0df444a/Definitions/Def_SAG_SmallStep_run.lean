-- Prove2me | Definitions.Def_SAG_SmallStep_run
-- name    : SAG_SmallStep_run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:10.53763+00:00
-- url     : https://prove2.me/theorems/bb2deb29-8ba4-46ad-ab1f-ccc3c9aeb1df
-- title:
--   The SAG step and the SAG run from an initial state (iteration (5); appendix form p. 13)
-- statement:
--   Let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be differentiable with gradients $f'_1,\dots,f'_n$, and fix a step size $\alpha\in\mathbb R$. The **stochastic average gradient (SAG)** method keeps a table of $n$ vectors $y=(y_1,\dots,y_n)\in(\mathbb R^p)^n$ together with an iterate $x\in\mathbb R^p$; write the state as $\theta=(y,x)$.
--
--   **One step** with index $i\in\{1,\dots,n\}$ maps $\theta=(y,x)$ to $\theta'=(y',x')$, where first the $i$-th table entry is refreshed and then the iterate moves along the average of the refreshed table:
--   $$
--   y'_j=\begin{cases} f'_i(x) & j=i,\\ y_j & j\neq i,\end{cases}
--   \qquad
--   x' = x-\frac{\alpha}{n}\sum_{j=1}^n y'_j .
--   $$
--
--   **The run.** Given an initial state $\theta^0=(y^0,x^0)$ and indices $i_1,\dots,i_k$, the state $\theta^k=(y^k,x^k)$ is obtained by applying the steps with indices $i_1,\dots,i_k$ in this order. This is the recursion of §A.1: for $k\ge1$, $y^k_i=f'_i(x^{k-1})$ if $i=i_k$ and $y^k_i=y^{k-1}_i$ otherwise, and $x^k=x^{k-1}-\frac{\alpha}{n}\sum_{i=1}^n y^k_i$. In the method the indices $i_k$ are drawn independently and uniformly from $\{1,\dots,n\}$.
--
--   This is the algorithm whose convergence Propositions 1 and 2 quantify; the convergence results start it from the zero table $y^0=0$.
--
--   **Formalization Note** Indices are `Fin n` (0-based); a state is a pair `(y, x) : (Fin n → ℝᵖ) × ℝᵖ` with $\mathbb R^p$ = `EuclideanSpace ℝ (Fin p)`. `step f' α i θ` is one step and `runFrom f' α θ0 js` is the state after the steps with indices `js 0, …, js (k-1)`; the initial table is a parameter. The gradients are given as an explicit map `f'`; their relation to the $f_i$ is a hypothesis of the theorems that need it.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 2, iteration (5); p. 13, §A.1

import Mathlib

namespace SAG.SmallStep

/-- One SAG step with index `i` (Le Roux–Schmidt–Bach, arXiv:1202.6258v4, p. 13, §A.1).
The state is `θ = (y, x)` with the gradient table `y = (y₁, …, yₙ)` and the iterate `x`.
First the table entry `i` is refreshed, `yᵢ ← f'ᵢ(x)`, the other entries are kept; then
`x ← x − (α/n) ∑ⱼ yⱼ` with the refreshed table. -/
noncomputable def step {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ) (i : Fin n)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) :
    (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) :=
  (Function.update θ.1 i (f' i θ.2),
    θ.2 - (α / (n : ℝ)) • ∑ j, Function.update θ.1 i (f' i θ.2) j)

/-- The SAG state `θᵏ = (yᵏ, xᵏ)` after the `k` steps with the indices
`js 0, …, js (k-1)` (that is, `i₁, …, i_k`), in order, from the initial state `θ0 = (y⁰, x⁰)`. -/
noncomputable def runFrom {p n k : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p))
    (js : Fin k → Fin n) :
    (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) :=
  (List.ofFn js).foldl (fun θ i => step f' α i θ) θ0

end SAG.SmallStep


