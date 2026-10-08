-- Prove2me | Definitions.Def_SAG_LargeStep_sagRun
-- name    : SAG_LargeStep_sagRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:10.883985+00:00
-- url     : https://prove2.me/theorems/5304a5ab-8f19-4d42-973e-658edd09b7a6
-- title:
--   The SAG iteration (5) on the state θ = (y, x) and its runs from a given start
-- statement:
--   The **stochastic average gradient (SAG)** method keeps a table $y=(y_1,\dots,y_n)$ of stored gradients and an iterate $x\in\mathbb R^p$; write the state as $\theta=(y,x)$. One iteration with step size $\alpha$ and selected index $i\in\{1,\dots,n\}$ sets
--   $$y_j'=\begin{cases}f_i'(x)&j=i,\\ y_j&j\ne i,\end{cases}\qquad x'=x-\frac{\alpha}{n}\sum_{j=1}^n y_j' .$$
--   In the paper's notation, $x^k=x^{k-1}-\frac\alpha n\sum_i y_i^k$ with $y_i^k=f_i'(x^{k-1})$ if $i=i_k$ and $y_i^k=y_i^{k-1}$ otherwise.
--
--   A **run** from the start $\theta^0=(y^0,x^0)$ along a finite sequence of indices $i_1,\dots,i_k$ applies these iterations in order and returns $\theta^k=(y^k,x^k)$. When the indices are drawn independently and uniformly from $\{1,\dots,n\}$, this is the SAG algorithm.
--
--   **Formalization Note** The step is `sagStep f' α θ i` and the run is `runFrom f' α θ0 l` for a list `l` of indices (a left fold). The randomness is not part of the definition: theorems average over all index sequences.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 2, iteration (5); p. 13, §A.1

import Mathlib

namespace SAG.LargeStep

/-- One SAG iteration (iteration (5), p. 2; appendix form p. 13) on the state `θ = (y, x)`, where
`y : Fin n → ℝᵖ` is the table of stored gradients and `x` the iterate, with step size `α` and
selected index `i`: the table entry `i` is replaced by `f'ᵢ(x)`, the other entries are kept, and
`x' = x − (α/n) ∑ⱼ y'ⱼ` with the updated table `y'`. -/
noncomputable def sagStep {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) (i : Fin n) :
    (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) :=
  (Function.update θ.1 i (f' i θ.2),
    θ.2 - (α / (n : ℝ)) • ∑ j, Function.update θ.1 i (f' i θ.2) j)

/-- The SAG state after applying, in order, the iterations with the indices of the list `l`,
starting from the state `θ0 = (y⁰, x⁰)`. -/
noncomputable def runFrom {p n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (α : ℝ)
    (θ0 : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) (l : List (Fin n)) :
    (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p) :=
  l.foldl (sagStep f' α) θ0

end SAG.LargeStep


