-- Prove2me | Definitions.Def_RobustMDP_EntropyInner_klBall
-- name    : RobustMDP_EntropyInner_klBall
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:28:29.086852+00:00
-- url     : https://prove2.me/theorems/c29aea25-8953-4963-8d11-2cd698aa593d
-- title:
--   Kullback–Leibler divergence $D(p\|q)$ and the entropy uncertainty set $\{p\in\Delta_n : D(p\|q)\le\beta\}$
-- statement:
--   Let $\Delta_n=\{p\in\mathbb R^n_+ : p^{\mathsf T}\mathbf 1=1\}$ be the probability simplex of $\mathbb R^n$. For vectors $p,q\in\mathbb R^n$ the **Kullback–Leibler divergence** is
--
--   $$
--   D(p\|q) := \sum_{j=1}^n p(j)\log\frac{p(j)}{q(j)} .
--   $$
--
--   Given a reference distribution $q$ and a level $\beta$, the **entropy uncertainty set** is
--
--   $$
--   \mathcal P = \{p\in\Delta_n : D(p\|q)\le\beta\}.
--   $$
--
--   In the robust dynamic programming recursion, $\mathcal P$ describes the uncertainty on one row of one transition matrix: the unknown next-state distribution is only known to lie within divergence $\beta$ of the nominal distribution $q$.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` and $\Delta_n$ is Mathlib's `stdSimplex ℝ (Fin n)`. With Lean's convention $\log 0 = 0$, a coordinate with $p(j)=0$ contributes $0$, which is the usual convention $0\log 0=0$. The theorems of this mission always assume $q\in\Delta_n$ with $q(j)>0$ for every $j$, as the paper does, so no division by zero occurs. Mathlib's measure-valued `InformationTheory.klDiv` is not used.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 791, §6.1 (definition of 𝒫 and D(p‖q)); p. 780, Notation (Δ_n)

import Mathlib

namespace RobustMDP.EntropyInner

/-- The Kullback–Leibler divergence of the entropy model (Nilim–El Ghaoui 2005, §6.1, p. 791):
`D(p‖q) := ∑ⱼ p(j) log (p(j)/q(j))`, for vectors `p q : Fin n → ℝ`.
With Mathlib's convention `Real.log 0 = 0`, a coordinate with `p j = 0` contributes `0`, which is the
usual convention `0 log 0 = 0`. The theorems of this mission only use it with `q j > 0` for all `j`
and `p` in the probability simplex. -/
noncomputable def klDiv {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  ∑ j, p j * Real.log (p j / q j)

/-- The entropy uncertainty set (Nilim–El Ghaoui 2005, §6.1, p. 791):
`𝒫 = {p ∈ Δₙ : D(p‖q) ≤ β}`, where `Δₙ` is the probability simplex of `ℝⁿ`
(`stdSimplex ℝ (Fin n)`: nonnegative coordinates summing to `1`). -/
def klBall {n : ℕ} (q : Fin n → ℝ) (β : ℝ) : Set (Fin n → ℝ) :=
  {p | p ∈ stdSimplex ℝ (Fin n) ∧ klDiv p q ≤ β}

end RobustMDP.EntropyInner


