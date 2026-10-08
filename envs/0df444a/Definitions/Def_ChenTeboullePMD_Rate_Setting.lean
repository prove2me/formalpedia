-- Prove2me | Definitions.Def_ChenTeboullePMD_Rate_Setting
-- name    : ChenTeboullePMD_Rate_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:24:23.775296+00:00
-- url     : https://prove2.me/theorems/bf55604c-5890-4f60-b63f-efdd206d9d76
-- title:
--   Definition 2.1 and (8) — Bregman functions, extended objectives, PMD runs, and cumulative steps
-- statement:
--   Let $E$ be a real normed space. A **Bregman function with zone** $S$ is a real function $\psi$ on $\bar S$, where $S$ is open, that is continuously differentiable on $S$ and strictly convex and continuous on $\bar S$. For every real $\alpha$, both partial level sets $\{x\in\bar S:D_\psi(x,y)\le\alpha\}$ for $y\in S$ and $\{y\in S:D_\psi(x,y)\le\alpha\}$ for $x\in\bar S$ are bounded. If $y^k\in S$ tends to $y^*$, then $D_\psi(y^*,y^k)\to0$. If $x^k\in\bar S$ is bounded, $y^k\in S$ tends to $y^*\in\bar S$, and $D_\psi(x^k,y^k)\to0$, then $x^k\to y^*$.
--
--   An extended objective is represented by an effective domain $C$ and a real function $f$ on $C$, with value $+\infty$ outside $C$; properness is imposed separately by requiring $C\ne\varnothing$. A **PMD run** $(x^k)_{k\ge0}$ begins at $x^0\in S$ and, for a step sequence $\lambda_k$, has each produced iterate $x^k\in S\cap C$ ($k\ge1$) minimizing
--   $$
--   f(u)+\lambda_k^{-1}D_\psi(u,x^{k-1})
--   $$
--   over $u\in C\cap\bar S$. The cumulative step is $\sigma_n=\sum_{k=1}^n\lambda_k$, with $\sigma_0=0$.
--
--   These definitions fix the objects shared by the convergence estimates; their theorem hypotheses separately require $\lambda_k>0$.
--
--   **Formalization Note** The definition layer works over a real normed space; the theorem statements assume finite dimensionality as on the page. Derivatives are covectors. The published Bregman distance differentiates at its second argument. Lean's total $\psi$ is used only on $\bar S$. Strict convexity on $\bar S$ includes convexity of that set. The condition $x^k\in\bar S$ in the last limit clause spells out the distance's domain. The run predicate includes existence and zone membership in place of the paper's surjectivity assumption on $\nabla\psi$; it never chooses a minimizer by an arbitrary choice operator.
-- source:
--   Chen & Teboulle, Convergence analysis of a proximal-like minimization algorithm using Bregman functions, SIAM J. Optim. 3 (1993), pp. 538–541, (1), (5), Definition 2.1, (7)–(8), definition of σ_n

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace ChenTeboullePMD.Rate

open BeckTeboulleMD.EMDA
open Filter
open scoped Topology

/-- Definition 2.1: a Bregman function with open zone `S`. The function is represented
on the whole ambient space, but only its restriction to `closure S` is used. -/
structure IsBregmanFunction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (ψ : E → ℝ) : Prop where
  isOpen : IsOpen S
  contDiffOn : ContDiffOn ℝ 1 ψ S
  strictConvexOn : StrictConvexOn ℝ (closure S) ψ
  continuousOn : ContinuousOn ψ (closure S)
  bounded_L₁ : ∀ (α : ℝ) (y : E), y ∈ S →
    Bornology.IsBounded {x | x ∈ closure S ∧ bregman ψ x y ≤ α}
  bounded_L₂ : ∀ (α : ℝ) (x : E), x ∈ closure S →
    Bornology.IsBounded {y | y ∈ S ∧ bregman ψ x y ≤ α}
  tendsto_zero : ∀ (y : ℕ → E) (ystar : E),
    (∀ k, y k ∈ S) → Tendsto y atTop (𝓝 ystar) →
    Tendsto (fun k => bregman ψ ystar (y k)) atTop (𝓝 0)
  tendsto_of_zero : ∀ (x y : ℕ → E) (ystar : E),
    (∀ k, x k ∈ closure S) → (∀ k, y k ∈ S) →
    Tendsto y atTop (𝓝 ystar) → ystar ∈ closure S →
    Bornology.IsBounded (Set.range x) →
    Tendsto (fun k => bregman ψ (x k) (y k)) atTop (𝓝 0) →
    Tendsto x atTop (𝓝 ystar)

/-- The proper extended-real objective represented by its effective domain `C` and
real restriction `f`. Outside `C` its value is positive infinity. -/
noncomputable def extendTop {E : Type*} (C : Set E) (f : E → ℝ) : E → EReal :=
  fun x => by classical exact if x ∈ C then (f x : EReal) else ⊤

/-- The paper's `σₙ = ∑_{k=1}^n λₖ`; `σ₀ = 0`. -/
def sigma (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, lam k

/-- A run of the PMD iteration (8), indexed from `x 0`. Each produced point lies
in the open zone and effective domain, and minimizes the objective over the latter
intersected with the closure of the zone. -/
def IsPMDRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S C : Set E) (ψ f : E → ℝ) (lam : ℕ → ℝ) (x : ℕ → E) : Prop :=
  x 0 ∈ S ∧ ∀ k : ℕ, x (k + 1) ∈ S ∧ x (k + 1) ∈ C ∧
    ∀ u ∈ C, u ∈ closure S →
      f (x (k + 1)) + (lam (k + 1))⁻¹ * bregman ψ (x (k + 1)) (x k) ≤
        f u + (lam (k + 1))⁻¹ * bregman ψ u (x k)

end ChenTeboullePMD.Rate


