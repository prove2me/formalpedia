-- Prove2me | Definitions.Def_DROOptimal_Predictor_Problem5
-- name    : DROOptimal_Predictor_Problem5
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:47.118991+00:00
-- url     : https://prove2.me/theorems/1309aa1c-9ffe-4dd0-919d-19a5dd77dd16
-- title:
--   (5), pp. 8–11 — disappointment set, feasibility and strong optimality in the prediction problem (5); convex combinations in 𝒫
-- statement:
--   This module states the paper's vector optimization problem (5) for data-driven predictors, in the finite-state setting of the `Setting` module ($\Xi=\{1,\dots,d\}$, model class $\mathcal P$, cost $\gamma$, expected cost $c(x,\mathbb P)$).
--
--   1. **Disappointment set.** For a data-driven predictor $\hat c:X\times\mathcal P\to\mathbb R$, a decision $x\in X$ and a model $\mathbb P\in\mathcal P$,
--   $$
--   \mathcal D(x,\mathbb P)=\{\mathbb P'\in\mathcal P : c(x,\mathbb P)>\hat c(x,\mathbb P')\}.
--   $$
--   The probability $\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D(x,\mathbb P))=\mathbb P^\infty\big(c(x,\mathbb P)>\hat c(x,\hat{\mathbb P}_T)\big)$ is the out-of-sample prediction disappointment (2a) (Definition 4, p. 8).
--   2. **Feasibility in (5).** $\hat c$ is feasible if it is continuous on $X\times\mathcal P$ (that is, $\hat c\in\mathcal C$) and
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\big(c(x,\mathbb P)>\hat c(x,\hat{\mathbb P}_T)\big)\le -r\qquad\forall x\in X,\ \mathbb P\in\mathcal P .
--   $$
--   3. **Strong optimality in (5).** $\hat c^\star$ is strongly optimal if it is feasible and $\hat c^\star\preceq_{\mathcal C}\hat c$, i.e. $\hat c^\star(x,\mathbb P')\le\hat c(x,\mathbb P')$ for all $x\in X$, $\mathbb P'\in\mathcal P$, for every feasible $\hat c$.
--   4. **Convex combinations.** For $\lambda\in[0,1]$ and $\mathbb P_1,\mathbb P_2\in\mathcal P$, the point $(1-\lambda)\mathbb P_1+\lambda\mathbb P_2\in\mathcal P$.
--
--   Strong optimality is the paper's notion of a *least conservative* predictor whose disappointment decays at rate at least $r$: it is not merely undominated, it lies below every feasible predictor pointwise.
--
--   **Formalization Note** Feasibility uses the logarithm-free rate predicate `RateLE` of the `Setting` module: for every $r'<r$, eventually the disappointment is at most $e^{-r'T}$. This is equivalent to the paper's $\limsup$ condition with $\log 0=-\infty$; the naive `Real.log` form would declare a never-disappointed predictor infeasible. Continuity is joint continuity on the product of the subtype $X$ with the subtype $\mathcal P$; no other restriction (conservativeness, measurability) is placed on $\hat c$.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 8, Definition 4 (2a); pp. 10–11, the class 𝒞, the order ⪯_𝒞, problem (5), strong optimality; p. 16, the disappointment set 𝒟(x,ℙ) in the proof of Theorem 3; p. 12, Proposition 1(ii) and p. 18 (convex combinations)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- The convex combination (1 − λ)ℙ₁ + λℙ₂ of two points of 𝒫, for λ ∈ [0, 1], as a point of 𝒫
(used in Proposition 1(ii), p. 12, and in the proof of Theorem 4, p. 18). -/
noncomputable def mix {d : ℕ} (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (ℙ₁ ℙ₂ : Δ d) : Δ d :=
  ⟨(1 - t) • (ℙ₁ : Fin d → ℝ) + t • (ℙ₂ : Fin d → ℝ),
    convex_stdSimplex ℝ (Fin d) ℙ₁.2 ℙ₂.2 (by linarith [ht.2]) ht.1 (by ring)⟩

/-- The disappointment set 𝒟(x, ℙ) = {ℙ′ ∈ 𝒫 : c(x, ℙ) > ĉ(x, ℙ′)} of a predictor ĉ at the decision
x under the model ℙ (proof of Theorem 3, p. 16). Its probability ℙ^∞(ℙ̂_T ∈ 𝒟(x, ℙ)) is the
out-of-sample prediction disappointment ℙ^∞(c(x, ℙ) > ĉ(x, ℙ̂_T)) of (2a), p. 8. -/
def disappointSet {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ)
    (chat : ↥X → Δ d → ℝ) (x : ↥X) (ℙ : Δ d) : Set (Δ d) :=
  {ℙ' | chat x ℙ' < cost γ x ℙ}

/-- Feasibility in (5), p. 10: ĉ ∈ 𝒞 (it is a continuous function on X × 𝒫) and for every decision
x ∈ X and model ℙ ∈ 𝒫 the prediction disappointment satisfies
limsup_{T→∞} (1/T) log ℙ^∞(c(x, ℙ) > ĉ(x, ℙ̂_T)) ≤ −r. -/
def Feasible5 {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (r : ℝ)
    (chat : ↥X → Δ d → ℝ) : Prop :=
  IsPredictor chat ∧
    ∀ (x : ↥X) (ℙ : Δ d), RateLE (fun T => empProb ℙ T (disappointSet γ chat x ℙ)) r

/-- Strong optimality in (5), p. 10: ĉ⋆ is feasible in (5) and ĉ⋆ ⪯_𝒞 ĉ, i.e.
ĉ⋆(x, ℙ′) ≤ ĉ(x, ℙ′) for all x ∈ X and ℙ′ ∈ 𝒫, for every predictor ĉ feasible in (5). -/
def StronglyOptimal5 {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (r : ℝ)
    (cstar : ↥X → Δ d → ℝ) : Prop :=
  Feasible5 γ r cstar ∧
    ∀ chat : ↥X → Δ d → ℝ, Feasible5 γ r chat → ∀ (x : ↥X) (ℙ' : Δ d), cstar x ℙ' ≤ chat x ℙ'

end DROOptimal.Predictor


