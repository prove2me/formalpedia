-- Prove2me | Definitions.Def_DROOptimal_Prescriptor_Pairs
-- name    : DROOptimal_Prescriptor_Pairs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:08.050782+00:00
-- url     : https://prove2.me/theorems/14e37b50-6a80-43e1-8272-31cda3110a87
-- title:
--   Notation p. 5, Def. 3–4, (6) p. 11 — quasi-continuity, arg-min selectors, the family 𝒳 of predictor–prescriptor pairs, prescription disappointment (2b), feasibility in (6), ⪯_𝒳, strong optimality
-- statement:
--   This module defines data-driven prescriptors and the meta-optimization problem (6) over predictor–prescriptor pairs.
--
--   Let $X\subseteq\mathbb R^n$ be the feasible set and $\mathcal P$ the probability simplex on $\Xi=\{1,\dots,d\}$, with $c(x,\mathbb P)$ the expected cost and $\mathbb P^\infty(\hat{\mathbb P}_T\in\cdot)$ the sampling probability of the empirical distribution.
--
--   1. **Quasi-continuity** (Notation, p. 5). A function $f:\mathcal P\to X$ is quasi-continuous at $\mathbb P\in\mathcal P$ if for every $\epsilon>0$ and every neighbourhood $U\subseteq\mathcal P$ of $\mathbb P$ there is a non-empty open set $V\subseteq U$ with $\|f(\mathbb P)-f(\mathbb Q)\|\le\epsilon$ for all $\mathbb Q\in V$; $V$ need not contain $\mathbb P$. It is quasi-continuous if this holds at every $\mathbb P$.
--   2. **Arg-min selector.** $\hat x:\mathcal P\to X$ selects from $\hat c$ if $\hat x(\mathbb P')\in\arg\min_{x\in X}\hat c(x,\mathbb P')$ for every $\mathbb P'\in\mathcal P$.
--   3. **The family $\mathcal X$** (p. 11). The pairs $(\hat c,\hat x)$ with $\hat c$ a data-driven predictor (continuous on $X\times\mathcal P$) and $\hat x$ a quasi-continuous arg-min selector of $\hat c$, i.e. a data-driven prescriptor induced by $\hat c$ (Definition 3).
--   4. **Prescription disappointment** ((2b), Definition 4). Under the model $\mathbb P$, the probability
--   $$
--   \mathbb P^\infty\big(c(\hat x(\hat{\mathbb P}_T),\mathbb P)>\hat c(\hat x(\hat{\mathbb P}_T),\hat{\mathbb P}_T)\big)
--   $$
--   that the true expected cost of the prescribed decision exceeds its in-sample estimate.
--   5. **Feasibility in (6).** $(\hat c,\hat x)\in\mathcal X$ and, for every model $\mathbb P\in\mathcal P$,
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\big(c(\hat x(\hat{\mathbb P}_T),\mathbb P)>\hat c(\hat x(\hat{\mathbb P}_T),\hat{\mathbb P}_T)\big)\le -r.
--   $$
--   6. **The order $\preceq_{\mathcal X}$** (p. 11). $(\hat c_1,\hat x_1)\preceq_{\mathcal X}(\hat c_2,\hat x_2)$ iff $\hat c_1(\hat x_1(\mathbb P'),\mathbb P')\le\hat c_2(\hat x_2(\mathbb P'),\mathbb P')$ for all $\mathbb P'\in\mathcal P$: the in-sample optimal values are compared, not the predictors.
--   7. **Strong optimality in (6).** $(\hat c^\star,\hat x^\star)$ is feasible in (6) and $(\hat c^\star,\hat x^\star)\preceq_{\mathcal X}(\hat c,\hat x)$ for every pair $(\hat c,\hat x)$ feasible in (6).
--
--   Problem (6) asks for the least conservative predictor–prescriptor pair whose prescriptions disappoint with probability decaying at rate at least $r$ under every model; Theorem 7 of the paper says the distributionally robust pair solves it in the strong sense.
--
--   **Formalization Note** Neighbourhoods and open sets in the definition of quasi-continuity are taken in $\mathcal P$ with its subspace topology, and the distance on $X$ is the Euclidean one (the paper writes $|f(\mathbb P)-f(\mathbb Q)|$). The disappointment event is the set of estimator realizations $\mathbb P'$ with $\hat c(\hat x(\mathbb P'),\mathbb P')<c(\hat x(\mathbb P'),\mathbb P)$, evaluated at $\mathbb P'=\hat{\mathbb P}_T$. The rate is the logarithm-free encoding of the `Setting` module.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, Notation p. 5 (quasi-continuity); p. 7, Definition 3; p. 8, Definition 4 (2b); pp. 10–11, strong optimality, the family 𝒳, the order ⪯_𝒳 and problem (6)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Prescriptor

open Topology

/-- Quasi-continuity at a point (Notation, p. 5): for every ε > 0 and every neighbourhood `U` of `ℙ`
in 𝒫 there is a non-empty open set `V ⊆ U` of 𝒫 with |f(ℙ) − f(ℚ)| ≤ ε for all ℚ ∈ V. The distance on
`↥X` is the Euclidean norm of the difference. `V` need not contain `ℙ`. -/
def QuasiContinuousAt {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (f : DROOptimal.Predictor.Δ d → ↥X) (ℙ : DROOptimal.Predictor.Δ d) :
    Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ U ∈ 𝓝 ℙ, ∃ V : Set (DROOptimal.Predictor.Δ d), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
    ∀ Q ∈ V, dist (f ℙ) (f Q) ≤ ε

/-- A function f : 𝒫 → X is quasi-continuous if it is quasi-continuous at every ℙ ∈ 𝒫. -/
def QuasiContinuous {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (f : DROOptimal.Predictor.Δ d → ↥X) : Prop :=
  ∀ ℙ, QuasiContinuousAt f ℙ

/-- x̂(ℙ′) ∈ arg min_{x ∈ X} ĉ(x, ℙ′) for every estimator realization ℙ′ ∈ 𝒫 (Definition 3, p. 7). -/
def IsArgminSelector {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (chat : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xhat : DROOptimal.Predictor.Δ d → ↥X) : Prop :=
  ∀ (ℙ' : DROOptimal.Predictor.Δ d) (x : ↥X), chat (xhat ℙ') ℙ' ≤ chat x ℙ'

/-- Membership in the family 𝒳 of data-driven predictor–prescriptor pairs (p. 11): ĉ ∈ 𝒞 and x̂ is a
quasi-continuous prescriptor induced by ĉ (Definition 3, p. 7). -/
def IsPair {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (chat : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xhat : DROOptimal.Predictor.Δ d → ↥X) : Prop :=
  DROOptimal.Predictor.IsPredictor chat ∧ QuasiContinuous xhat ∧ IsArgminSelector chat xhat

/-- The set of estimator realizations ℙ′ at which the prescription is disappointing under the model ℙ:
c(x̂(ℙ′), ℙ) > ĉ(x̂(ℙ′), ℙ′). Its probability ℙ^∞(ℙ̂_T ∈ ·) is the out-of-sample prescription
disappointment (2b), p. 8. -/
def disappointSet {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ)
    (chat : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xhat : DROOptimal.Predictor.Δ d → ↥X) (ℙ : DROOptimal.Predictor.Δ d) : Set (DROOptimal.Predictor.Δ d) :=
  {ℙ' | chat (xhat ℙ') ℙ' < DROOptimal.Predictor.cost γ (xhat ℙ') ℙ}

/-- Feasibility in (6), p. 11: (ĉ, x̂) ∈ 𝒳 and for every model ℙ ∈ 𝒫 the prescription disappointment
ℙ^∞(c(x̂(ℙ̂_T), ℙ) > ĉ(x̂(ℙ̂_T), ℙ̂_T)) satisfies limsup_{T→∞} (1/T) log(·) ≤ −r. -/
def Feasible6 {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (r : ℝ)
    (chat : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xhat : DROOptimal.Predictor.Δ d → ↥X) : Prop :=
  IsPair chat xhat ∧ ∀ ℙ : DROOptimal.Predictor.Δ d, DROOptimal.Predictor.RateLE (fun T => DROOptimal.Predictor.empProb ℙ T (disappointSet γ chat xhat ℙ)) r

/-- The partial order ⪯_𝒳 on pairs (p. 11):
(ĉ₁, x̂₁) ⪯_𝒳 (ĉ₂, x̂₂) ⟺ ĉ₁(x̂₁(ℙ′), ℙ′) ≤ ĉ₂(x̂₂(ℙ′), ℙ′) for all ℙ′ ∈ 𝒫. -/
def PairLE {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (chat₁ : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xhat₁ : DROOptimal.Predictor.Δ d → ↥X) (chat₂ : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xhat₂ : DROOptimal.Predictor.Δ d → ↥X) : Prop :=
  ∀ ℙ' : DROOptimal.Predictor.Δ d, chat₁ (xhat₁ ℙ') ℙ' ≤ chat₂ (xhat₂ ℙ') ℙ'

/-- Strong optimality in (6) (pp. 10–11): (ĉ⋆, x̂⋆) is feasible in (6) and (ĉ⋆, x̂⋆) ⪯_𝒳 (ĉ, x̂) for
every pair (ĉ, x̂) feasible in (6). -/
def StronglyOptimal6 {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (r : ℝ)
    (cstar : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xstar : DROOptimal.Predictor.Δ d → ↥X) : Prop :=
  Feasible6 γ r cstar xstar ∧
    ∀ (chat : ↥X → DROOptimal.Predictor.Δ d → ℝ) (xhat : DROOptimal.Predictor.Δ d → ↥X),
      Feasible6 γ r chat xhat → PairLE cstar xstar chat xhat

end DROOptimal.Prescriptor


