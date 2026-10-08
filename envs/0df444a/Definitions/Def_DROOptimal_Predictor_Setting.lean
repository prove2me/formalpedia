-- Prove2me | Definitions.Def_DROOptimal_Predictor_Setting
-- name    : DROOptimal_Predictor_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:11.893008+00:00
-- url     : https://prove2.me/theorems/8efa7544-76c4-4bab-b302-660ebe3d0f81
-- title:
--   §2–§4.1, pp. 6–14 — simplex 𝒫, c(x,ℙ), relative entropy I (Def. 5), empirical distribution, ℙ^∞(ℙ̂_T ∈ 𝒟), rate, predictor class 𝒞, ĉ_r (10)
-- statement:
--   This module fixes the finite-state setting of Van Parys, Mohajerin Esfahani and Kuhn and the objects shared by all of their finite-state results.
--
--   The random parameter $\xi$ takes values in $\Xi=\{1,\dots,d\}$, and decisions $x$ range over a set $X\subseteq\mathbb R^n$. The module defines:
--
--   1. **Model class.** $\mathcal P=\{\mathbb P\in\mathbb R^d_+ : \sum_{i\in\Xi}\mathbb P(i)=1\}$, the probability simplex, with the topology it inherits from $\mathbb R^d$.
--   2. **Model-based predictor** (Definition 1). For a cost $\gamma(x,i)$, $c(x,\mathbb P)=\sum_{i\in\Xi}\mathbb P(i)\gamma(x,i)$.
--   3. **Relative entropy** (Definition 5). For $\mathbb P',\mathbb P\in\mathcal P$,
--   $$
--   I(\mathbb P',\mathbb P)=\sum_{i\in\Xi}\mathbb P'(i)\log\frac{\mathbb P'(i)}{\mathbb P(i)}\in[0,+\infty],
--   $$
--   with the conventions $0\log(0/p)=0$ for $p\ge 0$ and $p'\log(p'/0)=+\infty$ for $p'>0$. Thus $I(\mathbb P',\mathbb P)=+\infty$ as soon as $\mathbb P(i)=0<\mathbb P'(i)$ for some $i$.
--   4. **Empirical distribution** (Definition 2). For a sample path $\xi_1,\dots,\xi_T$, $\hat{\mathbb P}_T(i)=\frac1T\sum_{t=1}^T\mathbb 1_{\xi_t=i}$.
--   5. **Sampling probability.** For $\mathcal D\subseteq\mathcal P$, $\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)=\sum_{(\xi_1,\dots,\xi_T)\in\Xi^T}\mathbb 1\{\hat{\mathbb P}_T\in\mathcal D\}\prod_{t=1}^T\mathbb P(\xi_t)$, the probability of the event when the samples are drawn independently from $\mathbb P$.
--   6. **Decay rate.** A sequence $p_T\ge 0$ satisfies $\limsup_{T\to\infty}\frac1T\log p_T\le -r$ (with $\log 0=-\infty$) if and only if for every $r'<r$, eventually $p_T\le e^{-r'T}$.
--   7. **Data-driven predictors** (Definition 3, the class $\mathcal C$). Continuous functions $\hat c: X\times\mathcal P\to\mathbb R$.
--   8. **Distributionally robust predictor** (Definition 6, (10)). For $r\ge0$,
--   $$
--   \hat c_r(x,\mathbb P')=\sup_{\mathbb P\in\mathcal P}\{c(x,\mathbb P): I(\mathbb P',\mathbb P)\le r\}.
--   $$
--
--   These objects are the vocabulary of the paper's prediction problem: the estimator realization $\mathbb P'$ is always the first argument of $I$, and $\hat c_r$ is the worst-case expected cost over all models from which the observed frequencies are not too unlikely.
--
--   **Formalization Note** $\mathcal P$ is the subtype of `stdSimplex ℝ (Fin d)`, so neighbourhoods are relative to $\mathcal P$, as footnote 1 (p. 12) requires. The relative entropy is valued in `EReal`: it is $\top$ unless every $i$ with $\mathbb P(i)=0$ has $\mathbb P'(i)=0$, and the real sum otherwise (under that condition Lean's `Real.log 0 = 0` gives exactly $0\log(0/p)=0$). The empirical vector at $T=0$ is the zero vector, which is not in $\mathcal P$, so every event $\{\hat{\mathbb P}_0\in\mathcal D\}$ has probability $0$; all statements are asymptotic in $T$ or assume $T\ge1$. The decay rate is encoded without logarithms (`RateLE`), so that a probability that vanishes for large $T$ has rate $-\infty$, not $0$. The supremum in $\hat c_r$ is a real `sSup`; for $r\ge0$ the set contains $c(x,\mathbb P')$ and is bounded by $\max_i\gamma(x,i)$ (for $r<0$ it is empty and the value is a junk $0$, which no statement uses). Mission 2 of this series defines the same objects, with identical content, in its own namespace; the two modules are candidates for merging.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, pp. 5–14, §2 (standing assumptions p. 5), Definitions 1–3, 5, 6, (10)

import Mathlib

namespace DROOptimal.Predictor

open Filter

/-- The model class 𝒫 = {ℙ ∈ ℜ^d₊ : Σ_i ℙ(i) = 1} (p. 6), as a subtype of `Fin d → ℝ`, so that
neighbourhoods, interiors and continuity are relative to 𝒫 (footnote 1, p. 12). -/
abbrev Δ (d : ℕ) : Type := ↥(stdSimplex ℝ (Fin d))

/-- The model-based predictor c(x, ℙ) = Σ_{i ∈ Ξ} ℙ(i) γ(x, i) (Definition 1, p. 6). -/
def cost {d : ℕ} {Y : Type*} (γ : Y → Fin d → ℝ) (x : Y) (ℙ : Δ d) : ℝ :=
  ∑ i, (ℙ : Fin d → ℝ) i * γ x i

open Classical in
/-- The relative entropy I(ℙ′, ℙ) = Σ_i ℙ′(i) log(ℙ′(i)/ℙ(i)) (Definition 5, p. 12), valued in `EReal`,
with the conventions 0 log(0/p) = 0 and p′ log(p′/0) = ∞ of p. 5: it is `⊤` unless every `i` with
`ℙ i = 0` has `ℙ' i = 0`, and the real sum otherwise. -/
noncomputable def relEntropy {d : ℕ} (ℙ' ℙ : Δ d) : EReal :=
  if ∀ i, (ℙ : Fin d → ℝ) i = 0 → (ℙ' : Fin d → ℝ) i = 0 then
    ((∑ i, (ℙ' : Fin d → ℝ) i * Real.log ((ℙ' : Fin d → ℝ) i / (ℙ : Fin d → ℝ) i) : ℝ) : EReal)
  else ⊤

/-- The vector of empirical state frequencies ℙ̂_T(i) = (1/T) Σ_{t=1}^T 1_{ξ_t = i} of a sample path
ω = (ξ_1, …, ξ_T) (Definition 2, p. 7). For `T ≥ 1` it lies in 𝒫; for `T = 0` it is the zero vector,
which is not in 𝒫. -/
noncomputable def empiricalVec {d T : ℕ} (ω : Fin T → Fin d) : Fin d → ℝ :=
  fun i => ((Finset.univ.filter (fun t => ω t = i)).card : ℝ) / (T : ℝ)

/-- The event "ℙ̂_T ∈ 𝒟" for the sample path `ω`: the empirical frequency vector lies in 𝒫 and,
as an element of 𝒫, in `D`. (For `T = 0` the event is empty.) -/
def EmpiricalIn {d T : ℕ} (ω : Fin T → Fin d) (D : Set (Δ d)) : Prop :=
  ∃ h : empiricalVec ω ∈ stdSimplex ℝ (Fin d), (⟨empiricalVec ω, h⟩ : Δ d) ∈ D

open Classical in
/-- The probability ℙ^∞(E) of an event `E` of the first `T` samples, when the samples are drawn
independently from ℙ: Σ_{ω ∈ Ξ^T} 1_E(ω) Π_t ℙ(ω_t). -/
noncomputable def pathProb {d : ℕ} (ℙ : Δ d) (T : ℕ) (E : (Fin T → Fin d) → Prop) : ℝ :=
  ∑ ω : Fin T → Fin d, if E ω then ∏ t, (ℙ : Fin d → ℝ) (ω t) else 0

/-- ℙ^∞(ℙ̂_T ∈ 𝒟) for a set `D ⊆ 𝒫` of estimator realizations. -/
noncomputable def empProb {d : ℕ} (ℙ : Δ d) (T : ℕ) (D : Set (Δ d)) : ℝ :=
  pathProb ℙ T (fun ω => EmpiricalIn ω D)

/-- `RateLE p r` encodes limsup_{T→∞} (1/T) log p_T ≤ −r (with log 0 = −∞) without logarithms:
for every `r' < r`, eventually `p T ≤ exp(−r' T)`. -/
def RateLE (p : ℕ → ℝ) (r : ℝ) : Prop :=
  ∀ r' : ℝ, r' < r → ∀ᶠ T : ℕ in atTop, p T ≤ Real.exp (-(r' * (T : ℝ)))

/-- A data-driven predictor (Definition 3, p. 7; the class 𝒞, p. 10): a function ĉ : X × 𝒫 → ℜ that
is jointly continuous. -/
def IsPredictor {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (chat : ↥X → Δ d → ℝ) : Prop :=
  Continuous (fun q : ↥X × Δ d => chat q.1 q.2)

/-- The distributionally robust predictor ĉ_r(x, ℙ′) = sup_{ℙ ∈ 𝒫} {c(x, ℙ) : I(ℙ′, ℙ) ≤ r}
(Definition 6, (10), p. 14). -/
noncomputable def drPredictor {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (γ : ↥X → Fin d → ℝ) (r : ℝ) (x : ↥X) (ℙ' : Δ d) : ℝ :=
  sSup ((fun ℙ => cost γ x ℙ) '' {ℙ : Δ d | relEntropy ℙ' ℙ ≤ (r : EReal)})

end DROOptimal.Predictor


