-- Prove2me | Definitions.Def_RobustCtxPricing_Evidence
-- name    : RobustCtxPricing_Evidence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:29.976379+00:00
-- url     : https://prove2.me/theorems/b0134129-9d47-4747-909b-224da61c508e
-- title:
--   Evidence sets — the prediction test (1), the interval (2), the commit price, correct evidence
-- statement:
--   An **evidence set** $\mathcal H_j$ is a finite list of samples $(u_i,p_i)$ (a context and the price posted for it). This module defines the objects of §3.1 built on evidence sets.
--
--   1. **Prediction test (1).** $\mathcal H_j=\{(u_1,p_1),\dots,(u_k,p_k)\}$ *predicts* a context $u$ if
--   $$
--   \min_{\lambda\in\mathbb R^k}\Big\{\epsilon\|\lambda\|_1+\Big\|u-\sum_{i=1}^k\lambda_iu_i\Big\|_2\Big\}\le\frac1{8T}.
--   $$
--   2. **Estimate and interval (2).** For coefficients $\lambda$ the estimate is $\hat v_j(u)=\sum_i\lambda_ip_i$ and the confidence interval is $I_j(u)=\big[\hat v_j(u)-\frac1{8T},\ \hat v_j(u)+\frac1{8T}\big]$.
--   3. **Commit price (Algorithm 2).** Given $2\bar C+1$ evidence sets with coefficients $\lambda^j$, the commit price $\underline v_t$ is the $(\bar C+1)$-st largest of the lower endpoints $\hat v_j(u)-\frac1{8T}$.
--   4. **Correct evidence (Definition 3.1).** A sample $(u_i,p_i)$ is correct if $|\langle\theta^\star,u_i\rangle-p_i|\le\epsilon$; an evidence set is correct if all its samples are.
--
--   The prediction test decides when the algorithm may commit; the order statistic makes the commit price robust to up to $\bar C$ evidence sets that are not correct.
--
--   **Formalization Note** The minimum in (1) is attained (for $\epsilon>0$ the objective is continuous and coercive), so (1) is stated as "some $\lambda$ achieves the bound" (`Predicts`), and `PredictsWith` names the coefficient vector. For the empty evidence set the test reads $\|u\|_2\le\frac1{8T}$. The $(k+1)$-st largest of $n$ reals is the entry with index $k$ of the values sorted non-increasingly (ties kept with multiplicity).
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §3.1, pp.13–14 (Algorithm 2, Definition 3.1, Equation (1), Equation (2))

import Mathlib

namespace RobustCtxPricing

/-- **The prediction test, Equation (1).** Castiglioni–Stradi, *Decoupling Corruption and Horizon in
Robust Contextual Pricing*, arXiv:2607.11210, §3.1, p.13: "given an evidence set `𝓗_j` of size `k`,
we say that `𝓗_j` predicts `u` if
`min_{λ_1,…,λ_k} { ϵ‖λ‖₁ + ‖u − ∑_{(u_i,p_i)∈𝓗_j} λ_i u_i‖₂ } ≤ 1/(8T)`. (1)"

`PredictsWith ϵ T H u lam` says that the coefficient vector `lam` achieves (1): the objective of (1)
at `lam` is at most `1/(8T)`.

**Formalization Note.** An evidence set is a `List` of samples `(u_i, p_i)` (context, price), in
insertion order; `lam` is indexed by the positions of the list. -/
def PredictsWith {d : ℕ} (ϵ : ℝ) (T : ℕ) (H : List (EuclideanSpace ℝ (Fin d) × ℝ))
    (u : EuclideanSpace ℝ (Fin d)) (lam : Fin H.length → ℝ) : Prop :=
  ϵ * ∑ i, |lam i| + ‖u - ∑ i, lam i • (H.get i).1‖ ≤ 1 / (8 * (T : ℝ))

/-- **`𝓗_j` predicts `u` (Equation (1)).** Castiglioni–Stradi, arXiv:2607.11210, §3.1, p.13.

**Formalization Note.** The paper writes "`min_λ {…} ≤ 1/(8T)`". The minimum is attained (for
`ϵ > 0` the objective is continuous and coercive in `λ`), so the test is the same as "some `λ`
achieves the bound", which is how it is stated here. For the empty evidence set (`k = 0`) the test
reads `‖u‖₂ ≤ 1/(8T)`. -/
def Predicts {d : ℕ} (ϵ : ℝ) (T : ℕ) (H : List (EuclideanSpace ℝ (Fin d) × ℝ))
    (u : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ lam : Fin H.length → ℝ, PredictsWith ϵ T H u lam

/-- **The estimate `v̂_j(u)`.** Castiglioni–Stradi, arXiv:2607.11210, §3.1, p.14: "This procedure
uses the solution to the inequality to estimate `v̂_j(u) = ∑_{(u_i,p_i)∈𝓗_j} λ_i p_i`." -/
def estimate {d : ℕ} (H : List (EuclideanSpace ℝ (Fin d) × ℝ)) (lam : Fin H.length → ℝ) : ℝ :=
  ∑ i, lam i * (H.get i).2

/-- **The `(k+1)`-st largest of finitely many reals.** `kthLargest f k` is the entry with index `k`
(counting from `0`) of the list of values `f 0, …, f (n−1)` sorted in non-increasing order; for
`k = C̄` it is the "`(C̄ + 1)`-st largest" of Algorithm 2, Line 2 (arXiv:2607.11210, p.13).

**Formalization Note.** Ties are kept with multiplicity (the sorted list is a permutation of the
values). For `k ≥ n` the value is the default `0`; Algorithm 4 only uses `k = C̄ < 2C̄ + 1 = n`. -/
noncomputable def kthLargest {n : ℕ} (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ((List.ofFn f).mergeSort (fun a b => decide (b ≤ a))).getD k 0

/-- **The commit price `v̲_t` (Algorithm 2, Equation (2)).** Castiglioni–Stradi, arXiv:2607.11210,
§3.1, pp.13–14. Each evidence set `𝓗_j` with coefficients `λ^j` gives the confidence interval
`I_j(u) = [v̂_j(u) − 1/(8T), v̂_j(u) + 1/(8T)]` (2); "the algorithm discards some of them by taking
the `(C̄ + 1)`-st largest between all the lower endpoints of the `I_j(u)` intervals, which we denote
by `v̲_t` (Line 2)".

`commitPrice T Cb H lam` is the `(Cb + 1)`-st largest of the lower endpoints
`v̂_j(u) − 1/(8T)`, `j < n`, where `v̂_j` is computed with the coefficients `lam j`. -/
noncomputable def commitPrice {d n : ℕ} (T Cb : ℕ)
    (H : Fin n → List (EuclideanSpace ℝ (Fin d) × ℝ)) (lam : ∀ j, Fin (H j).length → ℝ) : ℝ :=
  kthLargest (fun j => estimate (H j) (lam j) - 1 / (8 * (T : ℝ))) Cb

/-- **Correct evidence sample (Definition 3.1).** Castiglioni–Stradi, arXiv:2607.11210, p.13: "An
evidence sample `(u_i, p_i)` is correct if `|⟨θ⋆, u_i⟩ − p_i| ≤ ϵ`." -/
def SampleCorrect {d : ℕ} (ϵ : ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (s : EuclideanSpace ℝ (Fin d) × ℝ) : Prop :=
  |inner ℝ θ s.1 - s.2| ≤ ϵ

/-- **Correct evidence set (Definition 3.1).** Castiglioni–Stradi, arXiv:2607.11210, p.13: "An
evidence set `𝓗_j` is correct if all the samples `(u_i, p_i) ∈ 𝓗_j` are correct." -/
def SetCorrect {d : ℕ} (ϵ : ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (H : List (EuclideanSpace ℝ (Fin d) × ℝ)) : Prop :=
  ∀ s ∈ H, SampleCorrect ϵ θ s

end RobustCtxPricing


