-- Prove2me | Definitions.Def_RankAssort_SimpleLearn_Algorithm
-- name    : RankAssort_SimpleLearn_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:43.918316+00:00
-- url     : https://prove2.me/theorems/87d6ceea-3de4-45b5-88d9-dddb2d216e59
-- title:
--   Definition 1, p. 21; Algorithm 2, p. 23; (23), p. 58 — approximately best unranked product and a run of the Simple Learning Algorithm with an (ϵ′, δ′)-PAC black box
-- statement:
--   **Approximately best product.** Given a prefix $\sigma$ of a ranking (the products already placed), product $i$ is *tol-approximately best* if $i \notin \sigma$ and
--
--   $$
--   \Delta(\sigma, j) - \mathrm{tol} \le \Delta(\sigma, i) \quad \text{for every product } j \notin \sigma,
--   $$
--
--   where $\Delta(\sigma,i) = \mathbb E[H(\sigma\cup i)] - \mathbb E[H(\sigma)]$ is the marginal benefit. This is inequality (23), p. 58, with the maximum taken over the unranked products $U$ on which Algorithm 2 runs its black box.
--
--   **A run of the Simple Learning Algorithm** (Algorithm 2, p. 23). The algorithm fills ranks $1,\dots,n$ in order; at rank $r$ it runs an $(\epsilon',\delta')$-PAC algorithm (Definition 1, p. 21: with probability at least $1-\delta'$ it outputs an arm whose mean reward is within $\epsilon'$ of the best) on the unranked products, with reward $\nu_i = H(\tilde\pi \cup i) - H(\tilde\pi)$, and places the returned product. A run is modelled by a probability space $(\Omega, P)$ of learning randomness and the returned ranking $\tilde\pi(\omega)$, which is a permutation of $[n]$ for every $\omega$, with measurable level sets. The black box's guarantee is imposed at every rank $r$ and **conditionally on every prefix** $\sigma$ already fixed (p. 58: "(23) holds for any particular instantiation of $[\tilde\pi]_{r-1}$ with probability $1-\delta/n$"):
--
--   $$
--   P\bigl(\,[\tilde\pi]_{r-1} = \sigma \ \text{and}\ \tilde\pi^{-1}(r) \text{ is not } \epsilon'\text{-approximately best after } \sigma\,\bigr) \le \delta' \, P\bigl([\tilde\pi]_{r-1} = \sigma\bigr).
--   $$
--
--   Every theorem about Algorithm 2's output quantifies over such runs: this is the paper's "given any $(\epsilon',\delta')$-PAC algorithm as a black box".
--
--   **Formalization Note** Ranks are 0-based in Lean: the paper's rank $r$ is index $r-1$, a ranking is a duplicate-free list of the $n$ products (`Fin n`), and $\pi^{-1}(j)$ is the list entry at index $j-1$. `IsApproxBest D τ σ i tol` is the predicate above; `SimpleLearningRun D τ epsP deltaP P` bundles the output map `out : Ω → List (Fin n)`, measurability of its level sets, the permutation property, and the field `pac`, the per-rank prefix-conditional guarantee. How the black box samples customers (the sample complexity $\tilde T$ of Definition 1) is not modelled: it enters only the learning-phase length (Corollaries 1–2), not the approximation guarantee.
-- source:
--   Ferreira, Parthasarathy, Sekar, Learning to Rank an Assortment of Products, SSRN 3395992 author manuscript, p. 21, Definition 1; p. 23, Algorithm 2; p. 58, (23) and the sentence after it

import Mathlib
import Definitions.Def_RankAssort_SimpleLearn_Model

namespace RankAssort.SimpleLearn
open MeasureTheory

variable {n : ℕ}

/-- Product `i` is unranked after the prefix `σ` and its marginal benefit is within `tol` of the
best unranked product's (the inequality (23), p. 58, with the maximum over the unranked products). -/
def IsApproxBest {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ) (τ : Θ → CustomerType n)
    (σ : List (Fin n)) (i : Fin n) (tol : ℝ) : Prop :=
  i ∉ σ ∧ ∀ j, j ∉ σ → margBenefit D τ σ j - tol ≤ margBenefit D τ σ i

/-- A run of the Simple Learning Algorithm (Algorithm 2, p. 23) driven by an
`(epsP, deltaP)`-PAC black box (Definition 1, p. 21). `out ω` is the returned ranking `π̃` on the
learning randomness `ω ∼ P`. The black box's guarantee is imposed at every rank `r` (0-based),
conditionally on every prefix `σ` already fixed (p. 58): the probability that the prefix is `σ`
and the product placed at rank `r` is not `epsP`-best among the unranked products is at most
`deltaP` times the probability that the prefix is `σ`. -/
structure SimpleLearningRun {Θ : Type*} [MeasurableSpace Θ] (D : Measure Θ)
    (τ : Θ → CustomerType n) (epsP deltaP : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) where
  out : Ω → List (Fin n)
  out_meas : ∀ l, MeasurableSet (out ⁻¹' {l})
  out_perm : ∀ ω, (out ω).Nodup ∧ (out ω).length = n
  pac : ∀ r < n, ∀ σ : List (Fin n),
    P ({ω | (out ω).take r = σ} ∩
        {ω | ∃ i, (out ω)[r]? = some i ∧ ¬ IsApproxBest D τ σ i epsP}) ≤
      ENNReal.ofReal deltaP * P {ω | (out ω).take r = σ}

end RankAssort.SimpleLearn


