-- Prove2me | Definitions.Def_SubmodSparsify_bernProb
-- name    : SubmodSparsify_bernProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:40.699645+00:00
-- url     : https://prove2.me/theorems/6465af01-e3eb-41f5-9983-4bf0f5a0df63
-- title:
--   Independent $\mathrm{Bernoulli}(\min\{1,\Lambda p_i\})$ sampling, weights $w_i$ and $|\mathrm{supp}(w)|$
-- statement:
--   Components $1, \dots, m$ are sampled independently: component $i$ is sampled with probability $q_i$. A sample is a vector $\xi \in \{0,1\}^m$, and the probability of an event $\mathcal E \subseteq \{0,1\}^m$ is
--
--   $$\Pr[\mathcal E] = \sum_{\xi \in \mathcal E} \prod_{i=1}^m q_i^{\xi_i}(1 - q_i)^{1 - \xi_i}.$$
--
--   With weights $p_i \ge 0$ and a scale $\Lambda > 0$ the sampling probabilities are $q_i = \min\{1, \Lambda p_i\}$ and the reweighting is
--
--   $$w_i := \begin{cases} 1/\min\{1, \Lambda p_i\}, & \xi_i = 1,\\ 0, & \xi_i = 0.\end{cases}$$
--
--   The **support size** $|\mathrm{supp}(w)|$ is the number of nonzero $w_i$. This is the sampling of Lemma 3.1 and of Algorithm 1, lines 9–11.
--
--   **Formalization Note** The law is a probability law whenever every $q_i \in [0,1]$, as for $q_i = \min\{1, \Lambda p_i\}$ with $\Lambda, p_i \ge 0$. When $\Lambda p_i = 0$, Lean's $1/0 = 0$ gives $w_i = 0$, and component $i$ is sampled with probability $0$.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6…), Lemma 3.1, p.16 (PDF p.18); Algorithm 1, lines 9–11, p.18 (PDF p.20)

import Mathlib

namespace SubmodSparsify

/-!
# Independent Bernoulli sampling of the components (Lemma 3.1, p.16; Algorithm 1, lines 9–11)

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Lemma 3.1, p.16; Algorithm 1,
lines 9–11, p.18.

"Suppose each fi is sampled independently with probability min{1, piΛ}. Define the random
weight Wi := 1/min{1, piΛ} if fi is sampled, 0 otherwise." (p.16) "Independently draw
ξi ∼ Bernoulli(min{1, Λpi}); wi ← 1/ min{1, Λpi} if ξi = 1, and 0 otherwise" (p.18).

**Formalization Note.**
* The sample is `ξ : Fin m → Bool` (`ξ i = true` iff component `i` is sampled). Its law is the
  finite product of Bernoulli laws with success probabilities `q i`: `bernProb q E` is the
  probability of the event `E`. It is a probability law when every `q i ∈ [0, 1]`, which holds
  for `q i = min 1 (Λ * p i)` with `Λ, p i ≥ 0`.
* `1 / min 1 (Λ * p i)` is Lean's `1 / 0 = 0` when `Λ p i = 0`; then component `i` is sampled
  with probability `0`.
* `|supp(w)|` is the number of nonzero coordinates of the weight vector.
-/

variable {m : ℕ}

/-- The probability of the event `E` under independent `Bernoulli(q i)` coordinates. -/
noncomputable def bernProb (q : Fin m → ℝ) (E : (Fin m → Bool) → Prop) : ℝ := by
  classical exact ∑ ξ ∈ Finset.univ.filter E, ∏ i, if ξ i then q i else 1 - q i

/-- The sampling probability `min{1, Λ pᵢ}`. -/
noncomputable def sampleProb (p : Fin m → ℝ) (Λ : ℝ) (i : Fin m) : ℝ :=
  min 1 (Λ * p i)

/-- The reweighting `wᵢ = 1/min{1, Λpᵢ}` if `ξᵢ = 1`, and `0` otherwise. -/
noncomputable def sampledWeight (p : Fin m → ℝ) (Λ : ℝ) (ξ : Fin m → Bool) (i : Fin m) : ℝ :=
  if ξ i then 1 / min 1 (Λ * p i) else 0

/-- `|supp(w)|`: the number of nonzero coordinates of `w`. -/
noncomputable def supportCard (w : Fin m → ℝ) : ℕ := by
  classical exact (Finset.univ.filter (fun i => w i ≠ 0)).card

end SubmodSparsify


