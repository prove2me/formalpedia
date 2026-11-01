-- Prove2me | Definitions.Def_DecQueueLearning_CompSlack
-- name    : DecQueueLearning_CompSlack
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:18.831328+00:00
-- url     : https://prove2.me/theorems/8874a20c-a334-4308-9c46-078719a97bf0
-- title:
--   Matchings, the max-weight value of (Primal), and $\alpha$-complementary slackness (Definition 2)
-- statement:
--   A **matching** is a map $\sigma:\mathcal N\to\mathcal K\cup\{\bot\}$ such that for $i\ne i'$, either $\sigma(i)=\bot$ or $\sigma(i)\ne\sigma(i')$. For weights $w\in\mathbb R^{N\times K}$ write $w_{i,\bot}=0$, and let
--   $$
--   \max_{\phi\in\Phi}\sum_{i=1}^N\sum_{j=1}^K w_{i,j}\phi_{i,j}
--   $$
--   be the value of the linear program (Primal).
--
--   (**Definition 2**) A tuple $(\sigma,\hat p,\hat\pi)$ with $\hat p\in\mathbb R^K$, $\hat\pi\in\mathbb R^N$ satisfies **$\alpha$-complementary slackness** if
--   1. $\hat p_j=0$ for every unmatched server $j$ and $\hat p_j\ge0$ for every matched server $j$;
--   2. $\hat\pi_i=\max(\max_{j}w_{i,j}-\hat p_j,\,0)$ for every queue $i$;
--   3. $\hat\pi_i=0$ if $i$ is unmatched; otherwise $w_{i,\sigma(i)}>0$ and $\hat\pi_i+\hat p_{\sigma(i)}\le(1+\alpha)w_{i,\sigma(i)}$.
--
--   **Formalization Note** The maximum is written as the supremum of the objective over $\Phi$; $\Phi$ is compact and nonempty, so the supremum is attained.
-- source:
--   Freund, Lykouris, Weng, Efficient decentralized multi-agent learning in asymmetric bipartite queueing systems, arXiv:2206.03324v3, (Primal) p. 10; Definition 2 p. 14

import Mathlib
import Definitions.Def_DecQueueLearning_System

open Finset

namespace DecQueueLearning

/-- A (partial) **matching** of queues to servers, arXiv:2206.03324v3, p. 13: for `i ≠ i′`, either
`σ(i) = ⊥` or `σ(i) ≠ σ(i′)` (`none` is `⊥`). -/
def IsMatching {N K : ℕ} (σ : Fin N → Option (Fin K)) : Prop :=
  ∀ i i', i ≠ i' → σ i = none ∨ σ i ≠ σ i'

/-- The weight `w_{i,σ(i)}` of queue `i` under `σ`, with `w_{i,⊥} = 0`. -/
def selWeight {N K : ℕ} (w : Fin N → Fin K → ℝ) (σ : Fin N → Option (Fin K)) (i : Fin N) : ℝ :=
  match σ i with
  | none => 0
  | some j => w i j

/-- The optimal value `max_{ϕ ∈ Φ} Σᵢ Σⱼ wᵢⱼ ϕᵢⱼ` of the linear program (Primal),
arXiv:2206.03324v3, p. 10.

**Formalization Note** Written as `sSup` of the image of `Φ`; the image is nonempty (`ϕ = 0`) and
bounded (`0 ≤ ϕᵢⱼ ≤ 1`), and `Φ` is compact, so the supremum is the maximum. -/
noncomputable def maxWeight {N K : ℕ} (w : Fin N → Fin K → ℝ) : ℝ :=
  sSup ((fun ϕ : Fin N → Fin K → ℝ => ∑ i, ∑ j, w i j * ϕ i j) '' capacityRegion N K)

/-- **Definition 2** (`α`-complementary slackness), arXiv:2206.03324v3, p. 14. The tuple
`(σ, p̂, π̂)` satisfies `α`-complementary slackness if
* `p̂ⱼ = 0` for every unmatched server `j` and `p̂ⱼ ≥ 0` for every matched server `j`;
* `π̂ᵢ = max(maxⱼ (wᵢⱼ − p̂ⱼ), 0)` for every queue `i`;
* `π̂ᵢ = 0` if `i` is unmatched; otherwise `w_{i,σ(i)} > 0` and `π̂ᵢ + p̂_{σ(i)} ≤ (1 + α) w_{i,σ(i)}`.

**Formalization Note** `max(maxⱼ (wᵢⱼ − p̂ⱼ), 0)` is the greatest element of
`{0} ∪ {wᵢⱼ − p̂ⱼ : j}`. -/
def IsCompSlack {N K : ℕ} (α : ℝ) (w : Fin N → Fin K → ℝ) (σ : Fin N → Option (Fin K))
    (p : Fin K → ℝ) (π : Fin N → ℝ) : Prop :=
  (∀ j, (¬ ∃ i, σ i = some j) → p j = 0) ∧
  (∀ j, (∃ i, σ i = some j) → 0 ≤ p j) ∧
  (∀ i, IsGreatest (insert 0 (Set.range fun j => w i j - p j)) (π i)) ∧
  (∀ i, σ i = none → π i = 0) ∧
  (∀ i j, σ i = some j → 0 < w i j ∧ π i + p j ≤ (1 + α) * w i j)

end DecQueueLearning


