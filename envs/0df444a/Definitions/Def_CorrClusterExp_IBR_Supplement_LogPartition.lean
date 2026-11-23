-- Prove2me | Definitions.Def_CorrClusterExp_IBR_Supplement_LogPartition
-- name    : CorrClusterExp_IBR_Supplement_LogPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:26:21.070446+00:00
-- url     : https://prove2.me/theorems/efbbdc85-eea9-45ff-9cd1-c20bfbc90627
-- title:
--   §4.2.2, p. 26 and App. B.10, p. 50 — the logarithmic partition and the perturbed instance of Lemma B.5
-- statement:
--   Let $w_1\ge w_2\ge\dots\ge w_n\ge0$ be the sorted cluster sizes and let $\delta_1,\delta_2>0$. The **logarithmic partition** of §4.2.2 groups the sorted clusters into consecutive blocks as follows. Put
--   $$
--   \bar w=\sqrt{\frac{\sum_{i=1}^n w_i^2}{n^{1+\delta_1}}},\qquad \alpha=1+n^{-\delta_2}.
--   $$
--   1. **Block zero** consists of all clusters with $w_i\le\bar w$ (for sorted sizes, a final run of the list, possibly empty).
--   2. Among the remaining clusters (those with $w_i>\bar w$), repeatedly take the largest cluster $s$ not yet assigned and form one block of all unassigned clusters $i$ with $w_i>\bar w$ and $w_i\ge w_s/\alpha$. Because the sizes are sorted, each such block is a run of consecutive clusters. These blocks are labelled $1,\dots,K$ in decreasing order of their largest cluster.
--
--   The partition lists blocks $1,\dots,K$ followed by block zero (omitted when empty).
--
--   The file also defines the **perturbed instance** used in the proof of Theorem 4.10 (App. B.10, p. 50): drop block zero, and in every block $k\in[K]$ lower all cluster sizes to the smallest size $\underline w_k=\min_{i\in S_k}w_i$ of the block. Its clusters are the $n-n_0$ clusters outside block zero, partitioned into the blocks $1,\dots,K$.
--
--   These objects are the input of Lemma B.5 and Theorem 4.10; the IBR experiment of a partition, $V^{\mathrm{LB}}$ and $V^{\mathrm{OPT}}$ come from the published definitions of the mission.
--
--   **Formalization Note** Clusters are 0-based (`Fin n`). `numLarge w δ₁` counts the clusters with $w_i>\bar w$; for sorted sizes these are the indices $0,\dots,$`numLarge`$-1$. `nextStart` performs one greedy step: from the start $s$ of a block it returns the first index $e>s$ that is in block zero or has $w_e<w_s/\alpha$, so the block is $\{s,\dots,e-1\}$. The boundaries $0$, `numLarge`, $n$ and the iterates `nextStart^[t] 0` define the partition through Mathlib's `CompositionAsSet`. `greedyBlocks` is the partition of the first `numLarge` clusters into blocks $1,\dots,K$, and `perturbedSizes` gives each of them the minimum size of its block (a minimum over a nonempty finite block). The construction is meant for sorted sizes; every theorem using it assumes `Antitone w`. Powers $n^{1+\delta_1}$ and $n^{-\delta_2}$ are real powers. The definitions are total for every real parameter and for $n=0$; on the source domain $n>0$, $\delta_1,\delta_2\in(0,1)$ they give exactly the printed construction. The empty instance has the empty composition.
-- source:
--   Candogan, Chen, Niazadeh, Correlated Cluster-Based Randomized Experiments: Robust Variance Minimization, SSRN 3852100 (version of March 22, 2023), p. 26, §4.2.2 (logarithmic partition); p. 50, App. B.10 (perturbed instance)

import Mathlib

namespace CorrClusterExp.IBR.Supplement

open Finset

/-- The threshold `w̄ = √(Σᵢ wᵢ² / n^{1+δ₁})` of block zero of the logarithmic partition
(§4.2.2, p. 26). -/
noncomputable def wbar {n : ℕ} (w : Fin n → ℝ) (δ₁ : ℝ) : ℝ :=
  Real.sqrt ((∑ i, w i ^ 2) / (n : ℝ) ^ (1 + δ₁))

/-- The ratio parameter `α = 1 + n^{−δ₂}` of the logarithmic partition (§4.2.2, p. 26). -/
noncomputable def alpha (n : ℕ) (δ₂ : ℝ) : ℝ :=
  1 + (n : ℝ) ^ (-δ₂)

/-- The sizes `w`, extended by `0` beyond the last cluster, so that they can be read at a
natural-number index. -/
noncomputable def wext {n : ℕ} (w : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then w ⟨i, h⟩ else 0

/-- `n − n₀`, the number of clusters outside block zero: the clusters with `wᵢ > w̄`. For sorted
sizes they are the first `numLarge` clusters (0-based indices `0, …, numLarge − 1`). -/
noncomputable def numLarge {n : ℕ} (w : Fin n → ℝ) (δ₁ : ℝ) : ℕ :=
  (univ.filter fun i => wbar w δ₁ < w i).card

lemma numLarge_le {n : ℕ} (w : Fin n → ℝ) (δ₁ : ℝ) : numLarge w δ₁ ≤ n := by
  unfold numLarge
  exact (card_filter_le _ _).trans (by simp)

/-- One greedy step of the logarithmic partition (§4.2.2, p. 26). If the largest unassigned
cluster (outside block zero) is `s`, its block consists of the unassigned clusters `i < numLarge`
with `wᵢ ≥ w_s / α`; for sorted sizes these are the indices `s, s + 1, …, e − 1`, where `e` is
the first index after `s` that is in block zero or has `w_e < w_s / α`. The value is `e`, the
start of the next block (or `numLarge` when the greedy blocks are exhausted). Once `s` has reached
block zero the step is the identity. -/
noncomputable def nextStart {n : ℕ} (w : Fin n → ℝ) (δ₁ δ₂ : ℝ) (s : ℕ) : ℕ := by
  classical
  exact if h : s < numLarge w δ₁ then
    Nat.find (⟨numLarge w δ₁, h, Or.inl le_rfl⟩ :
      ∃ e, s < e ∧ (numLarge w δ₁ ≤ e ∨ wext w e < wext w s / alpha n δ₂))
  else s

/-- The block boundaries of the greedy blocks `1, …, K` of the logarithmic partition, as a
subset of `{0, …, numLarge}`: `0`, `numLarge`, and every start `nextStart^[t] 0` of a greedy
block. -/
noncomputable def greedyBoundaries {n : ℕ} (w : Fin n → ℝ) (δ₁ δ₂ : ℝ) :
    CompositionAsSet (numLarge w δ₁) := by
  classical
  exact
  { boundaries := univ.filter fun j : Fin (numLarge w δ₁).succ =>
      (j : ℕ) = 0 ∨ (j : ℕ) = numLarge w δ₁ ∨ ∃ t : ℕ, (nextStart w δ₁ δ₂)^[t] 0 = j
    zero_mem := by simp
    getLast_mem := by simp }

/-- The greedy blocks `1, …, K` of the logarithmic partition (§4.2.2, p. 26), as consecutive
blocks of the first `numLarge` sorted clusters, in order: block `k` is `greedyBlocks.embedding`
of index `k − 1`. This is the block structure of the perturbed instance of Lemma B.5 (block zero
dropped). -/
noncomputable def greedyBlocks {n : ℕ} (w : Fin n → ℝ) (δ₁ δ₂ : ℝ) :
    Composition (numLarge w δ₁) :=
  (greedyBoundaries w δ₁ δ₂).toComposition

/-- The logarithmic partition of the sorted clusters `0, …, n − 1` with parameters `δ₁, δ₂`
(§4.2.2, p. 26), as consecutive blocks: the greedy blocks `1, …, K` (boundaries `nextStart^[t] 0`)
followed by block zero `{numLarge, …, n − 1}` (the clusters with `wᵢ ≤ w̄`), which is omitted when
it is empty. -/
noncomputable def logPartition {n : ℕ} (w : Fin n → ℝ) (δ₁ δ₂ : ℝ) : Composition n := by
  classical
  exact
  ({ boundaries := univ.filter fun j : Fin n.succ =>
      (j : ℕ) = 0 ∨ (j : ℕ) = n ∨ (j : ℕ) = numLarge w δ₁ ∨
        ∃ t : ℕ, (nextStart w δ₁ δ₂)^[t] 0 = j
     zero_mem := by simp
     getLast_mem := by simp } : CompositionAsSet n).toComposition

/-- The perturbed sizes of Lemma B.5 (p. 50): block zero is dropped, and every cluster of a greedy
block `k` gets the smallest size `w_k = min_{i ∈ S_k} wᵢ` of its block. Indexed by the
`numLarge` clusters outside block zero. -/
noncomputable def perturbedSizes {n : ℕ} (w : Fin n → ℝ) (δ₁ δ₂ : ℝ) :
    Fin (numLarge w δ₁) → ℝ := fun i =>
  let c := greedyBlocks w δ₁ δ₂
  let k := c.index i
  (univ : Finset (Fin (c.blocksFun k))).inf'
    ⟨⟨0, c.one_le_blocksFun k⟩, mem_univ _⟩
    (fun j => w (Fin.castLE (numLarge_le w δ₁) (c.embedding k j)))

end CorrClusterExp.IBR.Supplement


