-- Prove2me | Definitions.Def_SparseBatchBandit_greedyArm
-- name    : SparseBatchBandit_greedyArm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:02.205231+00:00
-- url     : https://prove2.me/theorems/8b4f5836-5ccf-421a-a07e-f3b3891182a5
-- title:
--   Greedy action with lowest-index tie-break
-- statement:
--   Given contexts $(c_a)_{a\in[K]}$ and $\theta\in\mathbb R^d$, the **greedy action** is
--
--   $$
--   \operatorname*{argmax}_{a\in[K]}\ c_a^\top\theta,
--   $$
--
--   with ties broken by the lower action index, as Algorithm 1 prescribes. At $\theta=0$ every arm ties, so the rule returns the first arm.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
open Matrix

namespace SparseBatchBandit

/-- The greedy action `argmax_{a ∈ [K]} x_a⊤θ`, ties broken by the lower action index, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4,
Algorithm 1, p.16 (PDF 16). -/
noncomputable def greedyArm {K d : ℕ} [NeZero K] (c : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) : Fin K :=
  (Finset.univ.filter (fun a => ∀ b, c b ⬝ᵥ θ ≤ c a ⬝ᵥ θ)).min'
    (by
      obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun a => c a ⬝ᵥ θ)
        Finset.univ_nonempty
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun b => ha b (Finset.mem_univ b)⟩⟩)

end SparseBatchBandit


