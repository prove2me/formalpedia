-- Prove2me | Definitions.Def_BartlettNN_Sigmoid_Networks
-- name    : BartlettNN_Sigmoid_Networks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:51:54.109742+00:00
-- url     : https://prove2.me/theorems/9298f28c-1f93-4458-b69d-427d93332166
-- title:
--   The first-layer class {x ↦ σ(w·x + w₀)} of Corollary 24 and Theorem 28(1)
-- statement:
--   For an activation $\sigma:\mathbb R\to\mathbb R$ and an input dimension $n$, the class of single sigmoid units on $\mathbb R^n$ (Corollary 24, p. 533; Theorem 28(1), p. 534) is
--
--   $$F=\{x\mapsto\sigma(w\cdot x+w_0):w\in\mathbb R^n,\ w_0\in\mathbb R\},\qquad w\cdot x=\sum_{i=1}^n w_ix_i.$$
--
--   Its $\ell_1$-bounded combinations $\{\sum_{i=1}^N\alpha_if_i:N\in\mathbb N,\ f_i\in F,\ \sum_i|\alpha_i|\le A\}$ (the shared `combos`) are the two-layer networks of Corollary 24 and Theorem 28(1).
--
--   **Formalization Note.** $\mathbb R^n$ is `Fin n → ℝ` with the finite-sum dot product; the bias $w_0$ is unrestricted. The hypotheses on $\sigma$ (nondecreasing, bounded range) are carried by the theorems, not by this definition.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), pp. 532–534, Theorem 17, Corollary 24, Theorem 28(1); https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_FatNet_combos

namespace BartlettNN.Sigmoid

/-- All affine-input units with a fixed activation `σ`, including a free bias. -/
def sigmoidUnits (σ : ℝ → ℝ) (n : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  {f | ∃ (w : Fin n → ℝ) (w₀ : ℝ),
    f = (fun x => σ (∑ i, w i * x i + w₀))}

end BartlettNN.Sigmoid


