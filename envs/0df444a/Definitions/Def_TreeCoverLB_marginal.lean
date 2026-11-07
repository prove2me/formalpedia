-- Prove2me | Definitions.Def_TreeCoverLB_marginal
-- name    : TreeCoverLB_marginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:00.861558+00:00
-- url     : https://prove2.me/theorems/b553f19b-8769-4017-8f26-e00fe2ad457d
-- title:
--   Marginals $\mu_i(a)$ of a point of $|I_{p,k}|$
-- statement:
--   For a weight vector $\mu$ on words $x\in\mathbb Z_p^k$, the $i$-th **marginal** is
--   $$
--   \mu_i(a)=\sum_{x\in\mathbb Z_p^k:\ x_i=a}\mu(x)\qquad(a\in\mathbb Z_p).
--   $$
--   The paper writes $M_i(\mu)=\max_a\mu_i(a)$.
--
--   **Formalization Note** $M_i(\mu)\le c$ is stated in the theorems as $\mu_i(a)\le c$ for every $a$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §5, p.18 (PDF p.20)

import Mathlib

namespace TreeCoverLB

/-- The **`i`-th marginal** of a weight vector `µ` on words `x ∈ ℤ_p^k` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §5, p.18
(PDF p.20)): `µ_i(a) = Σ_{x ∈ ℤ_p^k : x_i = a} µ(x)`.

**Formalization Note** The paper's `M_i(µ) = max_a µ_i(a)` is not defined separately: the theorems
state `M_i(µ) ≤ c` as `∀ a, marginal µ i a ≤ c`. -/
noncomputable def marginal {p k : ℕ} [NeZero p] (μ : (Fin k → ZMod p) → ℝ) (i : Fin k)
    (a : ZMod p) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin k → ZMod p => x i = a), μ x

end TreeCoverLB


