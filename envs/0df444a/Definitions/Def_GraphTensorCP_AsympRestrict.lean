-- Prove2me | Definitions.Def_GraphTensorCP_AsympRestrict
-- name    : GraphTensorCP_AsympRestrict
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:15.706147+00:00
-- url     : https://prove2.me/theorems/efccddd8-e6c7-40cb-8741-da3b67403ecc
-- title:
--   Asymptotic restriction $S\lesssim T$
-- statement:
--   Let $S,T$ be tensors of a fixed order $k\ge2$ over $\mathbb F$. Then $S\lesssim T$ (**asymptotic restriction**) if there are positive integers $h_N$, indexed by $N$, with $\log h_N=o(N)$, such that
--
--   $$S^{\otimes_K N}\preceq T^{\otimes_K N}\otimes_K I_k(h_N)$$
--
--   for every sufficiently large $N$.
--
--   Strassen's duality characterizes this preorder by the asymptotic spectrum: $S\lesssim T$ iff $\phi(S)\le\phi(T)$ for every spectral point $\phi$.
--
--   **Formalization Note** $h:\mathbb N\to\mathbb N$ with $h(N)\ge1$ for all $N$, and $\log h_N=o(N)$ is `Real.log (h N) =o[atTop] N` (the base of the logarithm does not affect $o(N)$). Kronecker powers, products, restriction and $I_k(h)$ are the published MME operations.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.14, p.19

import Mathlib
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank

universe u

namespace GraphTensorCP

open Filter Asymptotics

/-- **Asymptotic restriction** `S ≲ T` (Zhou, *Asymptotic Rank of Weighted Graph Tensors via
Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), Definition 2.14, p.19):
"For tensors S, T of a fixed order k ≥ 2 over F, write S ≲ T if there are positive integers
h_N, indexed by positive integers N, with log h_N = o(N) such that
S^{⊗_K N} ⪯ T^{⊗_K N} ⊗_K I_k(h_N) for every sufficiently large N."

**Formalization Note.** `h : ℕ → ℕ` with `h N ≥ 1` for all `N` (its value at `N = 0` plays no
role); `log h_N = o(N)` is `Real.log (h N) =o[atTop] N` (the base of the logarithm does not
matter for `o(N)`). Kronecker powers are `MME.TensorObj.kronPow`, `I_k(h)` is
`MME.TensorObj.diagObj K k h`, and `⪯` is `MME.TensorObj.Restrict`. -/
def AsympRestrict {K : Type u} [Field K] {k : ℕ} (S T : MME.TensorObj K k) : Prop :=
  ∃ h : ℕ → ℕ, (∀ N, 0 < h N) ∧
    (fun N : ℕ => Real.log (h N)) =o[atTop] (fun N : ℕ => (N : ℝ)) ∧
    ∀ᶠ N in atTop, MME.TensorObj.Restrict (MME.TensorObj.kronPow S N)
      (MME.TensorObj.kron (MME.TensorObj.kronPow T N) (MME.TensorObj.diagObj K k (h N)))

end GraphTensorCP


