-- Prove2me | Definitions.Def_GraphTensorCP_profile
-- name    : GraphTensorCP_profile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:48.752919+00:00
-- url     : https://prove2.me/theorems/46597168-4e98-4d1f-9c94-f1bc0883f247
-- title:
--   Symmetric spectral profile $P_\phi(a_1,\dots,a_{n-1})$ and average edge weight $t_\phi$
-- statement:
--   Let $n\ge3$, let $\phi\in\Phi_{n,\mathbb F}$ and let $P^{(\phi)}$ be its spectral edge weights. Their **average** is
--
--   $$t_\phi=\frac1m\sum_{1\le i<j\le n}P^{(\phi)}_{i,j},\qquad m=\binom n2 .$$
--
--   For a permutation $\pi\in S_n$ put $\phi_\pi(T)=\phi(\pi T)$, where $\pi T$ moves old leg $d$ to new leg $\pi(d)$. For positive integers $a_1,\dots,a_{n-1}$ the **symmetric spectral profile** is
--
--   $$P_\phi(a_1,\dots,a_{n-1})=\Big(\prod_{\pi\in S_n}\phi_\pi\big(\mathcal C_n(a_1,\dots,a_{n-1})\big)\Big)^{1/(n!\,t_\phi)}.$$
--
--   The profile symmetrizes the spectral value of polynomial multiplication over all leg permutations; its growth along the diagonal bounds $t_\phi$ and hence the complete-graph exponent.
--
--   **Formalization Note** $\pi T$ is the published `MME.TensorObj.permObj π T` (new leg $\pi(d)$ = old leg $d$, Definition 2.11). The power is a real power with exponent $1/(n!\,t_\phi)$; positivity of $t_\phi$ is a consequence of Lemma 2.25, not an assumption.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 4.1, p.35; Definition 2.11, p.18 (leg permutations)

import Mathlib
import Definitions.Def_mme_permutation
import Definitions.Def_GraphTensorCP_specWeight
import Definitions.Def_GraphTensorCP_polyMulTensor

universe u

namespace GraphTensorCP

/-- The **average spectral edge weight** `t_ϕ = (1/m) Σ_{1≤i<j≤n} P^{(ϕ)}_{i,j}`, `m = (n choose 2)`
(Zhou, arXiv:2610.34273 (version of 2026-11-03), Definition 4.1, p.35). -/
noncomputable def tPhi {K : Type u} [Field K] {n : ℕ} {hn : 1 < n} (φ : Spec K n hn) : ℝ :=
  (1 / (n.choose 2 : ℝ)) * ∑ i, ∑ j, if i < j then specWeight φ i j else 0

/-- The **symmetric spectral profile** `P_ϕ` (Zhou, *Asymptotic Rank of Weighted Graph Tensors via
Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), Definition 4.1, p.35):
"For every permutation π ∈ S_n, put ϕ_π(T) = ϕ(πT) … define the symmetric spectral profile
P_ϕ(a₁, . . . , a_{n−1}) = ( ∏_{π∈S_n} ϕ_π(C_n(a₁, . . . , a_{n−1})) )^{1/(n! t_ϕ)}."

**Formalization Note.** `πT` is the published leg permutation `MME.TensorObj.permObj π T`, whose
new leg `π(d)` is the old leg `d`, as in Definition 2.11 (p.18). The power is `Real.rpow` with
exponent `1 / (n! · t_ϕ)`; the paper (and this mission's milestones) use it for `n ≥ 3`, where
`t_ϕ > 0` follows from Lemma 2.25 — it is not assumed. Input lengths are a vector
`a : Fin (n−1) → ℕ`; the paper takes them positive. -/
noncomputable def profile {K : Type u} [Field K] {n : ℕ} {hn : 1 < n} (φ : Spec K n hn)
    (a : Fin (n - 1) → ℕ) : ℝ :=
  (∏ π : Equiv.Perm (Fin n),
      φ (MME.TensorQ.toQ (MME.TensorObj.permObj π (polyMulTensor K n a)))) ^
    (1 / ((n.factorial : ℝ) * tPhi φ))

end GraphTensorCP


