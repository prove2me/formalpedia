-- Prove2me | Definitions.Def_GraphTensorCP_specWeight
-- name    : GraphTensorCP_specWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:54.8432+00:00
-- url     : https://prove2.me/theorems/e53df8e1-375e-49d3-b293-63f5bf1d0172
-- title:
--   Asymptotic spectrum $\Phi_{k,\mathbb F}$, spectral edge weights $P^{(\phi)}$ and the weighted graph exponent $\Gamma_{\mathbb F}(W)$
-- statement:
--   For $k\ge2$, the **asymptotic spectrum** $\Phi_{k,\mathbb F}$ of $k$-th order tensors over $\mathbb F$ is the set of maps $\phi$ from tensors to $\mathbb R_{\ge0}$ with
--
--   1. $\phi(0)=0$ and $\phi(I_k(1))=1$;
--   2. $\phi(A\oplus_K B)=\phi(A)+\phi(B)$;
--   3. $\phi(A\otimes_K B)=\phi(A)\phi(B)$;
--   4. $\phi(A)\le\phi(B)$ whenever $A\preceq B$ (restriction).
--
--   For $n\ge2$ and $\phi\in\Phi_{n,\mathbb F}$, the **spectral edge weights** form the symmetric zero-diagonal matrix
--
--   $$P^{(\phi)}_{i,i}=0,\qquad P^{(\phi)}_{i,j}=P^{(\phi)}_{j,i}=\log_2\phi\big(E^{(2)}_{i,j}\big)\quad(i\ne j).$$
--
--   For a nonnegative weight matrix $W$, the **weighted graph exponent** is
--
--   $$\Gamma_{\mathbb F}(W)=\max_{\phi\in\Phi_{n,\mathbb F}}\ \sum_{1\le i<j\le n}W_{i,j}P^{(\phi)}_{i,j},$$
--
--   and $\Gamma_{\mathbb F}(G)=\Gamma_{\mathbb F}(A_G)$ for a graph $G$.
--
--   By Strassen's duality, $\Gamma_{\mathbb F}$ equals $\log_2$ of the asymptotic rank of $\mathsf{WT}(Q)$ when $W=\log_2Q$; it extends that quantity to real edge weights.
--
--   **Formalization Note** $\Phi_{k,\mathbb F}$ is the published `MME.AsymptoticSpectrumPoint` of the tensor semiring `MME.TensorQ K k` (tensors modulo mutual restriction) under the restriction preorder `MME.TensorQ.tensorStrassen K k hk`: monotone semiring homomorphisms to $\mathbb R$. These are exactly the paper's spectral points. A point is evaluated on a tensor $T$ as $\phi(\mathrm{toQ}\,T)$. $\Gamma_{\mathbb F}$ is a real supremum over the spectrum; it is the paper's maximum because the coefficients lie in $[0,1]$ (Lemma 2.25) and the maximum is attained.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.19, p.21; Definition 2.24, p.24; Definition 2.26, p.25

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_spectrum
import Definitions.Def_GraphTensorCP_wt

universe u

namespace GraphTensorCP

/-- The **asymptotic spectrum** `Φ_{k,F}` of `k`-th order tensors over `F` (Zhou, *Asymptotic Rank
of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of
2026-11-03), Definition 2.19, p.21): maps `ϕ` with `ϕ(0) = 0`, `ϕ(I_k(1)) = 1`,
`ϕ(A ⊕_K B) = ϕ(A) + ϕ(B)`, `ϕ(A ⊗_K B) = ϕ(A)ϕ(B)`, and `A ⪯ B ⇒ ϕ(A) ≤ ϕ(B)`.

**Formalization Note.** `Φ_{k,F}` is the published `MME.AsymptoticSpectrumPoint` of the tensor
semiring `MME.TensorQ K k` (tensors modulo mutual restriction, with `⊕_K` as `+`, `⊗_K` as `*`)
under the restriction preorder `MME.TensorQ.tensorStrassen K k hk`: the monotone semiring
homomorphisms to `ℝ`. A spectral point of the paper is constant on mutual-restriction classes
(monotone both ways), and the paper's four conditions are exactly "monotone semiring
homomorphism", so the two classes coincide. A spectral point is evaluated on a tensor object
`T` as `ϕ (MME.TensorQ.toQ T)`. `hk : 1 < k` is the paper's `k ≥ 2`. -/
abbrev Spec (K : Type u) [Field K] (k : ℕ) (hk : 1 < k) : Type (u + 1) :=
  MME.AsymptoticSpectrumPoint (MME.TensorQ K k) (MME.TensorQ.tensorStrassen K k hk)

/-- **Spectral edge weights** `P^{(ϕ)}` (Zhou, arXiv:2610.34273 (version of 2026-11-03),
Definition 2.24, p.24): "P^{(ϕ)}_{i,i} = 0, P^{(ϕ)}_{i,j} = P^{(ϕ)}_{j,i} = log₂ ϕ(E^{(2)}_{i,j})
(1 ≤ i < j ≤ n)".

**Formalization Note.** `log₂` is `Real.logb 2`. `edgeTensor K i j 2` is symmetric in `i, j`,
so the matrix is symmetric. -/
noncomputable def specWeight {K : Type u} [Field K] {n : ℕ} {hn : 1 < n} (φ : Spec K n hn)
    (i j : Fin n) : ℝ :=
  if i = j then 0 else Real.logb 2 (φ (MME.TensorQ.toQ (edgeTensor K i j 2)))

/-- **Weighted graph exponent** `Γ_F(W)` (Zhou, arXiv:2610.34273 (version of 2026-11-03),
Definition 2.26, p.25): "Γ_F(W) = max_{ϕ∈Φ_{n,F}} ( Σ_{1≤i<j≤n} W_{i,j}P^{(ϕ)}_{i,j} )". For a
graph, `Γ_F(G) = Γ_F(A_G)`, i.e. `gammaF K hn (G.adjMatrix ℝ)`.

**Formalization Note.** A real `⨆` over the spectrum. The spectrum is nonempty, and the
coefficients `P^{(ϕ)}_{i,j}` lie in `[0, 1]` (Lemma 2.25), so the family is bounded and the
supremum is a genuine value; the paper notes it is attained (p.25). The sum is over unordered
pairs `i < j`. -/
noncomputable def gammaF (K : Type u) [Field K] {n : ℕ} (hn : 1 < n)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ φ : Spec K n hn, ∑ i, ∑ j, if i < j then W i j * specWeight φ i j else 0

end GraphTensorCP


