-- Prove2me | Definitions.Def_SetMultCost_IsTauSProduct
-- name    : SetMultCost_IsTauSProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:58.790823+00:00
-- url     : https://prove2.me/theorems/df51be0a-2b9d-43f5-b710-43e9ab96774c
-- title:
--   $(\tau,S)$-products
-- statement:
--   Let $\tau=(\tau_0,\dots,\tau_\ell)$ be integers and $S\subseteq\{1,\dots,\ell\}$. A product $G_1\cdots G_r$ is a **$(\tau,S)$-product** when there are $i\in S$ and $V\subseteq[r]$ with
--
--   $$\deg\prod_{j\in V}G_j>\tau_i\quad\text{and}\quad\deg G_j\le\tau_{i-1}\ \text{ for all }j\in V.$$
--
--   The associated set for restrictions $\mathbf r$ consists of the coordinates $i\in\{1,\dots,\Delta\}$ with $\tau_i<r_i\tau_{i-1}$. A factor set of low degree that adds up to high degree is what makes the relative rank small.
--
--   **Formalization Note** Degree is total degree, $0$ on the zero polynomial. Monotonicity of $\tau$ is a hypothesis of the statements using this. The product $r_i\tau_{i-1}$ is in $\mathbb N\cup\{\infty\}$, with $\infty\cdot0=0$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Definition 4.1, p.13; Lemma 4.2, p.13

import Mathlib

namespace SetMultCost

/-- **`(τ,S)`-product.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), Definition 4.1, p.13: "we shall say a product G1 · · · Gr is a
(τ,S)-product if there exists some i ∈ S and a subset V ⊆ [r] such that deg ∏j∈V Gj > τi and
deg Gj ≤ τi−1 for all j ∈ V."

**Formalization Note.** `G` is the list of factors; degree is total degree, `0` for the zero
polynomial. `τ` is a function on `ℕ`, read at `0, …, ℓ`, and monotonicity is a hypothesis of the
statements that use it. The clause `1 ≤ i` is the page's `S ⊆ {1, …, ℓ}`. -/
def IsTauSProduct {σ F : Type*} [CommSemiring F] (τ : ℕ → ℕ) (S : Finset ℕ)
    (G : List (MvPolynomial σ F)) : Prop :=
  ∃ i ∈ S, 1 ≤ i ∧ ∃ V : Finset (Fin G.length),
    τ i < (∏ j ∈ V, G.get j).totalDegree ∧ ∀ j ∈ V, (G.get j).totalDegree ≤ τ (i - 1)

open scoped Classical in
/-- The set `S` of Lemmas 4.2 and 5.5 (pp.13, 18): "the coordinates where τi < riτi−1", in
`{1, …, Δ}`. The product is in `ℕ∞`, with `⊤ · 0 = 0`. -/
noncomputable def tauS (Δ : ℕ) (r : ℕ → ℕ∞) (τ : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 Δ).filter fun i => (τ i : ℕ∞) < r i * (τ (i - 1) : ℕ∞)

end SetMultCost


