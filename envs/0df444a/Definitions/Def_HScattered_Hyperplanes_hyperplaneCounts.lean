-- Prove2me | Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts
-- name    : HScattered_Hyperplanes_hyperplaneCounts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:57.495662+00:00
-- url     : https://prove2.me/theorems/8865761f-2dd8-4340-8869-de7b91a305ec
-- title:
--   Hyperplane intersection numbers $h_i$ and the sums $\alpha_k$, $\beta_k$, $A$ (§5.2–5.3)
-- statement:
--   Let $\mathbb F_q \subseteq \mathbb F_{q^n}$ be finite fields, $V = V(r,q^n)$, and $U$ an $\mathbb F_q$-subspace of $V$.
--
--   1. For $i \in \mathbb N$, $h_i$ is the number of $(r-1)$-dimensional $\mathbb F_{q^n}$-subspaces $W$ of $V$ (hyperplanes) with $\dim_{\mathbb F_q}(W \cap U) = i$.
--   2. For $k \in \mathbb N$,
--   $$\alpha_k = \sum_i h_i (q^n - 1)\, q^{k i}, \qquad \beta_k = \sum_i h_i (q^n-1)(q^i-1)(q^i-q)\cdots(q^i-q^{k-1}),$$
--   so that $\beta_0 = \alpha_0$.
--   3. For an integer $h \ge 0$, with $s = h+1$,
--   $$A = \sum_i h_i (q^n-1)\,(q^i - q^{n(r-s)/s})(q^i - q^{n(r-s)/s + 1})\cdots(q^i - q^{n(r-s)/s + s - 1}).$$
--
--   All sums run over $i = 0, 1, \dots, \dim_{\mathbb F_q} U$ (for larger $i$, $h_i = 0$). These are the quantities of the double-counting argument of §5 that proves Theorem 2.7.
--
--   **Formalization Note** $h_i$ is `hCount F K U i`, named to avoid a clash with the scattered index $h$; it is the cardinality of a finite set of submodules when $\mathbb F_q$, $\mathbb F_{q^n}$ are finite and $V$ finite-dimensional. $\alpha_k$, $\beta_k$, $A$ are the integers `alphaSum`, `betaSum`, `quantityA` with $q = |\mathbb F_q|$, $n = \dim_{\mathbb F_q}\mathbb F_{q^n}$. In `quantityA` the exponent $n(r-s)/s = rn/s - n$ is written as $\dim_{\mathbb F_q} U - n$ (natural-number difference); in the setting of §5.2 one has $\dim_{\mathbb F_q} U = rn/s \ge n$, so the difference is exact.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 20 (§5.2, h_i and A) and p. 21 (§5.3, α_k and β_k)

import Mathlib

namespace HScattered.Hyperplanes

/-- §5.2 (arXiv:1906.10590v2, p. 20): `h_i` is the number of `(r − 1)`-dimensional
`K`-subspaces `W` of `V` (hyperplanes, `r = finrank K V`) meeting the `F`-subspace `U` in an
`F`-subspace of dimension `i`. (Named `hCount` to keep it apart from the scattered index `h`.)
For finite `F`, `K` and finite-dimensional `V` the set counted is finite. -/
noncomputable def hCount (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (U : Submodule F V) (i : ℕ) : ℕ :=
  Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - 1 ∧
    Module.finrank F ↥(W.restrictScalars F ⊓ U) = i}

/-- §5.3 (p. 21): `α_k = ∑_i h_i (qⁿ − 1) q^{k i}`, with `q = |F|`, `n = finrank F K`; the index
`i` runs over `0, …, dim_F U` (for larger `i`, `h_i = 0`). -/
noncomputable def alphaSum (F K : Type*) {V : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (U : Submodule F V) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (Module.finrank F U + 1),
    (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
      (Fintype.card F : ℤ) ^ (k * i)

/-- §5.3 (p. 21): `β_k = ∑_i h_i (qⁿ − 1)(q^i − 1)(q^i − q)⋯(q^i − q^{k−1})`; for `k = 0` the
product is empty and `β_0 = α_0`. -/
noncomputable def betaSum (F K : Type*) {V : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (U : Submodule F V) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (Module.finrank F U + 1),
    (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
      ∏ l ∈ Finset.range k, ((Fintype.card F : ℤ) ^ i - (Fintype.card F : ℤ) ^ l)

/-- §5.2 (p. 20): with `s = h + 1`,
`A = ∑_i h_i (qⁿ − 1)(q^i − q^{n(r−s)/s})⋯(q^i − q^{n(r−s)/s + s − 1})`.
Here `n(r − s)/s = rn/s − n` is written `finrank F U − finrank F K`, which is the exact value
when `dim_F U = rn/s` and `s ≤ r` (the setting of §5.2, where `dim_F U ≥ n`). -/
noncomputable def quantityA (F K : Type*) {V : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (h : ℕ) (U : Submodule F V) : ℤ :=
  ∑ i ∈ Finset.range (Module.finrank F U + 1),
    (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
      ∏ l ∈ Finset.range (h + 1), ((Fintype.card F : ℤ) ^ i -
        (Fintype.card F : ℤ) ^ (Module.finrank F U - Module.finrank F K + l))

end HScattered.Hyperplanes


