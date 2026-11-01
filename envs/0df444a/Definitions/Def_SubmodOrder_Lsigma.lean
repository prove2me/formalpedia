-- Prove2me | Definitions.Def_SubmodOrder_Lsigma
-- name    : SubmodOrder_Lsigma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:09.434736+00:00
-- url     : https://prove2.me/theorems/4a39568b-e685-4892-942c-ca5d556b720a
-- title:
--   The unions $O_\sigma(j)$ and $L_\sigma(j)$
-- statement:
--   Let $O_1,\dots,O_m$ be the blocks $O$ of an interleaved partition and $\sigma$ a permutation of $[m]$. For $j\in[m]$,
--
--   $$
--   O_\sigma(j)=\bigcup_{\ell:\ \sigma(\ell)\ge\sigma(j)}O_\ell,\qquad
--   L_\sigma(j)=\bigcup_{\ell:\ \ell<j,\ O_\ell\subseteq O_\sigma(j)}O_\ell .
--   $$
--
--   $L_\sigma(j)$ collects the blocks to the left of $O_j$ in the order $\pi$ that come after $O_j$ in the permutation $\sigma$. These unions appear in the family of upper bounds of Lemma 1, one for each $\sigma$.
--
--   **Formalization Note** Blocks are indexed by `Fin m` (0-based) and $\sigma$ is an `Equiv.Perm (Fin m)`. The index condition of $L_\sigma$ is the paper's literal $O_\ell\subseteq O_\sigma(j)$.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.19, definitions of Oσ(j) and Lσ(j)

import Mathlib

namespace SubmodOrder

/-- `O_σ(j) = ⋃_{ℓ | σ(ℓ) ≥ σ(j)} O_ℓ` (Udwani, arXiv:2107.02743v5, p.19), for a permutation
`σ` of the block indices.

**Formalization Note.** Blocks are indexed by `Fin m` (0-based) and `σ : Equiv.Perm (Fin m)`. -/
def Osigma {α : Type*} [DecidableEq α] {m : ℕ} (O : Fin m → Finset α) (σ : Equiv.Perm (Fin m))
    (j : Fin m) : Finset α :=
  (Finset.univ.filter fun ℓ : Fin m => σ j ≤ σ ℓ).biUnion O

/-- `L_σ(j) = ⋃_{ℓ | ℓ < j, O_ℓ ⊆ O_σ(j)} O_ℓ` (Udwani, arXiv:2107.02743v5, p.19: "for every
j ∈ [m] define Lσ(j) = ⋃_{ℓ | ℓ<j, Oℓ⊆Oσ(j)} Oℓ, which is the union over sets Oℓ that are to the
left of Oj in submodular order and to the right of Oj in permutation σ").

**Formalization Note.** Blocks are indexed by `Fin m` (0-based); the index condition is the
literal `O_ℓ ⊆ O_σ(j)` of the paper. -/
def Lsigma {α : Type*} [DecidableEq α] {m : ℕ} (O : Fin m → Finset α) (σ : Equiv.Perm (Fin m))
    (j : Fin m) : Finset α :=
  (Finset.univ.filter fun ℓ : Fin m => ℓ < j ∧ O ℓ ⊆ Osigma O σ j).biUnion O

end SubmodOrder


