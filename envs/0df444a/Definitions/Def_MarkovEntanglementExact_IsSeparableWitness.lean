-- Prove2me | Definitions.Def_MarkovEntanglementExact_IsSeparableWitness
-- name    : MarkovEntanglementExact_IsSeparableWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:23.314573+00:00
-- url     : https://prove2.me/theorems/a48a9fe8-e165-47ee-a70b-d490e011a2be
-- title:
--   A decomposition witnessing separability (Definition 1)
-- statement:
--   Let $P$ be a matrix on $S_A\times S_B$ for finite sets $S_A,S_B$. The data $K$, $(x_j)_{j\in[K]}$, $(P^{(j)}_A,P^{(j)}_B)_{j\in[K]}$ **witness separability** of $P$ if each $P^{(j)}_A$, $P^{(j)}_B$ is a transition matrix, $\sum_{j=1}^K x_j=1$, and
--   $$P=\sum_{j=1}^K x_j\,P^{(j)}_A\otimes P^{(j)}_B.$$
--
--   The published `IsSeparable P` says that a witness exists. The theorems of this mission need the witness explicitly, because they name the sums $\sum_j x_jP^{(j)}_A$.
--
--   **Formalization Note** The coefficients are signed: the paper's Definition 1 permits general linear coefficients (p.12). `K : ℕ` allows $0$, but the empty sum contradicts $\sum_j x_j=1$.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 1, p.9

import Mathlib
import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

variable {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]

/-- The data `(K, x, P^(j)_A, P^(j)_B)` is a decomposition of `P` as in Definition 1: every
`P^(j)_A`, `P^(j)_B` is a transition matrix, `Σ_j x_j = 1`, and
`P = Σ_j x_j P^(j)_A ⊗ P^(j)_B`. `MarkovEntanglement.IsSeparable P` says exactly that such a
decomposition exists.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Definition 1, p.9.

**Formalization Note.** The coefficients `x` are signed (p.12: "permits general linear
coefficients"). `K : ℕ` allows `0`, but then the empty sum contradicts `Σ_j x_j = 1`. -/
def IsSeparableWitness (P : Matrix (SA × SB) (SA × SB) ℝ) (K : ℕ) (x : Fin K → ℝ)
    (PAj : Fin K → Matrix SA SA ℝ) (PBj : Fin K → Matrix SB SB ℝ) : Prop :=
  (∀ k, IsTransitionMatrix (PAj k)) ∧ (∀ k, IsTransitionMatrix (PBj k)) ∧
    (∑ k, x k = 1) ∧
    P = ∑ k, x k • tensorProd (PAj k) (PBj k)

end MarkovEntanglementExact


