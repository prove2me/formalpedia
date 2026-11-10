-- Prove2me | Definitions.Def_QThermalClassical_Sampler
-- name    : QThermalClassical_Sampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:40.20717+00:00
-- url     : https://prove2.me/theorems/9ee1b5cd-9af0-449a-8efe-1951b0730ba2
-- title:
--   Sampling distributions over outcomes $(b,E)$ and their expectation
-- statement:
--   An **outcome** of the sampling primitive is a triple $(b,E,C(E))$: a real coefficient, an operator, and its term list. A **sampler** is a countable distribution over outcomes presented in finite blocks: block $t\in\mathbb N$ has probability $w_t\ge0$ with $\sum_tw_t=1$, and inside block $t$ the outcome $o_{t,j}$ has conditional probability $q_{t,j}\ge0$, summing to $1$ when $w_t>0$. Its **expectation** of an operator-valued function $f$ is
--   $$
--   \mathbb E[f]=\sum_{t\ge0}w_t\sum_jq_{t,j}\,f(o_{t,j}),
--   $$
--   the series in $t$ being required to converge.
--
--   This is the shape of the distribution built in the proof of Lemma 9, eq. (75), where block $t$ collects the outcomes of order $t$ with probability $2^{-t}$.
--
--   **Formalization Note** A countable distribution with an absolutely convergent expectation is a sampler with one outcome per block.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 9 and eq. (75), p.24; Algorithm 1, p.27

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

/-- One outcome `(b, E)` of the sampling primitive of Lemma 9, together with the term list
`C(E)` of `E`. -/
structure Outcome (Q : Type) where
  /-- The real coefficient `b`. -/
  b : ℝ
  /-- The operator `E`. -/
  E : Matrix (Q → Bool) (Q → Bool) ℂ
  /-- The ordered list `C(E)` of Hamiltonian terms making up `E`; its length is the order. -/
  C : List (Q → Fin 4)

/-- A countable distribution over outcomes, presented as a sequence of finite blocks: block `t`
has probability `w t`, and inside block `t` outcome `o t j` has conditional probability
`q t j`. This is the shape of the distribution built in the proof of Lemma 9, eq. (75), where
block `t` collects the outcomes of order `t`.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Lemma 9 and eq. (75), p.24; Algorithm 1,
p.27.

**Formalization Note.** The expectation is taken block by block (`Sampler.HasExpect`): the
blocks are summed as a series and each block is a finite conditional mean. The conditional
probabilities in a block of probability `0` are unconstrained and contribute nothing. -/
structure Sampler (Q : Type) where
  /-- Probability of block `t`. -/
  w : ℕ → ℝ
  /-- Number of outcomes in block `t`. -/
  N : ℕ → ℕ
  /-- Conditional probabilities inside block `t`. -/
  q : (t : ℕ) → Fin (N t) → ℝ
  /-- The outcomes of block `t`. -/
  o : (t : ℕ) → Fin (N t) → Outcome Q
  w_nonneg : ∀ t, 0 ≤ w t
  w_sum : HasSum w 1
  q_nonneg : ∀ t j, 0 ≤ q t j
  q_sum : ∀ t, 0 < w t → ∑ j, q t j = 1

/-- `𝔼[f(o)] = A` for a sampler, block by block:
`Σ_t w_t · Σ_j q_{t,j} f(o_{t,j}) = A` as a convergent series in `t`. -/
def Sampler.HasExpect {Q : Type} [Fintype Q] (σ : Sampler Q) (f : Outcome Q → Op Q)
    (A : Op Q) : Prop :=
  HasSum (fun t => σ.w t • ∑ j, σ.q t j • f (σ.o t j)) A

end QThermalClassical


