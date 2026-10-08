-- Prove2me | Definitions.Def_SuttonTD_Convergence_AbsorbingChain
-- name    : SuttonTD_Convergence_AbsorbingChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:26.468165+00:00
-- url     : https://prove2.me/theorems/f92168fa-7044-496a-a057-4df00074c64e
-- title:
--   Absorbing Markov chain with nonterminal block $Q$ and terminal vector $h$ (§4.1)
-- statement:
--   An **absorbing Markov chain** is given by a finite set $N$ of nonterminal states, a finite set $T$ of terminal states, and transition probabilities $p_{ij}\ge 0$ from each nonterminal state $i\in N$ to each state $j\in N\cup T$, with
--
--   $$\sum_{j\in N\cup T} p_{ij} = 1 \qquad (i\in N).$$
--
--   Let $Q$ be the $N\times N$ matrix with $[Q]_{ij}=p_{ij}$ for $i,j\in N$. The chain is *absorbing*: indefinite cycles among the nonterminal states are impossible, which for a finite chain is expressed, as in the paper, by
--
--   $$\lim_{k\to\infty} Q^k = 0 .$$
--
--   Given expected outcomes $\bar z_j$ attached to the terminal states $j\in T$, the vector $h$ has components
--
--   $$[h]_i=\sum_{j\in T} p_{ij}\,\bar z_j\qquad(i\in N).$$
--
--   These are the data of every result of §4.1: the ideal predictions are $[(I-Q)^{-1}h]_i$.
--
--   **Formalization Note** The two blocks $p_{ij}$ ($j\in N$) and $p_{ij}$ ($j\in T$) are separate fields `pN`, `pT`, so $N$ and $T$ are disjoint by construction; terminal states have no outgoing transitions. Nonemptiness of $T$ is not a field: with $N$ nonempty it follows from $Q^k\to0$.
-- source:
--   Sutton (1988), Learning to Predict by the Methods of Temporal Differences, Machine Learning 3:9–44, §4.1, pp. 23–24 (PDF pp. 15–16)

import Mathlib
open Filter Topology

namespace SuttonTD.Convergence

/-- An **absorbing Markov chain** with nonterminal states `N` and terminal states `T`
(Sutton 1988, *Learning to predict by the methods of temporal differences*, Machine Learning
3:9–44, §4.1, pp. 23–24, PDF pp. 15–16).

`pN i j` is the transition probability `p_ij` from the nonterminal state `i` to the nonterminal
state `j`, and `pT i j` is the transition probability `p_ij` from `i` to the terminal state `j`.
For every `i ∈ N` these are nonnegative and `∑_{j ∈ N ∪ T} p_ij = 1`. The "absorbing" property
("indefinite cycles among the nonterminal states are not possible", p. 23) is stated in the form
the paper itself uses on p. 24: the powers `Q^k` of the nonterminal block `[Q]_ij = p_ij`
(`i, j ∈ N`) converge to `0`.

Formalization Note: `N ∪ T` is encoded by the two blocks `pN`, `pT`, so `N` and `T` are disjoint
by construction. Terminal states have no outgoing transitions (the sequence stops there). -/
structure AbsorbingChain (N T : Type*) [Fintype N] [DecidableEq N] [Fintype T] where
  /-- `p_ij` for `i, j ∈ N`. -/
  pN : N → N → ℝ
  /-- `p_ij` for `i ∈ N`, `j ∈ T`. -/
  pT : N → T → ℝ
  pN_nonneg : ∀ i j, 0 ≤ pN i j
  pT_nonneg : ∀ i j, 0 ≤ pT i j
  row_sum : ∀ i, ∑ j, pN i j + ∑ j, pT i j = 1
  absorbing : Tendsto (fun k : ℕ => (Matrix.of pN) ^ k) atTop (𝓝 0)

namespace AbsorbingChain

variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

/-- The matrix `Q` with `[Q]_ij = p_ij` for `i, j ∈ N` (p. 24). -/
def Q (C : AbsorbingChain N T) : Matrix N N ℝ := Matrix.of C.pN

/-- The vector `h` with `[h]_i = ∑_{j ∈ T} p_ij z̄_j` (p. 24), for given expected outcomes
`z̄ : T → ℝ` of the terminal states. -/
def h (C : AbsorbingChain N T) (zbar : T → ℝ) : N → ℝ := fun i => ∑ j, C.pT i j * zbar j

end AbsorbingChain

end SuttonTD.Convergence


