-- Prove2me | Definitions.Def_SuttonTD_Convergence_EpisodeModel
-- name    : SuttonTD_Convergence_EpisodeModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:23:36.514347+00:00
-- url     : https://prove2.me/theorems/b0174ca2-abaa-4616-9dcc-54dd8f9b317d
-- title:
--   One observed sequence $q_1,\dots,q_m,q_{m+1},z$ and its probability $\mu_{q_1}p_{q_1q_2}\cdots p_{q_mq_{m+1}}$
-- statement:
--   An **episode** (one observed sequence) of an absorbing Markov chain consists of the nonterminal states $q_1,\dots,q_m\in N$ visited, the terminal state $q_{m+1}=j\in T$ in which it ends, and a scalar outcome $z\in\mathbb R$. Episodes carry the σ-algebra in which every set of (state list, terminal state) pairs is measurable and the outcome carries the Borel σ-algebra.
--
--   When the initial state is drawn from a distribution $\mu$ on $N$, the probability that an episode visits exactly $s=(s_1,\dots,s_m)$ ($m\ge1$) and terminates in $j$ is
--
--   $$\Pr(s,j)=\mu_{s_1}\,p_{s_1s_2}\,p_{s_2s_3}\cdots p_{s_{m-1}s_m}\,p_{s_mj},$$
--
--   and the empty list has probability $0$ (every sequence starts in a nonterminal state).
--
--   These weights define the law of a sequence used in Theorem 2 and the expected visit counts $d_i$.
--
--   **Formalization Note** `stepWeight C i [s_2,…,s_m] j` is $p_{is_2}\cdots p_{s_mj}$ and `pathWeight C μ s j` is $\Pr(s,j)$.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, pp. 23–24 (PDF pp. 15–16)

import Definitions.Def_SuttonTD_Convergence_AbsorbingChain

namespace SuttonTD.Convergence

/-- One **observed sequence** of an absorbing Markov chain (Sutton 1988, §4.1, pp. 23–24,
PDF pp. 15–16): the nonterminal states `q_1, …, q_m` (`path`), the terminal state `q_{m+1}`
(`term`) and the scalar outcome `z` (`out`). -/
structure Episode (N T : Type*) where
  path : List N
  term : T
  out : ℝ

/-- The σ-algebra on episodes: every set of (path, terminal state) pairs is measurable (the pair
ranges over a countable type), and the outcome carries the Borel σ-algebra of `ℝ`. -/
instance Episode.instMeasurableSpace (N T : Type*) : MeasurableSpace (Episode N T) :=
  MeasurableSpace.comap (fun e : Episode N T => (e.path, e.term)) ⊤ ⊔
    MeasurableSpace.comap Episode.out (borel ℝ)

namespace AbsorbingChain

variable {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]

/-- `stepWeight C i [s_2, …, s_m] j = p_{i s_2} p_{s_2 s_3} ⋯ p_{s_{m-1} s_m} p_{s_m j}`:
the probability, starting from the nonterminal state `i`, of visiting `s_2, …, s_m` next and then
terminating in `j ∈ T` (with `stepWeight C i [] j = p_ij`). -/
def stepWeight (C : AbsorbingChain N T) : N → List N → T → ℝ
  | i, [], j => C.pT i j
  | i, k :: rest, j => C.pN i k * C.stepWeight k rest j

/-- The probability that one sequence has nonterminal states exactly `s = (s_1, …, s_m)` and
terminates in `j ∈ T`, when the initial state is drawn from `μ` (pp. 23–24):
`μ_{s_1} p_{s_1 s_2} ⋯ p_{s_{m-1} s_m} p_{s_m j}`. A sequence has at least one nonterminal
state, so the empty list has weight `0`. -/
def pathWeight (C : AbsorbingChain N T) (μ : N → ℝ) : List N → T → ℝ
  | [], _ => 0
  | i :: rest, j => μ i * C.stepWeight i rest j

end AbsorbingChain

end SuttonTD.Convergence


