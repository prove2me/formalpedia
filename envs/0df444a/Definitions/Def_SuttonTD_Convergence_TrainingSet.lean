-- Prove2me | Definitions.Def_SuttonTD_Convergence_TrainingSet
-- name    : SuttonTD_Convergence_TrainingSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:49:59.35128+00:00
-- url     : https://prove2.me/theorems/fa2b8be6-5c52-4c95-b042-527376b000eb
-- title:
--   Finite training set, maximum-likelihood estimates $\hat Q$, $\hat h$, counts $\hat d$, $\hat\mu$, and repeated presentations
-- statement:
--   A **training set** consists of $S$ sequences; sequence $s$ is a nonempty list $q^s_1,\dots,q^s_{m_s}$ of nonterminal states with an outcome $z_s\in\mathbb R$. All sequences terminate in different terminal states. From it one forms:
--
--   1. $\hat d_i$, the number of times state $i$ appears in the training set;
--   2. $\eta_{ij}$, the number of transitions $i\to j$ between consecutive nonterminal states;
--   3. $[\hat\mu]_i$, the number of sequences that begin in $i$;
--   4. the maximum-likelihood estimates $[\hat Q]_{ij}=\hat p_{ij}=\eta_{ij}/\hat d_i$ and $[\hat h]_i=\sum_{j\in\hat T}\hat p_{ij}z_j$, which, since every sequence has its own terminal state, equals
--
--   $$[\hat h]_i=\frac{1}{\hat d_i}\sum_{s:\ q^s_{m_s}=i} z_s .$$
--
--   **Repeated presentations.** Linear TD(0) with weight updates after each complete presentation updates
--
--   $$w_{n+1}=w_n+\sum_{s}\sum_{t=1}^{m_s}\alpha\,(P^s_{t+1}-P^s_t)\,x_{q^s_t},\qquad P^s_t=w_n^\top x_{q^s_t},\ P^s_{m_s+1}=z_s .$$
--
--   These are the objects of Theorem 3.
--
--   **Formalization Note** The divisions by $\hat d_i$ are meaningful only for states that appear; the theorems using these objects assume every state appears.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.2, pp. 30–31 (PDF pp. 22–23)

import Definitions.Def_SuttonTD_Convergence_LinearTD0

namespace SuttonTD.Convergence

/-- A finite **training set** of `S` sequences (Sutton 1988, §4.2, pp. 30–31, PDF pp. 22–23):
sequence `s` consists of the nonterminal states `q^s_1, …, q^s_{m_s}` (`path s`, nonempty) and the
outcome `z_s` (`out s`). As on p. 30, "all sequences terminate in different states", so sequence
`s` has its own terminal state, whose outcome is `z_s`. -/
structure TrainingSet (N : Type*) (S : ℕ) where
  path : Fin S → List N
  out : Fin S → ℝ
  path_ne_nil : ∀ s, path s ≠ []

namespace TrainingSet

variable {N : Type*} [Fintype N] [DecidableEq N] {S : ℕ}

/-- `d̂_i`, "the number of times state `i` appears in the training set" (p. 31). -/
def visits (D : TrainingSet N S) (i : N) : ℕ := ∑ s, (D.path s).count i

/-- `η_ij` (`i, j ∈ N̂`), the number of times the transition `i → j` between consecutive
nonterminal states appears in the training set (p. 31). -/
def transitions (D : TrainingSet N S) (i j : N) : ℕ :=
  ∑ s, ((D.path s).zip (D.path s).tail).count (i, j)

/-- `[μ̂]_i`, "the number of sequences in the training set that begin in state `i`" (p. 31). -/
def starts (D : TrainingSet N S) (i : N) : ℕ :=
  (Finset.univ.filter fun s => (D.path s).head? = some i).card

/-- `[Q̂]_ij = p̂_ij = η_ij / d̂_i`, "the fraction of the times that state `i` was entered in
which a transition occurred to state `j`" (p. 30). -/
noncomputable def Qhat (D : TrainingSet N S) : Matrix N N ℝ :=
  Matrix.of fun i j => (D.transitions i j : ℝ) / (D.visits i : ℝ)

/-- `[ĥ]_i = ∑_{j ∈ T̂} p̂_ij z_j` (p. 30). Since every sequence ends in its own terminal state
`j`, `p̂_ij = 1/d̂_i` if the sequence terminating in `j` has last nonterminal state `i`, and `0`
otherwise; hence `[ĥ]_i = (1/d̂_i) ∑_{s : q^s_{m_s} = i} z_s`. -/
noncomputable def hhat (D : TrainingSet N S) : N → ℝ := fun i =>
  (∑ s ∈ Finset.univ.filter (fun s => (D.path s).getLast? = some i), D.out s) / (D.visits i : ℝ)

/-- Linear TD(0) under repeated presentations of the training set, with weight updates after
each complete presentation (p. 31):
`w_{n+1} = w_n + ∑_s ∑_{t=1}^{m_s} α (P^s_{t+1} − P^s_t) x_{q^s_t}`,
where all predictions use `w_n` and `P^s_{m_s+1} = z_s`. `presentWeights x α w₀ D n` is `w_n`. -/
def presentWeights {K : ℕ} (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ)
    (D : TrainingSet N S) : ℕ → Fin K → ℝ
  | 0 => w₀
  | n + 1 =>
    presentWeights x α w₀ D n +
      ∑ s, tdIncrement x α (presentWeights x α w₀ D n) (D.path s) (D.out s)

end TrainingSet

end SuttonTD.Convergence


