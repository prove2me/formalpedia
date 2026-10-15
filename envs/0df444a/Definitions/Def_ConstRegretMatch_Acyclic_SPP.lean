-- Prove2me | Definitions.Def_ConstRegretMatch_Acyclic_SPP
-- name    : ConstRegretMatch_Acyclic_SPP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:45.507748+00:00
-- url     : https://prove2.me/theorems/ecb8f985-b7e4-4e1e-a748-26830ef5b361
-- title:
--   §2.1, Def. 2.2, §4.2 — (SPP) with a general right-hand side, GP, ℳ₊, ℳ₀, 𝒬₊, 𝒬₀ and the optimal basis matrix ℬ
-- statement:
--   This file defines the **static-planning problem** (SPP) of a matching network for an arbitrary right-hand side, the **general position condition** and the **optimal basis matrix**.
--
--   Let $M$ be the matching matrix and $r$ the match values. For a right-hand side $b \in \mathbb R^n$ the static-planning problem is the linear program
--   $$\max\ r\cdot z \quad\text{s.t.}\quad Mz + s = b,\quad z \in \mathbb R^d_{\ge 0},\ s \in \mathbb R^n_{\ge 0}.$$
--   The paper's (SPP) is $b = \lambda$. A pair $(z, s)$ is **feasible** if it satisfies the constraints, **optimal** if it is feasible and $r\cdot z \ge r\cdot z'$ for every feasible $(z',s')$, and the **unique optimal solution** if moreover every optimal solution equals it.
--
--   Given $(z, s)$, the sets
--   $$\mathcal M_+ = \{m : z_m > 0\},\quad \mathcal M_0 = \mathcal M\setminus\mathcal M_+,\quad \mathcal Q_+ = \{j : s_j > 0\},\quad \mathcal Q_0 = \mathcal A\setminus\mathcal Q_+$$
--   are the active matches, the redundant matches, the under-demanded queues and the over-demanded queues.
--
--   1. **General position (Definition 2.2).** The network with values $r$ and arrival rates $\lambda$ satisfies GP with witness $(z^*, s^*)$ if $(z^*, s^*)$ is the unique optimal solution of (SPP) and it is non-degenerate: $|\mathcal M_+| + |\mathcal Q_+| = n$.
--   2. **Optimal basis matrix (§4.2).** $\mathcal B$ is the $n \times (|\mathcal M_+|+|\mathcal Q_+|)$ matrix whose columns are the columns of $M$ indexed by $\mathcal M_+$ followed by the unit vectors $e_j$, $j \in \mathcal Q_+$. The **basic part** of $(z^*, s^*)$ is the vector $(z^*_{\mathcal M_+}, s^*_{\mathcal Q_+})$.
--   3. For a vector $w$ indexed by $\mathcal M_+ \sqcup \mathcal Q_+$, the **solution with this basis and basic values $w$** is $\tilde z_m = w_m$ for $m \in \mathcal M_+$, $\tilde z_m = 0$ for $m \in \mathcal M_0$, $\tilde s_j = w_j$ for $j \in \mathcal Q_+$, $\tilde s_j = 0$ for $j \in \mathcal Q_0$.
--
--   These objects carry the paper's structural results on the optimal solution of (SPP): its representation through the inverse of $\mathcal B$ and its stability under changes of $\lambda$.
--
--   **Formalization Note** The optimal solution is not obtained by a choice operator: every statement takes $(z^*, s^*)$ as an argument together with the hypothesis `IsGP`. The column index type of $\mathcal B$ is `{m // m ∈ Mplus z} ⊕ {j // j ∈ Qplus s}`, so no inverse of a non-square matrix is ever formed.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 10, (SPP) and the partition ℳ₊, ℳ₀, 𝒬₊, 𝒬₀; p. 11, Definition 2.2; pp. 19–20, §4.2 (basis matrix ℬ)

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP

namespace ConstRegretMatch.Acyclic

variable {n d : ℕ}

/-- Feasibility for the static-planning problem with a general right-hand side `b`:
`z ≥ 0`, `s ≥ 0` and `M z + s = b`. The paper's (SPP) (§2.1, p. 10) is `b = λ`. -/
def SPPFeasible (N : MatchingNetwork n d) (b : Fin n → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ) :
    Prop :=
  (∀ m, 0 ≤ z m) ∧ (∀ i, 0 ≤ s i) ∧ ∀ i, ∑ m, N.M i m * z m + s i = b i

/-- `(z, s)` is an optimal solution of `max r · z s.t. M z + s = b, z ≥ 0, s ≥ 0`: it is feasible
and its objective is at least that of every feasible `(z', s')`. -/
def SPPOptimal (N : MatchingNetwork n d) (r : Fin d → ℝ) (b : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) : Prop :=
  SPPFeasible N b z s ∧
    ∀ z' s', SPPFeasible N b z' s' → ∑ m, r m * z' m ≤ ∑ m, r m * z m

/-- `(z, s)` is the unique optimal solution of the static-planning problem with right-hand side `b`:
it is optimal, and every optimal solution equals it. -/
def SPPUniqueOptimal (N : MatchingNetwork n d) (r : Fin d → ℝ) (b : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) : Prop :=
  SPPOptimal N r b z s ∧ ∀ z' s', SPPOptimal N r b z' s' → z' = z ∧ s' = s

/-- The general position condition (GP, Definition 2.2, p. 11) for the network `N`, match values `r`
and arrival rates `lam`, with `(z, s)` its witness: `(z, s)` is the unique optimal solution of (SPP)
(right-hand side `λ`), and it is non-degenerate, i.e. `|ℳ₊| + |𝒬₊| = n` (p. 11). -/
def IsGP (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) : Prop :=
  SPPUniqueOptimal N r lam z s ∧ (ConstRegretMatch.Upper.Mplus z).card + (ConstRegretMatch.Upper.Qplus s).card = n

/-- The optimal basis matrix `ℬ` (§4.2, p. 19): its columns are the columns of `M` indexed by `ℳ₊`
and the unit columns `e_j` indexed by `j ∈ 𝒬₊` (the columns of the slack variables). -/
noncomputable def basisMatrix (N : MatchingNetwork n d) (z : Fin d → ℝ) (s : Fin n → ℝ) :
    Matrix (Fin n) (ConstRegretMatch.Upper.BasisIdx z s) ℝ :=
  fun i c => match c with
    | Sum.inl m => N.M i m.1
    | Sum.inr j => if i = j.1 then 1 else 0

/-- The match part of the solution with basis `ℳ₊ ∪ 𝒬₊` (of `(z, s)`) and basic values `w`:
`z̃_m = w_m` for `m ∈ ℳ₊` and `z̃_m = 0` for `m ∈ ℳ₀`. -/
noncomputable def basisSolZ {z : Fin d → ℝ} {s : Fin n → ℝ} (w : ConstRegretMatch.Upper.BasisIdx z s → ℝ) :
    Fin d → ℝ :=
  fun m => if h : m ∈ ConstRegretMatch.Upper.Mplus z then w (Sum.inl ⟨m, h⟩) else 0

/-- The slack part of the solution with basis `ℳ₊ ∪ 𝒬₊` (of `(z, s)`) and basic values `w`:
`s̃_j = w_j` for `j ∈ 𝒬₊` and `s̃_j = 0` for `j ∈ 𝒬₀`. -/
noncomputable def basisSolS {z : Fin d → ℝ} {s : Fin n → ℝ} (w : ConstRegretMatch.Upper.BasisIdx z s → ℝ) :
    Fin n → ℝ :=
  fun j => if h : j ∈ ConstRegretMatch.Upper.Qplus s then w (Sum.inr ⟨j, h⟩) else 0

end ConstRegretMatch.Acyclic


