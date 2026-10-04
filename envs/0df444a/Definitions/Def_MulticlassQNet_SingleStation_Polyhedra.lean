-- Prove2me | Definitions.Def_MulticlassQNet_SingleStation_Polyhedra
-- name    : MulticlassQNet_SingleStation_Polyhedra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:53:53.422627+00:00
-- url     : https://prove2.me/theorems/864af678-8d1f-4779-b53e-28c1aebeaf58
-- title:
--   §8.1–8.2 — the multiclass M/M/1 polyhedra P1 (64)–(65) and P2 (69)–(71), and the vectors v(π) of (58)
-- statement:
--   Consider a single-server queue with $n$ customer classes $E=\{1,\dots,n\}$. Customers of class $i$ arrive at rate $\lambda_i>0$ and are served at rate $\mu_i>0$; the **traffic intensity** of class $i$ is $\rho_i=\lambda_i/\mu_i$. For a set of classes $S\subseteq E$ put
--   $$
--   b(S)=\frac{\sum_{i\in S}\rho_i/\mu_i}{1-\sum_{i\in S}\rho_i},
--   $$
--   so $b(\emptyset)=0$; under the load condition $\sum_{i\in E}\rho_i<1$ every denominator is positive.
--
--   1. The polyhedron **P1** (Theorem 8.3) is the set of vectors $(n_1,\dots,n_n)\in\mathbb R_+^n$ with
--   $$
--   \sum_{i\in S}\frac{n_i}{\mu_i}\ \ge\ b(S)\quad (S\subset E),\qquad \sum_{i\in E}\frac{n_i}{\mu_i}=b(E).
--   $$
--   It is the base $\mathcal B(f,b)$ of (60) with $f_i^S=1/\mu_i$.
--   2. The polyhedron **P2** (Theorem 8.4) lives in the $O(n^2)$ variables $n_i$ and $I_{ij}$ ($i,j\in E$, including $i=j$), all nonnegative, and is cut out by
--   $$
--   \mu_iI_{ii}-\lambda_in_i=\lambda_i\ \ (i\in E),\qquad \mu_iI_{ij}+\mu_jI_{ji}-\lambda_jn_i-\lambda_in_j=0\ \ (i\neq j),\qquad \sum_{i\in E}I_{ij}=n_j\ \ (j\in E).
--   $$
--   3. For a permutation $\pi=(\pi_1,\dots,\pi_n)$ of $E$, the vector $v(\pi)$ of (58) is the unique solution of the triangular system
--   $$
--   \sum_{j=1}^{k}\frac{x_{\pi_j}}{\mu_{\pi_j}}=b(\{\pi_1,\dots,\pi_k\}),\qquad k=1,\dots,n,
--   $$
--   namely $v(\pi)_{\pi_k}=\mu_{\pi_k}\bigl(b(\{\pi_1,\dots,\pi_k\})-b(\{\pi_1,\dots,\pi_{k-1}\})\bigr)$.
--
--   In the queueing model, $n_i$ is the steady-state mean number of class $i$ customers and $I_{ij}$ the steady-state mean of $n_j$ on the event that the server is busy with class $i$; P1 is the performance region obtained from conservation laws, and P2 is what the paper's nonparametric method (Theorem 4.2) produces for this queue. None of that stochastic meaning enters the definitions: they are explicit polyhedra.
--
--   **Formalization Note** Classes are `Fin n` (the paper's class $i$ is `i.val + 1`); the vector $(n_i)$ is written `x`, since `n` is the number of classes, and a point of P2 is a pair `(x, I)` with `I i j` $=I_{ij}$. P1 is the platform definition `AllocationIndices.achievablePolytope` with the matrix $A^S_i=1/\mu_i$ (its inequality is quantified over $S\neq E$, its equality at $S=E$, exactly (60)). The paper writes $N$ for the class set $E$ in (65) and (71); both sums run over all classes. $v(\pi)$ is defined by the closed form above, with $\pi_k$ = `π ⟨k-1, _⟩` and $\{\pi_1,\dots,\pi_k\}$ = `AllocationIndices.lowSet π k`; it solves (58). The positivity and load hypotheses are not part of the definitions; the theorems carry them.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), pp. 33–38, §8.1 Eqs. (57)–(60), §8.2 Theorem 8.3 Eqs. (64)–(65), Theorem 8.4 Eqs. (69)–(71)

import Mathlib
import Definitions.Def_AllocationIndices_Achievable

namespace MulticlassQNet.SingleStation

open Finset

/-!
# The multiclass M/M/1 queue: the polyhedra P1 and P2 and the vectors v(π)

Bertsimas, Paschalidis, Tsitsiklis, *Optimization of Multiclass Queueing Networks: Polyhedral and
Nonlinear Characterizations of Achievable Performance*, MIT Sloan WP #3509-92-MSA (Dec. 1992),
§8.1–§8.2, pp. 33–38.

A single server serves `n` customer classes `E = Fin n` (the paper's class `i` is `i.val + 1`).
Class `i` arrives at rate `lam i` (the paper's `λ_i`) and is served at rate `mu i` (`μ_i`); its
traffic intensity is `ρ_i = λ_i / μ_i`. The variable `x i` is the paper's `n_i`, the mean number
of class `i` customers in steady state (renamed because `n` is the number of classes); the
variable `I i j` is the paper's `I_ij`. All objects here are explicit polyhedra and vectors; no
policy or probability appears.
-/

/-- The traffic intensity `ρ_i = λ_i / μ_i` of class `i` (p. 35). -/
noncomputable def rho {n : ℕ} (lam mu : Fin n → ℝ) (i : Fin n) : ℝ := lam i / mu i

/-- The right-hand side of (64)–(65) (p. 35):
`b(S) = (∑_{i∈S} ρ_i/μ_i) / (1 − ∑_{i∈S} ρ_i)`. Under the load condition `∑_i ρ_i < 1` and
`ρ_i > 0` the denominator is positive for every `S`; `b(∅) = 0`. -/
noncomputable def b {n : ℕ} (lam mu : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, rho lam mu i / mu i) / (1 - ∑ i ∈ S, rho lam mu i)

/-- The polyhedron **P1** of Theorem 8.3 (pp. 35–36):
`∑_{i∈S} n_i/μ_i ≥ b(S)` for `S ⊂ E` (64), `∑_{i∈E} n_i/μ_i = b(E)` (65), `n_i ≥ 0`.
It is the base `B(f, b)` of (60) with `f_i^S = 1/μ_i`, i.e. the platform's
`AllocationIndices.achievablePolytope` with the matrix `A S i = 1 / μ_i`. -/
noncomputable def P1 {n : ℕ} (lam mu : Fin n → ℝ) : Set (Fin n → ℝ) :=
  AllocationIndices.achievablePolytope (fun _ i => 1 / mu i) (b lam mu)

/-- The polyhedron **P2** of Theorem 8.4 (p. 38), in the variables `(n_i, I_ij)`:
`μ_i I_ii − λ_i n_i = λ_i` (69); `μ_i I_ij + μ_j I_ji − λ_j n_i − λ_i n_j = 0` for `i ≠ j` (70);
`∑_{i∈E} I_ij = n_j` (71); `n_i, I_ij ≥ 0`. A point is a pair `(x, I)` with `x i = n_i` and
`I i j = I_ij`. -/
def P2 {n : ℕ} (lam mu : Fin n → ℝ) : Set ((Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ (∀ i j, 0 ≤ p.2 i j) ∧
    (∀ i, mu i * p.2 i i - lam i * p.1 i = lam i) ∧
    (∀ i j, i ≠ j → mu i * p.2 i j + mu j * p.2 j i - lam j * p.1 i - lam i * p.1 j = 0) ∧
    (∀ j, ∑ i, p.2 i j = p.1 j)}

/-- The vector `v(π)` of (58) (p. 33) for P1, i.e. with `f_i^S = 1/μ_i` and the `b` above.
The permutation `π` lists the classes as `π_k = π ⟨k − 1, _⟩`, and
`AllocationIndices.lowSet π k = {π_1, …, π_k}`. `v(π)` is the unique solution of
`∑_{j=1}^{k} x_{π_j}/μ_{π_j} = b({π_1, …, π_k})` for `k = 1, …, n`; solving the triangular system
gives the closed form used here,
`v(π)_{π_k} = μ_{π_k} · (b({π_1, …, π_k}) − b({π_1, …, π_{k−1}}))`. -/
noncomputable def v {n : ℕ} (lam mu : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  mu i * (b lam mu (AllocationIndices.lowSet π ((π.symm i : ℕ) + 1)) -
    b lam mu (AllocationIndices.lowSet π (π.symm i : ℕ)))

end MulticlassQNet.SingleStation


