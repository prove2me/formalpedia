-- Prove2me | Definitions.Def_MatrixAnalytic_Stability_QBD
-- name    : MatrixAnalytic_Stability_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:01.065711+00:00
-- url     : https://prove2.me/theorems/d89d341f-1aa6-4d4e-8bc7-7f21f4f4d9c2
-- title:
--   Homogeneous discrete-time QBD with blocks B, A₀, A₁, A₂ (6.1), the phase matrix A, the mean drift μ, and nonnegative matrices in [0, ∞]
-- statement:
--   A **quasi-birth-and-death process (QBD)** is a Markov chain on the states $(n, i)$, where $n \ge 0$ is the **level** and $i$ ranges over a set of **phases** (finite or countably infinite). The level $\ell(n)$ is the set of states $(n, i)$. Given four matrices $B, A_0, A_1, A_2$ indexed by phases, the transition matrix (6.1) is block tridiagonal:
--   $$P = \begin{bmatrix} B & A_0 & 0 & 0 & \cdots \\ A_2 & A_1 & A_0 & 0 & \cdots \\ 0 & A_2 & A_1 & A_0 & \cdots \\ \vdots & & \ddots & \ddots & \ddots \end{bmatrix}.$$
--   From level $0$ the chain moves within level $0$ according to $B$ and to level $1$ according to $A_0$; from a level $n \ge 1$ it moves up one level according to $A_0$, stays according to $A_1$, and moves down one level according to $A_2$. All other transitions have probability $0$.
--
--   The **phase matrix** is $A = A_0 + A_1 + A_2$; when $P$ is stochastic, $A$ is stochastic. For finitely many phases and a row vector $\alpha$, the **mean drift** is
--   $$\mu = \alpha A_0 \mathbf 1 - \alpha A_2 \mathbf 1 = \sum_i \alpha_i \sum_j (A_0)_{ij} - \sum_i \alpha_i \sum_j (A_2)_{ij}.$$
--
--   The file also provides arithmetic for matrices with entries in $[0, \infty]$: entrywise reading of a real matrix, products $(MM')_{ij} = \sum_k M_{ik}M'_{kj}$, powers $M^0 = I$, $M^{\nu+1} = M^\nu M$, and **irreducibility of a nonnegative matrix**: for every pair $i, j$ some power $M^t$ with $t \ge 1$ has a nonzero $(i, j)$ entry.
--
--   **Formalization Note** States are pairs in $\mathbb N \times \iota$ with an arbitrary phase type $\iota$; levels are counted from $0$ as in the book. The QBD is the function `qbdP B A₀ A₁ A₂`; that it is stochastic and irreducible (the standing assumption of the monograph, p. 130) is a hypothesis of each theorem. Values in $[0,\infty]$ (`ℝ≥0∞`) make every series of nonnegative terms meaningful, with $\infty$ for a divergent one. Irreducibility of a nonnegative matrix asks for a power $t \ge 1$, so a $1 \times 1$ zero matrix is not irreducible.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 130, Eq. (6.1); p. 152 (A = A₀ + A₁ + A₂); p. 155, Theorem 7.2.3 (μ)

import Mathlib

namespace MatrixAnalytic.Stability

noncomputable section

open scoped ENNReal

/-!
The homogeneous discrete-time QBD of §6.1 of Latouche & Ramaswami (pp. 129–130), the object of
Chapter 7: a Markov chain on the states `(n, i)`, `n ≥ 0` the level and `i` the phase, with
block-tridiagonal transition matrix (6.1). The phase set is an arbitrary type `ι` (the book allows
`m = ∞`); levels are counted from `0`.

Matrices with nonnegative entries indexed by phases are also handled with values in `ℝ≥0∞`,
where every product and every series of nonnegative terms is defined (an infinite expectation is
`⊤`, never a junk value).
-/

variable {ι : Type*}

/-- The transition matrix (6.1) of a homogeneous QBD with blocks `B, A₀, A₁, A₂`:
from level `0` the chain moves to level `0` with probabilities `B` and to level `1` with
probabilities `A₀`; from a level `n ≥ 1` it moves to level `n + 1` with probabilities `A₀`,
stays in level `n` with probabilities `A₁` and moves to level `n − 1` with probabilities `A₂`;
every other transition has probability `0`. -/
def qbdP (B A₀ A₁ A₂ : ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun x y =>
    if x.1 = 0 then
      (if y.1 = 0 then B x.2 y.2 else if y.1 = 1 then A₀ x.2 y.2 else 0)
    else
      (if y.1 = x.1 + 1 then A₀ x.2 y.2
        else if y.1 = x.1 then A₁ x.2 y.2
        else if y.1 + 1 = x.1 then A₂ x.2 y.2
        else 0)

/-- The level `ℓ(n) = {(n, 1), …, (n, m)}`. -/
def level (n : ℕ) : Set (ℕ × ι) := {x | x.1 = n}

/-- The phase matrix `A = A₀ + A₁ + A₂` (§7.2, p. 152). -/
def matA (A₀ A₁ A₂ : ι → ι → ℝ) : ι → ι → ℝ :=
  fun i j => A₀ i j + A₁ i j + A₂ i j

/-- The mean drift `μ = αA₀1 − αA₂1` of Theorem 7.2.3 (p. 155), for a row vector `α` on a finite
phase set. -/
def meanDrift [Fintype ι] (A₀ A₂ : ι → ι → ℝ) (α : ι → ℝ) : ℝ :=
  (∑ i, α i * ∑ j, A₀ i j) - ∑ i, α i * ∑ j, A₂ i j

/-- A real matrix read entrywise in `ℝ≥0∞` (used for matrices with nonnegative entries). -/
def ennMat {κ : Type*} (A : κ → κ → ℝ) : κ → κ → ℝ≥0∞ := fun i j => ENNReal.ofReal (A i j)

/-- Matrix product in `ℝ≥0∞`: `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`. -/
def matMulE {κ : Type*} (M M' : κ → κ → ℝ≥0∞) : κ → κ → ℝ≥0∞ :=
  fun i j => ∑' k, M i k * M' k j

/-- The identity matrix in `ℝ≥0∞`. -/
def matOneE {κ : Type*} [DecidableEq κ] : κ → κ → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- Matrix powers in `ℝ≥0∞`: `M⁰ = I`, `M^{ν+1} = M^ν M`. -/
def matPowE {κ : Type*} [DecidableEq κ] (M : κ → κ → ℝ≥0∞) : ℕ → κ → κ → ℝ≥0∞
  | 0 => matOneE
  | ν + 1 => matMulE (matPowE M ν) M

/-- An irreducible nonnegative matrix: for every pair of indices `i, j` some power `M^t` with
`t ≥ 1` has a nonzero `(i, j)` entry (the directed graph of the nonzero entries is strongly
connected and every index lies on a cycle). -/
def IrreducibleE {κ : Type*} [DecidableEq κ] (M : κ → κ → ℝ≥0∞) : Prop :=
  ∀ i j : κ, ∃ t : ℕ, 0 < t ∧ matPowE M t i j ≠ 0

end

end MatrixAnalytic.Stability


