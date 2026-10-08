-- Prove2me | Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant
-- name    : QuantumWalkSearch_SingularGap_Discriminant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:40:37.956985+00:00
-- url     : https://prove2.me/theorems/ec778bf2-c46b-4902-8d35-f0cd7030426e
-- title:
--   Stationary distribution π, the discriminant D(P) = diag(π)^{1/2}·P·diag(π)^{−1/2}, its singular values, and v = (√π_x) (§1.2, §2)
-- statement:
--   Let $X$ be a finite state space and $P=(p_{xy})_{x,y\in X}$ a real matrix, thought of as the transition matrix of a Markov chain ($p_{xy}$ is the probability of moving from $x$ to $y$). This module fixes the objects that the rest of the mission is about.
--
--   1. **Stationary distribution.** A vector $\pi=(\pi_x)_{x\in X}$ is a *stationary distribution* of $P$ if its coordinates are positive, sum to one, and $\pi$ is a left eigenvector of $P$ with eigenvalue $1$:
--   $$\pi_x>0\ \ (x\in X),\qquad \sum_{x\in X}\pi_x=1,\qquad \sum_{x\in X}\pi_x\,p_{xy}=\pi_y\ \ (y\in X).$$
--   2. **Discriminant matrix.** The *discriminant* of $P$ is the $X\times X$ matrix
--   $$D(P)=\operatorname{diag}(\pi)^{1/2}\cdot P\cdot\operatorname{diag}(\pi)^{-1/2},\qquad D(P)_{xy}=\frac{\sqrt{\pi_x}\,p_{xy}}{\sqrt{\pi_y}},$$
--   regarded as a complex matrix acting on the Hilbert space $\mathbb C^X$ with its standard inner product $\langle u,w\rangle=\sum_x\overline{u_x}\,w_x$.
--   3. **Singular values.** The singular values $\sigma_0\ge\sigma_1\ge\dots\ge\sigma_{|X|-1}\ge0$ of $D(P)$ are the square roots of the eigenvalues of $D(P)^\dagger D(P)$, listed in non-increasing order and repeated according to multiplicity; the sequence is continued by $\sigma_i=0$ for $i\ge|X|$.
--   4. **The vector $v$.** $v=(\sqrt{\pi_x})_{x\in X}\in\mathbb C^X$.
--
--   The discriminant is the matrix whose singular value decomposition governs the spectrum of Szegedy's quantum walk $W(P)$; when $P$ is reversible it is symmetric and has the same spectrum as $P$, but for a non-reversible chain its singular values can differ from the eigenvalues of $P$.
--
--   **Formalization Note** The stationary distribution is taken as data together with the three properties above (the Perron–Frobenius existence and uniqueness are not needed). The entry formula uses Lean's real division and square root; if some $\pi_y$ were $0$ the corresponding entry would be read as $0$, but every theorem of the mission assumes $\pi$ positive. Singular values are Mathlib's `LinearMap.singularValues` of the operator $\mathbb C^X\to\mathbb C^X$ given by $D(P)$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 2 (Section 1.2: Markov chain, stationary distribution), p. 7 (Section 2: discriminant matrix D(P)), p. 17 (Section 5: the vector v = (√π_x))

import Mathlib

open Matrix

namespace QuantumWalkSearch.SingularGap

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `π` is a stationary distribution of the transition matrix `P` (Magniez–Nayak–Roland–Santha,
§1.2, p. 2): a left eigenvector of `P` with eigenvalue `1` whose coordinates are positive and sum
to `1`. -/
structure IsStationaryDistribution (P : Matrix X X ℝ) (π : X → ℝ) : Prop where
  pos : ∀ x, 0 < π x
  sum_eq_one : ∑ x, π x = 1
  stationary : ∀ y, ∑ x, π x * P x y = π y

/-- The discriminant matrix `D(P) = diag(π)^{1/2} · P · diag(π)^{-1/2}` (§2, p. 7), as a complex
matrix: its `(x, y)` entry is `√π_x · p_{xy} / √π_y`. (When `π_y = 0` Lean's division returns `0`;
every theorem about `D(P)` assumes `π` positive, so this case never arises.) -/
noncomputable def discriminant (P : Matrix X X ℝ) (π : X → ℝ) : Matrix X X ℂ :=
  Matrix.of fun x y => ((Real.sqrt (π x) * P x y / Real.sqrt (π y) : ℝ) : ℂ)

/-- `D(P)` as a linear operator on the Hilbert space `ℂ^X` (with the standard inner product). -/
noncomputable def discriminantOp (P : Matrix X X ℝ) (π : X → ℝ) :
    EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X :=
  Matrix.toEuclideanLin (discriminant P π)

/-- The singular values of `D(P)`, in Mathlib's convention: `σ 0 ≥ σ 1 ≥ ⋯`, the first `|X|`
entries are the square roots of the eigenvalues of `D(P)† D(P)` repeated according to
multiplicity, and every later entry is `0`. -/
noncomputable def discriminantSingularValues (P : Matrix X X ℝ) (π : X → ℝ) : ℕ →₀ ℝ :=
  (discriminantOp P π).singularValues

/-- The vector `v = (√π_x)_{x ∈ X}` in `ℂ^X`. -/
noncomputable def sqrtStationary (π : X → ℝ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 fun x => ((Real.sqrt (π x) : ℝ) : ℂ)

end QuantumWalkSearch.SingularGap


