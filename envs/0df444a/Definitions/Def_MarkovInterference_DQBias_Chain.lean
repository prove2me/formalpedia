-- Prove2me | Definitions.Def_MarkovInterference_DQBias_Chain
-- name    : MarkovInterference_DQBias_Chain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:20.980275+00:00
-- url     : https://prove2.me/theorems/e3e1a0e1-83f9-4c57-be94-5216b01c3b3d
-- title:
--   Finite Markov-chain notation: stationary laws, total variation, row norm, and group inverse
-- statement:
--   For a finite state space $S$, a transition matrix $P$ has nonnegative entries and each row sums to one. A stationary distribution $\rho$ is a nonnegative vector of total mass one satisfying $\rho^\top P=\rho^\top$. A matrix is primitive when some power has every entry strictly positive, the finite-state form of irreducibility and aperiodicity.
--
--   The definitions use total variation and the maximum absolute row sum:
--
--   $$d_{\mathrm{TV}}(\mu,\nu)=\frac12\sum_{s\in S}|\mu(s)-\nu(s)|,\qquad \|M\|_{1,\infty}=\max_{i\in S}\sum_{j\in S}|M_{ij}|.$$
--
--   For a primitive $P$ and its stationary law $\rho$, the group inverse is represented as
--
--   $$(I-P)^\#=(I-P+\mathbf1\rho^\top)^{-1}-\mathbf1\rho^\top.$$
--
--   These notions support the perturbation identity and the mixing bound used in the bias analysis.
--
--   **Formalization Note** The formula for the group inverse is a total Lean definition; theorems using it require primitivity and a stationary probability vector. On an empty state type the row-norm supremum defaults to zero, but a stationary distribution cannot exist there.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, pp. 13–14, 28, Lemma 1 and Appendix A

import Mathlib

namespace MarkovInterference.DQBias

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A finite transition matrix has nonnegative entries and row sums one. -/
def IsStochastic (P : Matrix S S ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- A stationary probability distribution of a finite transition matrix. -/
def IsStationaryDist (P : Matrix S S ℝ) (rho : S → ℝ) : Prop :=
  (∀ s, 0 ≤ rho s) ∧ (∑ s, rho s = 1) ∧ Matrix.vecMul rho P = rho

/-- For a finite stochastic matrix, primitivity is irreducibility and aperiodicity. -/
def IsPrimitive (P : Matrix S S ℝ) : Prop :=
  ∃ k : ℕ, ∀ i j, 0 < (P ^ k) i j

/-- Total variation distance on a finite state space. -/
noncomputable def tvDist (mu nu : S → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, |mu s - nu s|

/-- The maximum absolute row sum, written `‖M‖₁,∞` in the paper. -/
noncomputable def norm1inf (M : Matrix S S ℝ) : ℝ :=
  ⨆ i, ∑ j, |M i j|

/-- The rank-one matrix `1 rhoᵀ`. -/
def onesRho (rho : S → ℝ) : Matrix S S ℝ :=
  Matrix.vecMulVec (fun _ => (1 : ℝ)) rho

/-- The group inverse `(I-P)^#` in Appendix A, when `P` is primitive. -/
noncomputable def groupInv (P : Matrix S S ℝ) (rho : S → ℝ) : Matrix S S ℝ :=
  (1 - P + onesRho rho)⁻¹ - onesRho rho

end MarkovInterference.DQBias


