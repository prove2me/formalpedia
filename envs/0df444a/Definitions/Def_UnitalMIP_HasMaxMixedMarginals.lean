-- Prove2me | Definitions.Def_UnitalMIP_HasMaxMixedMarginals
-- name    : UnitalMIP_HasMaxMixedMarginals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:38.449193+00:00
-- url     : https://prove2.me/theorems/28d65188-08fb-46af-8a7d-0576917e2e38
-- title:
--   Maximally mixed marginals $\psi_A=\mathbb 1/d_A$, $\psi_B=\mathbb 1/d_B$; normalized trace; entangled states
-- statement:
--   Let $\psi$ be an operator on $\mathbb C^{d_A}\otimes\mathbb C^{d_B}$, with Alice's system the first factor. Its **marginals** are the partial traces $\psi_A=\mathrm{Tr}_B\,\psi$ and $\psi_B=\mathrm{Tr}_A\,\psi$. The state $\psi$ has **maximally mixed marginals** if
--
--   $$
--   \psi_A=\frac{\mathbb 1}{d_A},\qquad \psi_B=\frac{\mathbb 1}{d_B};
--   $$
--
--   for a two-qubit state this is $\psi_A=\psi_B=\mathbb 1/2$. The module also fixes the **normalized trace** $\tau_d(X)=\frac1d\mathrm{Tr}(X)$ on $M_d$ and calls a density matrix **entangled** when it is not separable, i.e. not a finite convex combination $\sum_j w_jA_j\otimes B_j$ of product states.
--
--   Two-qubit states with maximally mixed marginals are exactly the EPR pair after unital qubit noise; they are the resources classified by the main theorem.
--
--   **Formalization Note** $\psi_A$ is `traceRight ψ` (defined here) and $\psi_B$ is the published `QAlgorithms.traceLeft ψ`. Density matrices and separability are the published `QAlgorithms.IsDensityMatrix` and `QAlgorithms.Entanglement.IsSeparableDensity`. On an empty index type $\tau_d$ is $0$.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), §1.1, p.4; §2.1, (4), p.10; Definition 2.20, p.18; Theorem 1.1, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

open scoped Matrix

namespace UnitalMIP

/-- The normalized trace `τ_d(X) := Tr(X)/d` on `M_d` (Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for
MIP* in the Presence of Unital Noise*, arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…,
§2.1, (4), p.10).

**Formalization Note** `d` is the cardinality of the index type; on an empty index type the value
is `0`. -/
noncomputable def ntr {d : Type} [Fintype d] (X : Matrix d d ℂ) : ℂ :=
  ((Fintype.card d : ℂ))⁻¹ * Matrix.trace X

/-- The partial trace over the second (Bob's) tensor factor,
`(Tr_B M)_{a a'} = ∑_b M_{(a,b),(a',b)}`: the marginal `ψ_A` of a bipartite operator
(arXiv:2609.39318, version of 2026-11-03, §2.4, p.18). -/
def traceRight {dA dB : Type} [Fintype dB] (M : Matrix (dA × dB) (dA × dB) ℂ) :
    Matrix dA dA ℂ :=
  Matrix.of fun a a' => ∑ b, M (a, b) (a', b)

/-- **Maximally mixed marginals** (arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…,
§1.1, p.4 and Definition 2.20, p.18): a bipartite operator `ψ` on `ℂ^{dA} ⊗ ℂ^{dB}` has
`ψ_A = 𝟙/d_A` and `ψ_B = 𝟙/d_B`. For a two-qubit state this is `ψ_A = ψ_B = 𝟙/2`.

**Formalization Note** `ψ_A` is `traceRight ψ` (trace over Bob) and `ψ_B` is the published
`QAlgorithms.traceLeft ψ` (trace over Alice). Alice's system is the first factor of the index type
`dA × dB`. -/
def HasMaxMixedMarginals {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : Matrix (dA × dB) (dA × dB) ℂ) : Prop :=
  traceRight ψ = ((Fintype.card dA : ℂ))⁻¹ • (1 : Matrix dA dA ℂ) ∧
    QAlgorithms.traceLeft ψ = ((Fintype.card dB : ℂ))⁻¹ • (1 : Matrix dB dB ℂ)

/-- **Entangled state** (arXiv:2609.39318, version of 2026-11-03, Theorem 1.1, p.4; Proposition
3.8, p.30): a density matrix on `ℂ^{dA} ⊗ ℂ^{dB}` that is not separable, i.e. not a finite convex
combination of product states.

**Formalization Note** Separability is the published `QAlgorithms.Entanglement.IsSeparableDensity`
(`ψ = ∑_j w_j A_j ⊗ B_j`, `w_j ≥ 0`, `∑ w_j = 1`, every `A_j`, `B_j` a density matrix), and a
density matrix is the published `QAlgorithms.IsDensityMatrix` (positive semidefinite, trace one). -/
def IsEntangled {dA dB : Type} [Fintype dA] [Fintype dB] [Nonempty dA] [Nonempty dB]
    (ψ : Matrix (dA × dB) (dA × dB) ℂ) : Prop :=
  QAlgorithms.IsDensityMatrix ψ ∧ ¬ QAlgorithms.Entanglement.IsSeparableDensity ψ

end UnitalMIP


