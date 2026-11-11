-- Prove2me | Definitions.Def_QMultiMean_IsBinaryOracle
-- name    : QMultiMean_IsBinaryOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:04.147834+00:00
-- url     : https://prove2.me/theorems/35e416b1-a724-4f68-bed2-5afc203ec41a
-- title:
--   Quantum experiment $U_{\mathbb P}$ and binary oracle $\mathcal B_X$
-- statement:
--   Let $X:\Omega\to E$ be a finite random variable with probability mass function $P$, where $0\in\Omega$ and the finite value set $E$ contains $\vec 0$. Let $\mathcal H_\Omega$ and $\mathcal H_E$ be Hilbert spaces with orthonormal bases $\{|\omega\rangle\}_{\omega\in\Omega}$ and $\{|x\rangle\}_{x\in E}$.
--
--   1. A **quantum experiment** is a unitary $U_P$ on $\mathcal H_\Omega$ with
--   $$U_P:|0\rangle\mapsto\sum_{\omega\in\Omega}\sqrt{P(\omega)}\,|\omega\rangle .$$
--   Applying $U_P$ or $U_P^{-1}$ counts as one quantum experiment.
--   2. A **binary oracle** is a unitary $\mathcal B_X$ on $\mathcal H_\Omega\otimes\mathcal H_E$ with
--   $$\mathcal B_X:|\omega\rangle|\vec 0\rangle\mapsto|\omega\rangle|X(\omega)\rangle\qquad(\omega\in\Omega).$$
--
--   These two unitaries are the input of every quantum estimator in the paper. Only their action on $|0\rangle$, respectively on $|\omega\rangle|\vec0\rangle$, is specified, so the guarantees are required for every unitary with that action.
--
--   **Formalization Note** The unitaries are complex matrices indexed by $\Omega=\mathrm{Fin}(N+1)$ and by $\mathrm{Fin}(N+1)\times E$, and unitarity is part of each predicate.
-- source:
--   Cornelissen, Hamoudi, Jerbi, Near-Optimal Quantum Algorithms for Multivariate Mean Estimation, arXiv:2111.09787v2, p.7, Definitions 2.5 and 2.6

import Mathlib
import Definitions.Def_QMultiMean_FiniteRandomVariable

set_option autoImplicit false

namespace QMultiMean

/-- A **quantum experiment** for the probability mass function `P` (Cornelissen, Hamoudi, Jerbi,
arXiv:2111.09787v2, Definition 2.5, p.7): a unitary `U_P` on `H_Ω = ℂ^Ω` with
`U_P : |0⟩ ↦ Σ_{ω ∈ Ω} √P(ω) |ω⟩`, i.e. column `0` of `U_P` is `(√P(ω))_ω`.

**Formalization Note.** `Ω = Fin (N+1)` and `0 ∈ Ω` is the distinguished point the definition
assumes. Only the action on `|0⟩` is specified, so every statement of the mission quantifies over all
such unitaries. A quantum experiment is an application of `U_P` or `U_P⁻¹ = U_P†`. -/
def IsQuantumExperiment {N : ℕ} (P : Fin (N + 1) → ℝ) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Prop :=
  U ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ ∧ ∀ ω, U ω 0 = (Real.sqrt (P ω) : ℂ)

open Classical in
/-- A **binary oracle** for the finite random variable `X : Ω → E` (arXiv:2111.09787v2,
Definition 2.6, p.7): a unitary `B_X` on `H_Ω ⊗ H_E` with `B_X : |ω⟩|0⃗⟩ ↦ |ω⟩|X(ω)⟩` for all
`ω ∈ Ω`, assuming `0⃗ ∈ E`. The basis of `H_E` is indexed by the elements of the finite set `E`.

**Formalization Note.** Only the columns `(ω, 0⃗)` are specified, so every statement of the
mission quantifies over all such unitaries. A unitary with these columns exists exactly when
`X(ω) ∈ E` for every `ω`, which every statement assumes. -/
def IsBinaryOracle {N : ℕ} {V : Type} [Zero V] (E : Finset V) (h0 : (0 : V) ∈ E)
    (X : Fin (N + 1) → V) (B : Matrix (Fin (N + 1) × E) (Fin (N + 1) × E) ℂ) : Prop :=
  B ∈ Matrix.unitaryGroup (Fin (N + 1) × E) ℂ ∧
    ∀ (ω : Fin (N + 1)) (q : Fin (N + 1) × E),
      B q (ω, ⟨0, h0⟩) = if q.1 = ω ∧ (q.2 : V) = X ω then 1 else 0

end QMultiMean


