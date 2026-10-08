-- Prove2me | Definitions.Def_ShadowTomography_QuantumLB_POVM
-- name    : ShadowTomography_QuantumLB_POVM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:48:27.585824+00:00
-- url     : https://prove2.me/theorems/9077ddf3-6d8c-45af-bb8c-abc146181b96
-- title:
--   Finite-outcome measurement (POVM) and the probability of an event
-- statement:
--   A **measurement with finitely many classical outcomes** on a quantum system with finite basis $n$ is a family $(\Pi_\omega)_{\omega\in\Omega}$ of positive semidefinite matrices, indexed by a finite set $\Omega$, with
--
--   $$
--   \sum_{\omega\in\Omega} \Pi_\omega = I .
--   $$
--
--   On a state $\sigma$ the outcome $\omega$ occurs with probability $\operatorname{Tr}(\Pi_\omega\sigma)$, and an event $A\subseteq\Omega$ has probability $\Pr[A] = \sum_{\omega\in A}\operatorname{Tr}(\Pi_\omega\sigma)$.
--
--   A shadow-tomography strategy using $k$ copies is such a measurement of $\rho^{\otimes k}$ together with a map assigning to each outcome the estimates $b_1,\dots,b_M$.
--
--   **Formalization Note** The probability is the real part of the trace. Classical post-processing randomness can be absorbed into $\Omega$, so deterministic outputs $b(\omega)$ lose no generality.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 2, Problem 1 ("a measurement of ρ^{⊗k}") and p. 12, Section 3 (POVM)

import Mathlib

open scoped ComplexOrder

namespace ShadowTomography.QuantumLB

/-- A measurement with finitely many classical outcomes: positive semidefinite operators,
one per outcome, summing to the identity. -/
structure POVM (Ω n : Type) [Fintype Ω] [Fintype n] [DecidableEq n] where
  op : Ω → Matrix n n ℂ
  positive : ∀ ω, (op ω).PosSemidef
  complete : ∑ ω, op ω = 1

/-- Probability that the outcome of `P` on the state `σ` lies in the event `A`. -/
noncomputable def POVM.prob {Ω n : Type} [Fintype Ω] [Fintype n] [DecidableEq n]
    (P : POVM Ω n) (σ : Matrix n n ℂ) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω ∈ Finset.univ.filter A, ((P.op ω) * σ).trace.re

end ShadowTomography.QuantumLB


