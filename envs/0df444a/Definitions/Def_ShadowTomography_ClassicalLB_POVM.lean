-- Prove2me | Definitions.Def_ShadowTomography_ClassicalLB_POVM
-- name    : ShadowTomography_ClassicalLB_POVM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:22.854984+00:00
-- url     : https://prove2.me/theorems/e05bb973-19bb-4021-8094-cb0329a848b9
-- title:
--   Finite-outcome quantum measurement and event probability
-- statement:
--   A **finite-outcome POVM** on a finite-dimensional system consists of positive semidefinite operators $P_\omega$, one for each outcome $\omega$ in a finite set $\Omega$, satisfying
--
--   $$
--   \sum_{\omega\in\Omega}P_\omega=I.
--   $$
--
--   For a state $\sigma$ and an event $A\subseteq\Omega$, its probability is $\sum_{\omega\in A}\operatorname{Tr}(P_\omega\sigma)$. The outcome may carry the entire vector of shadow-tomography estimates, so this models a general finite-output measurement procedure on the copies.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 2, Problem 1; p. 12, Section 3 (POVM)

import Mathlib

open scoped ComplexOrder

namespace ShadowTomography.ClassicalLB

/-- A finite-outcome measurement whose effects sum to the identity. -/
structure POVM (Ω n : Type) [Fintype Ω] [Fintype n] [DecidableEq n] where
  op : Ω → Matrix n n ℂ
  positive : ∀ ω, (op ω).PosSemidef
  complete : ∑ ω, op ω = 1

/-- Probability of an event among the measurement outcomes. -/
noncomputable def POVM.prob {Ω n : Type} [Fintype Ω] [Fintype n] [DecidableEq n]
    (P : POVM Ω n) (σ : Matrix n n ℂ) (A : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω ∈ Finset.univ.filter A, ((P.op ω) * σ).trace.re

end ShadowTomography.ClassicalLB


