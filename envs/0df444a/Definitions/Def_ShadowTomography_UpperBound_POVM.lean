-- Prove2me | Definitions.Def_ShadowTomography_UpperBound_POVM
-- name    : ShadowTomography_UpperBound_POVM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T01:56:05.909867+00:00
-- url     : https://prove2.me/theorems/ec5d1576-beb3-4a8b-b391-da40d9548bb6
-- title:
--   Measurement with finitely many classical outcomes (POVM) and the probability of an event
-- statement:
--   A **measurement with classical outcomes** in a finite set $\Omega$ on a finite-dimensional system is a family $(P_\omega)_{\omega\in\Omega}$ of positive semidefinite matrices summing to the identity:
--
--   $$
--   P_\omega \succeq 0 \quad (\omega\in\Omega), \qquad \sum_{\omega\in\Omega} P_\omega = \mathbb 1 .
--   $$
--
--   Measuring a state $\sigma$ yields outcome $\omega$ with probability $\mathrm{Tr}(P_\omega\sigma)$ (Born rule). For an event $A\subseteq\Omega$ the probability of observing an outcome in $A$ is
--
--   $$
--   \Pr_{P,\sigma}[A] = \sum_{\omega\in A} \mathrm{Tr}(P_\omega \sigma).
--   $$
--
--   This is the object behind the phrase "do this via a measurement of $\rho^{\otimes k}$" in the shadow tomography problem: any procedure that measures the $k$ copies, possibly adaptively and with classical post-processing, and then outputs a classical answer, is described by one such POVM on $\rho^{\otimes k}$.
--
--   **Formalization Note** `POVM Ω n` is a structure with fields `op`, `psd` and `complete`; `POVM.prob P σ A` is $\sum_{\omega\in A}\mathrm{Re}\,\mathrm{Tr}(P_\omega\sigma)$, with the event given as a predicate on outcomes (decided classically).
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 2, Problem 1 ("a measurement of ρ^{⊗k}"); p. 12, Section 3 (POVM)

import Mathlib

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- A measurement with finitely many classical outcomes `Ω` on a system with basis labels `n`
(a POVM): one positive semidefinite operator per outcome, summing to the identity. -/
structure POVM (Ω n : Type) [Fintype Ω] [Fintype n] [DecidableEq n] where
  /-- The POVM element of outcome `ω`. -/
  op : Ω → Matrix n n ℂ
  /-- Every POVM element is positive semidefinite. -/
  psd : ∀ ω, (op ω).PosSemidef
  /-- The POVM elements sum to the identity. -/
  complete : ∑ ω, op ω = 1

open Classical in
/-- The probability that measuring the state `σ` with the POVM `P` yields an outcome in the
event `A` (Born rule): `∑_{ω ∈ A} Re Tr(P_ω σ)`. -/
noncomputable def POVM.prob {Ω n : Type} [Fintype Ω] [Fintype n] [DecidableEq n]
    (P : POVM Ω n) (σ : Matrix n n ℂ) (A : Ω → Prop) : ℝ :=
  ∑ ω ∈ Finset.univ.filter A, ((P.op ω) * σ).trace.re

end ShadowTomography.UpperBound


