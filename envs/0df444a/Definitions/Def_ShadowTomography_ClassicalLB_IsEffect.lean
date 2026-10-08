-- Prove2me | Definitions.Def_ShadowTomography_ClassicalLB_IsEffect
-- name    : ShadowTomography_ClassicalLB_IsEffect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:06.873605+00:00
-- url     : https://prove2.me/theorems/16b5604e-c382-4060-b358-776b349414d6
-- title:
--   Two-outcome measurement effect
-- statement:
--   A **two-outcome measurement** on a finite-dimensional quantum system is represented by an effect $E$: a Hermitian matrix whose eigenvalues lie in $[0,1]$. Equivalently, both $E$ and $I-E$ are positive semidefinite.
--
--   On a mixed state $\rho$, the measurement accepts with probability $\operatorname{Tr}(E\rho)$. This is the measurement model used throughout the paper.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 12, Section 3, two-outcome measurement

import Mathlib

open scoped ComplexOrder

namespace ShadowTomography.ClassicalLB

/-- A two-outcome measurement effect: a Hermitian operator with eigenvalues in `[0, 1]`.
Its acceptance probability on `ρ` is `((E * ρ).trace).re`. -/
def IsEffect {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

end ShadowTomography.ClassicalLB


