-- Prove2me | Definitions.Def_ShadowTomography_UpperBound_IsEffect
-- name    : ShadowTomography_UpperBound_IsEffect
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T01:22:53.238645+00:00
-- url     : https://prove2.me/theorems/744ffe4c-a0d6-484b-a389-af1013f8a451
-- title:
--   Two-outcome measurement: a Hermitian matrix E with all eigenvalues in [0, 1]
-- statement:
--   A **two-outcome measurement** on a $D$-dimensional quantum system is described by a $D\times D$ Hermitian matrix $E$ with all eigenvalues in $[0,1]$; in particular $E$ is positive semidefinite. Equivalently, both $E$ and $\mathbb 1 - E$ are positive semidefinite:
--
--   $$
--   0 \preceq E \preceq \mathbb 1 .
--   $$
--
--   On a mixed state $\rho$, the measurement $E$ accepts with probability $\mathrm{Tr}(E\rho)$ and rejects with probability $1-\mathrm{Tr}(E\rho)$. Such an operator is also called an *effect*: it is the accepting element of the two-element POVM $\{E, \mathbb 1 - E\}$.
--
--   Every statement of this mission about "known two-outcome measurements $E_1,\dots,E_M$" assumes each $E_i$ satisfies this predicate, and every amplified or composed test the mission constructs is required to satisfy it as well, so that its acceptance probability lies in $[0,1]$.
--
--   **Formalization Note** Operators are complex matrices `Matrix n n ℂ` over a finite index type `n`. `IsEffect E` is `E.PosSemidef ∧ (1 - E).PosSemidef`; Mathlib's `PosSemidef` includes Hermiticity, so this is exactly "Hermitian with spectrum in $[0,1]$". The acceptance probability on $\rho$ is written `((E * ρ).trace).re`, the real part of the complex trace.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 12, Section 3 (two-outcome measurement, POVM)

import Mathlib

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- A two-outcome measurement (an *effect*) on a finite-dimensional quantum system: a complex
matrix `E` with `0 ≤ E ≤ 1` in the Loewner order, i.e. `E` and `1 - E` are both positive
semidefinite. Equivalently, `E` is Hermitian with all eigenvalues in `[0, 1]`
(Aaronson, arXiv:1711.01053v2, p. 12). On a state `ρ` it accepts with probability
`((E * ρ).trace).re`. -/
def IsEffect {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

end ShadowTomography.UpperBound


