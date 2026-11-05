-- Prove2me | Definitions.Def_SpedalieriQHT_pureState
-- name    : SpedalieriQHT_pureState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:01.618919+00:00
-- url     : https://prove2.me/theorems/fc6057c5-8287-44e9-a3f6-1d3c8448f134
-- title:
--   Pure-state operator $|\psi\rangle\langle\psi|$
-- statement:
--   For a vector $\psi$ of a complex Hilbert space $\mathcal H$, the **pure-state operator** is the rank-one operator
--   $$
--   |\psi\rangle\langle\psi| : x\mapsto \langle\psi|x\rangle\,\psi .
--   $$
--
--   When $\|\psi\|=1$ it is the density operator of the pure state $\psi$; the unit norm is a hypothesis of each theorem that uses it, not part of the definition.
--
--   **Formalization Note** Mathlib's `InnerProductSpace.rankOne ℂ ψ ψ`; Mathlib's inner product is conjugate-linear in its first argument, so `⟪ψ, x⟫` is $\langle\psi|x\rangle$.
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. III, Eqs. (17) and (21), p.3

import Mathlib

namespace SpedalieriQHT

/-- The pure-state operator `|ψ⟩⟨ψ|`, i.e. `x ↦ ⟨ψ|x⟩ ψ`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. III, p.3 ("ρ0 = |ψ0⟩⟨ψ0|", and in (21)
"ρ0 = |ψ0⟩⟨ψ0| and ρ1 = |ψ1⟩⟨ψ1|").

**Formalization Note.** Mathlib's `InnerProductSpace.rankOne ℂ ψ ψ`, which maps `x` to
`⟪ψ, x⟫ • ψ` (Mathlib's inner product is conjugate-linear in the first argument, so
`⟪ψ, x⟫ = ⟨ψ|x⟩`). The unit norm `‖ψ‖ = 1` that makes this a state is a hypothesis of each
theorem, not part of the definition. -/
noncomputable def pureState {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) : H →L[ℂ] H :=
  InnerProductSpace.rankOne ℂ ψ ψ

end SpedalieriQHT


