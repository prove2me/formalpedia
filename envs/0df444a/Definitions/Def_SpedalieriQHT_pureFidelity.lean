-- Prove2me | Definitions.Def_SpedalieriQHT_pureFidelity
-- name    : SpedalieriQHT_pureFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:02.949134+00:00
-- url     : https://prove2.me/theorems/cb1b98e5-9470-4e0c-9c2a-9fd3acdeeb30
-- title:
--   Fidelity $F(|\psi\rangle,\rho)=\langle\psi|\rho|\psi\rangle$ of a pure state
-- statement:
--   For a vector $\psi$ and a bounded operator $\rho$ on a complex Hilbert space, the **fidelity** between the pure state $|\psi\rangle$ and $\rho$ is
--   $$
--   F(|\psi\rangle,\rho)=\langle\psi|\rho|\psi\rangle .
--   $$
--
--   This is the squared (Uhlmann) fidelity used by the paper, following its Ref. [19]: for $\rho=|\phi\rangle\langle\phi|$ it is $|\langle\psi|\phi\rangle|^2$, as Eq. (21) states. It enters the fidelity bound (18)–(19) on the quantum Hoeffding bound.
--
--   **Formalization Note** Lean takes the real part of $\langle\psi,\rho\psi\rangle\in\mathbb C$, which is real for self-adjoint $\rho$.
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. III, Eqs. (17) and (21), p.3

import Mathlib

namespace SpedalieriQHT

/-- The fidelity `F(|ψ⟩, ρ) = ⟨ψ|ρ|ψ⟩` between a pure state `|ψ⟩` and an operator `ρ`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. III, Eq. (17), p.3 ("F is the fidelity between
|ψ0⟩ and ρ1"), and Eq. (21), p.3 (`F(|ψ0⟩, |ψ1⟩) = |⟨ψ0|ψ1⟩|²`).

**Formalization Note.** The paper follows the convention of its Ref. [19] (squared fidelity),
as (21) shows: for a pure state and a density operator this is `⟨ψ|ρ|ψ⟩`. Lean takes the real
part of `⟪ψ, ρ ψ⟫_ℂ`, which is real for self-adjoint `ρ`. -/
noncomputable def pureFidelity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (ρ : H →L[ℂ] H) : ℝ :=
  (inner ℂ ψ (ρ ψ)).re

end SpedalieriQHT


