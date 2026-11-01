-- Prove2me | Definitions.Def_BaconThesis_Control_StationaryControlMixed
-- name    : BaconThesis_Control_StationaryControlMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:48.862005+00:00
-- url     : https://prove2.me/theorems/423c9c0b-dd6b-4a61-9ef0-0001bd484895
-- title:
--   Commuting mixed state stationary control (Definition 3.2.2, condition (3.10))
-- statement:
--   Let $H$ be a system-apparatus Hamiltonian on $\mathcal H_S\otimes\mathcal H_A$ and $M$ a set of apparatus states. $H$ performs **mixed state stationary control** for $M$ when for every $\rho_a\in M$ there is a Hermitian system operator $H_a$ such that for every real time $t$ and every density matrix $\rho_S$ of the system
--   $$
--   U(t)\,\big(\rho_S\otimes\rho_a\big)\,U(t)^\dagger = U_a(t)\,\rho_S\,U_a(t)^\dagger\otimes\rho_a,
--   $$
--   with $U(t) = \exp[-iHt]$ and $U_a(t) = \exp[-iH_a t]$.
--
--   In the book $M$ is a commuting set of mixed states (Definition 3.2.2); the predicate is defined for any set, and the theorems state what they assume.
--
--   **Formalization Note** $H_a$ is a single Hermitian matrix for each $\rho_a$, independent of $t$ and $\rho_S$; $t$ ranges over all reals, as in the page's "$\forall t$".
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.2, Definition 3.2.2 and eq. (3.10), p.33 (PDF p.50)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_evol

open scoped Kronecker Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.2, Definition 3.2.2 (Commuting mixed state stationary control) with the condition (3.10),
p.33 (PDF p.50): a system-apparatus Hamiltonian `H` performs **mixed state stationary control**
for a set `M` of apparatus states when for every `ρ_a ∈ M` there is a Hermitian `H_a` on the system
such that for all times `t` and every system density matrix `ρ_S`,
`U(t) (ρ_S ⊗ ρ_a) U(t)† = U_a(t) ρ_S U_a(t)† ⊗ ρ_a`, with `U(t) = exp[−iHt]` and
`U_a(t) = exp[−iH_a t]`.

**Formalization Note.** The system is the first tensor factor. `t` ranges over all reals (the
page's "∀t"). `H_a` is one Hermitian matrix per `ρ_a`, independent of `t` and `ρ_S`. In the book
`M` is a commuting set of density operators; the predicate is defined for any set of matrices,
and the theorems state what they assume about `M`. -/
def StationaryControlMixed {s a : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    (H : Matrix (s × a) (s × a) ℂ) (M : Set (Matrix a a ℂ)) : Prop :=
  ∀ ρa ∈ M, ∃ Ha : Matrix s s ℂ, Ha.IsHermitian ∧
    ∀ t : ℝ, ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      evol H t * (ρ ⊗ₖ ρa) * (evol H t)ᴴ = (evol Ha t * ρ * (evol Ha t)ᴴ) ⊗ₖ ρa

end BaconThesis.Control


