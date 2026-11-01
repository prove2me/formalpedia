-- Prove2me | Definitions.Def_BaconThesis_Control_StationaryControlPure
-- name    : BaconThesis_Control_StationaryControlPure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:45.821044+00:00
-- url     : https://prove2.me/theorems/337425a8-b9e6-4e81-aea2-a61b09efa87c
-- title:
--   Orthogonal pure state stationary control (Definition 3.2.1, condition (3.2))
-- statement:
--   Let $H$ be a system-apparatus Hamiltonian on $\mathcal H_S\otimes\mathcal H_A$ and $\mathcal A$ a set of apparatus vectors. $H$ performs **pure state stationary control** for $\mathcal A$ when for every $|a\rangle\in\mathcal A$ there is a Hermitian system operator $H_a$ such that for every real time $t$ and every density matrix $\rho_S$ of the system
--   $$
--   U(t)\,\big(\rho_S\otimes|a\rangle\langle a|\big)\,U(t)^\dagger = U_a(t)\,\rho_S\,U_a(t)^\dagger\otimes|a\rangle\langle a|,
--   $$
--   with $U(t) = \exp[-iHt]$ and $U_a(t) = \exp[-iH_a t]$. In words: started in $|a\rangle$, the apparatus stays in $|a\rangle$, and the system evolves unitarily under its own Hamiltonian $H_a$.
--
--   In the book $\mathcal A$ is an orthogonal set of pure states (Definition 3.2.1); the predicate is defined for any set, and the theorems state what they assume.
--
--   **Formalization Note** $H_a$ is a single Hermitian matrix for each $|a\rangle$, independent of $t$ and $\rho_S$; $t$ ranges over all reals, as in the page's "$\forall t$".
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.1, Definition 3.2.1, p.31 (PDF p.48), and eq. (3.2), p.32 (PDF p.49)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_evol

open scoped Kronecker Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.1, Definition 3.2.1 (Orthogonal pure state stationary control), p.31 (PDF p.48), with the
condition (3.2), p.32 (PDF p.49): a system-apparatus Hamiltonian `H` performs **pure state
stationary control** for a set `A` of apparatus vectors when for every `|a⟩ ∈ A` there is a
Hermitian `H_a` on the system such that for all times `t` and every system density matrix `ρ_S`,
`U(t) (ρ_S ⊗ |a⟩⟨a|) U(t)† = U_a(t) ρ_S U_a(t)† ⊗ |a⟩⟨a|`, with `U(t) = exp[−iHt]` and
`U_a(t) = exp[−iH_a t]`.

**Formalization Note.** `|a⟩⟨a|` is `vecMulVec a (star a)`; the system is the first tensor factor.
`t` ranges over all reals (the page's "∀t"). `H_a` is one Hermitian matrix per `|a⟩`, independent
of `t` and `ρ_S`. In the book `A` is an orthogonal set of pure (unit) states; the predicate is
defined for any set of vectors, and the theorems state what they assume about `A`. -/
def StationaryControlPure {s a : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    (H : Matrix (s × a) (s × a) ℂ) (A : Set (a → ℂ)) : Prop :=
  ∀ v ∈ A, ∃ Ha : Matrix s s ℂ, Ha.IsHermitian ∧
    ∀ t : ℝ, ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      evol H t * (ρ ⊗ₖ Matrix.vecMulVec v (star v)) * (evol H t)ᴴ =
        (evol Ha t * ρ * (evol Ha t)ᴴ) ⊗ₖ Matrix.vecMulVec v (star v)

end BaconThesis.Control


