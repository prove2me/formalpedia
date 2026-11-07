-- Prove2me | Definitions.Def_QMAPlusGap_expect
-- name    : QMAPlusGap_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:20.383021+00:00
-- url     : https://prove2.me/theorems/26f47d33-8039-4eb4-b6cb-4fad323b6698
-- title:
--   Expectation $\langle\psi|B|\psi\rangle$
-- statement:
--   For an operator $B$ on $\mathbb C^{\kappa}$ and a vector $\psi$,
--   $$
--   \langle\psi|B|\psi\rangle=\sum_{a,b\in\kappa}\overline{\psi_a}\,B_{ab}\,\psi_b .
--   $$
--   It is the acceptance probability of the POVM element $B$ on the pure state $\psi$ when $\psi$ is a unit vector.
--
--   **Formalization Note** The value is complex; for Hermitian $B$ it is real, and statements compare its real part.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 8, p.14; Proposition 9, p.15; Lemma 10, p.17

import Mathlib

set_option autoImplicit false

namespace QMAPlusGap

/-- The **expectation** `⟨ψ|B|ψ⟩ = Σ_{a,b} conj(ψ_a) B_{ab} ψ_b` of an operator `B` on `ℂ^κ` in a vector `ψ`,
as in `⟨h|A|h⟩` (Lemma 8, p.14) and `⟨ψ|B|ψ⟩` (Proposition 9, p.15; Lemma 10, p.17) of Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…).

**Formalization Note** The value is complex; for Hermitian `B` it is real and the statements use its real part. -/
def expect {κ : Type} [Fintype κ] (B : Matrix κ κ ℂ) (ψ : κ → ℂ) : ℂ :=
  ∑ a, ∑ b, star (ψ a) * B a b * ψ b

end QMAPlusGap


