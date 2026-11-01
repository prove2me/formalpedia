-- Prove2me | Definitions.Def_WildeQIT_HSW_IsProjector
-- name    : WildeQIT_HSW_IsProjector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:11:53.823997+00:00
-- url     : https://prove2.me/theorems/82beef16-c998-4f3b-8a37-6db8fa06f0c8
-- title:
--   Projector $\Pi = \Pi^\dagger = \Pi^2$
-- statement:
--   An operator $\Pi$ on a finite-dimensional Hilbert space is a projector (an orthogonal projection onto a subspace) if
--
--   $$
--   \Pi = \Pi^\dagger \qquad\text{and}\qquad \Pi^2 = \Pi .
--   $$
--
--   The code subspace projector and the codeword subspace projectors of the packing lemma, and the typical projectors used to build them, are projectors in this sense.
--
--   **Formalization Note** Operators are complex matrices indexed by a finite type; $\Pi^\dagger$ is the conjugate transpose.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 16.5.1, p. 496 ("they project onto subspaces of H"); Lemma 16.3.1, pp. 488–489

import Mathlib

namespace WildeQIT.HSW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §3.4.3 and Lemma
16.3.1 / Corollary 16.5.1, pp. 488–489, 496 ("projectors … project onto subspaces of `H`"):
`P` is an (orthogonal) **projector**, `P = P†` and `P² = P`.

**Formalization Note.** Operators are complex matrices indexed by a finite type. -/
def IsProjector {a : Type} [Fintype a] (P : Matrix a a ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

end WildeQIT.HSW


