-- Prove2me | Definitions.Def_KTUnitary_Synth_IsExtension
-- name    : KTUnitary_Synth_IsExtension
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:30:29.122205+00:00
-- url     : https://prove2.me/theorems/f9895a86-0b39-4b04-8c69-5e429075f747
-- title:
--   Extension of a unitary
-- statement:
--   For an $n$-qubit unitary $U$ and $N=n+a$, an $N$-qubit matrix $\bar U$ is an **$a$-qubit extension** of $U$ if $\bar U$ is unitary and
--   $$\bar U\,|\psi\rangle|0^a\rangle=(U|\psi\rangle)|0^a\rangle\qquad\text{for every }n\text{-qubit }|\psi\rangle.$$
--
--   Extensions are how the paper defines a garbage-free implementation: an algorithm must be close to some extension of $U_n$ in operator norm, so its ancillas return to $|0^a\rangle$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.1, p. 16

import Mathlib
import Definitions.Def_KTUnitary_Synth_ancPad

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Extension** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 5.1, p. 16): "If `U` is an `n`-qubit unitary, we say that an
`(n + a)`-qubit unitary `Ū` is an `a`-qubit extension of `U` if, for every `n`-qubit `|ψ⟩`,
`Ū |ψ⟩|0^a⟩ = (U |ψ⟩) |0^a⟩`."

Here `N = n + a` with `n ≤ N`: `Ū` is unitary and `Ū (ψ ⊗ 0^a) = (U ψ) ⊗ 0^a` for every vector `ψ`.

**Formalization Note** The identity is asked for every vector `ψ`, not only unit vectors; by
linearity the two are the same. -/
def IsExtension {n N : ℕ} (h : n ≤ N) (U : Matrix (Bits n) (Bits n) ℂ)
    (Ub : Matrix (Bits N) (Bits N) ℂ) : Prop :=
  Ub ∈ Matrix.unitaryGroup (Bits N) ℂ ∧ ∀ ψ : Bits n → ℂ, Ub.mulVec (ancPad h ψ) = ancPad h (U.mulVec ψ)

end KTUnitary.Synth


