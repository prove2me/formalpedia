-- Prove2me | Definitions.Def_KempeCloning_cre
-- name    : KempeCloning_cre
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:20.739955+00:00
-- url     : https://prove2.me/theorems/e03045e6-30c8-4a53-9805-3db6600dd44d
-- title:
--   Creation operator of a mode
-- statement:
--   For a mode $k$, the creation (raising) operator $k^\dagger$ acts on number states by
--
--   $$k^\dagger\,|n\rangle = \sqrt{n_k + 1}\;|n + e_k\rangle ,$$
--
--   where $n+e_k$ raises the occupation of mode $k$ by one, and is extended linearly to finite superpositions. It is the adjoint of the annihilation operator of the same mode.
--
--   **Formalization Note** Defined on the basis $|n\rangle$ and extended linearly (`Finsupp.linearCombination`).
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, sentence after (11), p.4

import Definitions.Def_KempeCloning_FockVec

namespace KempeCloning

/-- **The creation (raising) operator of mode `k`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, p.4: "c† is a harmonic oscillator
operator creating “e” type excitations"; `c†` and the `h.c.` part of (14) use the raising
operators of the five oscillator modes.

On number states, `cre k |n⟩ = √(n_k + 1) |n + e_k⟩`, extended linearly.

**Formalization Note.** Built with `Finsupp.linearCombination` from its action on the basis
`|n⟩ = Finsupp.single n 1`; `n + e_k` is `Function.update n k (n k + 1)`. -/
noncomputable def cre (k : Mode) : FockVec →ₗ[ℂ] FockVec :=
  Finsupp.linearCombination ℂ fun n : FockIndex =>
    ((Real.sqrt ((n k : ℝ) + 1) : ℝ) : ℂ) • Finsupp.single (Function.update n k (n k + 1)) 1

end KempeCloning


