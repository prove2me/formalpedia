-- Prove2me | Definitions.Def_KempeCloning_ann
-- name    : KempeCloning_ann
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:10.223099+00:00
-- url     : https://prove2.me/theorems/9254b06c-9510-4c95-8591-ac857419f916
-- title:
--   Annihilation operator of a mode
-- statement:
--   For a mode $k$, the annihilation (lowering) operator $k$ (written $a_1, a_2, b_1, b_2, c$ in the paper) acts on number states by
--
--   $$k\,|n\rangle = \sqrt{n_k}\;|n - e_k\rangle \quad (n_k \ge 1), \qquad k\,|n\rangle = 0 \quad (n_k = 0),$$
--
--   where $n-e_k$ lowers the occupation of mode $k$ by one, and is extended linearly to finite superpositions. In the paper, "$c^\dagger$ is a harmonic oscillator operator creating 'e' type excitations, while $b_1$ destroys 'g1' excitations".
--
--   **Formalization Note** Defined on the basis $|n\rangle$ and extended linearly (`Finsupp.linearCombination`). The case $n_k = 0$ is explicit, so no truncated natural-number subtraction is used.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, sentence after (11), p.4

import Definitions.Def_KempeCloning_FockVec

namespace KempeCloning

/-- **The annihilation (lowering) operator of mode `k`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, p.4: "c† is a harmonic oscillator
operator creating “e” type excitations, while b1 destroys “g1” excitations"; the operators
`c, b1, b2, a1, a2` of (14) are the lowering operators of the five oscillator modes.

On number states, `ann k |n⟩ = √(n_k) |n − e_k⟩`, and `ann k |n⟩ = 0` when `n_k = 0`; it is
extended linearly to finite superpositions.

**Formalization Note.** Built with `Finsupp.linearCombination` from its action on the basis
`|n⟩ = Finsupp.single n 1`. The case `n_k = 0` is written out explicitly, so the truncated
natural-number subtraction `n_k − 1` is never used at `n_k = 0`. -/
noncomputable def ann (k : Mode) : FockVec →ₗ[ℂ] FockVec :=
  Finsupp.linearCombination ℂ fun n : FockIndex =>
    if n k = 0 then 0
    else ((Real.sqrt (n k : ℝ) : ℝ) : ℂ) • Finsupp.single (Function.update n k (n k - 1)) 1

end KempeCloning


