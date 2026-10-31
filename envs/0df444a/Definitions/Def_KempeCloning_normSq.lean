-- Prove2me | Definitions.Def_KempeCloning_normSq
-- name    : KempeCloning_normSq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:30.045631+00:00
-- url     : https://prove2.me/theorems/b449b132-e958-4fdb-b933-7ee08b6c1469
-- title:
--   Squared norm $\langle\psi|\psi\rangle$ of a Fock vector
-- statement:
--   For a finite superposition $|\psi\rangle = \sum_n \psi(n)|n\rangle$ of number states,
--
--   $$\langle\psi|\psi\rangle = \sum_n |\psi(n)|^2 ,$$
--
--   since the number states are orthonormal. A state is normalized when this equals $1$.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, sentence after (19), p.5

import Definitions.Def_KempeCloning_FockVec

namespace KempeCloning

/-- **The squared norm `⟨ψ|ψ⟩` of a Fock vector.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, p.5: "|F_l⟩ is a normalized state";
the number states are orthonormal.

`normSq ψ = Σ_n |ψ(n)|²`, the sum over the (finite) support of `ψ`. -/
noncomputable def normSq (ψ : FockVec) : ℝ :=
  ∑ n ∈ ψ.support, ‖ψ n‖ ^ 2

end KempeCloning


