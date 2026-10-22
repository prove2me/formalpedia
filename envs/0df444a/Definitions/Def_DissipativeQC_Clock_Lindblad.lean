-- Prove2me | Definitions.Def_DissipativeQC_Clock_Lindblad
-- name    : DissipativeQC_Clock_Lindblad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:34.446586+00:00
-- url     : https://prove2.me/theorems/53a35a5f-467c-41f2-8719-9706f58ce4ec
-- title:
--   Eq. (1), p. 1 — finite dimensional purely dissipative Lindblad generator
-- statement:
--   For a finite matrix carrier and a finite family of jump matrices $L_k$, define the complex linear Lindblad generator by
--
--   $$\mathcal L(X)=\sum_k\left(L_kXL_k^\dagger-\frac12(L_k^\dagger L_kX+XL_k^\dagger L_k)\right).$$
--
--   The definition is independent of the circuit clock and can be reused for other finite dimensional dissipative processes. It contains no Hamiltonian contribution.
--
--   **Formalization Note** The carrier and jump index may be any finite types; the circuit model instantiates this general definition.
-- source:
--   Verstraete, Wolf & Cirac, Quantum computation, quantum state engineering, and quantum phase transitions driven by dissipation, arXiv:0803.1447v2, p. 1, eq. (1)

import Mathlib

noncomputable section
open scoped Matrix ComplexConjugate

namespace DissipativeQC.Clock

/-- Eq. (1): the purely dissipative Lindblad generator for any finite matrix carrier. -/
def lindbladian {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (L : J → Matrix ι ι ℂ) : Module.End ℂ (Matrix ι ι ℂ) :=
  ∑ k, ((LinearMap.mulLeft ℂ (L k)).comp (LinearMap.mulRight ℂ (L k)ᴴ)
    - (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ ((L k)ᴴ * L k) +
      LinearMap.mulRight ℂ ((L k)ᴴ * L k)))

end DissipativeQC.Clock


