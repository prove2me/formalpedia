-- Prove2me | Definitions.Def_AccessibleMaps_reducedEvolution
-- name    : AccessibleMaps_reducedEvolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:04.871005+00:00
-- url     : https://prove2.me/theorems/ce776ae6-1a1f-4476-9836-39069ab49645
-- title:
--   Reduced unitary evolution $T\mapsto\operatorname{tr}_B(UTU^\dagger)$
-- statement:
--   For a unitary $U$ on $\mathbb C^{a}\otimes\mathcal H$ ($U^\dagger U=UU^\dagger=\mathbb 1$) and an operator $T$ on the composite space, the **reduced evolution** is the $a\times a$ matrix
--   $$
--   \operatorname{tr}_B\big(U\,T\,U^\dagger\big).
--   $$
--   Applied to the extended state it gives the accessible map (22); applied to $\rho\otimes\omega$ it gives the tensor-product dynamics (6).
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (6), p.1 and Eq. (22), p.4

import Mathlib
import Definitions.Def_AccessibleMaps_trB

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Unitary evolution followed by the partial trace over the ancilla, `T ↦ tr_B (U T U†)`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (6), p.1 (PDF p.1) and Eq. (22), p.4 (PDF p.4).

**Formalization Note.** `U` is unitary on the composite space, so `U U† = U† U = 𝟙`. -/
noncomputable def reducedEvolution (U : unitary (Composite a H →L[ℂ] Composite a H))
    (T : Composite a H →L[ℂ] Composite a H) : Matrix a a ℂ :=
  trB ((U : Composite a H →L[ℂ] Composite a H) ∘L T ∘L
    ContinuousLinearMap.adjoint (U : Composite a H →L[ℂ] Composite a H))

end AccessibleMaps


