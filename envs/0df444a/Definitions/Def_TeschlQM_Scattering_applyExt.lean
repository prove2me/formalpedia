-- Prove2me | Definitions.Def_TeschlQM_Scattering_applyExt
-- name    : TeschlQM_Scattering_applyExt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T10:11:54.683805+00:00
-- url     : https://prove2.me/theorems/a99102e2-b1c2-49f7-9c79-c873040b4d53
-- title:
--   Value of a partially defined operator, extended by zero
-- statement:
--   For an operator $A$ with domain $\mathfrak D(A)$ and $\psi \in \mathfrak H$, `applyExt A ψ` is $A\psi$ if $\psi \in \mathfrak D(A)$ and $0$ otherwise. It lets an integrand such as $t \mapsto \|(H - H_0)\exp(\mp\mathrm itH_0)\psi\|$ be written as a function of $t$; the statements that use it assume that the vectors it is applied to lie in the domain.
--
--   **Formalization Note.** A notational device, not a definition from the book.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 249, Eq. (12.11) (notation)

import Mathlib

namespace TeschlQM.Scattering

open Classical in
/-- The value `Aψ` of a partially defined operator `A` at `ψ ∈ 𝔇(A)`, extended by `0` outside
`𝔇(A)`. In this mission it is only evaluated at vectors that the statement assumes to lie in
`𝔇(A)`, where it is `Aψ`. -/
noncomputable def applyExt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (ψ : H) : H :=
  if h : ψ ∈ A.domain then A ⟨ψ, h⟩ else 0

end TeschlQM.Scattering


