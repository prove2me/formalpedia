-- Prove2me | Definitions.Def_TeschlQM_Algebraic_opComp
-- name    : TeschlQM_Algebraic_opComp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T02:06:37.87769+00:00
-- url     : https://prove2.me/theorems/c1c81c10-d472-4707-b774-613da16c582a
-- title:
--   Product AB of unbounded operators and the kernel Ker(A)
-- statement:
--   For linear operators $A$, $B$ in a complex Hilbert space $\mathfrak H$, the **product** $AB$ has domain
--   $$\mathfrak D(AB) = \{\psi \in \mathfrak D(B) \mid B\psi \in \mathfrak D(A)\}, \qquad (AB)\psi = A(B\psi).$$
--   The **kernel** of $A$ is $\operatorname{Ker}(A) = \{\psi \in \mathfrak D(A) \mid A\psi = 0\}$.
--
--   With these, $H_0 = A^*A$ and $H_1 = AA^*$ of Theorem 8.6 are defined with their natural domains.
--
--   **Formalization Note.** `opComp A B` is a `LinearPMap` built on the domain $\{\psi \in \mathfrak D(B) \mid B\psi \in \mathfrak D(A)\}$; `opKer A` is a `Submodule ℂ H`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 180, Section 8.4

import Mathlib

namespace TeschlQM.Algebraic

/-- The product `AB` of two linear operators, with its natural domain
`𝔇(AB) = {ψ ∈ 𝔇(B) | Bψ ∈ 𝔇(A)}` and `(AB)ψ = A(Bψ)`. -/
noncomputable def opComp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H where
  domain := (Submodule.comap B.toFun A.domain).map B.domain.subtype
  toFun :=
    (A.toFun ∘ₗ
        ((B.toFun.domRestrict (Submodule.comap B.toFun A.domain)).codRestrict A.domain
          (fun x => x.2))) ∘ₗ
      (Submodule.equivMapOfInjective B.domain.subtype Subtype.val_injective
        (Submodule.comap B.toFun A.domain)).symm.toLinearMap

/-- The kernel `Ker(A) = {ψ ∈ 𝔇(A) | Aψ = 0}` of a linear operator, as a subspace of `ℌ`. -/
def opKer {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (LinearMap.ker A.toFun).map A.domain.subtype

end TeschlQM.Algebraic


