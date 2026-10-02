-- Prove2me | Definitions.Def_TeschlQM_SelfAdjoint_addScalar
-- name    : TeschlQM_SelfAdjoint_addScalar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:17:35.388857+00:00
-- url     : https://prove2.me/theorems/ea0eff36-e446-4798-9b2c-077814e4261e
-- title:
--   The operator A + z, and Ran(A + z), Ker(A + z)
-- statement:
--   For a linear operator $A$ with domain $\mathfrak{D}(A)$ and a complex number $z$, the operator $A + z$ has the same domain $\mathfrak{D}(A)$ and acts by $(A+z)\psi = A\psi + z\psi$. Its range and kernel are the subspaces
--   $$\operatorname{Ran}(A+z) = \{A\psi + z\psi \mid \psi \in \mathfrak{D}(A)\}, \qquad \operatorname{Ker}(A+z) = \{\psi \in \mathfrak{D}(A) \mid A\psi + z\psi = 0\}$$
--   of $\mathfrak{H}$. The operator $A - z$ is $A + (-z)$.
--
--   These are the ranges and kernels appearing in Lemmas 2.3 and 2.7 and in the defect spaces (2.101).
--
--   **Formalization Note.** `addScalar A z` is `(z • id) +ᵥ A`, Mathlib's sum of a total linear map and a `LinearPMap` on the latter's domain. `rangeAdd A z` and `kerAdd A z` are `Submodule ℂ H`. Applied to `A.adjoint` they give $\operatorname{Ker}(A^* + z)$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 63, Section 2.2 (notation of Lemma 2.3)

import Mathlib

namespace TeschlQM.SelfAdjoint

/-- The operator `A + z` of Teschl, for `z ∈ ℂ`: same domain `𝔇(A)`, `(A + z)ψ = Aψ + zψ`.
(Mathlib's `f +ᵥ g` adds a total linear map to a partial one on the partial one's domain.)
`A - z` is `addScalar A (-z)`. -/
noncomputable def addScalar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : H →ₗ.[ℂ] H :=
  (z • LinearMap.id : H →ₗ[ℂ] H) +ᵥ A

/-- `Ran(A + z) = {Aψ + zψ | ψ ∈ 𝔇(A)}` as a subspace of `ℌ`. -/
noncomputable def rangeAdd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  LinearMap.range (addScalar A z).toFun

/-- `Ker(A + z) = {ψ ∈ 𝔇(A) | Aψ + zψ = 0}` as a subspace of `ℌ`. -/
noncomputable def kerAdd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  (LinearMap.ker (addScalar A z).toFun).map (addScalar A z).domain.subtype

end TeschlQM.SelfAdjoint


