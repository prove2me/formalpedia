-- Prove2me | Definitions.Def_TeschlQM_MinMax_eigenspace
-- name    : TeschlQM_MinMax_eigenspace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:55:14.133681+00:00
-- url     : https://prove2.me/theorems/956900f7-d43a-423e-bf45-7cc2351ff8f3
-- title:
--   Eigenspace Ker(A − z) of an unbounded operator
-- statement:
--   For a linear operator $A$ on a complex Hilbert space $\mathfrak H$ with domain $\mathfrak D(A)$ and $z \in \mathbb C$, the **eigenspace** of $A$ at $z$ is
--   $$\operatorname{Ker}(A - z) = \{ \psi \in \mathfrak D(A) \mid A\psi = z\psi \},$$
--   regarded as a linear subspace of $\mathfrak H$. It is nonzero exactly when $z$ is an eigenvalue of $A$, and its dimension is the multiplicity of that eigenvalue.
--
--   **Formalization Note.** Defined as the image in `H` of the kernel of `A.toFun - z • A.domain.subtype` on `A.domain`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 77, Section 2.4

import Mathlib

namespace TeschlQM.MinMax

/-- Teschl, p. 77: the **eigenspace** `Ker(A − z) = {ψ ∈ 𝔇(A) | Aψ = zψ}` of the operator `A`
at `z ∈ ℂ`, as a subspace of `ℌ`. It is `{0}` unless `z` is an eigenvalue; its dimension is
the multiplicity of the eigenvalue `z`. -/
def eigenspace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  Submodule.map A.domain.subtype (LinearMap.ker (A.toFun - z • A.domain.subtype))

end TeschlQM.MinMax


